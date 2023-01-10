{
  description = "hevm";

  inputs = {
    flake-utils.url = "github:numtide/flake-utils";
    nixpkgs.url = "github:nixos/nixpkgs";
    flake-compat = {
      url = "github:edolstra/flake-compat";
      flake = false;
    };
    solidity = {
      url = "github:ethereum/solidity/1c8745c54a239d20b6fb0f79a8bd2628d779b27e";
      flake = false;
    };
    ethereum-tests = {
      url = "github:ethereum/tests/v11.2";
      flake = false;
    };
  };

  outputs = { self, nixpkgs, flake-utils, solidity, ethereum-tests, ... }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = nixpkgs.legacyPackages.${system};
        secp256k1-static = pkgs.secp256k1.overrideAttrs (attrs: {
          configureFlags = attrs.configureFlags ++ [ "--enable-static" ];
        });
        hevmUnwrapped = (with pkgs; lib.pipe (
          haskellPackages.callCabal2nix "hevm" ./. {
            # Haskell libs with the same names as C libs...
            # Depend on the C libs, not the Haskell libs.
            # These are system deps, not Cabal deps.
            inherit secp256k1;
          })
          [
            (haskell.lib.compose.overrideCabal (old : {
              testTarget = "test";
            }))
            (haskell.lib.compose.addTestToolDepends [ solc z3 cvc5 ])
            (haskell.lib.compose.appendConfigureFlags (
              [ "--ghc-option=-O2" "-fci" ]
              ++ lib.optionals stdenv.isLinux [
                "--enable-executable-static"
                "--extra-lib-dirs=${gmp.override { withStatic = true; }}/lib"
                "--extra-lib-dirs=${secp256k1-static}/lib"
                "--extra-lib-dirs=${libff.override { enableStatic = true; }}/lib"
                "--extra-lib-dirs=${ncurses.override { enableStatic = true; }}/lib"
                "--extra-lib-dirs=${zlib.static}/lib"
                "--extra-lib-dirs=${libffi.overrideAttrs (_: { dontDisableStatic = true; })}/lib"
                "--extra-lib-dirs=${glibc}/lib"
                "--extra-lib-dirs=${glibc.static}/lib"
              ]))
            haskell.lib.dontHaddock
          ]).overrideAttrs(final: prev: {
            HEVM_SOLIDITY_REPO = solidity;
            HEVM_ETHEREUM_TESTS_REPO = ethereum-tests;
          });
        hevmWrapped = with pkgs; symlinkJoin {
          name = "hevm";
          paths = [ hevmUnwrapped ];
          buildInputs = [ makeWrapper ];
          postBuild = ''
            wrapProgram $out/bin/hevm \
              --prefix PATH : "${lib.makeBinPath ([ bash coreutils git solc z3 cvc5 ])}"
          '';
        };
      in rec {

        # --- packages ----

        packages.hevm = hevmWrapped;
        packages.hevmUnwrapped = hevmUnwrapped;
        packages.default = hevmWrapped;

        # --- apps ----

        apps.hevm = flake-utils.lib.mkApp { drv = hevmWrapped; };
        apps.default = apps.hevm;

        # --- shell ---

        devShell = with pkgs;
          let libraryPath = "${lib.makeLibraryPath [ libff secp256k1 ]}";
          in haskellPackages.shellFor {
            packages = _: [ hevmUnwrapped ];
            buildInputs = [
              z3
              cvc5
              solc
              mdbook
              yarn
              haskellPackages.cabal-install
              haskellPackages.haskell-language-server
            ];
            withHoogle = true;

            # NOTE: hacks for bugged cabal new-repl
            LD_LIBRARY_PATH = libraryPath;
            HEVM_SOLIDITY_REPO = solidity;
            HEVM_ETHEREUM_TESTS_REPO = ethereum-tests;
            shellHook = lib.optionalString stdenv.isDarwin ''
              export DYLD_LIBRARY_PATH="${libraryPath}";
            '';
          };
      }
    );
}
