{
  description = "HEVM";

  inputs = {
    flake-utils.url = "github:numtide/flake-utils";
    nixpkgs.url = "github:nixos/nixpkgs/nixos-22.05";
    flake-compat = {
      url = "github:edolstra/flake-compat";
      flake = false;
    };
  };

  outputs = { self, nixpkgs, flake-utils, ... }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = nixpkgs.legacyPackages.${system};
        secp256k1-static = pkgs.secp256k1.overrideAttrs (attrs: {
          configureFlags = attrs.configureFlags ++ [ "--enable-static" ];
        });
        hevm = with pkgs; lib.pipe (
          haskellPackages.callCabal2nix "hevm" ./src/hevm {
            # Haskell libs with the same names as C libs...
            # Depend on the C libs, not the Haskell libs.
            # These are system deps, not Cabal deps.
            inherit secp256k1;
          })
          [
            (haskell.lib.compose.addTestToolDepends [ solc z3 cvc5 ])
            (haskell.lib.compose.appendConfigureFlags (
              [ "--ghc-option=-O2" ]
              ++ lib.optionals stdenv.isLinux [
                "--enable-executable-static"
                "--extra-lib-dirs=${gmp.override { withStatic = true; }}/lib"
                "--extra-lib-dirs=${secp256k1-static}/lib"
                "--extra-lib-dirs=${libff}/lib"
                "--extra-lib-dirs=${ncurses.override { enableStatic = true; }}/lib"
                "--extra-lib-dirs=${zlib.static}/lib"
                "--extra-lib-dirs=${libffi.overrideAttrs (_: { dontDisableStatic = true; })}/lib"
                "--extra-lib-dirs=${glibc}/lib"
                "--extra-lib-dirs=${glibc.static}/lib"
              ]))
            haskell.lib.dontHaddock
          ];
        hevmWrapped = with pkgs; symlinkJoin {
          name = "hevm";
          paths = [ hevm ];
          buildInputs = [ makeWrapper ];
          postBuild = ''
            wrapProgram $out/bin/hevm \
              --prefix PATH : "${lib.makeBinPath ([ bash coreutils git solc ])}"
          '';
        };
      in rec {

        # --- packages ----

        packages.hevm = hevmWrapped;
        packages.default = hevmWrapped;

        # --- apps ----

        apps.hevm = flake-utils.lib.mkApp { drv = hevmWrapped; };
        apps.default = apps.hevm;

        # --- shell ---

        devShell = with pkgs;
          let
            # libff is static on Linux, ghci needs dynamic
            libff-dynamic = pkgs.libff.overrideAttrs (_: {
              postPatch = ''substituteInPlace libff/CMakeLists.txt --replace "STATIC" "SHARED"'';
            });
            libraryPath = "${lib.makeLibraryPath [ libff-dynamic secp256k1 ]}";
          in haskellPackages.shellFor {
            packages = _: [ hevm ];
            buildInputs = [
              z3
              cvc5
              solc
              haskellPackages.cabal-install
              haskellPackages.haskell-language-server
            ];
            withHoogle = true;

            # NOTE: hacks for bugged cabal new-repl
            LD_LIBRARY_PATH = libraryPath;
            shellHook = lib.optionalString stdenv.isDarwin ''
              export DYLD_LIBRARY_PATH="${libraryPath}";
            '';
          };
      }
    );
}
