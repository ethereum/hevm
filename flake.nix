{
  description = "hevm";

  inputs = {
    flake-utils.url = "github:numtide/flake-utils";
    nixpkgs.url = "github:nixos/nixpkgs";
    # nixpkgs with working solc
    nixpkgs-solc.url = "github:nixos/nixpkgs/1b71def42b74811323de2df52f180b795ec506fc";
    foundry.url = "github:shazow/foundry.nix/monthly";
    flake-compat = {
      url = "github:edolstra/flake-compat";
      flake = false;
    };
    solidity = {
      url = "github:ethereum/solidity/1c8745c54a239d20b6fb0f79a8bd2628d779b27e";
      flake = false;
    };
    ethereum-tests = {
      url = "github:ethereum/tests/v12.2";
      flake = false;
    };
  };

  outputs = { self, nixpkgs, nixpkgs-solc, flake-utils, solidity, ethereum-tests, foundry, ... }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = nixpkgs.legacyPackages.${system};
        solc' = nixpkgs-solc.legacyPackages.${system}.solc;
        testDeps = with pkgs; [
          go-ethereum
          solc'
          z3
          cvc5
          git
        ] ++ lib.optionals (!stdenv.isDarwin) [
          foundry.defaultPackage.${system}
        ];

        secp256k1-static = stripDylib (pkgs.secp256k1.overrideAttrs (attrs: {
          configureFlags = attrs.configureFlags ++ [ "--enable-static" ];
        }));

        patchedHaskellPackages = pkgs.haskell.packages.ghc94.override {
          overrides = self: super: {
            # disable tests in optics
            optics-core = pkgs.haskell.lib.dontCheck (self.callCabal2nix "optics-core" (pkgs.fetchFromGitHub {
              owner = "well-typed";
              repo = "optics";
              rev = "46b03019bd7d9eddb767b19a68b94125eec3b17a";
              sha256 = "sha256-wzZ/64G7nVAzIFjKNs/jBvv6gQdTIQS4X/OvM5KWfnU=";
            } + "/optics-core") {});
            optics = pkgs.haskell.lib.dontCheck (self.callCabal2nix "optics" (pkgs.fetchFromGitHub {
              owner = "well-typed";
              repo = "optics";
              rev = "46b03019bd7d9eddb767b19a68b94125eec3b17a";
              sha256 = "sha256-wzZ/64G7nVAzIFjKNs/jBvv6gQdTIQS4X/OvM5KWfnU=";
            } + "/optics") {});
            indexed-profunctors = pkgs.haskell.lib.dontCheck (self.callCabal2nix "optics" (pkgs.fetchFromGitHub {
              owner = "well-typed";
              repo = "optics";
              rev = "46b03019bd7d9eddb767b19a68b94125eec3b17a";
              sha256 = "sha256-wzZ/64G7nVAzIFjKNs/jBvv6gQdTIQS4X/OvM5KWfnU=";
            } + "/indexed-profunctors") {});
            # use obsidian systems fork of string-qq
            string-qq = self.callCabal2nix "string-qq" (pkgs.fetchFromGitHub {
              owner = "obsidiansystems";
              repo = "string-qq";
              rev = "82ad6d72b694dc61e9b6b7eb856cb2d3d27e2865";
              sha256 = "sha256-CNtB8jkNyNBR+ZJbtLoeA6U1ivT3gEs4UVFVHIZe27w=";
            }) {};
          };
        };

        hevmUnwrapped = (with pkgs; lib.pipe (
          patchedHaskellPackages.callCabal2nix "hevm" ./. {
            # Haskell libs with the same names as C libs...
            # Depend on the C libs, not the Haskell libs.
            # These are system deps, not Cabal deps.
            inherit secp256k1;
          })
          [
            (haskell.lib.compose.overrideCabal (old: { testTarget = "test"; }))
            (haskell.lib.compose.addTestToolDepends testDeps)
            (haskell.lib.compose.appendBuildFlags ["-v3"])
            (haskell.lib.compose.appendConfigureFlags (
              [ "-fci"
                "-O2"
                "--extra-lib-dirs=${stripDylib (pkgs.gmp.override { withStatic = true; })}/lib"
                "--extra-lib-dirs=${stripDylib secp256k1-static}/lib"
                "--extra-lib-dirs=${stripDylib (libff.override { enableStatic = true; })}/lib"
                "--extra-lib-dirs=${zlib.static}/lib"
                "--extra-lib-dirs=${stripDylib (libffi.overrideAttrs (_: { dontDisableStatic = true; }))}/lib"
                "--extra-lib-dirs=${stripDylib (ncurses.override { enableStatic = true; })}/lib"
              ]
              ++ lib.optionals stdenv.isLinux [
                "--enable-executable-static"
                # TODO: replace this with musl: https://stackoverflow.com/a/57478728
                "--extra-lib-dirs=${glibc}/lib"
                "--extra-lib-dirs=${glibc.static}/lib"
              ]))
            haskell.lib.dontHaddock
            haskell.lib.doJailbreak
          ]).overrideAttrs(final: prev: {
            HEVM_SOLIDITY_REPO = solidity;
            HEVM_ETHEREUM_TESTS_REPO = ethereum-tests;
            DAPP_SOLC = "${solc'}/bin/solc";
          });

        # wrapped binary for use on systems with nix available. ensures all
        # required runtime deps are available and on path
        hevmWrapped = with pkgs; symlinkJoin {
          name = "hevm";
          paths = [ (haskell.lib.dontCheck hevmUnwrapped) ];
          buildInputs = [ makeWrapper ];
          postBuild = ''
            wrapProgram $out/bin/hevm \
              --prefix PATH : "${lib.makeBinPath ([ bash coreutils git solc' z3 cvc5 ])}"
          '';
        };

        # "static" binary for distribution
        # on linux this is actually a real fully static binary
        # on macos this has everything except libcxx, libsystem and libiconv
        # statically linked. we can be confident that these three will always
        # be provided in a well known location by macos itself.
        hevmRedistributable = let
          grep = "${pkgs.gnugrep}/bin/grep";
          otool = "${pkgs.darwin.binutils.bintools}/bin/otool";
          install_name_tool = "${pkgs.darwin.binutils.bintools}/bin/install_name_tool";
        in if pkgs.stdenv.isLinux
        then pkgs.haskell.lib.dontCheck hevmUnwrapped
        else pkgs.runCommand "stripNixRefs" {} ''
          mkdir -p $out/bin
          cp ${pkgs.haskell.lib.dontCheck hevmUnwrapped}/bin/hevm $out/bin/

          # get the list of dynamic libs from otool and tidy the output
          libs=$(${otool} -L $out/bin/hevm | tail -n +2 | sed 's/^[[:space:]]*//' | cut -d' ' -f1)

          # get the paths for libcxx and libiconv
          cxx=$(echo "$libs" | ${grep} '^/nix/store/.*-libcxx')
          iconv=$(echo "$libs" | ${grep} '^/nix/store/.*-libiconv')

          # rewrite /nix/... library paths to point to /usr/lib
          chmod 777 $out/bin/hevm
          ${install_name_tool} -change "$cxx" /usr/lib/libc++.1.dylib $out/bin/hevm
          ${install_name_tool} -change "$iconv" /usr/lib/libiconv.dylib $out/bin/hevm
          chmod 555 $out/bin/hevm
        '';

        # if we pass a library folder to ghc via --extra-lib-dirs that contains
        # only .a files, then ghc will link that library statically instead of
        # dynamically (even if --enable-executable-static is not passed to cabal).
        # we use this trick to force static linking of some libraries on macos.
        stripDylib = drv : pkgs.runCommand "${drv.name}-strip-dylibs" {} ''
          mkdir -p $out
          mkdir -p $out/lib
          cp -r ${drv}/* $out/
          rm -rf $out/**/*.dylib
        '';

      in rec {

        # --- packages ----

        packages.withTests = hevmUnwrapped;
        packages.noTests = pkgs.haskell.lib.dontCheck hevmUnwrapped;
        packages.hevm = hevmWrapped;
        packages.redistributable = hevmRedistributable;
        packages.default = packages.hevm;

        # --- apps ----

        apps.hevm = flake-utils.lib.mkApp { drv = packages.hevm; };
        apps.default = apps.hevm;

        # --- shell ---

        devShell = with pkgs;
          let libraryPath = "${lib.makeLibraryPath [ libff secp256k1 gmp ]}";
          in patchedHaskellPackages.shellFor {
            packages = _: [ hevmUnwrapped ];
            buildInputs = [
              mdbook
              yarn
              go-ethereum
              patchedHaskellPackages.cabal-install
              patchedHaskellPackages.haskell-language-server
            ] ++ testDeps;
            withHoogle = true;

            # NOTE: hacks for bugged cabal new-repl
            LD_LIBRARY_PATH = libraryPath;
            HEVM_SOLIDITY_REPO = solidity;
            DAPP_SOLC = "${solc'}/bin/solc";
            HEVM_ETHEREUM_TESTS_REPO = ethereum-tests;
            shellHook = lib.optionalString stdenv.isDarwin ''
              export DYLD_LIBRARY_PATH="${libraryPath}";
            '';
          };
      }
    );
}
