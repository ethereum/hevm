{
  description = "hevm";

  inputs = {
    flake-utils.url = "github:numtide/flake-utils";
    nixpkgs.url = "github:nixos/nixpkgs/nixpkgs-unstable";
    foundry.url = "github:shazow/foundry.nix/monthly";
    bitwuzla-pkgs.url = "github:d-xo/nixpkgs/94e802bce3a1bc05b3acfc5e876de15fd2ecb564";
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
    cabal-head = {
      url = "github:haskell/cabal";
      flake = false;
    };
    forge-std = {
      url = "github:foundry-rs/forge-std";
      flake = false;
    };
  };

  outputs = { self, nixpkgs, flake-utils, solidity, forge-std, ethereum-tests, foundry, cabal-head, bitwuzla-pkgs, ... }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = (import nixpkgs { inherit system; config = { allowBroken = true; }; });
        bitwuzla = (import bitwuzla-pkgs { inherit system; }).bitwuzla;
        testDeps = with pkgs; [
          go-ethereum
          solc
          z3
          cvc5
          git
          bitwuzla
          foundry.defaultPackage.${system}
        ];

        # custom package set capable of building latest (unreleased) `cabal-install`.
        # This gives us support for multiple home units in cabal repl
        cabal-multi-pkgs = pkgs.haskell.packages.ghc94.override {
          overrides = with pkgs.haskell.lib; self: super: rec {
            cabal-install = dontCheck (self.callCabal2nix "cabal-install" "${cabal-head}/cabal-install" {});
            cabal-install-solver = dontCheck (self.callCabal2nix "cabal-install-solver" "${cabal-head}/cabal-install-solver" {});
            Cabal-described = dontCheck (self.callCabal2nix "Cabal-described" "${cabal-head}/Cabal-described" {});
            Cabal-QuickCheck = dontCheck (self.callCabal2nix "Cabal-QuickCheck" "${cabal-head}/Cabal-QuickCheck" {});
            Cabal-tree-diff = dontCheck (self.callCabal2nix "Cabal-tree-diff" "${cabal-head}/Cabal-tree-diff" {});
            Cabal-syntax = dontCheck (self.callCabal2nix "Cabal-syntax" "${cabal-head}/Cabal-syntax" {});
            Cabal = dontCheck (self.callCabal2nix "Cabal" "${cabal-head}/Cabal" {});
            unix = dontCheck (doJailbreak super.unix_2_8_1_1);
            filepath = dontCheck (doJailbreak super.filepath_1_4_100_4);
            process = dontCheck (doJailbreak super.process_1_6_17_0);
            directory = dontCheck (doJailbreak (super.directory_1_3_7_1));
            tasty = dontCheck (doJailbreak super.tasty);
            QuickCheck = dontCheck (doJailbreak super.QuickCheck);
            hashable = dontCheck (doJailbreak super.hashable);
            async = dontCheck (doJailbreak super.async);
            hspec-meta = dontCheck (doJailbreak super.hspec-meta);
            hpc = dontCheck (doJailbreak super.hpc);
            ghci = dontCheck (doJailbreak super.ghci);
            ghc-boot = dontCheck (doJailbreak super.ghc-boot);
            setenv = dontCheck (doJailbreak super.setenv);
            vector = dontCheck (doJailbreak super.vector);
            network-uri = dontCheck (doJailbreak super.network-uri);
            aeson = dontCheck (doJailbreak super.aeson);
            th-compat = dontCheck (doJailbreak super.th-compat);
            safe-exceptions = dontCheck (doJailbreak super.safe-exceptions);
            bifunctors = dontCheck (doJailbreak super.bifunctors);
            base-compat-batteries = dontCheck (doJailbreak super.base-compat-batteries);
            distributative = dontCheck (doJailbreak super.distributative);
            semialign = dontCheck (doJailbreak super.semialign);
            semigroupoids = dontCheck (doJailbreak super.semigroupoids);
            hackage-security = dontCheck (doJailbreak super.hackage-security);
          };
        };

        secp256k1-static = stripDylib (pkgs.secp256k1.overrideAttrs (attrs: {
          configureFlags = attrs.configureFlags ++ [ "--enable-static" ];
        }));

        hevmUnwrapped = (with pkgs; lib.pipe (
          haskellPackages.callCabal2nix "hevm" ./. {
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
          ]).overrideAttrs(final: prev: {
            HEVM_SOLIDITY_REPO = solidity;
            HEVM_ETHEREUM_TESTS_REPO = ethereum-tests;
            HEVM_FORGE_STD_REPO = forge-std;
            DAPP_SOLC = "${pkgs.solc}/bin/solc";
          });

        # wrapped binary for use on systems with nix available. ensures all
        # required runtime deps are available and on path
        hevmWrapped = with pkgs; symlinkJoin {
          name = "hevm";
          paths = [ (haskell.lib.dontCheck hevmUnwrapped) ];
          buildInputs = [ makeWrapper ];
          postBuild = ''
            wrapProgram $out/bin/hevm \
              --prefix PATH : "${lib.makeBinPath ([ bash coreutils git solc z3 cvc5 bitwuzla ])}"
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
          codesign_allocate = "${pkgs.darwin.binutils.bintools}/bin/codesign_allocate";
          codesign = "${pkgs.darwin.sigtool}/bin/codesign";
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
          CODESIGN_ALLOCATE=${codesign_allocate} ${codesign} -f -s - $out/bin/hevm
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

        packages.ci = with pkgs.haskell.lib; doBenchmark (dontHaddock (disableLibraryProfiling hevmUnwrapped));
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
          in haskellPackages.shellFor {
            packages = _: [ hevmUnwrapped ];
            buildInputs = [
              # cabal from nixpkgs
              # haskellPackages.cabal-install
              cabal-multi-pkgs.cabal-install
              mdbook
              yarn
              haskellPackages.eventlog2html
              haskellPackages.haskell-language-server
            ] ++ testDeps;
            withHoogle = true;

            HEVM_SOLIDITY_REPO = solidity;
            DAPP_SOLC = "${pkgs.solc}/bin/solc";
            HEVM_ETHEREUM_TESTS_REPO = ethereum-tests;
            HEVM_FORGE_STD_REPO = forge-std;

            # NOTE: hacks for bugged cabal new-repl
            LD_LIBRARY_PATH = libraryPath;
            shellHook = lib.optionalString stdenv.isDarwin ''
              export DYLD_LIBRARY_PATH="${libraryPath}";
            '';
          };
      }
    );
}
