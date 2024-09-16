{
  description = "hevm";

  inputs = {
    flake-utils.url = "github:numtide/flake-utils";
    nixpkgs.url = "github:nixos/nixpkgs/nixpkgs-unstable";
    foundry.url = "github:shazow/foundry.nix/47f8ae49275eeff9bf0526d45e3c1f76723bb5d3";
    flake-compat = {
      url = "github:edolstra/flake-compat";
      flake = false;
    };
    solidity = {
      url = "github:ethereum/solidity/8a97fa7a1db1ec509221ead6fea6802c684ee887";
      flake = false;
    };
    ethereum-tests = {
      url = "github:ethereum/tests/v13";
      flake = false;
    };
    forge-std = {
      url = "github:foundry-rs/forge-std";
      flake = false;
    };
    solc-pkgs = {
      url = "github:hellwolf/solc.nix";
      inputs.nixpkgs.follows = "nixpkgs";
    };
  };

  outputs = { self, nixpkgs, flake-utils, solidity, forge-std, ethereum-tests, foundry, solc-pkgs, ... }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = (import nixpkgs {
          inherit system;
          overlays = [solc-pkgs.overlay];
          config = { allowBroken = true; };
        });
        solc = (solc-pkgs.mkDefault pkgs pkgs.solc_0_8_26);
        testDeps = with pkgs; [
          go-ethereum
          solc
          z3_4_12
          cvc5
          git
          bitwuzla
          foundry.defaultPackage.${system}
        ];

        secp256k1-static = stripDylib (pkgs.secp256k1.overrideAttrs (attrs: {
          configureFlags = attrs.configureFlags ++ [ "--enable-static" ];
        }));

        hsPkgs = ps :
          ps.haskellPackages.override {
            overrides = hfinal: hprev: {
              with-utf8 =
                if (with ps.stdenv; hostPlatform.isDarwin && hostPlatform.isx86)
                then ps.haskell.lib.compose.overrideCabal (_ : { extraLibraries = [ps.libiconv]; }) hprev.with-utf8
                else hprev.with-utf8;
              # TODO: temporary fix for static build which is still on 9.4
              witch = ps.haskell.lib.doJailbreak hprev.witch;
            };
          };

        hevmBase = ps :
          ((hsPkgs ps).callCabal2nix "hevm" ./. {
            # Haskell libs with the same names as C libs...
            # Depend on the C libs, not the Haskell libs.
            # These are system deps, not Cabal deps.
            secp256k1 = ps.secp256k1;
          }).overrideAttrs(final: prev: {
            HEVM_SOLIDITY_REPO = solidity;
            HEVM_ETHEREUM_TESTS_REPO = ethereum-tests;
            HEVM_FORGE_STD_REPO = forge-std;
            DAPP_SOLC = "${solc}/bin/solc";
          });

        hevmUnwrapped = let
            ps = if pkgs.stdenv.isDarwin then pkgs else pkgs.pkgsStatic;
          in (with ps; lib.pipe
            (hevmBase ps)
            [
              (haskell.lib.compose.overrideCabal (old: { testTarget = "test"; }))
              (haskell.lib.compose.addTestToolDepends testDeps)
              (haskell.lib.compose.appendConfigureFlags (
                [ "-fci"
                  "-O2"
                ]
                ++ lib.optionals stdenv.isDarwin
                [ "--extra-lib-dirs=${stripDylib (pkgs.gmp.override { withStatic = true; })}/lib"
                  "--extra-lib-dirs=${stripDylib secp256k1-static}/lib"
                  "--extra-lib-dirs=${stripDylib (libff.override { enableStatic = true; })}/lib"
                  "--extra-lib-dirs=${zlib.static}/lib"
                  "--extra-lib-dirs=${stripDylib (libffi.overrideAttrs (_: { dontDisableStatic = true; }))}/lib"
                  "--extra-lib-dirs=${stripDylib (ncurses.override { enableStatic = true; })}/lib"
                ]))
              haskell.lib.compose.dontHaddock
              haskell.lib.compose.doCheck
          ]);

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
          cxx=$(echo "$libs" | ${grep} '^/nix/store/.*/libc++\.')
          cxxabi=$(echo "$libs" | ${grep} '^/nix/store/.*/libc++abi\.')
          iconv=$(echo "$libs" | ${grep} '^/nix/store/.*/libiconv\.')

          # rewrite /nix/... library paths to point to /usr/lib
          chmod 777 $out/bin/hevm
          ${install_name_tool} -change "$cxx" /usr/lib/libc++.1.dylib $out/bin/hevm
          ${install_name_tool} -change "$cxxabi" /usr/lib/libc++abi.dylib $out/bin/hevm
          ${install_name_tool} -change "$iconv" /usr/lib/libiconv.dylib $out/bin/hevm
          # check that no nix deps remain
          nixdeps=$(${otool} -L $out/bin/hevm | tail -n +2 | { ${grep} /nix/store -c || test $? = 1; })
          if [ ! "$nixdeps" = "0" ]; then
            echo "Nix deps remain in redistributable binary!"
            exit 255
          fi
          # re-sign binary
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

        devShells.default = with pkgs; let
          libraryPath = "${lib.makeLibraryPath [ libff secp256k1 gmp ]}";
        in haskellPackages.shellFor {
          packages = _: [ (hevmBase pkgs) ];
          buildInputs = [
            curl
            haskellPackages.cabal-install
            mdbook
            yarn
            haskellPackages.eventlog2html
            haskellPackages.haskell-language-server
          ] ++ testDeps;
          withHoogle = true;

          # hevm tests expect these to be set
          HEVM_SOLIDITY_REPO = solidity;
          DAPP_SOLC = "${solc}/bin/solc";
          HEVM_ETHEREUM_TESTS_REPO = ethereum-tests;
          HEVM_FORGE_STD_REPO = forge-std;

          # point cabal repl to system deps
          LD_LIBRARY_PATH = libraryPath;
          shellHook = lib.optionalString stdenv.isDarwin ''
            export DYLD_LIBRARY_PATH="${libraryPath}";
          '';
        };
      }
    );
}
