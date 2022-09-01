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
        dontCheck = x: y:
          pkgs.haskell.lib.dontCheck
            (pkgs.haskellPackages.callCabal2nix x y {});
      in rec {

        # --- packages ----

        packages = flake-utils.lib.flattenTree {
          libff = pkgs.callPackage (import ./nix/libff.nix) {};
          hevm = pkgs.haskell.lib.dontHaddock ((
            pkgs.haskellPackages.callCabal2nix "hevm" (./src/hevm) {
              # Haskell libs with the same names as C libs...
              # Depend on the C libs, not the Haskell libs.
              # These are system deps, not Cabal deps.
              inherit (pkgs) secp256k1;
            }
          ).overrideAttrs (attrs: {
            postInstall = ''
                wrapProgram $out/bin/hevm --prefix PATH \
                  : "${pkgs.lib.makeBinPath (with pkgs; [bash coreutils git solc])}"
              '';

            enableSeparateDataOutput = true;
            buildInputs = attrs.buildInputs ++ [
              pkgs.solc
              pkgs.z3
              pkgs.cvc4
            ];
            nativeBuildInputs = attrs.nativeBuildInputs ++ [pkgs.makeWrapper];
            configureFlags = attrs.configureFlags ++ [
                "--ghc-option=-O2"
                "--enable-static"
                "--enable-executable-static"
                "--extra-lib-dirs=${pkgs.gmp.static}/lib"
                "--extra-lib-dirs=${pkgs.glibc}/lib"
                "--extra-lib-dirs=${pkgs.glibc.static}/lib"
                "--extra-lib-dirs=${packages.libff.override { enableStatic = true; }}/lib"
                "--extra-lib-dirs=${pkgs.ncurses.override {enableStatic = true; }}/lib"
                "--extra-lib-dirs=${pkgs.zlib.static}/lib"
                "--extra-lib-dirs=${pkgs.libffi.overrideAttrs (old: { dontDisableStatic = true; })}/lib"
            ];
          }));
        };
        defaultPackage = packages.hevm;

        # --- apps ----

        apps.hevm = flake-utils.lib.mkApp { drv = packages.hevm; };
        defaultApp = apps.hevm;

        # --- shell ---

        devShell = (pkgs.haskellPackages.shellFor {
          packages = _: [
            packages.hevm
          ];
          buildInputs = with pkgs.haskellPackages; [
            pkgs.z3
            pkgs.cvc4
            cabal-install
            haskell-language-server
          ];
          withHoogle = true;
        }).overrideAttrs (_: {
          LD_LIBRARY_PATH = "${pkgs.secp256k1}/lib:${pkgs.libff}/lib";
        });
      }
    );
}
