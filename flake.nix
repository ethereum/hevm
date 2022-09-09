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
        hevm = with pkgs; haskell.lib.dontHaddock ((
          haskellPackages.callCabal2nix "hevm" (./src/hevm) {
            # Haskell libs with the same names as C libs...
            # Depend on the C libs, not the Haskell libs.
            # These are system deps, not Cabal deps.
            inherit secp256k1;
          }).overrideAttrs (attrs: {
            preInstall = ''
              pwd
              ls
            '';
            postInstall = ''
              wrapProgram $out/bin/hevm --prefix PATH \
                : "${lib.makeBinPath ([ bash coreutils git solc ])}"
            '';

            buildInputs = attrs.buildInputs ++ [ solc z3 cvc4 ];
            nativeBuildInputs = attrs.nativeBuildInputs ++ [ makeWrapper ];
            configureFlags = attrs.configureFlags ++ [
              "--ghc-option=-O2"
              "--enable-static"
              (lib.optionalString stdenv.isLinux "--enable-executable-static")
              "--extra-lib-dirs=${gmp.override { withStatic = true; }}/lib"
              "--extra-lib-dirs=${secp256k1-static}/lib"
              "--extra-lib-dirs=${libff}/lib"
              "--extra-lib-dirs=${ncurses.override { enableStatic = true; }}/lib"
              "--extra-lib-dirs=${zlib.static}/lib"
              "--extra-lib-dirs=${libffi.overrideAttrs (old: { dontDisableStatic = true; })}/lib"
            ] ++ lib.optionals stdenv.isDarwin [
              "--extra-lib-dirs=${libiconv}/lib"
              "--extra-lib-dirs=${libiconv.override { enableStatic = true; }}/lib"
            ] ++ lib.optionals stdenv.isLinux [
              "--extra-lib-dirs=${glibc}/lib"
              "--extra-lib-dirs=${glibc.static}/lib"
            ];
          }));
      in rec {

        # --- packages ----

        packages.hevm = hevm;
        defaultPackage = hevm;

        # --- apps ----

        apps.hevm = flake-utils.lib.mkApp { drv = hevm; };
        defaultApp = apps.hevm;

        # --- shell ---

        devShell = with pkgs;
          let
            # libff is static on Linux, ghci needs dynamic
            libff-dynamic = pkgs.libff.overrideAttrs (_: {
              postPatch = ''substituteInPlace libff/CMakeLists.txt --replace "STATIC" "SHARED"'';
            });
            libraryPath = "${lib.makeLibraryPath [ libff-dynamic secp256k1 ]}";
          in haskellPackages.shellFor {
            packages = _: [
              packages.hevm
            ];
            buildInputs = [
              z3
              cvc4
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
