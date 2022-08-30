self: super:

let
  lib = self.pkgs.lib;
  stdenv = self.pkgs.stdenv;

in rec {
  dapptoolsSrc = self.callPackage (import ./nix/dapptools-src.nix) {};

  haskellPackages =
    super.haskellPackages.override (old: {
    overrides = lib.composeExtensions (old.overrides or (_: _: {})) (
      import ./haskell.nix { inherit lib; pkgs = self;}
    );
  });

  unwrappedHaskellPackages =
    super.haskellPackages.override (old: {
    overrides = lib.composeExtensions (old.overrides or (_: _: {})) (
      import ./haskell.nix { inherit lib; pkgs = self; wrapped = false;}
    );
  });

  sharedHaskellPackages =
    super.haskellPackages.override (old: {
    overrides = lib.composeExtensions (old.overrides or (_: _: {})) (
      import ./haskell.nix { inherit lib; pkgs = self; wrapped = false; shared = true; }
    );
  });

  # experimental dapp builder, allows for easy overriding of phases
  buildDappPackage = import ./nix/build-dapp-package.nix { inherit (self) pkgs; };

  # Here we can make e.g. integration tests for Dappsys.
  dapp-tests = import ./src/dapp-tests { inherit (self) pkgs; };

  # These are tests that verify the correctness of hevm symbolic using various
  # external test suites (e.g. the solc tests)
  hevm-tests = import ./nix/hevm-tests { pkgs = self.pkgs; };

  solc = self.pkgs.runCommand "solc" { } "mkdir -p $out/bin; ln -s ${solc-static-versions.solc_0_8_6}/bin/solc-0.8.6 $out/bin/solc";

  solc-static-versions =
    let
      make-solc-drv = _: solc:
        self.callPackage (
          import ./nix/solc-static.nix {
            path    = solc.path;
            version = solc.version;
            sha256  = solc.sha256;
        }) {};
    in builtins.mapAttrs make-solc-drv
        (builtins.getAttr super.system (import ./nix/solc-static-versions.nix));

  # uses solc, z3 and cvc4 from nix
  hevm = self.pkgs.haskell.lib.justStaticExecutables self.haskellPackages.hevm;

  # uses solc, z3 and cvc4 from PATH
  hevmUnwrapped = self.pkgs.haskell.lib.justStaticExecutables self.unwrappedHaskellPackages.hevm;

  libff = self.callPackage (import ./nix/libff.nix) {};

  blade = self.pkgs.haskell.lib.justStaticExecutables self.haskellPackages.hevm;

  secp256k1 = super.secp256k1.overrideDerivation (_: {
    dontDisableStatic = true;
  });
}
