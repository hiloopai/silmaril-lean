{
  description = "Silmaril development tools";

  inputs.nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";

  outputs = { nixpkgs, ... }:
    let
      systems = [ "x86_64-linux" "aarch64-linux" "x86_64-darwin" "aarch64-darwin" ];
      forAllSystems = nixpkgs.lib.genAttrs systems;
    in {
      devShells = forAllSystems (system:
        let
          pkgs = import nixpkgs { inherit system; };
          base = with pkgs; [ elan python3 nodejs_24 git gnumake clang pkg-config zlib ];
          shell = extra: pkgs.mkShell {
            packages = base ++ extra;
            shellHook = pkgs.lib.optionalString pkgs.stdenv.hostPlatform.isDarwin ''
              # Match the pinned Lean binary's static libraries after Nix's SDK setup.
              export MACOSX_DEPLOYMENT_TARGET=15.0
            '';
          };
        in {
          default = shell [ ];
          cross-test = shell (with pkgs; [ binaryen wasmtime ]);
        });
    };
}
