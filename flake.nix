{
  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
    rust-overlay.url = "github:oxalica/rust-overlay";
  };

  outputs = { self, nixpkgs, rust-overlay }:
    let
      system = "x86_64-linux";
      pkgs = import nixpkgs {
        inherit system;
        overlays = [ rust-overlay.overlays.default ];
      };
      rust-toolchain = pkgs.rust-bin.fromRustupToolchainFile ./rust-toolchain.toml;
    in
    {
      devShells.default = pkgs.mkShell {
        nativeBuildInputs = [
          rust-toolchain
          pkgs.sccache
        ];

        shellHook = ''
          export RUSTC_WRAPPER="${pkgs.sccache}/bin/sccache"
          echo "Rust development environment loaded!"
          rustc --version
          cargo --version
        '';
      };
    };
}
