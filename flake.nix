{
  description = "finalsay: dev shell with Lean (via elan), Cedar, OPA, Python, Node, and srt";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixpkgs-unstable";
    # Anthropic's Sandbox Runtime, tracking upstream main.
    # `nix flake update sandbox-runtime` moves to the latest commit;
    # to pin a release instead, use "github:anthropics/sandbox-runtime/v0.0.83".
    sandbox-runtime = {
      url = "github:anthropics/sandbox-runtime";
      flake = false;
    };
  };

  outputs = { self, nixpkgs, sandbox-runtime }:
    let
      systems = [ "aarch64-darwin" "x86_64-darwin" "aarch64-linux" "x86_64-linux" ];
      forAll = f: nixpkgs.lib.genAttrs systems (system: f nixpkgs.legacyPackages.${system});
      srtFor = pkgs: pkgs.callPackage ./nix/sandbox-runtime.nix { src = sandbox-runtime; };
    in {
      packages = forAll (pkgs: {
        sandbox-runtime = srtFor pkgs;
      });

      devShells = forAll (pkgs: {
        default = pkgs.mkShell {
          packages = [
            pkgs.elan               # reads lean-toolchain, so Lean stays pinned there
            pkgs.cedar              # cedar CLI (cedar-policy)
            pkgs.open-policy-agent  # opa
            pkgs.python3            # examples/python/check.py
            pkgs.nodejs             # examples/pi tests (runs .ts directly)
            pkgs.git                # a real git for experiments/ (not a shim)
            (srtFor pkgs)           # `srt`: Seatbelt on macOS, bubblewrap on Linux
          ];
        };
      });
    };
}
