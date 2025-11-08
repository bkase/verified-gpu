{ pkgs, ... }:
{
  # https://devenv.sh/packages/
  packages = [
    pkgs.git
    pkgs.elan
    pkgs.nodejs_20
    pkgs.uv
    pkgs.ripgrep
    pkgs.fd
    pkgs.bun
  ];

  # Environment variables for Lean (elan will manage toolchain)
  env = {
    LEAN_PATH = ".lake/packages";
    LEAN_SRC_PATH = ".";
  };

  # https://devenv.sh/supported-languages/rust/
  languages.rust.enable = true;

  # https://devenv.sh/scripts/
  scripts.build.exec = "lake build";
  scripts.check.exec = "lean HelloWorld.lean";

  enterShell = ''
    echo "✅ Lean 4 + Mathlib4 environment loaded (elan-managed)"
    echo "Installing toolchain from lean-toolchain..."
    elan install $(cat lean-toolchain | grep -oP 'v\d+\.\d+\.\d+.*')
    lean --version
    echo "Try: lake build"
  '';
}
