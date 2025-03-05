with import (builtins.fetchTarball {
  name = "nixpkgs-lean4_10";
  url = "https://github.com/nixos/nixpkgs/archive/ccc0c2126893dd20963580b6478d1a10a4512185.tar.gz";
  sha256 ="sha256:1sm9mgz970p5mbxh8ws5xdqkb6w46di58binb4lpjfzclbxhhx70";
}) {}; mkShell {
  name = "lean 4.10";
  buildInputs = [
    lean4
    elan
  ];
}
