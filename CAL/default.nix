let pkgs =import <nixpkgs> {}; 
in
with pkgs;

stdenv.mkDerivation {
  name = "certikos";

  buildInputs = with ocamlPackages; [
    ocaml menhir findlib coq_8_6
  ];

}
