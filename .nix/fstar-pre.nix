{ lib, stdenv, version }:

stdenv.mkDerivation {
  pname = "fstar-pre";
  inherit version;

  src = ./..;

  buildPhase = "true";

  installPhase = ''
    mkdir -p $out/lib/fstar
    cp version.txt $out/lib/fstar/
  '';
}
