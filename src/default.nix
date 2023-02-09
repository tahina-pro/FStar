{ fstar, lib, ocamlPackages, stdenv, version }:
stdenv.mkDerivation {
  pname = "fstar-ocaml-snapshot";
  inherit version;

  src = lib.cleanSourceWith {
    src = ./..;
    filter = path: _:
      let relPath = lib.removePrefix (toString ./.. + "/") (toString path);
      in lib.hasPrefix "src" relPath || lib.hasPrefix "ulib" relPath
      || lib.hasPrefix "ocaml" relPath || lib.hasSuffix ".common.mk" relPath;
  };

  preConfigure = ''
    mkdir bin
    cp ${fstar}/bin/fstar.exe bin
    cd src/ocaml-output
  '';

  nativeBuildInputs = with ocamlPackages; [ ocaml menhir ];

  buildTargets = [ "dune-snapshot" ];

  installPhase = "mv ../../ocaml $out";
}
