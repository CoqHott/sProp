# sProp
repository containing the examples of the POPL paper

The repository contains the companion code of the publication
"Definiitonal Proof Irrelevance without K" (accepted at POPL' 19).

## Compilation

You need Coq with sProp and a recent version of Agda

To get Coq with sProp, clone http://github.com/SkySkimmer/coq and checkout the `sprop` branch, then

    opam pin coq .
    
Alternatively you can follow the instructions in https://github.com/SkySkimmer/coq/blob/sprop/INSTALL
    
To get Agda with Prop, compile Agda from the GitHub repository
https://github.com/agda/agda.


To compile the coq development:

   If `coqc` is not in `PATH`, set `$COQBIN` to the directory where coqc (with sProp) is (`export
   COQBIN=/.../bin/`).

   Then run `make`
