# sProp
repository containing the examples of the POPL paper

The repository contains the companion code of the publication
"Definiitonal Proof Irrelevance without K" (accepted at POPL' 19).

## Structure

- ./examples
  contains examples making use of sProp

## Compilation

You need Coq with sProp and a recent version of Agda

To get Coq with sProp, you can use

    opam install coq+sprop

To get Agda with Prop, compile Agda from the GitHub repository
https://github.com/agda/agda.


To compile the coq development:

   set `$COQBIN` to the path where coqc (with sProp) is (`export
   COQBIN=/.../bin/`).

   Then, in the / directory, run:

	make
