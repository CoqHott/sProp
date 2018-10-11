# sProp
repository containing the examples of the POPL paper

The repository contains the companion code of the publication
"Definiitonal Proof Irrelevance without K" (accepted at POPL' 19).

## Structure

- ./examples
  contains examples making use of sProp

## Compilation

You need Coq with sProp and a recent version of Agda

To compile the coq development:

   set `$COQBIN` to the path where coqc (with sProp) is (`export
   COQBIN=/.../bin/`).

   Then, in the / directory, run:

	make
