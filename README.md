# sProp

The repository contains the companion code of the publication
"Definitional Proof Irrelevance without K" (accepted at POPL '19).
Below you can find the installation instructions for the appropriate
versions of Coq and Agda required to check these examples. 

## Coq

To get Coq with sProp, clone http://github.com/SkySkimmer/coq and
checkout the `sprop` branch, then run

    opam pin coq .
    
Alternatively you can follow the instructions in
https://github.com/SkySkimmer/coq/blob/sprop/INSTALL

To compile the coq development:

* If `coqc` is not in `PATH`, set `$COQBIN` to the directory where
   coqc (with sProp) is (`export COQBIN=/.../bin/`).
* Then run `make`.


## Agda

To get Agda with Prop, compile Agda from the master branch on the
GitHub repository https://github.com/agda/agda.

Detailed instructions (tested on a freshly installed machine running
Ubuntu 18.04):

```
sudo apt-get install make ghc cabal-install alex emacs zlib1g-dev libgc-dev libicu-dev
cabal update
export PATH=$PATH:~/.cabal/bin
cabal install cpphs happy epic filemanip quickcheck edisoncore
cd agda
cabal install --only-dependencies --force-reinstalls
make install
```

This will install the Agda binary in ~/.cabal/bin under the name agda-2.6.0.