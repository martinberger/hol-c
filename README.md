# A modest proposal: explicit support for foundational pluralism

Target conference: ITP'23 https://mizar.uwb.edu.pl/ITP2023/

Abstract deadline: February 13, 2023 (AOE)

Paper submission deadline: February 20, 2023 (AOE)

Author notification: April 17, 2023

TODO:

- [X] Implement Peirce's law
- [X] Make code presentable 
- [X] Sync paper and code
- [X] Sync taint ordering with paper (remove unused taint?)
- [X] Add GitHub actions with some basic CI
- [X] Prepare repo for going public
- [X] Make short documentation on how to use code
- [X] Make `thm` opaque
- [ ] Add licence & copyright to code (if needed)
- [ ] Make repo public

--- 

**Introduction.** This repo contains a basic  Scala 3 implementation of an LCF-style interactive theorem prover for the HOL(C) logic introduced in the paper

>   *A modest proposal: explicit support for foundational pluralism* 


by Dominic Mulligan and Martin Berger. A draft version of the paper is available:
[Arxiv version for downloads](https://arxiv.org/).

The purpose of this implementation is to serve as a
proof-of-concept for fine-tuning the logic and for reviewing the paper. It is not intended to enable large-scale proof in HOL(C).

**Compiling, testing and the code.** All relevant code is in the `src` directory and can be compiled by invoking

    sbt compile

Invoking

    sbt test

executes a few property-based unit tests.  Invoking

    sbt run

executes some integration tests, and proves some theorems, including *Peirce's law*.

