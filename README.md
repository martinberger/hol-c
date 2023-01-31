## A modest proposal: explicit support for foundational pluralism


**Introduction.** This repo contains a basic  Scala 3 implementation of an LCF-style interactive theorem prover for the HOL(C) logic introduced in the paper

>   *A modest proposal: explicit support for foundational pluralism* 


by [Dominic Mulligan](https://dominicpm.github.io/) and [Martin Berger](https://martinfriedrichberger.net/). A draft version of the paper will be submitted for publication in the next few days.
The purpose of this implementation is to serve as a
proof-of-concept for fine-tuning the logic and for reviewing the paper. It is not intended to enable large-scale proof in HOL(C).

**Compiling, testing and running the code.** All relevant code is in the `src`
directory and can be compiled and executed with the `scalac`
compiler. It most naturally used using `sbt`, by invoking

    sbt compile

Invoking

    sbt test

executes a few property-based unit tests.  Invoking

    sbt run

executes some integration tests, and proves some theorems, including *Peirce's law*.
