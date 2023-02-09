object Main:
    import Prover.Tests.{run, allTests}

    def main(argv: Array[String]): Unit =
        val failed = run(allTests)
        System.exit(failed)
