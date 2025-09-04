object Main:
    import Prover.Tests.{run, allTests}

    def main(argv: Array[String]): Unit =
        val failed = run(allTests)
        sys.exit(failed)
