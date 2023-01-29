object Tests:

    def eval(runner: () => (Int, Int), name: String): Int =
        println(s"\n----------- ${name} Tests -----------")
        val (all, failed) = runner()
        println(s"Passed ${all - failed} out of ${all} tests")
        failed

    def main(argv: Array[String]): Unit =
        import Prover._
        var failedTests = 0
        failedTests += eval(KindTests.run, "Kind")
        failedTests += eval(TypeTests.run, "Type")
        failedTests += eval(TermTests.run, "Term")
        failedTests += eval(RuleTests.run, "Rule")
        failedTests += eval(Prover.TacTests.run, "Tactic")
        // TODO enable this: System.exit(failedTests);
