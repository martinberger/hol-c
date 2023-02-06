object Main:

    def eval(runner: () => (Int, Int), name: String): Int =
        println(s"\n----------- ${name} Tests -----------")
        val (all, failed) = runner()
        println(s"Passed ${all - failed} out of ${all} tests")
        failed

    def main(argv: Array[String]): Unit =
        import Prover._
        var failed = 0
        failed += eval(KindTests.run, "Kind")
        failed += eval(TypeTests.run, "Type")
        failed += eval(TermTests.run, "Term")
        failed += eval(RuleTests.run, "Rule")
        failed += eval(Prover.TacTests.run, "Tactic")
        System.exit(failed)
