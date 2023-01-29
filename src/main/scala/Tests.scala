object Tests:

    def eval(runner: () => (Int, Int), name: String): Unit =
        println(s"\n----------- ${name} Tests -----------")
        val (all, failed) = runner()
        println(s"Passed ${all - failed} out of ${all} tests")

    def main(argv: Array[String]): Unit =
        import Prover._
        eval(KindTests.run, "Kind")
        eval(TypeTests.run, "Type")
        eval(TermTests.run, "Term")
        eval(RuleTests.run, "Rule")
        eval(Prover.TacTests.run, "Tactic")
