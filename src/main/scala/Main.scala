object Main:

    type Runner = (() => (Int, Int))
    def run(tests: List[(Runner, String)]): Int =
        def eval(runner: Runner, name: String): Int =
            println(s"\n----------- ${name} Tests -----------")
            val (all, failed) = runner()
            println(s"Passed ${all - failed} out of ${all} tests")
            failed
        tests.foldLeft(0)((accu, t) => accu + eval(t._1, t._2))

    import Prover._
    val allTests = List(
      (KindTests.run _, "Kind"),
      (TypeTests.run _, "Type"),
      (TermTests.run _, "Term"),
      (RuleTests.run _, "Rule"),
      (TacTests.run _, "Tactic")
    )

    def main(argv: Array[String]): Unit =
        val failed = run(allTests)
        System.exit(failed)
