package Prover

object Tests:

    type Runner = (() => (Int, Int))

    def run(tests: List[(Runner, String)]): Int =
        def eval(runner: Runner, name: String): Int =
            println(s"\n----------- ${name} Tests -----------")
            val (all, failed) = runner()
            println(s"   Passed ${all - failed} out of ${all} tests")
            failed
        tests.foldLeft(0)((accu, t) => accu + eval(t._1, t._2))

    val allTests = List(
      (() => KindTests.run(), "Kind"),
      (() => TypeTests.run(), "Type"),
      (() => TermTests.run(), "Term"),
      (() => RuleTests.run(), "Rule"),
      (() => TacTests.run(), "Tactic")
    )
