object Main:

    def eval(runner: () => (Int, Int), name: String): Int =
        println(s"\n----------- ${name} Tests -----------")
        val (all, failed) = runner()
        println(s"Passed ${all - failed} out of ${all} tests")
        failed

    import Prover._
    val all = List(
      (KindTests.run _, "Kind"),
      (TypeTests.run _, "Type"),
      (TermTests.run _, "Term"),
      (RuleTests.run _, "Rule"),
      (TacTests.run _, "Tactic")
    )

    def main(argv: Array[String]): Unit =
        val failed = all.foldLeft(0)((accu, t) => accu + eval(t._1, t._2))
        System.exit(failed)
