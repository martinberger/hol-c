object Tests {
    def main(argv: Array[String]): Unit =
        var n = 0

        // println("----------- Rule Tests -----------")
        // n += Prover.RuleTests.run()
        println("----------- Tac Tests -----------")
        n += Prover.TacTests.run()

        println(s"\n\nRan ${n} tests\n")

}

