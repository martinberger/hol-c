package Prover

import ProofState.{Goal}
import ThmClass._
import Context._
import ProofState.{qed, mkFreshNamed, act}
import TypeTests.{tvar_T, tvar_X, int_ty, prop_ty}
import Tactic.{AndThenList, makeGeneric}

class TestCase(
    val name: String,
    val ctx: Context,
    val goalTm: Term,
    val taint: Taint,
    val tactic: Tactic
):
    def this(name: String, ctx: Context, goalTm: Term, taint: Taint, l: List[Tactic]) =
        this(name, ctx, goalTm, taint, AndThenList(l))

    override def toString(): String = s"""
        name = $name
        ctx = $ctx
        goalTm = $goalTm
        taint = $taint
        tactic = $tactic
    """

    type Handler = (TestCase, Option[ProofState]) => Unit
    def id: Handler        = { (_, _) => () }
    def printFail: Handler = { (_, res) => if res == None then println(s"FAIL ${this}") }
    def runGenericNoQED(resultHandler: Handler = printFail): Option[ProofState] =
        println(s"------------- runGenericNoQED ${name} -------------")
        Lib.reset() // Unfortunately, needed at this point. TODO: remove
        val goal    = (ctx, goalTm, taint)
        val initial = "my_goal"
        val ps      = mkFreshNamed(goal, initial)
        val res     = act(ps)(tactic)
        resultHandler(this, res)
        res

    type QEDHandler = (TestCase, Option[Thm]) => Boolean
    def idQED: QEDHandler        = { (_, _) => true }
    def printFailQED: QEDHandler = { (_, res) => res != None }
    def runGeneric(resultHandler: QEDHandler = printFailQED): Boolean =
        // println(s"------------- runGeneric ${name} -------------")
        Lib.reset() // Unfortunately, needed at this point. TODO: remove
        // println(tactic) // TODO remove
        val goal    = (ctx, goalTm, taint)
        val initial = "my_goal"
        val ps      = mkFreshNamed(goal, initial)
        val res = for (
          res0 <- act(ps)(Select(List(initial)));
          res1 <- act(res0)(tactic);
          res2 <- qed(res1)
        ) yield res2
        resultHandler(this, res)
        // res match
        //     case Some(thm) => println(s"Just got theorem: ${thm}")
        //     case _         => println("Did not woooork")

object TacTests:

    import TermTests._
    val printState: Tactic = PrintState(false) // For easy global changes of logging

    val context0: Context = List()
    val context1: Context = List(eq_x_x)
    val context2: Context = List(eq_x_x, eq_x_y)
    val context3: Context = List(eq_x_y, eq_y_z, eq_m_m)
    val t1                = TestCase("test1", context0, eq_x_x, I, Id())
    val t2                = TestCase("test2", context0, eq_x_x, I, printState)

    // val simpleTacs = List(
    //   Id(),
    //   PrintState(),
    //   AndThen(Id(), Id()),
    //   AndThenList(List(Id(), Id(), Id())),
    //   AndThenList(List(printState, Id(), Id(), Id(), printState)),
    //   AndThenList(List(AndThenList(List(printState, Id(), Id(), Id(), printState))))
    // )
    // val simpleTacs2: List[Tactic] = Lib.sandwich(Id())(simpleTacs)

    def select(i: Int): Tactic = Select(List(s"goal_${i.toString}"))

    val t3 = TestCase("eq_x_x", context0, eq_x_x, I, Apply(Refl_pretac()))
    val t4 = TestCase("eq_x_y |- eq_x_y", context2, eq_x_y, I, Apply(Init_pretac()))

    val tac5 = List(Apply(Sym_pretac()), select(1), Apply(Init_pretac()))
    val t5   = TestCase("eq_x_y |- eq_y_x", context2, eq_y_x, I, AndThenList(tac5))

    val tac6 = List(Apply(Trans_pretac(y)), select(1), Apply(Init_pretac()), select(2), Apply(Init_pretac()))
    val t6   = TestCase("eq_x_y, eq_y_z |- eq_x_z", context3, eq_x_z, I, tac6)

    val tac7 = List(
      Apply(ImpI_pretac()),
      select(1),
      Apply(ConjI_pretac()),
      select(2),
      Apply(ConjE2_pretac(eq_m_m)),
      select(4),
      Apply(Init_pretac()),
      select(3),
      Apply(ConjE1_pretac(eq_x_y)),
      select(5),
      Apply(Init_pretac())
    )
    val t7 = TestCase("(A && B) -> (B && A)", gamma_empty, a_and_b_implies_b_and_a, I, tac7)

    val a_implies_b                 = Implies(a, b)
    val a_and_a_implies_b           = And(a, a_implies_b)
    val a_and_a_implies_b_implies_b = Implies(a_and_a_implies_b, b)
    val goal                        = (gamma_empty, a_and_a_implies_b_implies_b, I)
    val tac8 = List(
      Apply(ImpI_pretac()),
      select(1),
      Apply(ImpE_pretac(a)),
      select(2),
      Apply(ConjE2_pretac(a)),
      select(4),
      Apply(Init_pretac()),
      select(3),
      Apply(ConjE1_pretac(a_implies_b)),
      select(5),
      Apply(Init_pretac())
    )
    val t8 = TestCase("A && (A -> B)) -> B", gamma_empty, a_and_a_implies_b_implies_b, I, tac8)

    val tac9 = List(Apply(Lift_pretac(I)), select(1), Apply(Init_pretac()))
    val t9   = TestCase("trivial use of lifting", context3, eq_x_y, C, tac9)

    val neg_a               = Neg(a)
    val neg_neg_a           = Neg(neg_a)
    val neg_neg_a_implies_a = Implies(neg_neg_a, a)
    val tac10 = List(
      Apply(ImpI_pretac()),
      select(1),
      Apply(Raa_pretac(I)),
      select(2),
      Apply(NegE_pretac(neg_a)),
      select(3),
      Apply(Init_pretac()),
      select(4),
      Apply(Init_pretac())
    )
    val t10 = TestCase("Double negation (1): !!A -> A : C", gamma_empty, neg_neg_a_implies_a, C, tac10)

    val a_implies_neg_neg_a = Implies(a, neg_neg_a)
    val tac11 = List(
      Apply(ImpI_pretac()),
      select(1),
      Apply(NegI_pretac()),
      select(2),
      Apply(NegE_pretac(a)),
      select(3),
      Apply(Init_pretac()),
      select(4),
      Apply(Init_pretac())
    )
    val t11 = TestCase("Double negation (2): A -> !!A : I", gamma_empty, a_implies_neg_neg_a, I, tac11)

    val tac12 = List(
      ImpI_pretac(),
      NegI_pretac(),
      NegE_pretac(a),
      Init_pretac(),
      Init_pretac()
    ).map(Apply(_))
    val t12 = TestCase("A -> !!A : I but with goal stack", gamma_empty, a_implies_neg_neg_a, I, tac12)

    val a_iff_neg_neg_a = Equivalence(a, neg_neg_a)
    val tac13 = List(
      IffI_pretac(),
      Lift_pretac(I),
      NegI_pretac(),
      NegE_pretac(a),
      Init_pretac(),
      Init_pretac(),
      Raa_pretac(I),
      NegE_pretac(neg_a),
      Init_pretac(),
      Init_pretac()
    )

    val t13 = TestCase("A <-> !!A : I", gamma_empty, a_iff_neg_neg_a, C, makeGeneric(tac13))

    val gamma_13   = List(neg_a, neg_neg_a)
    val tac13_8    = List(Init_pretac())
    val t13_8      = TestCase("", gamma_13, neg_a, I, makeGeneric(tac13_8))
    val tac13_7    = List(Init_pretac())
    val t13_7      = TestCase("", gamma_13, neg_neg_a, I, makeGeneric(tac13_7))
    val tac13_6    = List(NegE_pretac(neg_a), Init_pretac(), Init_pretac())
    val t13_6      = TestCase("", gamma_13, FalseProp(), I, makeGeneric(tac13_6))
    val tac13_5    = List(Raa_pretac(I), NegE_pretac(neg_a), Init_pretac(), Init_pretac())
    val gamma_13_5 = List(neg_neg_a)
    val t13_5      = TestCase("", gamma_13_5, a, C, makeGeneric(tac13_5))
    val gamma13_4  = List(a, neg_a)
    val tac13_4    = List(NegE_pretac(a), Init_pretac(), Init_pretac())
    val t13_4      = TestCase("", gamma13_4, FalseProp(), I, makeGeneric(tac13_4))
    val gamma13_3  = List(a)
    val tac13_3    = List(NegI_pretac(), NegE_pretac(a), Init_pretac(), Init_pretac())
    val t13_3      = TestCase("", gamma13_3, neg_neg_a, I, makeGeneric(tac13_3))
    val tac13_2    = List(Lift_pretac(I), NegI_pretac(), NegE_pretac(a), Init_pretac(), Init_pretac())
    val t13_2      = TestCase("", gamma13_3, neg_neg_a, C, makeGeneric(tac13_2))
    val tac13_1    = IffI_pretac() :: tac13_2 ++ tac13_5
    val t13_1      = TestCase("", gamma_empty, a_iff_neg_neg_a, C, makeGeneric(tac13_1))

    val neg_b               = Neg(b)
    val neg_b_implies_neg_a = Implies(neg_b, neg_a)
    val contraposition      = Implies(a_implies_b, neg_b_implies_neg_a)

// (=, m), m), (not, ((=, x), y)), ((implies, ((=, m), m)), ((=, x), y))) |- ((implies, ((=, m), m)), ((=, x), y)) : I

    val gamma14 = List(a, neg_b, a_implies_b)
    val t14     = TestCase("A, !B, A -> B |- A -> B", gamma14, a_implies_b, I, List(Apply(Init_pretac())))
    val t15     = TestCase("A, !B, A -> B |- A", gamma14, a, I, List(Apply(Init_pretac())))
    val tac16 = Lib.sandwich(SelectLast())(
      List(
        ImpE_pretac(a),
        Init_pretac(),
        Init_pretac()
      ).map(Apply(_))
    )
    val t16 = TestCase("A, !B, A -> B |- B", gamma14, b, I, tac16)
    val t17 = TestCase("A, !B, A -> B |- !B", gamma14, neg_b, I, List(Apply(Init_pretac())))

    val tac18 =
        List(
          NegE_pretac(b),
          Init_pretac(),
          ImpE_pretac(a),
          Init_pretac(),
          Init_pretac()
        )

    val t18 = TestCase("A, !B, A -> B |- FALSE", gamma14, FalseProp(), I, makeGeneric(tac18))

    val tac_contraposition = Lib.sandwich(SelectLast())(
      List(
        ImpI_pretac(),
        ImpI_pretac(),
        NegI_pretac(),
        NegE_pretac(b),
        Init_pretac(),
        ImpE_pretac(a),
        Init_pretac(),
        Init_pretac()
      ).map(Apply(_))
    )

    val t_contraposition = TestCase("(A -> B) -> !A -> !B", gamma_empty, contraposition, I, tac_contraposition)

    val ex_falso_quodlibet   = Implies(neg_a, Implies(a, b))
    val tac_ex_falso         = List(ImpI_pretac(), ImpI_pretac(), Raa_pretac(I), NegE_pretac(a), Init_pretac(), Init_pretac())
    val t_ex_falso_quodlibet = TestCase("!A -> A -> B", gamma_empty, ex_falso_quodlibet, C, makeGeneric(tac_ex_falso))

    def ex_falso_quodlibet(tm: Term): List[PreTactic] = List(
      ImpI_pretac(),
      ImpI_pretac(),
      Raa_pretac(I),
      NegE_pretac(tm),
      Init_pretac(),
      Init_pretac()
    )

    val x_implies_y                      = Implies(x, y)
    val open_x_implies_y_close_implies_x = Implies(x_implies_y, x)
    val peirce_law                       = Implies(open_x_implies_y_close_implies_x, x)
    val tac_peirce: List[PreTactic] = List(
      ImpI_pretac(),
      Raa_pretac(C),
      NegE_pretac(x),
      Lift_pretac(I),
      Init_pretac(),
      ImpE_pretac(x_implies_y),
      ImpI_pretac(),
      Raa_pretac(I),
      NegE_pretac(x),
      Init_pretac(),
      Init_pretac(),
      Lift_pretac(I),
      Init_pretac()
    )
    //    ++ ex_falso_quodlibet(a)
    // ++ List(Init_pretac(), Init_pretac())

    val t_peirce = TestCase("Peirce Law (1)", context0, peirce_law, C, makeGeneric(tac_peirce, false))
// val t_peirceQuantified = TestCase("Peirce Law (2)", context0, all_quantified_peirce_law, C, List()) // TODO

// val testsNoQED = List(t1, t2) ++ ts

    val testsWithQED = List(
      // ("t3", t3),
      // ("t4", t4),
      // ("t5", t5),
      // ("t6", t6),
      // ("t7", t7),
      // ("t8", t8),
      // ("t9", t9),
      // ("t10", t10),
      // ("t11", t11),
      // ("t12", t12),
      // ("t13", t13),
      // ("t13_8", t13_8),
      // ("t13_7", t13_7),
      // ("t13_6", t13_6),
      // ("t13_5", t13_5),
      // ("t13_4", t13_4),
      // ("t13_3", t13_3),
      // ("t13_2", t13_2),
      // ("t13_1", t13_1),
      // ("t14", t14),
      // ("t15", t15),
      // ("t16", t16),
      // ("t17", t17),
      // ("t18", t18),
      // ("t_contraposition", t_contraposition),
      // ("t_ex_falso_quodlibet", t_ex_falso_quodlibet),
      ("t_peirce", t_peirce)
    )
    val allTests = /*testsNoQED ++ */ testsWithQED

    def run(): (Int, Int) =
        var n      = 0
        var failed = 0
        // import TacticsTests.{allTests, testsWithQED}
        // allTests.map(_.runGenericNoQED())
        testsWithQED.foreach(t =>
            val (name, test) = t
            n += 1
            if !test.runGeneric() then
                failed += 1
                println(s"   Failed test ${name}")
        )
        (n, failed)
