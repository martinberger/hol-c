package Prover

import Thm._
import Context._
import ProofState.{qed, mkFreshNamed, act}
import Tactic.{AndThenList, makeGeneric}
import javax.naming.InitialContext

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

    type QEDHandler = (TestCase, Option[Thm]) => Boolean
    def idQED: QEDHandler        = { (_, _) => true }
    def printFailQED: QEDHandler = { (_, res) => res != None }
    def runGeneric(resultHandler: QEDHandler = printFailQED): Boolean =
        val goal    = (ctx, goalTm, taint)
        val initial = "my_goal"
        val ps      = mkFreshNamed(goal, initial)
        val res = for (
          res1 <- act(ps)(tactic);
          res2 <- qed(res1)
        ) yield res2
        resultHandler(this, res)

object TacTests:

    import TermTests._
    val printState: Tactic = PrintState() // For easy global changes of logging

    val context0: Context = List()
    val context1: Context = List(eq_x_x)
    val context2: Context = List(eq_x_x, eq_x_y)
    val context3: Context = List(eq_x_y, eq_y_z, eq_m_m)
    val t1                = TestCase("test1", context0, eq_x_x, I, Id())
    val t2                = TestCase("test2", context0, eq_x_x, I, printState)

    val t3 = TestCase("eq_x_x", context0, eq_x_x, I, Apply(Refl_pretac()))
    val t4 = TestCase("eq_x_y |- eq_x_y", context2, eq_x_y, I, Apply(Init_pretac()))

    val tac5 = List(Apply(Sym_pretac()), Apply(Init_pretac()))
    val t5   = TestCase("eq_x_y |- eq_y_x", context2, eq_y_x, I, AndThenList(tac5))

    val tac6 = List(Apply(Trans_pretac(y)), Apply(Init_pretac()), Apply(Init_pretac()))
    val t6   = TestCase("eq_x_y, eq_y_z |- eq_x_z", context3, eq_x_z, I, tac6)

    val tac_trueI = List(Lift_pretac(I), TrueI_pretac())
    val t_trueI   = TestCase("|- True : C)", context0, TrueProp(), C, makeGeneric(tac_trueI))

    val false_or_true     = Or(FalseProp(), TrueProp())
    val tac_false_or_true = List(DisjI2_pretac(), TrueI_pretac())
    val t_false_or_true   = TestCase("|- false || true", context0, false_or_true, I, makeGeneric(tac_false_or_true))

    val true_or_false     = Or(TrueProp(), FalseProp())
    val tac_true_or_false = List(DisjI1_pretac(), TrueI_pretac())
    val t_true_or_false   = TestCase("|- true || false", context0, true_or_false, I, makeGeneric(tac_true_or_false))

    val tac7 = List(
      Apply(ImpI_pretac()),
      Apply(ConjI_pretac()),
      Apply(ConjE1_pretac(eq_x_y)),
      Apply(Init_pretac()),
      Apply(ConjE2_pretac(eq_m_m)),
      Apply(Init_pretac())
    )
    val t7 = TestCase("(A && B) -> (B && A)", gamma_empty, a_and_b_implies_b_and_a, I, tac7)

    val a_implies_b                 = Implies(a, b)
    val a_and_a_implies_b           = And(a, a_implies_b)
    val a_and_a_implies_b_implies_b = Implies(a_and_a_implies_b, b)
    val goal                        = (gamma_empty, a_and_a_implies_b_implies_b, I)
    val tac8 = List(
      Apply(ImpI_pretac()),
      Apply(ImpE_pretac(a)),
      Apply(ConjE1_pretac(a_implies_b)),
      Apply(Init_pretac()),
      Apply(ConjE2_pretac(a)),
      Apply(Init_pretac())
    )
    val t8 = TestCase("A && (A -> B)) -> B", gamma_empty, a_and_a_implies_b_implies_b, I, tac8)

    val tac9 = List(Apply(Lift_pretac(I)), Apply(Init_pretac()))
    val t9   = TestCase("trivial use of lifting", context3, eq_x_y, C, tac9)

    val neg_a               = Neg(a)
    val neg_neg_a           = Neg(neg_a)
    val neg_neg_a_implies_a = Implies(neg_neg_a, a)
    val tac10 = List(
      Apply(ImpI_pretac()),
      Apply(Raa_pretac(I)),
      Apply(NegE_pretac(neg_a)),
      Apply(Init_pretac()),
      Apply(Init_pretac())
    )
    val t10 = TestCase("Double negation (1): !!A -> A : C", gamma_empty, neg_neg_a_implies_a, C, tac10)

    val a_implies_neg_neg_a = Implies(a, neg_neg_a)
    val tac11 = List(
      Apply(ImpI_pretac()),
      Apply(NegI_pretac()),
      Apply(NegE_pretac(a)),
      Apply(Init_pretac()),
      Apply(Init_pretac())
    )
    val t11 = TestCase("Double negation (2): A -> !!A : I", gamma_empty, a_implies_neg_neg_a, I, tac11)

    val tac12 = List(
      ImpI_pretac(),
      NegI_pretac(),
      NegE_pretac(a),
      Init_pretac(),
      Init_pretac()
    )
    val t12 = TestCase("A -> !!A : I but with goal stack", gamma_empty, a_implies_neg_neg_a, I, makeGeneric(tac12))

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

    val gamma14 = List(a, neg_b, a_implies_b)
    val t14     = TestCase("A, !B, A -> B |- A -> B", gamma14, a_implies_b, I, List(Apply(Init_pretac())))
    val t15     = TestCase("A, !B, A -> B |- A", gamma14, a, I, List(Apply(Init_pretac())))
    val tac16 = List(
      ImpE_pretac(a),
      Init_pretac(),
      Init_pretac()
    )
    val t16 = TestCase("A, !B, A -> B |- B", gamma14, b, I, makeGeneric(tac16))
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

    val tac_contraposition = List(
      ImpI_pretac(),
      ImpI_pretac(),
      NegI_pretac(),
      NegE_pretac(b),
      Init_pretac(),
      ImpE_pretac(a),
      Init_pretac(),
      Init_pretac()
    )

    val t_contraposition = TestCase("(A -> B) -> !A -> !B", gamma_empty, contraposition, I, makeGeneric(tac_contraposition))

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

    val t_peirce = TestCase("Peirce Law (1)", context0, peirce_law, C, makeGeneric(tac_peirce, false))

    val neg_x                      = Neg(x)
    val neg_y                      = Neg(y)
    val x_and_y                    = And(x, y)
    val neg_x_or_neg_y             = Or(neg_x, neg_y)
    val neg_bra_neg_x_or_neg_y_bra = Neg(neg_x_or_neg_y)
    val boolean1                   = Implies(x_and_y, neg_bra_neg_x_or_neg_y_bra)

    val tac_boolean1 = List(
      ImpI_pretac(),
      NegI_pretac(),
      DisjE_pretac(neg_x, neg_y)
    ) ++
        List(
          NegE_pretac(y),
          Init_pretac(),
          ConjE2_pretac(x),
          Init_pretac() // This handles right premise of DisjE
        ) ++
        List(
          NegE_pretac(x),
          Init_pretac(),
          ConjE1_pretac(y),
          Init_pretac() // This handles middle premise of DisjE
        ) ++
        List(Init_pretac()) // For rightmosgt premise of DisjE
    val t_boolean1 = TestCase("(x & y) -> !(!x | !y)", context0, boolean1, I, makeGeneric(tac_boolean1))

    val boolean2 = Implies(neg_bra_neg_x_or_neg_y_bra, x_and_y)

    val tac_boolean2 = List(
      ImpI_pretac(),
      ConjI_pretac()
    )
    val t_boolean2 = TestCase("(x & y) <- !(!x | !y)", context0, boolean2, I, makeGeneric(tac_boolean2))

    val tac_lem_implies_raa = List(
      ImpI_pretac(),
      DisjE_pretac(neg_x, x),
      Lift_pretac(I),
      Init_pretac()
    )

    val x_or_not_x                     = Or(x, neg_x)
    val x_or_not_x_implies_y           = Implies(x_or_not_x, y)
    val x_or_not_x_implies_y_implies_y = Implies(x_or_not_x_implies_y, y)
    val tac_19 = List(
      ImpI_pretac(),
      ImpE_pretac(x_or_not_x),
      Lem_pretac(),
      Lift_pretac(I),
      Init_pretac()
    )
    val t19 = TestCase("((x | !x) -> y)->y)", context0, x_or_not_x_implies_y_implies_y, C, makeGeneric(tac_19))

    val false_implies_x = Implies(FalseProp(), x)
    val tac_20 = List(
      ImpI_pretac(),
      FalseE_pretac(),
      Init_pretac()
    )
    val t20 = TestCase("false implies x", context0, false_implies_x, I, makeGeneric(tac_20))

    val x_iff_y = Equivalence(x, y)
    val tac_21 = List(
      IffE1_pretac(x),
      Init_pretac(),
      Init_pretac()
    )
    val t21 = TestCase("", List(x_iff_y, x), y, I, makeGeneric(tac_21))

    val tac_22 = List(
      IffE2_pretac(y),
      Init_pretac(),
      Init_pretac()
    )
    val t22 = TestCase("", List(x_iff_y, y), x, I, makeGeneric(tac_22))

    val tvar_t1 = TyVar("T1")
    val tvar_t2 = TyVar("T2")
    val t_PV    = FunctionTy(Prop(), tvar_t1)
    val t_VP    = FunctionTy(tvar_t2, Prop())
    val t_VV    = FunctionTy(tvar_t2, tvar_t1)

    val x_VV = Var("x_VV", t_VV)
    val y_VV = Var("y_VV", t_VV)
    val z_VV = Var("z_VV", t_VV)

    val eq_xy          = Equation(x_VV, y_VV, t_VV)
    val eq_yz          = Equation(y_VV, z_VV, t_VV)
    val context_VV     = List(eq_xy)
    val context_subst1 = tySubst(context_VV, Prop(), tvar_t1)
    val context_subst2 = tySubst(context_subst1, Prop(), tvar_t2)
    val eq_xy_subst1   = Term.tySubst(eq_xy, Prop(), tvar_t1)
    val eq_xy_subst2   = Term.tySubst(eq_xy_subst1, Prop(), tvar_t2)

    val tac_23 = List(
      Inst_pretac(context_subst1, eq_xy_subst1, Prop(), tvar_t2),
      Inst_pretac(context_VV, eq_xy, Prop(), tvar_t1),
      Init_pretac()
    )
    val t23 = TestCase("t23", context_subst2, eq_xy_subst2, I, makeGeneric(tac_23))

    val int_ty     = TyFormer("Int", TyKind)
    val ty_int_int = FunctionTy(int_ty, int_ty)
    val m_int      = Var("m", ty_int_int)
    val eq_24      = Equation(m_int, m_int, ty_int_int)
    val eq_lam_lam = Equation(lam, lam, ty_int_int)
    val tac_24 = List(
      Subst_pretac(context0, eq_24, lam, m_int),
      Refl_pretac()
    )
    val t24 = TestCase("subst_pretac", context0, eq_lam_lam, I, makeGeneric(tac_24))

    val n1      = Var("n1", int_ty)
    val n2      = Var("n2", int_ty)
    val f1_int  = Var("f1", ty_int_int)
    val f2_int  = Var("f2", ty_int_int)
    val eq25_f  = Equation(f1_int, f2_int, ty_int_int)
    val eq25_n  = Equation(n1, n2, int_ty)
    val app25   = Equation(App(f1_int, n1), App(f2_int, n2), int_ty)
    val gamma25 = List(eq25_f, eq25_n)

    val tac_25 = List(
      Acong_pretac(),
      Init_pretac(),
      Init_pretac()
    )
    val t25 = TestCase("acong_pretac", gamma25, app25, I, makeGeneric(tac_25))

    val lam26 = Lam(n1, n1)
    val eq26  = Equation(lam26, lam26, ty_int_int)
    val tac_26 = List(
      Lcong_pretac(),
      Refl_pretac()
    )
    val t26 = TestCase("lcong_pretac", context0, eq26, I, makeGeneric(tac_26))

    val eq27   = Equation(App(lam26, n2), n2, int_ty)
    val tac_27 = List(Beta_pretac())
    val t27    = TestCase("beta", context0, eq27, I, makeGeneric(tac_27))

    val f       = Var("f", ty_int_int)
    val fn1     = App(f, n1)
    val lam_fn1 = Lam(n1, fn1)
    val eq28    = Equation(lam_fn1, f, ty_int_int)
    val tac_28  = List(Eta_pretac())
    val t28     = TestCase("eta", context0, eq28, I, makeGeneric(tac_28))

    val tac_29 = List(AllI_pretac(), Refl_pretac())
    val t29    = TestCase("allI", context0, Forall("x", int_ty, eq_m_m), I, makeGeneric(tac_29))

    val phi30 = Forall("n1", int_ty, eq25_n)
    val tac_30 = List(
      AllE_pretac(eq25_n, n2, n1),
      Init_pretac()
    )
    val eq_30 = Equation(n2, n2, int_ty)
    val t30   = TestCase("AllE_pretac", List(phi30), eq_30, I, makeGeneric(tac_30))

    val tac_31 = List(
      ExI_pretac(n2),
      Refl_pretac()
    )
    val eq_31 = Equation(n1, n2, int_ty)
    val t31   = TestCase("ExI", context0, Exists("n1", int_ty, eq_31), I, makeGeneric(tac_31))

    val n3       = Var("n3", int_ty)
    val eq32_1_1 = Equation(n1, n2, int_ty)
    val tac_32 = List(
      ExE_pretac(eq32_1_1, n1, n3),
      Init_pretac(),
      Init_pretac()
    )
    val eq32    = Equation(n3, n2, int_ty)
    val tm32    = Exists("n1", int_ty, eq32_1_1)
    val gamma32 = List(tm32)
    val t32     = TestCase("ExE", gamma32, eq32, I, makeGeneric(tac_32))

    val neg_neg_x                   = Neg(neg_x)
    val neg_neg_neg_x               = Neg(neg_neg_x)
    val neg_neg_neg_x_implies_neg_x = Implies(neg_neg_neg_x, neg_x)

    val tac_33 = List(
      ImpI_pretac(),
      NegI_pretac(),
      NegE_pretac(neg_neg_x),
      Init_pretac(),
      NegI_pretac(),
      NegE_pretac(x),
      Init_pretac(),
      Init_pretac()
    )

    val t33 = TestCase("!!!x -> !x", context0, neg_neg_neg_x_implies_neg_x, I, makeGeneric(tac_33))

    val tac_34 = List(
      ImpI_pretac(),
      NegI_pretac(),
      NegE_pretac(neg_x),
      Init_pretac(),
      Init_pretac()
    )
    val neg_x_implies_neg_neg_neg_x = Implies(neg_x, neg_neg_neg_x)
    val t34                         = TestCase("!x -> !!!x", context0, neg_x_implies_neg_neg_neg_x, I, makeGeneric(tac_34))

    val tac_35 = List(
      IffI_pretac(),
      NegI_pretac(),
      NegE_pretac(neg_x),
      Init_pretac(),
      Init_pretac(),
      NegI_pretac(),
      NegE_pretac(neg_neg_x),
      Init_pretac(),
      NegI_pretac(),
      NegE_pretac(x),
      Init_pretac(),
      Init_pretac()
    )
    val neg_x_iff_neg_neg_neg_x = Equivalence(neg_x, neg_neg_neg_x)
    val t35                     = TestCase("!x <-> !!!x", context0, neg_x_iff_neg_neg_neg_x, I, makeGeneric(tac_35))

    val testsWithQED = List(
      ("t3", t3),
      ("t4", t4),
      ("t5", t5),
      ("t6", t6),
      ("t_trueI", t_trueI),
      ("t_false_or_true", t_false_or_true),
      ("t_true_or_false", t_true_or_false),
      ("t7", t7),
      ("t8", t8),
      ("t9", t9),
      ("t10", t10),
      ("t11", t11),
      ("t12", t12),
      ("t13", t13),
      ("t13_8", t13_8),
      ("t13_7", t13_7),
      ("t13_6", t13_6),
      ("t13_5", t13_5),
      ("t13_4", t13_4),
      ("t13_3", t13_3),
      ("t13_2", t13_2),
      ("t13_1", t13_1),
      ("t14", t14),
      ("t15", t15),
      ("t16", t16),
      ("t17", t17),
      ("t18", t18),
      ("t_contraposition", t_contraposition),
      ("t_ex_falso_quodlibet", t_ex_falso_quodlibet),
      ("t_peirce", t_peirce),
      ("t_boolean1", t_boolean1),
      // ("t_boolean2", t_boolean2)
      ("t19", t19),
      ("t20", t20),
      ("t21", t21),
      ("t22", t22),
      ("t23", t23),
      ("t24", t24),
      ("t25", t25),
      ("t26", t26),
      ("t27", t27),
      ("t28", t28),
      ("t29", t29),
      ("t30", t30),
      ("t31", t31),
      ("t32", t32),
      ("t33", t33),
      ("t34", t34),
      ("t35", t35)
    )


    def run(): (Int, Int) =
        var n      = 0
        var failed = 0
        testsWithQED.foreach(t =>
            val (name, test) = t
            n += 1
            if !test.runGeneric() then
                failed += 1
                println(s"   Failed test ${name}")
        )
        (n, failed)
