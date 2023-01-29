package Prover

// import Goal._
import ThmClass._
import Context._

// import TypeTests.{tvar_T, tvar_X, int_ty, prop_ty}
import TermTests._

object RuleTests {
    // var n = 0
    // def evalTests(l: List[(String, Option[Thm])]): Unit =
    //     l.foreach(t => {
    //         val (name, test) = t
    //         println(s"    --- ${name} ---")
    //         n += 1
    //         test match
    //             case None      => println("      None (FAILED?)")
    //             case Some(thm) => {} // println(s"      ${thm}")
    //     })

    // val tvar = TyVar("T")

    // val context0: Context = List()
    // val context1: Context = List(eq_x_x)
    // val context2: Context = List(eq_x_x, eq_x_y)
    // val context3: Context = List(eq_x_x, eq_x_y, eq_m_m)

    // def run_Ninit_tests(): Unit = {
    //     println(s"\n\n-------------- Running Ninit_tests")
    //     val l = List(
    //       ("context3, eq_x_x, I", (context3, eq_x_x)),
    //       ("context3, eq_x_y, I", (context3, eq_x_y)),
    //       ("context3, eq_m_m, I", (context3, eq_m_m))
    //     )
    //     val res = l.map(t => (t._1, ThmClass.init(t._2._1, t._2._2)))
    //     evalTests(res)
    // }

    // def run_NtrueI_tests(): Unit = {
    //     println(s"\n\n-------------- Running NtrueI_tests")
    //     val l = List(
    //       ("context0", (context0)),
    //       ("context3", (context3))
    //     )
    //     val res = l.map(t => (t._1, ThmClass.trueI(t._2)))
    //     evalTests(res)
    // }

    // def run_NfalseE_tests(): Unit = {
    //     println(s"\n\n-------------- Running NtrueI_tests")
    //     val l = List[(String, Thm, Term)](
    //       ("context0, eq_m_m, I), App(lam, c)", (context0, eq_m_m, I), App(lam, c)),
    //       ("context3, eq_m_m, I), App(lam, c)", (context3, eq_m_m, I), App(lam, c))
    //     )
    //     val res = l.map(t => (t._1, ThmClass.falseE(t._2, t._3)))
    //     evalTests(res)

    // }

    // def run_Nlift_tests(): Unit = {
    //     println(s"\n\n-------------- Running Nlift_tests")
    //     val l = List(
    //       ("(context3, eq_m_m, I), I", (context3, eq_m_m, I), I),
    //       ("(context3, eq_m_m, I), C", (context3, eq_m_m, I), C),
    //       ("(context3, eq_m_m, C), I This MUST fail", (context3, eq_m_m, C), I) // Must fail
    //     )
    //     val res = l.map(t => (t._1, ThmClass.lift(t._2, t._3)))
    //     evalTests(res)

    // }

    // def run_Nrefl_tests(): Unit    = { val l = List() /* ; println(s"\n -------------- Running ${l.size} Nrefl_tests") */ }
    // def run_Nsym_tests(): Unit     = { val l = List() /* ; println(s"\n -------------- Running ${l.size} Nsym_tests") */ }
    // def run_Ntrans_tests(): Unit   = { val l = List() /* ; println(s"\n -------------- Running ${l.size} Ntrans_tests") */ }
    // def run_Nlamcong_tests(): Unit = { val l = List() /* ; println(s"\n -------------- Running ${l.size} Nlamcong_tests") */ }
    // def run_Nappcong_tests(): Unit = { val l = List() /* ; println(s"\n -------------- Running ${l.size} Nappcong_tests") */ }
    // def run_Nbeta_tests(): Unit    = { val l = List() /* ; println(s"\n -------------- Running ${l.size} Nbeta_tests") */ }
    // def run_Ntysubst_tests(): Unit = { val l = List() /* ; println(s"\n -------------- Running ${l.size} Ntysubst_tests") */ }
    // def run_Neta_tests(): Unit     = { val l = List() /* ; println(s"\n -------------- Running ${l.size} Neta_tests") */ }
    // def run_Nsubst_tests(): Unit   = { val l = List() /* ; println(s"\n -------------- Running ${l.size} Nsubst_tests") */ }
    // def run_NiffE1_tests(): Unit   = { val l = List() /* ; println(s"\n -------------- Running ${l.size} NiffE1_tests") */ }
    // def run_NiffE2_tests(): Unit   = { val l = List() /* ; println(s"\n -------------- Running ${l.size} NiffE2_tests") */ }
    // def run_NiffI_tests(): Unit    = { val l = List() /* ; println(s"\n -------------- Running ${l.size} NiffI_tests") */ }
    // def run_NconjI_tests(): Unit   = { val l = List() /* ; println(s"\n -------------- Running ${l.size} NconjI_tests") */ }
    // def run_NconjE1_tests(): Unit  = { val l = List() /* ; println(s"\n -------------- Running ${l.size} NconjE1_tests") */ }
    // def run_NconjE2_tests(): Unit  = { val l = List() /* ; println(s"\n -------------- Running ${l.size} NconjE2_tests") */ }
    // def run_NdisjI1_tests(): Unit  = { val l = List() /* ; println(s"\n -------------- Running ${l.size} NdisjI1_tests") */ }
    // def run_NdisjI2_tests(): Unit  = { val l = List() /* ; println(s"\n -------------- Running ${l.size} NdisjI2_tests") */ }
    // def run_NdisjE_tests(): Unit   = { val l = List() /* ; println(s"\n -------------- Running ${l.size} NdisjE_tests") */ }
    // def run_NimpI_tests(): Unit    = { val l = List() /* ; println(s"\n -------------- Running ${l.size} NimpI_tests") */ }
    // def run_NimpE_tests(): Unit    = { val l = List() /* ; println(s"\n -------------- Running ${l.size} NimpE_tests") */ }
    // def run_NnegI_tests(): Unit    = { val l = List() /* ; println(s"\n -------------- Running ${l.size} NnegI_tests") */ }
    // def run_NnegE_tests(): Unit    = { val l = List() /* ; println(s"\n -------------- Running ${l.size} NnegE_tests") */ }
    // def run_NallI_tests(): Unit    = { val l = List() /* ; println(s"\n -------------- Running ${l.size} NallI_tests") */ }
    // def run_NallE_tests(): Unit    = { val l = List() /* ; println(s"\n -------------- Running ${l.size} NallE_tests") */ }
    // def run_NexI_tests(): Unit     = { val l = List() /* ; println(s"\n -------------- Running ${l.size} NexI_tests") */ }
    // def run_NexE_tests(): Unit     = { val l = List() /* ; println(s"\n -------------- Running ${l.size} NexE_tests") */ }

    // def runRuleTests(): Unit =
    //     val l = List(
    //       run_Ninit_tests _,
    //       run_NtrueI_tests _,
    //       run_NfalseE_tests _,
    //       run_Nlift_tests _,
    //       run_Nrefl_tests _,
    //       run_Nsym_tests _,
    //       run_Ntrans_tests _,
    //       run_Nlamcong_tests _,
    //       run_Nappcong_tests _,
    //       run_Nbeta_tests _,
    //       run_Ntysubst_tests _,
    //       run_Neta_tests _,
    //       run_Nsubst_tests _,
    //       run_NiffE1_tests _,
    //       run_NiffE2_tests _,
    //       run_NiffI_tests _,
    //       run_NconjI_tests _,
    //       run_NconjE1_tests _,
    //       run_NconjE2_tests _,
    //       run_NdisjI1_tests _,
    //       run_NdisjI2_tests _,
    //       run_NdisjE_tests _,
    //       run_NimpI_tests _,
    //       run_NimpE_tests _,
    //       run_NnegI_tests _,
    //       run_NnegE_tests _,
    //       run_NallI_tests _,
    //       run_NallE_tests _,
    //       run_NexI_tests _,
    //       run_NexE_tests _
    //     )
    //     l.foreach(_())

    // val simple_context: Context = List(eq_x_x)

    // val int_int_ty = FunctionTy(int_ty, int_ty)
    // val thm_eq_lam_lam_int_int = refl(empty_context, lam, int_int_ty)
    // val thm_eq_m_m_int         = refl(empty_context, m, int_ty)

    // val three_eq_context     = List(eq_x_y, eq_x_x, eq_y_x)
    // val simple_equiv_formula = Equivalence(eq_x_y, eq_y_x)

    // val thm_eq_x_y               = ax(List(eq_x_y), eq_x_y)
    // val thm_simple_equiv_forumla = ax(List(simple_equiv_formula), simple_equiv_formula)
    // val thm_three_eq_x_y         = ax(three_eq_context, eq_x_y)
    // val thm_three_eq_x_x         = ax(three_eq_context, eq_x_x)
    // val thm_three_eq_y_x         = ax(three_eq_context, eq_y_x)
    // val thm_eq_x_x_Y             = refl(simple_context, x, tvar_T)

    // def run_ax_tests(): Unit =
    //     val l = List(
    //       //   ("ax(List(eq_x_y), eq_x_y)", thm_eq_x_y),
    //       //   ("Equivalence(eq_x_y, eq_y_x)", thm_simple_equiv_forumla),
    //       //   ("ax(three_eq_context, eq_x_y)", thm_three_eq_x_y),
    //       //   ("ax(three_eq_context, eq_x_x)", thm_three_eq_x_x),
    //       //   ("ax(three_eq_context, eq_y_x)", thm_three_eq_y_x)
    //       // ("", ax(three_eq_context, Equivalence(eq_x_y, eq_y_x))) // should fail
    //     )
    //     evalTests(l)

    // def run_refl_tests(): Unit =
    //     val l = List(
    //       ("refl(empty_context, c, int_ty)", refl(empty_context, c, int_ty)),
    //       ("refl(empty_context, lam, int_int_ty)", refl(empty_context, lam, int_int_ty)),
    //       ("refl(empty_context, eq_m_m, int_ty)", refl(empty_context, m, int_ty))
    //     )
    //     evalTests(l)

    // def run_sym_tests(): Unit =
    //     val l = List(
    //       ("sym(thm_eq_x_y.get)", sym(thm_eq_x_y.get))
    //     )
    //     evalTests(l)

    // def run_trans_tests(): Unit =
    //     val l = List(
    //       ("trans(thm_eq_x_y.get, thm_three_eq_y_x.get)", trans(thm_eq_x_y.get, thm_three_eq_y_x.get))
    //     )
    //     evalTests(l)

    // def run_cong1_tests(): Unit =
    //     val l = List(
    //       ("cong1(thm_eq_x_y.get, m)", cong1(thm_eq_x_y.get, m))
    //     )
    //     evalTests(l)

    // def run_cong2_tests(): Unit =
    //     val l = List(
    //       ("cong2(thm_eq_lam_lam_int_int.get, thm_eq_m_m_int.get)", cong2(thm_eq_lam_lam_int_int.get, thm_eq_m_m_int.get))
    //     )
    //     evalTests(l)

    // def run_beta_tests(): Unit =
    //     val l = List(
    //       ("beta(empty_context, lam, int_ty, int_ty, m)", beta(empty_context, lam, int_ty, int_ty, m))
    //     )
    //     evalTests(l)

    // def run_inst_tests(): Unit =
    //     val l = List(
    //       ("inst(thm_eq_x_x_Y.get, int_ty, tvar)", inst(thm_eq_x_x_Y.get, int_ty, tvar))
    //     )
    //     evalTests(l)

    // def run_subst_tests(): Unit =
    //     val l = List(
    //       ("ThmClass.subst(thm_eq_x_x_Y.get, TermTests.c, int_ty, TermTests.x)", ThmClass.subst(thm_eq_x_x_Y.get, TermTests.c, int_ty, TermTests.x))
    //     )
    //     evalTests(l)

    // def run_lift_tests(): Unit =
    //     val l = List(
    //       ("ThmClass.lift(thm_eq_x_y.get, C)", ThmClass.lift(thm_eq_x_y.get, C))
    //     )
    //     evalTests(l)

    // def run_weaken_tests(): Unit =
    //     val l = List(
    //       ("ThmClass.weaken(thm_eq_x_y.get, Var(\"z17\", prop_ty))", ThmClass.weaken(thm_eq_x_y.get, Var("z17", prop_ty)))
    //     )
    //     evalTests(l)

    def run(): (Int, Int) = (0, 0)

}
