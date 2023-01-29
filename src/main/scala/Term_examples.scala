package Prover

import Context._
import TypeTests.{tvar_T, tvar_X, int_ty, prop_ty}

object TermTests:
    val x        = Var("x", tvar_T)
    val y        = Var("y", tvar_T)
    val z        = Var("z", tvar_T)
    val m        = Var("m", int_ty)
    val c        = Const("17", int_ty)
    val p        = Var("p", prop_ty)
    val fp       = Var("fp", UnaryPredicateTy(int_ty))
    val f2p      = Var("f2p", BinaryPredicateTy(int_ty, tvar_T))
    val c_eq_int = Const("=", BinaryPredicateTy(int_ty, int_ty))
    val c_eq     = Const("=", BinaryPredicateTy(tvar_T, tvar_T))
    val c_eq_2 = Const(
      "=",
      TyApp(
        TyApp(TyFormer("->", ConstructorKind(ConstructorKind(TyKind))), tvar_T),
        TyApp(TyApp(TyFormer("->", ConstructorKind(ConstructorKind(TyKind))), tvar_T), TyFormer("Prop", TyKind))
      )
    )
    val eq_x_x        = Equation(x, x, tvar_T)
    val eq_x_y        = Equation(x, y, tvar_T)
    val eq_y_x        = Equation(y, x, tvar_T)
    val eq_y_z        = Equation(y, z, tvar_T)
    val eq_x_z        = Equation(x, z, tvar_T)
    val eq_m_m        = Equation(m, m, int_ty)
    val app_ill_typed = App(c, x)
    val lam_bad       = Lam(x, x)
    val lam_complex   = Lam(x, eq_x_y)
    val lam           = Lam(m, m)
    val app_good      = App(lam, c)

    // val all_quantified_peirce_law        = Forall("x", tvar_T, peirce_law)

    val gamma_empty: Context = List()

    val a                       = eq_m_m
    val b                       = eq_x_y
    val a_and_b                 = And(a, b)
    val b_and_a                 = And(b, a)
    val a_and_b_implies_b_and_a = Implies(a_and_b, b_and_a)
