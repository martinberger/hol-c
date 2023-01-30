package Prover

import Context._
import TypeTests.{tvar_T, tvar_X, int_ty, prop_ty}

object TermTests:
    val x = Var("x", Prop())
    val y = Var("y", Prop())
    val z = Var("z", prop_ty)
    val m = Var("m", int_ty)
    val p = Var("p", tvar_T)
    val q = Var("q", tvar_T)
    val c = Const("17", int_ty)
    // val p        = Var("p", prop_ty)
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
    val eq_x_x = Equation(x, x, Prop())
    val eq_x_y = Equation(x, y, Prop())
    val eq_y_x = Equation(y, x, Prop())
    val eq_y_z = Equation(y, z, Prop())
    val eq_x_z = Equation(x, z, Prop())
    val eq_m_m = Equation(m, m, int_ty)
    val eq_p_q = Equation(p, q, tvar_T)
    val eq_q_q = Equation(q, q, tvar_T)
    // val app_ill_typed = App(c, x)
    val lam_bad     = Lam(x, x)
    val lam_complex = Lam(x, eq_x_y)
    val lam         = Lam(m, m)
    val app_good    = App(lam, c)

    val gamma_empty: Context = List()

    val a                       = eq_m_m
    val b                       = eq_x_y
    val a_and_b                 = And(a, b)
    val b_and_a                 = And(b, a)
    val a_and_b_implies_b_and_a = Implies(a_and_b, b_and_a)

    val tests = List(
      ("a", a),
      ("b", b),
      ("a_and_b", a_and_b),
      ("b_and_a", b_and_a),
      ("a_and_b_implies_b_and_a", a_and_b_implies_b_and_a),
      ("x", x),
      ("y", y),
      ("z", z),
      ("m", m),
      ("c", c),
      ("p", p),
      ("fp", fp),
      ("f2p", f2p),
      ("c_eq_int", c_eq_int),
      ("c_eq", c_eq),
      ("c_eq_2", c_eq_2),
      ("eq_x_x", eq_x_x),
      ("eq_x_y", eq_x_y),
      ("eq_y_x", eq_y_x),
      ("eq_y_z", eq_y_z),
      ("eq_x_z", eq_x_z),
      ("eq_m_m", eq_m_m),
      ("eq_q_q", eq_q_q),
      ("eq_p_q", eq_p_q),
      ("lam_bad", lam_bad),
      ("lam_complex", lam_complex),
      ("lam", lam),
      ("app_good", app_good)
    )

    def run(): (Int, Int) =
        var n      = 0
        var failed = 0
        tests.foreach(t =>
            n += 1
            val (name, tm) = t
            if Term.tyInference(tm) == None then { failed += 1; println(s"   Failed test ${name}") }
        )
        (n, failed)
