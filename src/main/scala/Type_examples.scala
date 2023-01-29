package Prover

object TypeTests:

    val tvar_T                     = TyVar("T")
    val tvar_X                     = TyVar("X")
    val int_ty                     = TyFormer("Int", TyKind)
    val prop_ty                    = TyFormer("Prop", TyKind)
    val function_ty                = TyFormer("->", KindTests.binarytyfunkind)
    val prop_function_ty           = TyApp(function_ty, prop_ty)
    val prop_prop_function_ty      = TyApp(prop_function_ty, prop_ty)
    val prop_prop_prop_function_ty = TyApp(prop_function_ty, prop_prop_function_ty)

    val t_function_ty     = TyApp(function_ty, tvar_T)
    val x_function_ty     = TyApp(function_ty, tvar_X)
    val t_t_function_ty   = TyApp(t_function_ty, tvar_T)
    val x_t_t_function_ty = TyApp(x_function_ty, t_t_function_ty)

    val tests = List(
      ("tvar_T", tvar_T, TyKind),
      ("tvar_X", tvar_X, TyKind),
      ("int_ty", int_ty, TyKind),
      ("prop_ty", prop_ty, TyKind),
      ("function_ty", function_ty, KindTests.binarytyfunkind),
      ("prop_function_ty", prop_function_ty, TyFunctionKind()),
      ("prop_prop_function_ty", prop_prop_function_ty, TyKind),
      ("prop_prop_prop_function_ty", prop_prop_prop_function_ty, TyKind),
      ("t_function_ty", t_function_ty, TyFunctionKind()),
      ("x_function_ty", x_function_ty, TyFunctionKind()),
      ("t_t_function_ty", t_t_function_ty, TyKind),
      ("x_t_t_function_ty", x_t_t_function_ty, TyKind)
    )

    def run(): (Int, Int) =
        var n      = 0
        var failed = 0
        tests.foreach(t =>
            n += 1
            val (name, ty, ki) = t
            if !Ty.check(ty, ki) then { failed += 1; println(s"   Failed test ${name}") }
        )
        (n, failed)
