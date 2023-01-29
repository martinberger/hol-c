package Prover

object TypeTests:
    var n = 0

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
