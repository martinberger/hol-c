package Prover

object KindTests:
    var n = 0

    val tykind          = TyKind
    val ckind1          = ConstructorKind(tykind)
    val ckind2          = ConstructorKind(ckind1)
    val ckind3          = ConstructorKind(ckind2)
    val tyfunkind_apply = TyFunctionKind()
    val binarytyfunkind = BinaryTyFunctionKind()

    def run(): (Int, Int) = (0, 0)
