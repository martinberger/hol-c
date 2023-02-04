package Prover

import org.scalacheck.Properties
import org.scalacheck.Prop.{forAll, propBoolean}
import org.scalacheck._
import Gen._
// import org.scalacheck.Arbitrary

object MyGenerators:
    val genTyKind = const(TyKind)
    val genConstructorKind = for {
        ki <- genKind
    } yield ConstructorKind(ki)
    def genKind: Gen[Kind] = oneOf(genTyKind, lzy(genConstructorKind))

    val genTyVar       = for { x <- Gen.alphaStr } yield TyVar(x)
    val genTyFormer    = for { x <- Gen.alphaStr; k <- genKind } yield TyFormer(x, k)
    val genTyApp       = for { l <- genTy; r <- genTy } yield TyApp(l, r)
    def genTy: Gen[Ty] = oneOf(genTyVar, genTyFormer, lzy(genTyApp))

    val genVar           = for { x <- Gen.alphaStr; ty <- genTy } yield Var(x, ty)
    val genConst         = for { c <- Gen.alphaStr; ty <- genTy } yield Const(c, ty)
    val genApp           = for { l <- genTm; r <- genTm } yield App(l, r)
    val genLam           = for { x <- genVar; b <- genTm } yield Lam(x, b)
    def genTm: Gen[Term] = oneOf(genVar, genConst, lzy(genApp), lzy(genLam))

    def genTaint: Gen[Taint] = oneOf(I, W, C, CH)

object KindsPropTests extends Properties("KindsPropTests"):
    import MyGenerators.{genKind}
    property("Kinds Equality 1") = forAll(genKind)((k: Kind) => k == k)
    property("Kinds Equality 2") = forAll(genKind)((k: Kind) => ConstructorKind(k) != k)
    property("Kinds Equality 3") = forAll(genKind, genKind)((k1: Kind, k2: Kind) => (k1 == k2) == (ConstructorKind(k1) == ConstructorKind(k2)))

object TypesPropTests extends Properties("TypesPropTests"):
    import MyGenerators.{genTy, genKind}
    property("Type Equality 1") = forAll(genTy)((ty: Ty) => ty == ty)
    property("Type Equality 2") = forAll((x1: String, x2: String) => { (x1 == x2) == (TyVar(x1) == TyVar(x2)) })
    property("Type Equality 3") = forAll(genKind, genKind)((k1: Kind, k2: Kind) =>
        forAll((x1: String, x2: String) => (x1 == x2 && k1 == k2) == (TyFormer(x1, k1) == TyFormer(x2, k2)))
    )
    property("Type Equality 4") =
        forAll(genTy, genTy, genTy, genTy)((ty1: Ty, ty2: Ty, ty3: Ty, ty4: Ty) => (ty1 == ty3 && ty2 == ty4) == (TyApp(ty1, ty2) == TyApp(ty3, ty4)))

object FreshnessPropTests extends Properties("FreshnessPropTests"):
    import MyGenerators.{genVar, genTy}
    import Lib.{gensym, fresh, freshVar}
    property("gensym always fresh 1") = forAll((x: String) => Lib.gensym() != Lib.gensym())
    property("fresh always fresh 1") = forAll((s: Set[String]) => fresh(s) != fresh(s))
    property("fresh always fresh 2") = forAll((s1: Set[String], s2: Set[String]) => fresh(s1) != fresh(s2))
    property("fresh var") =
        forAll(Gen.listOf[Var](genVar), genTy, Gen.listOf[Var](genVar), genTy)((vs1: List[Var], ty1: Ty, vs2: List[Var], ty2: Ty) =>
            freshVar(vs1.toSet, ty1) != freshVar(vs1.toSet, ty2)
        )

object TermPropTests extends Properties("TermPropTests"):
    import MyGenerators.{genTm, genVar, genTy, genTyVar}
    import Term.{subst, tySubst}
    property("Term equality 0") = forAll(genTy)((ty: Ty) => Var("", ty) == Var("", ty))
    property("Term equality 1") = forAll(genVar)((x: Var) => x == x)
    property("Term equality 2") = forAll(genTm, genTm)((t1: Term, t2: Term) => { (t1 == t2) == (t2 == t1) })
    // property("Term equality 3") = forAll(genTm, genTm, genTm)((t1: Term, t2: Term, t3: Term) => { (t1 == t2 && t2 == t3) ==> (t1 == t3) })
    property("Substitution 1") = forAll(genVar, genTm)((x: Var, t: Term) => t == subst(x, t, x))
    property("empty string 1") = forAll(genTy)((ty: Ty) => Var("", ty) == Var("", ty))
    property("empty string 2") = forAll(genTy)((ty: Ty) => Var("", ty) ne Var("", ty))
    property("Substitution 1") = forAll(genVar, genTm)((x: Var, t: Term) => { t == subst(x, t, x) })
    property("Substitution 2") = forAll(genVar, genVar, genTm)((x: Var, y: Var, t: Term) => (x != y) ==> (x == subst(x, t, y)))
    property("Type substitution 1") = forAll((x: String) => forAll(genTyVar, genTy)((tv: TyVar, ty: Ty) => Var(x, ty) == tySubst(Var(x, tv), ty, tv)))
    property("Type substitution 2") = forAll((x: String) =>
        forAll(genTyVar, genTyVar, genTy)((tv1: TyVar, tv2: TyVar, ty: Ty) => {
            (tv1 != tv2) ==>
                (Var(x, tv1) == tySubst(Var(x, tv1), ty, tv2))
        })
    )

object TaintPropTests extends Properties("TaintPropTests"):

    import TaintLattice._
    import MyGenerators.{genTaint}
    property("Reflexivity") = forAll(genTaint)((t: Taint) => lub(t, t) == t)
    property("Symmetry") = forAll(genTaint, genTaint)((t1: Taint, t2: Taint) => lub(t1, t2) == lub(t2, t1))
    property("Associativity") =
        forAll(genTaint, genTaint, genTaint)((t1: Taint, t2: Taint, t3: Taint) => lub(lub(t1, t2), t3) == lub(t1, lub(t2, t3)))
    property("Top") = forAll(genTaint)((t: Taint) => leq(t, top))
    property("C") = forAll(genTaint)((t: Taint) => t != top ==> leq(t, C))
    property("W") = forAll(genTaint)((t: Taint) => t != bot ==> leq(W, t))
    property("Bottom") = forAll(genTaint)((t: Taint) => leq(bot, t))
