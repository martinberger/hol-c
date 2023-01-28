package Prover

import Context._
import TaintLattice._
import Ty._
import Term._
import scala.quoted.FromExpr.NoneFromExpr

object ThmClass extends ProofSystem:

    /* opaque JUST FOR NOW, TO MAKE SETTING UP TESTS EASIER. TODO: remove*/
    type Thm = (Context, Term, Taint)

    def init(gamma: Context, phi: Term): Option[Thm] =
        if valid(gamma) && gamma.contains(phi) && Term.check(phi, Prop()) then Some((gamma, phi, I))
        else { /* println("init NONE"); */
            None
        }

    def refl(gamma: Context, tm: Term, ty: Ty): Option[Thm] =
        if valid(gamma) && Term.check(tm, ty) then
            val phi = Equation(tm, tm, ty)
            Some((gamma, phi, I))
        else None

    def sym(thm: Thm): Option[Thm] =
        val (gamma, tm, taint) = thm
        tm match
            case Equation(l, r, ty) => Some((gamma, Equation(r, l, ty), taint))
            case _                  => None

    def trans(thm1: Thm, thm2: Thm): Option[Thm] =
        val (gamma1, tm1, taint1) = thm1
        val (gamma2, tm2, taint2) = thm2
        if gamma1 != gamma2 || taint1 != taint2 then return None
        (tm1, tm2) match
            case (Equation(l1, r1, ty1), Equation(l2, r2, ty2)) if r1 == l2 && ty1 == ty2 =>
                Some((gamma1, Equation(l1, r2, ty1), taint1))
            case _ => None

    def lcong(thm: Thm, x: Var): Option[Thm] =
        val (gamma, tm, taint) = thm
        if Context.fv(gamma).contains(x) then return None
        tm match
            case Equation(l, r, ty) =>
                val tm1 = Lam(x, l)
                val tm2 = Lam(x, r)
                Some((gamma, Equation(tm1, tm2, FunctionTy(x.ty, ty)), taint))
            case _ => None

    def acong(thm1: Thm, thm2: Thm): Option[Thm] =
        val (gamma1, tm1, taint1) = thm1
        val (gamma2, tm2, taint2) = thm2
        if gamma1 != gamma2 || taint1 != taint2 then return None
        (tm1, tm2) match
            case (Equation(l1, r1, FunctionTy(ty1, ty)), Equation(l2, r2, ty2)) if ty1 == ty2 =>
                val tm = Equation(App(l1, l2), App(r1, r2), ty)
                Some((gamma1, tm, taint1))
            case _ => None

    def lift(thm: Thm, bigTaint: Taint): Option[Thm] =
        val (gamma, tm, smallTaint) = thm
        if !leq(smallTaint, bigTaint) then return { println("lift fails"); None }
        Some((gamma, tm, bigTaint))

    def beta(gamma: Context, lam: Lam, src: Ty, target: Ty, tm: Term): Option[Thm] =
        val Lam(x, body) = lam
        if !valid(gamma) || !Term.check(lam, FunctionTy(src, target)) || !Term.check(tm, src) || x.ty != src then return None
        val newTm = Equation(App(lam, tm), Term.subst(body, tm, x), target)
        Some((gamma, newTm, I))

    def tysubst(thm: Thm, ty: Ty, tv: TyVar): Option[Thm] =
        val (gamma, phi, taint) = thm
        if !Ty.check(ty, TyKind) then return None
        val newGamma = Context.tySubst(gamma, ty, tv)
        val newTm    = Term.tySubst(phi, ty, tv)
        Some((newGamma, newTm, taint))

    def subst(thm: Thm, tm: Term, ty: Ty, x: Var): Option[Thm] =
        val (gamma, phi, taint) = thm
        if !Term.check(tm, ty) then return None
        Some((Context.subst(gamma, tm, x), Term.subst(phi, tm, x), taint))

    def iffE1(thm1: Thm, thm2: Thm): Option[Thm] =
        val (gamma1, tm1, taint1) = thm1
        val (gamma2, tm2, taint2) = thm2
        if gamma1 != gamma2 || taint1 != taint2 then return None
        tm1 match
            case Equivalence(l, r) if l == tm2 => Some((gamma1, r, taint1))
            case _                             => None

    def iffE2(thm1: Thm, thm2: Thm): Option[Thm] =
        val (gamma1, tm1, taint1) = thm1
        val (gamma2, tm2, taint2) = thm2
        if gamma1 != gamma2 || taint1 != taint2 then return None
        tm1 match
            case Equivalence(l, r) if r == tm2 => Some((gamma1, l, taint1))
            case _                             => None

    def iffI(thm1: Thm, thm2: Thm): Option[Thm] =
        val (gamma1, tm1, taint1) = thm1
        val (gamma2, tm2, taint2) = thm2
        println(s"iffI thm1 = ${thm1}")
        println(s"iffI thm2 = ${thm2}")
        if !gamma1.contains(tm2) then { println(s"iffI fails1a, gamma1 = ${gamma1}, tm2 = $tm2"); return None }
        if !gamma2.contains(tm1) then { println(s"iffI fails1b"); return None }
        if taint1 != taint2 then { println(s"iffI fails1 taint1 = ${taint1} taint2 = $taint2"); return None }
        // if !gamma1.contains(tm2) || !gamma2.contains(tm1) || taint1 != taint2 then {
        //     println(s"iffI fails1 taint1 = ${taint1} taint2 = $taint2"); return None

        val gamma3 = remove(gamma1, tm2)
        val gamma4 = remove(gamma2, tm1)
        if gamma3 != gamma4 then { println("iffI failss"); return None }
        Some((gamma3, Equivalence(tm1, tm2), taint1))

    def trueI(gamma: Context): Option[Thm] =
        if !valid(gamma) then return None
        Some((gamma, TrueProp(), I))

    def falseE(thm: Thm, phi: Term): Option[Thm] =
        if !Term.check(phi, Prop()) then return None
        thm match
            case (gamma, FalseProp(), taint) => Some((gamma, phi, taint))
            case _                           => None

    def conjI(thm1: Thm, thm2: Thm): Option[Thm] =
        // println(">>>>>>>>>>>>>>>>> conjI")
        val (gamma1, tm1, taint1) = thm1
        val (gamma2, tm2, taint2) = thm2
        if gamma1 != gamma2 || taint1 != taint2 then return None
        Some((gamma1, And(tm1, tm2), taint1))

    def conjE1(thm: Thm): Option[Thm] =
        thm match
            case (gamma, And(l, _), taint) => Some((gamma, l, taint))
            case _                         => None

    def conjE2(thm: Thm): Option[Thm] =
        thm match
            case (gamma, And(_, r), taint) => Some((gamma, r, taint))
            case _                         => None

    def disjI1(thm: Thm, tm2: Term): Option[Thm] =
        if !Term.check(tm2, Prop()) then return None
        val (gamma, tm1, taint) = thm
        Some((gamma, Or(tm1, tm2), taint))

    def disjI2(thm: Thm, tm1: Term): Option[Thm] =
        if !Term.check(tm1, Prop()) then return None
        val (gamma, tm2, taint) = thm
        Some((gamma, Or(tm1, tm2), taint))

    def disjE(thm1: Thm, thm2: Thm, thm3: Thm): Option[Thm] =
        val (gamma2, tm2, taint2) = thm2
        val (gamma3, tm3, taint3) = thm3
        thm1 match
            case (gamma1, Or(l, r), taint1) =>
                if taint1 != taint2 || taint2 != taint3 ||
                    !gamma2.contains(l) || !gamma3.contains(r) || tm2 != tm3 ||
                    gamma1 != remove(gamma2, l) || gamma1 != remove(gamma3, r)
                then return None
                Some((gamma1, tm2, taint1))
            case _ => None

    def impI(thm: Thm, tm1: Term): Option[Thm] =
        val (gamma, tm2, taint) = thm
        if !gamma.contains(tm1) then
            return { /* println("implI NONE"); */
                None
            }
        Some((remove(gamma, tm1), Implies(tm1, tm2), taint))

    def impE(thm1: Thm, thm2: Thm): Option[Thm] = // TODO remove debug junk
        val (gamma2, tm2, taint2) = thm2
        thm1 match
            case (gamma1, Implies(l, r), taint1) if l == tm2 && taint1 == taint2 && gamma1 == gamma2 => Some((gamma1, r, taint1))
            case _ => {
                /* println("implE NONE"); */
                None
            }

    def negI(thm: Thm, phi: Term): Option[Thm] =
        val (gamma, tm, taint) = thm
        if tm != FalseProp() || !gamma.contains(phi) then
            return {
                println("negI NONE");
                None
            }
        Some((remove(gamma, phi), Neg(tm), taint))

    def negE(thm1: Thm, thm2: Thm): Option[Thm] = // TODO remove println junk
        // println(s"   negE(${thm1}, ${thm2})")
        val (gamma1, tm1, taint1) = thm1
        thm2 match
            case (gamma2, Neg(tm2), taint2) if tm1 == tm2 && gamma1 == gamma2 && taint1 == taint2 =>
                // if tm1 != tm2 then { println(s"tm1 (${tm1}) != tm2 (${tm2})"); return None }
                // if gamma1 != gamma2 then { println("gamma1 != gamma2"); return None }
                // if taint1 != taint2 then { println("taint1 != taint2"); return None }
                Some((gamma1, FalseProp(), taint1))
            case (_, tm2, _) => {
                /* println(s"negE NONE: $tm1 =?= ${tm2}"); */
                None
            }

    def allE(thm: Thm, tm: Term): Option[Thm] =
        val (gamma, phi, taint) = thm
        phi match
            case Forall(x, ty, body) if Term.check(tm, ty) =>
                Some((gamma, Term.subst(phi, tm, Var(x, ty)), taint))
            case _ => None

    def allI(thm: Thm, x: Var): Option[Thm] =
        val (gamma, tm, taint) = thm
        if Context.fv(gamma).contains(x) then return None
        Some((gamma, Forall(x.name, x.ty, tm), taint))

    def exI(thm: Thm, phi: Term, x: Var, tm: Term): Option[Thm] =
        if !Term.check(tm, x.ty) || !Term.check(phi, Prop()) then return None
        val (gamma, tm2, taint) = thm
        val tm3                 = Term.subst(phi, tm, x)
        if tm3 != tm2 then return None
        Some(gamma, Exists(x.name, x.ty, phi), taint)

    def exE(thm1: Thm, thm2: Thm, name: String): Option[Thm] =
        val (gamma1, tm1, taint1) = thm1
        val (gamma2, tm2, taint2) = thm2
        if taint1 != taint2 then return None
        tm1 match
            case Exists(x, ty, phi) =>
                val y   = Var(name, ty)
                val tm3 = Term.subst(phi, y, Var(x, ty))
                if gamma1 != remove(gamma2, tm2) || !gamma2.contains(tm3) ||
                    (Context.fv(gamma1) ++ Term.fv(phi)).contains(y)
                then return None
                Some((gamma1, tm2, taint1))
            case _ => None

    def eta(gamma: Context, tm: Term, ty: Ty): Option[Thm] =
        if !Context.valid(gamma) || !Term.check(tm, ty) then return None
        (tm, ty) match
            case (Lam(x, App(f, y)), FunctionTy(l, r)) if l == x.ty && x == y =>
                if Term.fv(f).contains(x) then return None
                val phi = Equation(tm, f, ty)
                Some((gamma, phi, I))
            case _ => None

    def lem(gamma: Context, tm: Term): Option[Thm] =
        if !valid(gamma) || !Term.check(tm, Prop()) then return None
        Some((gamma, Or(tm, Neg(tm)), C))

    def raa(thm: Thm, tm: Term): Option[Thm] = // TODO remove debug junk
        // println(s"raa($thm, $tm)")
        thm match
            case (gamma, FalseProp(), _) if gamma.contains(Neg(tm)) =>
                println(s"raa Success ctx = ${remove(gamma, Neg(tm))}, formula = ${tm}")
                Some((remove(gamma, Neg(tm)), tm, C))
            case _ => { println("raa FAILS"); None }

    def weaken(thm: Thm, tm2: Term): Option[Thm] =
        val (gamma1, tm1, taint) = thm
        val gamma2               = tm2 :: gamma1
        if !valid(gamma2) then return None
        Some((gamma2, tm1, taint))

    // def choice(thm: Thm, f0: String): Option[Thm] = // This is N // TODO this is super ugly and too complex, needs refactoring
    //     val (gamma, tm, taint) = thm
    //     // TODO: check that f0 is fresh
    //     tm match
    //         case Forall(x1, x1_ty, Exists(y1, y1_ty, BinaryPredicate(p, x2, y2))) if Var(x1, x1_ty) == x2 && Var(y1, y1_ty) == y2 =>
    //             val f         = Var(f0, FunctionTy(x1_ty, y1_ty))
    //             val choiceThm = Exists(f0, f.ty, Forall(x1, x1_ty, BinaryPredicate(p, Var(x1, x1_ty), App(f, Var(x1, x1_ty)))))
    //             Some((gamma, choiceThm, CH))
    //         case _ => None

    // def lift(thm: Thm, newTaint: Taint): Option[Thm] = // This is N5
    //     val (gamma, tm, oldTaint) = thm
    //     if !TaintLattice.leq(oldTaint, newTaint) then return None
    //     Some((gamma, tm, newTaint))

    // def weaken(thm: Thm, x: Var): Option[Thm] = // This is N
    //     val (gamma, tm, taint) = thm
    //     val newGamma           = x :: gamma
    //     if !valid(newGamma) || Context.fv(gamma).contains(x) then return None
    //     Some((newGamma, tm, taint))

    // def weakExcludedMiddle(gamma: Context, tm: Term): Option[Thm] = // This is N34
    //     if !valid(gamma) || !Term.check(tm, Prop()) then return None
    //     Some((gamma, Or(Neg(tm), Neg(Neg(tm))), W))

    // def n36(gamma: Context, tv: TyVar, s: Term, t: Term): Option[Thm] =
    //     if !valid(gamma) then return None
    //     if !Term.check(s, SetTy(tv)) || !Term.check(t, SetTy(tv)) then return None
    //     val tmp1 = UnionSet(tv, s, t)
    //     val tmp2 = UnionSet(tv, t, s)
    //     Some((gamma, Equation(tmp1, tmp2, tv), I))

    // def n37(gamma: Context, tv: TyVar): Option[Thm] =
    //     if !valid(gamma) then return None
    //     val tmp = FunctionTy(SetTy(tv), SetTy(tv))
    //     val ty  = TernaryFunctionTy(tmp, tmp, tv, tv)
    //     val eq  = Equation(FunctComposer(tv, tv, tv, Cmpl(tv), Cmpl(tv)), Identity(tv), tv)
    //     Some((gamma, eq, C))

    // def n38(thm: Thm): Option[Thm] =
    //     val (gamma, tm, taint) = thm
    //     tm match
    //         case Equation(
    //               App(f @ Var(_, FunctionTy(ty_f, ty_f_res)), x @ Var(x1, ty_x1)),
    //               App(g @ Var(_, FunctionTy(ty_g, ty_g_res)), Var(x2, ty_x2)),
    //               ty
    //             ) if ty_f == ty_x1 && ty_g == ty_x2 && ty_f_res == ty_g_res && !Context.fv(gamma).contains(x) =>
    //             Some((gamma, Equation(f, g, ty_f_res), taint))
    //         case _ => None

    // def n39(thm: Thm): Option[Thm] =
    //     val (gamma, tm, taint) = thm
    //     tm match
    //         case Equivalence(MemberCheck(tv_s, x_s, s), MemberCheck(tv_t, x_t, t))
    //             if tv_s == tv_t && x_s == x_t && !Context.fv(gamma).contains(x_s) =>
    //             Some((gamma, Equation(s, t, SetTy(tv_s)), taint))
    //         case _ => None

    // def n40(gamma: Context): Option[Thm] =
    //     if !valid(gamma) then return None
    //     Some((gamma, Equation(App(Lift(), TrueBool()), TrueProp(), Prop()), I))

    // def n41(gamma: Context): Option[Thm] =
    //     if !valid(gamma) then return None
    //     Some((gamma, Equation(App(Lift(), FalseBool()), FalseProp(), Prop()), I))

    // def n42(thm: Thm, x: Var, tm: Term): Option[Thm] =
    //     thm match
    //         case (gamma, FalseProp(), taint) =>
    //             val tmp1 = App(tm, x)
    //             val tmp  = Forall(x.name, x.ty, Neg(tmp1))
    //             if !gamma.contains(tmp) then return None
    //             Some((remove(gamma, tmp), Exists(x.name, x.ty, tmp1), C))
    //         case _ => None

    // def n43(gamma: Context, tv: TyVar): Option[Thm] =
    //     if !valid(gamma) then return None
    //     Some((gamma, App(Finite(tv), EmptySet(tv)), I))

    // def n44(thm: Thm, tv: TyVar, x: Var): Option[Thm] =
    //     val (gamma, tm, taint) = thm
    //     tm match
    //         case App(Finite(tv), s) if Term.check(s, SetTy(tv)) && Term.check(x, tv) =>
    //             val tm = App(Finite(tv), s)
    //             Some((gamma, UnionSet(tv, tm, SingletonSet(tv, x)), taint))
    //         case _ => None

    def show(thm: Thm): (Context, Term, Taint) = thm
