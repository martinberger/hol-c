package Prover

import Context.{Context, valid, remove, fv, tySubst}
import TaintLattice.{leq}
import Term.{check}

case class Thm private (ctx: Context, tm: Term, t: Taint)

object Thm:

    def init(gamma: Context, phi: Term): Option[Thm] =
        if valid(gamma) && gamma.contains(phi) && check(phi, Prop()) then Some(Thm(gamma, phi, I))
        else None

    def refl(gamma: Context, tm: Term, ty: Ty): Option[Thm] =
        if valid(gamma) && check(tm, ty) then
            val phi = Equation(tm, tm, ty)
            Some(Thm(gamma, phi, I))
        else None

    def sym(thm: Thm): Option[Thm] =
        val Thm(gamma, tm, taint) = thm
        tm match
            case Equation(l, r, ty) => Some(Thm(gamma, Equation(r, l, ty), taint))
            case _                  => None

    def trans(thm1: Thm, thm2: Thm): Option[Thm] =
        val Thm(gamma1, tm1, taint1) = thm1
        val Thm(gamma2, tm2, taint2) = thm2
        if gamma1 != gamma2 || taint1 != taint2 then return None
        (tm1, tm2) match
            case (Equation(l1, r1, ty1), Equation(l2, r2, ty2)) if r1 == l2 && ty1 == ty2 =>
                Some(Thm(gamma1, Equation(l1, r2, ty1), taint1))
            case _ => None

    def lcong(thm: Thm, x: Var): Option[Thm] =
        val Thm(gamma, tm, taint) = thm
        if fv(gamma).contains(x) then return None
        tm match
            case Equation(l, r, ty) =>
                val tm1 = Lam(x, l)
                val tm2 = Lam(x, r)
                Some(Thm(gamma, Equation(tm1, tm2, FunctionTy(x.ty, ty)), taint))
            case _ => None

    def acong(thm1: Thm, thm2: Thm): Option[Thm] =
        val Thm(gamma1, tm1, taint1) = thm1
        val Thm(gamma2, tm2, taint2) = thm2
        if gamma1 != gamma2 || taint1 != taint2 then return None
        (tm1, tm2) match
            case (Equation(l1, r1, FunctionTy(ty1, ty)), Equation(l2, r2, ty2)) if ty1 == ty2 =>
                val tm = Equation(App(l1, l2), App(r1, r2), ty)
                Some(Thm(gamma1, tm, taint1))
            case _ => None

    def lift(thm: Thm, bigTaint: Taint): Option[Thm] =
        val Thm(gamma, tm, smallTaint) = thm
        if !leq(smallTaint, bigTaint) then return None
        Some(Thm(gamma, tm, bigTaint))

    def beta(gamma: Context, lam: Lam, src: Ty, target: Ty, tm: Term): Option[Thm] =
        val Lam(x, body) = lam
        if !valid(gamma) || !check(lam, FunctionTy(src, target)) || !check(tm, src) || x.ty != src then return None
        val newTm = Equation(App(lam, tm), Term.subst(body, tm, x), target)
        Some(Thm(gamma, newTm, I))

    def inst(thm: Thm, ty: Ty, tv: TyVar): Option[Thm] =
        val Thm(gamma, phi, taint) = thm
        if !Ty.check(ty, TyKind) then return None
        val newGamma = Context.tySubst(gamma, ty, tv)
        val newTm    = Term.tySubst(phi, ty, tv)
        Some(Thm(newGamma, newTm, taint))

    def subst(thm: Thm, tm: Term, ty: Ty, x: Var): Option[Thm] =
        val Thm(gamma, phi, taint) = thm
        if !Term.check(tm, ty) then return None
        Some(Thm(Context.subst(gamma, tm, x), Term.subst(phi, tm, x), taint))

    def iffE1(thm1: Thm, thm2: Thm): Option[Thm] =
        val Thm(gamma1, tm1, taint1) = thm1
        val Thm(gamma2, tm2, taint2) = thm2
        if gamma1 != gamma2 || taint1 != taint2 then return None
        tm1 match
            case Equivalence(l, r) if l == tm2 => Some(Thm(gamma1, r, taint1))
            case _                             => None

    def iffE2(thm1: Thm, thm2: Thm): Option[Thm] =
        val Thm(gamma1, tm1, taint1) = thm1
        val Thm(gamma2, tm2, taint2) = thm2
        if gamma1 != gamma2 || taint1 != taint2 then return None
        tm1 match
            case Equivalence(l, r) if r == tm2 => Some(Thm(gamma1, l, taint1))
            case _                             => None

    def iffI(thm1: Thm, thm2: Thm): Option[Thm] =
        val Thm(gamma1, tm1, taint1) = thm1
        val Thm(gamma2, tm2, taint2) = thm2
        if !gamma1.contains(tm2) || !gamma2.contains(tm1) || taint1 != taint2 then return None
        val gamma3 = remove(gamma1, tm2)
        val gamma4 = remove(gamma2, tm1)
        if gamma3 != gamma4 then return None
        Some(Thm(gamma3, Equivalence(tm1, tm2), taint1))

    def trueI(gamma: Context): Option[Thm] =
        if !valid(gamma) then return None
        Some(Thm(gamma, TrueProp(), I))

    def falseE(thm: Thm, phi: Term): Option[Thm] =
        if !check(phi, Prop()) then return None
        thm match
            case Thm(gamma, FalseProp(), taint) => Some(Thm(gamma, phi, taint))
            case _                              => None

    def conjI(thm1: Thm, thm2: Thm): Option[Thm] =
        val Thm(gamma1, tm1, taint1) = thm1
        val Thm(gamma2, tm2, taint2) = thm2
        if gamma1 != gamma2 || taint1 != taint2 then return None
        Some(Thm(gamma1, And(tm1, tm2), taint1))

    def conjE1(thm: Thm): Option[Thm] =
        thm match
            case Thm(gamma, And(l, _), taint) => Some(Thm(gamma, l, taint))
            case _                            => None

    def conjE2(thm: Thm): Option[Thm] =
        thm match
            case Thm(gamma, And(_, r), taint) => Some(Thm(gamma, r, taint))
            case _                            => None

    def disjI1(thm: Thm, tm2: Term): Option[Thm] =
        if !check(tm2, Prop()) then return None
        val Thm(gamma, tm1, taint) = thm
        Some(Thm(gamma, Or(tm1, tm2), taint))

    def disjI2(thm: Thm, tm1: Term): Option[Thm] =
        if !check(tm1, Prop()) then return None
        val Thm(gamma, tm2, taint) = thm
        Some(Thm(gamma, Or(tm1, tm2), taint))

    def disjE(thm1: Thm, thm2: Thm, thm3: Thm): Option[Thm] =
        val Thm(gamma2, tm2, taint2) = thm2
        val Thm(gamma3, tm3, taint3) = thm3
        thm1 match
            case Thm(gamma1, Or(l, r), taint1)
                if taint1 == taint2
                    && taint2 == taint3
                    && gamma2.contains(l)
                    && gamma3.contains(r)
                    && tm2 == tm3
                    && gamma1 == remove(gamma2, l)
                    && gamma1 == remove(gamma3, r) =>
                Some(Thm(gamma1, tm2, taint1))
            case _ => None

    def impI(thm: Thm, tm1: Term): Option[Thm] =
        val Thm(gamma, tm2, taint) = thm
        if !gamma.contains(tm1) then return None
        Some(Thm(remove(gamma, tm1), Implies(tm1, tm2), taint))

    def impE(thm1: Thm, thm2: Thm): Option[Thm] =
        val Thm(gamma2, tm2, taint2) = thm2
        thm1 match
            case Thm(gamma1, Implies(l, r), taint1) if l == tm2 && taint1 == taint2 && gamma1 == gamma2 => Some(Thm(gamma1, r, taint1))
            case _                                                                                      => None

    def negI(thm: Thm, phi: Term): Option[Thm] =
        val Thm(gamma, tm, taint) = thm
        if tm != FalseProp() || !gamma.contains(phi) then return None
        Some(Thm(remove(gamma, phi), Neg(phi), taint))

    def negE(thm1: Thm, thm2: Thm): Option[Thm] =
        val Thm(gamma1, tm1, taint1) = thm1
        thm2 match
            case Thm(gamma2, Neg(tm2), taint2) if tm1 == tm2 && gamma1 == gamma2 && taint1 == taint2 =>
                Some(Thm(gamma1, FalseProp(), taint1))
            case _ => None

    def allE(thm: Thm, tm: Term): Option[Thm] =
        val Thm(gamma, phi, taint) = thm
        phi match
            case Forall(x, ty, body) if check(tm, ty) =>
                Some(Thm(gamma, Term.subst(phi, tm, Var(x, ty)), taint))
            case _ => None

    def allI(thm: Thm, x: Var): Option[Thm] =
        val Thm(gamma, tm, taint) = thm
        if fv(gamma).contains(x) then return None
        Some(Thm(gamma, Forall(x.name, x.ty, tm), taint))

    def exI(thm: Thm, phi: Term, x: Var, tm: Term): Option[Thm] =
        if !check(tm, x.ty) || !check(phi, Prop()) then return None
        val Thm(gamma, tm2, taint) = thm
        val tm3                    = Term.subst(phi, tm, x)
        if tm3 != tm2 then return None
        Some(Thm(gamma, Exists(x.name, x.ty, phi), taint))

    def exE(thm1: Thm, thm2: Thm, name: String): Option[Thm] =
        val Thm(gamma1, tm1, taint1) = thm1
        val Thm(gamma2, tm2, taint2) = thm2
        if taint1 != taint2 then return None
        tm1 match
            case Exists(x, ty, phi) =>
                val y   = Var(name, ty)
                val tm3 = Term.subst(phi, y, Var(x, ty))
                if gamma1 != remove(gamma2, tm2) || !gamma2.contains(tm3) ||
                    (fv(gamma1) ++ Term.fv(phi)).contains(y)
                then return None
                Some(Thm(gamma1, tm2, taint1))
            case _ => None

    def eta(gamma: Context, tm: Term, ty: Ty): Option[Thm] =
        if !valid(gamma) || !check(tm, ty) then return None
        (tm, ty) match
            case (Lam(x, App(f, y)), FunctionTy(l, r)) if l == x.ty && x == y =>
                if Term.fv(f).contains(x) then return None
                val phi = Equation(tm, f, ty)
                Some(Thm(gamma, phi, I))
            case _ => None

    def lem(gamma: Context, tm: Term): Option[Thm] =
        if !valid(gamma) || !check(tm, Prop()) then return None
        Some(Thm(gamma, Or(tm, Neg(tm)), C))

    def raa(thm: Thm, tm: Term): Option[Thm] =
        thm match
            case Thm(gamma, FalseProp(), _) if gamma.contains(Neg(tm)) => Some(Thm(remove(gamma, Neg(tm)), tm, C))
            case _                                                     => None

    def wk(thm: Thm, tm2: Term): Option[Thm] =
        val Thm(gamma1, tm1, taint) = thm
        val gamma2                  = tm2 :: gamma1
        if !valid(gamma2) then return None
        Some(Thm(gamma2, tm1, taint))

    def weakLem(gamma: Context, tm: Term): Option[Thm] =
        if !valid(gamma) || !check(tm, Prop()) then return None
        Some(Thm(gamma, Or(Neg(tm), Neg(Neg(tm))), W))

    def axiomOfChoice(
        gamma: Context,
        p: Term,
        alpha: TyVar,
        beta: TyVar,
        x: Var,
        y: Var,
        f: Var
    ): Option[Thm] =
        val targetTy = BinaryPredicateTy(alpha, beta)
        if !valid(gamma) || !check(p, targetTy) || x.ty != alpha || y.ty != beta || f.ty != FunctionTy(alpha, beta) then return None
        val tm1 = Forall(x.name, x.ty, Exists(y.name, y.ty, App(App(p, x), y)))
        val tm2 = Exists(f.name, f.ty, Forall(x.name, x.ty, App(App(p, x), App(f, x))))
        val tm  = Implies(tm1, tm2)
        if !check(tm, Prop()) then return None
        Some(Thm(gamma, tm, CH))

    def show(thm: Thm): (Context, Term, Taint) = (thm.ctx, thm.tm, thm.t)
