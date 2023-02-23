package Prover

import Context._
import Thm._
import ProofState.{Goal}

sealed trait PreTactic
case class Init_pretac()                                              extends PreTactic
case class TrueI_pretac()                                             extends PreTactic
case class FalseE_pretac()                                            extends PreTactic
case class Lift_pretac(smallTaint: Taint)                             extends PreTactic
case class Refl_pretac()                                              extends PreTactic
case class Sym_pretac()                                               extends PreTactic
case class Trans_pretac(tm: Term)                                     extends PreTactic
case class Lcong_pretac()                                             extends PreTactic
case class Acong_pretac()                                             extends PreTactic
case class Beta_pretac()                                              extends PreTactic
case class Inst_pretac(gamma: Context, tm: Term, ty: Ty, tv: TyVar)   extends PreTactic
case class Eta_pretac()                                               extends PreTactic
case class Subst_pretac(gamma: Context, tm1: Term, tm2: Term, x: Var) extends PreTactic
case class IffE1_pretac(tmL: Term)                                    extends PreTactic
case class IffE2_pretac(tmR: Term)                                    extends PreTactic
case class IffI_pretac()                                              extends PreTactic
case class ConjI_pretac()                                             extends PreTactic
case class ConjE1_pretac(tmR: Term)                                   extends PreTactic
case class ConjE2_pretac(tmL: Term)                                   extends PreTactic
case class DisjI1_pretac()                                            extends PreTactic
case class DisjI2_pretac()                                            extends PreTactic
case class DisjE_pretac(tm1: Term, tm2: Term)                         extends PreTactic
case class ImpI_pretac()                                              extends PreTactic
case class ImpE_pretac(tm1: Term)                                     extends PreTactic
case class NegI_pretac()                                              extends PreTactic
case class NegE_pretac(tm: Term)                                      extends PreTactic
case class AllI_pretac()                                              extends PreTactic
case class AllE_pretac(phi: Term, r: Term, x: Var)                    extends PreTactic
case class ExI_pretac(r: Term)                                        extends PreTactic
case class ExE_pretac(phi: Term, x: Var, y: Var)                      extends PreTactic
case class Lem_pretac()                                               extends PreTactic
case class Raa_pretac(taint: Taint)                                   extends PreTactic
case class WeakLem_pretac()                                           extends PreTactic
case class axiomOfChoice_pretac()                                     extends PreTactic
case class iteTrue()                                                  extends PreTactic
case class Weaken_pretac(tm: Term)                                    extends PreTactic
case class NTrans_pretac(l: List[Term])                               extends PreTactic

//case class ConjSplitLeft_pretact(l: Term, r: Term) extends PreTactic

object PreTactic:

    // recall that     type Goal = (Context, Term, Taint)
    type PreGoals = (List[Goal], List[Thm] => Option[Thm])
    // type PreTactic = Goal => Option[PreGoals]

    def apply(pretac: PreTactic): Goal => Option[PreGoals] =
        println(s" -----------> about to run ${pretac}")
        pretac match
            case Init_pretac() =>
                (goal: Goal) =>
                    val (gamma, tm, taint) = goal
                    (valid(gamma), gamma.contains(tm), taint) match
                        case (true, true, I) =>
                            def justification(ts: List[Thm]): Option[Thm] =
                                ts match
                                    case List() => init(gamma, tm)
                                    case _      => None
                            Some(List(), justification)
                        case _ => None

            case TrueI_pretac() =>
                (goal: Goal) =>
                    val (gamma, tm, taint) = goal
                    (valid(gamma), taint) match
                        case (true, I) =>
                            def justification(ts: List[Thm]): Option[Thm] =
                                ts match
                                    case List() => trueI(gamma)
                                    case _      => None
                            Some(List(), justification)
                        case _ => None

            case FalseE_pretac() =>
                (goal: Goal) =>
                    val (gamma, tm, taint) = goal
                    Term.check(tm, Prop()) match
                        case true =>
                            val subgoal = (gamma, FalseProp(), taint)
                            def justification(ts: List[Thm]): Option[Thm] =
                                ts match
                                    case List(thm) => falseE(thm, tm)
                                    case _         => None
                            Some(List(subgoal), justification)
                        case _ => None

            case Lift_pretac(smallTaint: Taint) =>
                (goal: Goal) =>
                    val (gamma, tm, bigTaint) = goal
                    TaintLattice.leq(smallTaint, bigTaint) match
                        case true =>
                            val subgoal = (gamma, tm, smallTaint)
                            def justification(ts: List[Thm]): Option[Thm] =
                                ts match
                                    case List(thm) => lift(thm, bigTaint)
                                    case _         => None
                            Some(List(subgoal), justification)
                        case _ => None

            case Refl_pretac() =>
                (goal: Goal) =>
                    goal match
                        case (gamma, Equation(l, r, ty), I) if l == r && valid(gamma) && Term.check(l, ty) =>
                            def justification(ts: List[Thm]): Option[Thm] =
                                ts match
                                    case List() => refl(gamma, l, ty)
                                    case _      => None
                            Some(List(), justification)
                        case _ => None

            case Sym_pretac() =>
                (goal: Goal) =>
                    goal match
                        case (gamma, Equation(l, r, ty), taint) =>
                            val subgoal = (gamma, Equation(r, l, ty), taint)
                            def justification(ts: List[Thm]): Option[Thm] =
                                ts match
                                    case List(thm) => sym(thm)
                                    case _         => None
                            Some(List(subgoal), justification)
                        case _ => None

            case Trans_pretac(tm: Term) =>
                (goal: Goal) =>
                    goal match
                        case (gamma, Equation(l, r, ty), taint) if Term.check(tm, ty) =>
                            val subgoal1 = (gamma, Equation(l, tm, ty), taint)
                            val subgoal2 = (gamma, Equation(tm, r, ty), taint)
                            def justification(ts: List[Thm]): Option[Thm] =
                                ts match
                                    case List(thm1, thm2) => trans(thm1, thm2)
                                    case _                => None
                            Some(List(subgoal1, subgoal2), justification)
                        case _ => None

            case Lcong_pretac() =>
                (goal) =>
                    val (gamma, tm, taint) = goal
                    tm match
                        case Equation(Lam(x1, body1), Lam(x2, body2), ty) if x1 == x2 && !fv(gamma).contains(x1) =>
                            Term.tyInference(body1) match
                                case Some(ty) =>
                                    val subgoal = (gamma, Equation(body1, body2, ty), taint)
                                    def justification(ts: List[Thm]): Option[Thm] =
                                        ts match
                                            case List(thm) => lcong(thm, x1)
                                            case _         => None
                                    Some(List(subgoal), justification)
                                case _ => None
                        case _ => None

            case Acong_pretac() =>
                (goal) =>
                    val (gamma, tm, taint) = goal
                    tm match
                        case Equation(App(l1, r1), App(l2, r2), ty_eq) =>
                            Term.tyInference(l1) match
                                case Some(ty @ FunctionTy(tyl, tyr)) if tyr == ty_eq =>
                                    val subgoalL = (gamma, Equation(l1, l2, ty), taint)
                                    val subgoalR = (gamma, Equation(r1, r2, tyr), taint)
                                    def justification(ts: List[Thm]): Option[Thm] =
                                        ts match
                                            case List(thm1, thm2) => acong(thm1, thm2)
                                            case _                => None
                                    Some(List(subgoalL, subgoalR), justification)
                                case _ => None
                        case _ => None

            case Beta_pretac() =>
                (goal) =>
                    val (gamma, tm, taint) = goal
                    tm match
                        case Equation(App(lam @ Lam(x, body), arg), r, ty_target) if r == Term.subst(body, arg, x) =>
                            def justification(ts: List[Thm]): Option[Thm] =
                                ts match
                                    case List() => beta(gamma, lam, x.ty, ty_target, r)
                                    case _      => None
                            Some(List(), justification)
                        case _ => None

            case Eta_pretac() =>
                (goal) =>
                    goal match
                        case (gamma, Equation(tm @ Lam(x1, App(f1, x2)), f2, ty @ FunctionTy(ty1, ty2)), I)
                            if f1 == f2 && x1 == x2 && ty1 == x1.ty && !Term.fv(f1).contains(x1) && Context.valid(gamma) =>
                            def justification(ts: List[Thm]): Option[Thm] =
                                ts match
                                    case List() => eta(gamma, tm, ty)
                                    case _      => None
                            Some(List(), justification)
                        case _ => None

            case Inst_pretac(gamma: Context, tm: Term, ty: Ty, tv: TyVar) =>
                (goal) =>
                    val (gamma1, tm1, taint) = goal
                    (Context.tySubst(gamma, ty, tv) == gamma1, Term.tySubst(tm, ty, tv) == tm1) match
                        case (true, true) if Ty.check(ty, TyKind) =>
                            val subgoal = (gamma, tm, taint)
                            def justification(ts: List[Thm]): Option[Thm] =
                                ts match
                                    case List(thm) => inst(thm, ty, tv)
                                    case _         => None
                            Some(List(subgoal), justification)
                        case _ => None

            case Subst_pretac(gamma: Context, phi: Term, r: Term, x: Var) =>
                (goal) =>
                    val (gamma1, phi1, taint) = goal
                    (Context.subst(gamma, r, x) == gamma1, Term.subst(phi, r, x) == phi1) match
                        case (true, true) if Term.check(r, x.ty) =>
                            val subgoal = (gamma, phi, taint)
                            def justification(ts: List[Thm]): Option[Thm] =
                                ts match
                                    case List(thm) => Thm.subst(thm, r, x.ty, x)
                                    case _         => None
                            Some(List(subgoal), justification)
                        case _ => None

            case IffE1_pretac(tmL: Term) =>
                (goal) =>
                    val (gamma, tmR, taint) = goal
                    val subgoal1            = (gamma, Equivalence(tmL, tmR), taint)
                    val subgoal2            = (gamma, tmL, taint)
                    def justification(ts: List[Thm]): Option[Thm] =
                        ts match
                            case List(thm1, thm2) => iffE1(thm1, thm2)
                            case _                => None
                    Some(List(subgoal1, subgoal2), justification)

            case IffE2_pretac(tmR: Term) =>
                (goal) =>
                    val (gamma, tmL, taint) = goal
                    val subgoal1            = (gamma, Equivalence(tmL, tmR), taint)
                    val subgoal2            = (gamma, tmR, taint)
                    def justification(ts: List[Thm]): Option[Thm] =
                        ts match
                            case List(thm1, thm2) => iffE2(thm1, thm2)
                            case _                => None
                    Some(List(subgoal1, subgoal2), justification)

            case IffI_pretac() =>
                (goal) =>
                    val (gamma, tm, taint) = goal
                    tm match
                        case Equivalence(l, r) =>
                            val subgoalL = (r :: gamma, l, taint)
                            val subgoalR = (l :: gamma, r, taint)
                            def justification(ts: List[Thm]): Option[Thm] =
                                ts match
                                    case List(thm1, thm2) => iffI(thm1, thm2)
                                    case _                => None
                            Some(List(subgoalL, subgoalR), justification)
                        case _ => None

            case ConjI_pretac() =>
                (goal) =>
                    val (gamma, tm, taint) = goal
                    tm match
                        case And(l, r) =>
                            val subgoal1 = (gamma, l, taint)
                            val subgoal2 = (gamma, r, taint)
                            def justification(ts: List[Thm]): Option[Thm] =
                                ts match
                                    case List(thm1, thm2) => conjI(thm1, thm2)
                                    case _                => None
                            Some(List(subgoal1, subgoal2), justification)
                        case _ => None

            case ConjE1_pretac(r: Term) =>
                (goal) =>
                    val (gamma, l, taint) = goal
                    val subgoal           = (gamma, And(l, r), taint)
                    def justification(ts: List[Thm]): Option[Thm] =
                        ts match
                            case List(thm) => conjE1(thm)
                            case _         => None
                    Some(List(subgoal), justification)

            case ConjE2_pretac(l: Term) =>
                (goal) =>
                    val (gamma, r, taint) = goal
                    val subgoal           = (gamma, And(l, r), taint)
                    def justification(ts: List[Thm]): Option[Thm] =
                        ts match
                            case List(thm) => conjE2(thm)
                            case _         => None
                    Some(List(subgoal), justification)

            case DisjI1_pretac() =>
                (goal) =>
                    val (gamma, tm, taint) = goal
                    tm match
                        case Or(l, r) =>
                            val subgoal = (gamma, l, taint)
                            def justification(ts: List[Thm]): Option[Thm] =
                                ts match
                                    case List(thm) => disjI1(thm, r)
                                    case _         => None
                            Some(List(subgoal), justification)
                        case _ => None

            case DisjI2_pretac() =>
                (goal) =>
                    val (gamma, tm, taint) = goal
                    tm match
                        case Or(l, r) =>
                            val subgoal = (gamma, r, taint)
                            def justification(ts: List[Thm]): Option[Thm] =
                                ts match
                                    case List(thm) => disjI2(thm, l)
                                    case _         => None
                            Some(List(subgoal), justification)
                        case _ => None

            case DisjE_pretac(tm1: Term, tm2: Term) =>
                (goal) =>
                    val (gamma, tm, taint) = goal
                    val subgoal            = (gamma, Or(tm1, tm2), taint)
                    val subgoal1           = (gamma ++ Set(tm1), tm, taint)
                    val subgoal2           = (gamma ++ Set(tm2), tm, taint)
                    def justification(ts: List[Thm]): Option[Thm] =
                        ts match
                            case List(thm, thm1, thm2) => disjE(thm, thm1, thm2)
                            case _                     => None
                    Some(List(subgoal, subgoal1, subgoal2), justification)

            case ImpI_pretac() =>
                (goal) =>
                    val (gamma, tm, taint) = goal
                    tm match
                        case Implies(l, r) =>
                            val subgoal = (l :: gamma, r, taint)
                            def justification(ts: List[Thm]): Option[Thm] =
                                ts match
                                    case List(thm) => impI(thm, l)
                                    case _         => None
                            Some(List(subgoal), justification)
                        case _ => None

            case ImpE_pretac(tm1: Term) =>
                (goal) =>
                    val (gamma, tm2, taint) = goal
                    val subgoal1            = (gamma, Implies(tm1, tm2), taint)
                    val subgoal2            = (gamma, tm1, taint)
                    def justification(ts: List[Thm]): Option[Thm] =
                        ts match
                            case List(thm1, thm2) => impE(thm1, thm2)
                            case _                => None
                    Some(List(subgoal1, subgoal2), justification)

            case NegI_pretac() =>
                (goal) =>
                    val (gamma, tm, taint) = goal
                    tm match
                        case Neg(tm1) =>
                            val subgoal = (tm1 :: gamma, FalseProp(), taint)
                            def justification(ts: List[Thm]): Option[Thm] =
                                ts match
                                    case List(thm) => negI(thm, tm1)
                                    case _         => None
                            Some(List(subgoal), justification)
                        case _ => None

            case NegE_pretac(tm: Term) =>
                (goal) =>
                    goal match
                        case (gamma, FalseProp(), taint) =>
                            val subgoal1 = (gamma, tm, taint)
                            val subgoal2 = (gamma, Neg(tm), taint)
                            def justification(ts: List[Thm]): Option[Thm] =
                                ts match
                                    case List(thm1, thm2) => negE(thm1, thm2)
                                    case _                => None
                            Some(List(subgoal1, subgoal2), justification)
                        case _ => None

            case AllI_pretac() =>
                (goal) =>
                    val (gamma, tm, taint) = goal
                    tm match
                        case Forall(x, ty, body) if !fv(gamma).contains(Var(x, ty)) =>
                            val subgoal = (gamma, body, taint)
                            def justification(ts: List[Thm]): Option[Thm] =
                                ts match
                                    case List(thm) => allI(thm, Var(x, ty))
                                    case _         => None
                            Some(List(subgoal), justification)
                        case _ => None

            case AllE_pretac(phi: Term, r: Term, x: Var) =>
                (goal) =>
                    val (gamma, phi1, taint) = goal
                    (Term.subst(phi, r, x) == phi1, Term.check(r, x.ty)) match
                        case (true, true) =>
                            val subgoal = (gamma, Forall(x.name, x.ty, phi), taint)
                            def justification(ts: List[Thm]): Option[Thm] =
                                ts match
                                    case List(thm) => allE(thm, r)
                                    case _         => None
                            Some(List(subgoal), justification)
                        case _ => None

            case ExI_pretac(r: Term) =>
                (goal) =>
                    goal match
                        case (gamma, Exists(name, ty, phi), taint) =>
                            val x       = Var(name, ty)
                            val subgoal = (gamma, Term.subst(phi, r, x), taint)
                            def justification(ts: List[Thm]): Option[Thm] =
                                ts match
                                    case List(thm) => exI(thm, phi, x, r)
                                    case _         => None
                            Some(List(subgoal), justification)
                        case _ => None

            case ExE_pretac(phi: Term, x: Var, y: Var) =>
                (goal) =>
                    goal match
                        case (gamma, psi, taint) if x.ty == y.ty && !fv(gamma).union(Term.fv(phi)).contains(y) =>
                            val subgoal1 = (gamma, Exists(x.name, x.ty, phi), taint)
                            val subgoal2 = (Term.subst(phi, y, x) :: gamma, psi, taint)
                            def justification(ts: List[Thm]): Option[Thm] =
                                ts match
                                    case List(thm1, thm2) => exE(thm1, thm2, y.name)
                                    case _                => None
                            Some(List(subgoal1, subgoal2), justification)
                        case _ => None

            case Lem_pretac() =>
                (goal) =>
                    goal match
                        case (gamma, Or(tm1, Neg(tm2)), C) if tm1 == tm2 && valid(gamma) && Term.check(tm1, Prop()) =>
                            def justification(ts: List[Thm]): Option[Thm] =
                                ts match
                                    case List() => lem(gamma, tm1)
                                    case _      => None
                            Some(List(), justification)
                        case _ => None

            case Raa_pretac(taint: Taint) =>
                (goal) =>
                    goal match
                        case (gamma, tm, C) =>
                            val subgoal = (Neg(tm) :: gamma, FalseProp(), taint)
                            def justification(ts: List[Thm]): Option[Thm] =
                                ts match
                                    case List(thm) => raa(thm, tm)
                                    case _         => None
                            Some(List(subgoal), justification)
                        case _ => None

            case Weaken_pretac(tm1: Term) =>
                (goal) =>
                    val (gamma, tm2, taint) = goal
                    val subgoal             = (tm1 :: gamma, tm2, taint)
                    def justification(ts: List[Thm]): Option[Thm] =
                        ts match
                            case List(thm) => wk(thm, tm1)
                            case _         => None
                    Some(List(subgoal), justification)

            case WeakLem_pretac() =>
                (goal) =>
                    goal match
                        case (gamma, Or(Neg(tm1), Neg(Neg(tm2))), W) if tm1 == tm2 && valid(gamma) && Term.check(tm1, Prop()) =>
                            def justification(ts: List[Thm]): Option[Thm] =
                                ts match
                                    case List() => weakLem(gamma, tm1)
                                    case _      => None
                            Some(List(), justification)
                        case _ => None

            case axiomOfChoice_pretac() => // The branching structure below is uncomfortably complex!
                (goal) =>
                    goal match
                        case (
                              gamma,
                              Implies(
                                Forall(x1, x1_ty, Exists(y1, y1_ty, App(App(p1, x2), y2))),
                                Exists(f1, f1_ty, Forall(x3, x3_ty, App(App(p2, x4), App(f2, x5))))
                              ),
                              CH
                            )
                            if Var(x1, x1_ty) == x2 && x2 == Var(x3, x3_ty) && x2 == x4 && x4 == x5 &&
                                Var(y1, y1_ty) == y2 &&
                                Var(f1, f1_ty) == f2 &&
                                p1 == p2 &&
                                Term.check(goal._2, Prop()) =>
                            (x2, x1_ty, y2, y1_ty, f2) match
                                case (x @ Var(_, _), alpha @ TyVar(_), y @ Var(_, _), beta @ TyVar(_), f @ Var(_, _)) =>
                                    def justification(ts: List[Thm]): Option[Thm] =
                                        ts match
                                            case List() => axiomOfChoice(gamma, p1, alpha, beta, x, y, f)
                                            case _      => None
                                    Some(List(), justification)
                                case _ => None
                        case _ => None

            case iteTrue() => ???
            // (goal) =>
            //     goal match
            //         case (gamma, Equation(IfThenElse(ty1, cond, thn, els), rhs, ty2), taint) if ty1 == ty2 =>
            //             val subgoal1 = (gamma, Equation(cond, TrueBool(), Bool()), taint)
            //             val subgoal2 = (gamma, Equation(thn, rhs, ty2), taint)
            //             def justification(ts: List[Thm]): Option[Thm] =
            //                 ts match
            //                     case List(thm1, thm2) =>
            //                     case _                => None
            //             Some(List(subgoal1, subgoal2), justification)
            //         case _ => None

            case NTrans_pretac(tms: List[Term]) =>
                (goal) =>
                    goal match
                        case (gamma, Equation(l, r, ty), taint) =>
                            val candidates = (l :: tms ++ List(r))
                            val subgoals   = Lib.map2(candidates)((tm1, tm2) => (gamma, Equation(tm1, tm2, ty), taint))
                            def justification(ts: List[Thm]): Option[Thm] =
                                ts match
                                    case fst :: rest => rest.foldLeft(Some(fst): Option[Thm])((accu, thm) => accu.flatMap(trans(_, thm)))
                                    case _           => None
                            Some(subgoals, justification)
                        case _ => None
