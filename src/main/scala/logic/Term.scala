package Prover

import java.security.Identity

sealed trait Term
case class Var(name: String, ty: Ty) extends Term { override def toString: String = s"${name}"      } // ^${ty.toString}" }
case class Const(c: String, ty: Ty)  extends Term { override def toString: String = s"${c}"         }
case class App(l: Term, r: Term)     extends Term { override def toString: String = s"(${l}, ${r})" }
case class Lam(x: Var, body: Term)   extends Term

given CanEqual[Term, Term] = CanEqual.derived

object Term:

    def ftv(t: Term): Set[TyVar] =
        t match
            case Var(x, ty)   => Ty.ftv(ty)
            case Const(c, ty) => Ty.ftv(ty)
            case App(l, r)    => ftv(l) ++ ftv(r)
            case Lam(x, body) => Ty.ftv(x.ty) ++ ftv(body)

    def tySubst(t: Term, ty2: Ty, x: TyVar): Term = // this is t[ty2/x]
        t match
            case Var(y, ty)            => Var(y, Ty.subst(ty, ty2, x))
            case Const(c, ty)          => Const(c, Ty.subst(ty, ty2, x))
            case App(l, r)             => App(tySubst(l, ty2, x), tySubst(r, ty2, x))
            case Lam(Var(y, ty), body) => Lam(Var(y, Ty.subst(ty, ty2, x)), tySubst(body, ty2, x))

    def fv(t: Term): Set[Var] =
        t match
            case x @ Var(_, _) => Set(x)
            case Const(c, ty)  => Set.empty
            case App(l, r)     => fv(l) ++ fv(r)
            case Lam(x, body)  => fv(body).diff(Set(x))

    def subst(t: Term, t2: Term, x: Var): Term = // this is t[t2/x]
        t match
            case z @ Var(_, _) => if z == x then t2 else t
            case Const(_, _)   => t
            case App(l, r)     => App(subst(l, t2, x), subst(r, t2, x))
            case Lam(y, body)  =>
                // assert(!fv(t2).contains(y)) // TODO WARINING: we leave it to the user to avoid free name capture
                if x.name == y.name then t else Lam(y, subst(body, t2, x))

    def check(tm: Term, ty: Ty): Boolean =
        tyInference(tm) match
            case Some(ty2) if ty == ty2 => true
            case _                      => false

    def tyInference(t: Term): Option[Ty] =
        t match
            case Var(_, ty)   => Some(ty)
            case Const(_, ty) => Some(ty)
            case App(l, r) =>
                (tyInference(l), tyInference(r)) match
                    case (Some(FunctionTy(ty_l_source, ty_l_target)), Some(ty_r)) if (ty_l_source == ty_r) => Some(ty_l_target)
                    case _                                                                                 => None
            case Lam(Var(x, ty), body) =>
                tyInference(body) match
                    case Some(tyBody) => Some(FunctionTy(ty, tyBody))
                    case _            => None

object TrueProp:
    def apply(): Term = Const("TrueProp", Prop()) // TODO make enum so we don't get crazy strings
    def unapply(tm: Term): Boolean =
        tm match
            case Const("TrueProp", Prop()) => true
            case _                         => false

object FalseProp:
    def apply(): Term = Const("FalseProp", Prop()) // TODO make enum so we don't get crazy strings
    def unapply(tm: Term): Boolean =
        tm match
            case Const("FalseProp", Prop()) => true
            case _                          => false

object TrueBool:
    def apply(): Term = Const("TrueBool", Bool()) // TODO make enum so we don't get crazy strings
    def unapply(tm: Term): Boolean =
        tm match
            case Const("TrueBool", Bool()) => true
            case _                         => false

object FalseBool:
    def apply(): Term = Const("FalseBool", Bool()) // TODO make enum so we don't get crazy strings
    def unapply(tm: Term): Boolean =
        tm match
            case Const("FalseBool", Bool()) => true
            case _                          => false

object IfThenElseConst:
    def apply(tv: TyVar): Term = Const("IfThenElse", IfThenElseTy(tv))
    def unapply(tm: Term): Option[TyVar] =
        tm match
            case Const("IfThenElse", IfThenElseTy(tv)) => Some(tv)
            case _                                     => None

object IfThenElse:
    def apply(tv: TyVar, cond: Term, thn: Term, els: Term): Term = ???
    def unapply(tm: Term): Option[TyVar]                         = ???

object UnaryPredicate:
    def apply(pred: Term, arg: Term): Term = App(pred, arg)
    def unapply(tm: Term): Option[(Term, Term)] =
        tm match
            case App(pred, arg) => Some((pred, arg))
            case _              => None

object Unop:
    def apply(tm: Term, name: String): Term = UnaryPredicate(Const(name, UnaryPredicateTy(Prop())), tm)
    def unapply(tm: Term): Option[(Term, String)] =
        tm match
            case UnaryPredicate(Const(name, UnaryPredicateTy(Prop())), tm) => Some((tm, name))
            case _                                                         => None

object Neg:
    def apply(tm: Term): Term = Unop(tm, "not")
    def unapply(tm: Term): Option[Term] =
        tm match
            case Unop(tm, "not") => Some(tm)
            case _               => None

object BinaryPredicate:
    def apply(pred: Term, arg1: Term, arg2: Term): Term = App(App(pred, arg1), arg2)
    def unapply(tm: Term): Option[(Term, Term, Term)] =
        tm match
            case App(App(pred, arg1), arg2) => Some((pred, arg1, arg2))
            case _                          => None

object Binop: // TODO make an enumeration of binops, so we cannot construct weird logical ops like "hello"
    def apply(tm1: Term, tm2: Term, name: String): Term =
        BinaryPredicate(Const(name, FunctionTyPropPropProp()), tm1, tm2)
    def unapply(tm: Term): Option[(Term, Term, String)] =
        tm match
            case BinaryPredicate(Const(name, FunctionTyPropPropProp()), tm1, tm2) => Some((tm1, tm2, name))
            case _                                                                => None

object And:
    def apply(tm1: Term, tm2: Term): Term = Binop(tm1, tm2, "and")
    def unapply(tm: Term): Option[(Term, Term)] =
        tm match
            case Binop(tm1, tm2, "and") => Some((tm1, tm2))
            case _                      => None

object Or:
    def apply(tm1: Term, tm2: Term): Term = Binop(tm1, tm2, "or")
    def unapply(tm: Term): Option[(Term, Term)] =
        tm match
            case Binop(tm1, tm2, "or") => Some((tm1, tm2))
            case _                     => None

object Implies:
    def apply(tm1: Term, tm2: Term): Term = Binop(tm1, tm2, "implies")
    def unapply(tm: Term): Option[(Term, Term)] =
        tm match
            case Binop(tm1, tm2, "implies") => Some((tm1, tm2))
            case _                          => None

object Quantifier: // TODO: make enumeration of forall/exists so we cannot construct a qunatifier "howeowier"
    def apply(x: String, ty: Ty, body: Term, constructorName: String): Term =
        val q_ty = QuantifierTy(ty)
        val lam  = Lam(Var(x, ty), body)
        App(Const(constructorName, q_ty), lam)
    def unapply(tm: Term): Option[(String, Ty, Term, String)] =
        tm match
            case App(Const(constructorName, QuantifierTy(ty)), Lam(Var(x, ty1), body)) if ty == ty1 =>
                Some((x, ty, body, constructorName))
            case _ => None

object Forall:
    def apply(x: String, ty: Ty, body: Term): Term = Quantifier(x, ty, body, "forall")
    def unapply(tm: Term): Option[(String, Ty, Term)] =
        tm match
            case Quantifier(x, ty, body, "forall") => Some((x, ty, body))
            case _                                 => None

object Exists:
    def apply(x: String, ty: Ty, body: Term): Term = Quantifier(x, ty, body, "exists")
    def unapply(tm: Term): Option[(String, Ty, Term)] =
        tm match
            case Quantifier(x, ty, body, "exists") => Some((x, ty, body))
            case _                                 => None

object Equation:
    def apply(l: Term, r: Term, ty: Ty): Term = BinaryPredicate(Const("=", BinaryPredicateTy(ty, ty)), l, r)
    def unapply(tm: Term): Option[(Term, Term, Ty)] =
        tm match
            case BinaryPredicate(Const("=", BinaryPredicateTy(ty_l, ty_r)), l, r) if ty_l == ty_r => Some((l, r, ty_l))
            case _                                                                                => None

object Equivalence:
    def apply(l: Term, r: Term): Term = Equation(l, r, Prop())
    def unapply(tm: Term): Option[(Term, Term)] =
        tm match
            case Equation(l, r, Prop()) => Some((l, r))
            case _                      => None

object Member:
    def apply(tv: TyVar): Term = Const("Member", FunctionTyVarSetProp(tv)) // TODO make enum so we don't get crazy strings
    def unapply(tm: Term): Option[TyVar] =
        tm match
            case Const("Member", FunctionTyVarSetProp(tv)) => Some(tv)
            case _                                         => None

object MemberCheck: // MemberCheck(x, S) is short for ((Member S)x)
    def apply(tv: TyVar, x: Var, s: Term): Term = BinaryPredicate(Member(tv), x, s)
    def unapply(tm: Term): Option[(TyVar, Var, Term)] =
        tm match
            case BinaryPredicate(Member(tv), x @ Var(_, _), s) => Some(tv, x, s) // TODO don't we have to check more?
            case _                                             => ???

object EmptySet: // TODO this should be defined in terms of Member
    def apply(ty: Ty): Term = Const("EmptySet", SetTy(ty)) // TODO make enum so we don't get crazy strings
    def unapply(tm: Term): Option[Ty] =
        tm match
            case Const("EmptySet", SetTy(ty)) => Some(ty)
            case _                            => None

object UnionSet: // TODO this should be defined in terms of Member
    def apply(ty: Ty, s1: Term, s2: Term): Term     = ???
    def unapply(tm: Term): Option[(Ty, Term, Term)] = ???

object Cmpl:
    def apply(tv: TyVar): Term = Const("Compl", FunctionTy(SetTy(tv), SetTy(tv)))
    def unapply(tm: Term): Option[TyVar] =
        tm match
            case Const("Compl", FunctionTy(SetTy(tv1 @ TyVar(_)), SetTy(tv2 @ TyVar(_)))) if tv1 == tv2 => Some(tv1)
            case _                                                                                      => None

object CmplementSet: // TODO this should be defined in terms of Member
    def apply(ty: Ty, s: Term): Term          = ???
    def unapply(tm: Term): Option[(Ty, Term)] = ???

object ComprehensionSet:
    def apply(x: Var, tm: Term): Term = Lam(x, tm)
    def unapply(tm: Term): Option[(Var, Term)] =
        tm match
            case Lam(x, tm) => Some((x, tm))
            case _          => None

object SingletonSet:
    def apply(ty: Ty, tm: Term): Term =
        val x = Lib.freshVar(Term.fv(tm), ty)
        ComprehensionSet(x, Equation(x, tm, ty))
    def unapply(tm: Term): Option[(Ty, Term)] =
        tm match
            case ComprehensionSet(_, Equation(_, tm, ty)) => Some((ty, tm))
            case _                                        => None

object Lift: // Can/should be defined with ITE?
    def apply(): Term = Const("lift", FunctionTy(Bool(), Prop()))
    def unapply(tm: Term): Boolean =
        tm match
            case Const("lift", FunctionTy(Bool(), Prop())) => true
            case _                                         => false

object Finite:
    def apply(tv: TyVar): Term = Const("Finite", FunctionTy(SetTy(tv), Prop()))
    def unapply(tm: Term): Option[TyVar] =
        tm match
            case Const("Finite", FunctionTy(SetTy(tv @ TyVar(_)), Prop())) => Some(tv)
            case _                                                         => None

object FunctCompose:
    def apply(tv1: TyVar, tv2: TyVar, tv3: TyVar): Term =
        val ty1 = FunctionTy(tv1, tv2)
        val ty2 = FunctionTy(tv2, tv3)
        Const("o", TernaryFunctionTy(ty1, ty2, tv1, tv3))
    def unapply(tm: Term): Option[(TyVar, TyVar, TyVar)] =
        tm match
            case Const(
                  "o",
                  TernaryFunctionTy(
                    FunctionTy(tv1a @ TyVar(_), tv2a @ TyVar(_)),
                    FunctionTy(tv2b @ TyVar(_), tv3b @ TyVar(_)),
                    tv1c @ TyVar(_),
                    tv3d @ TyVar(_)
                  )
                ) if tv1a == tv1c && tv2a == tv2b && tv3b == tv3d =>
                Some((tv1a, tv2a, tv3b))
            case _ => None

object FunctComposer:
    def apply(tv1: TyVar, tv2: TyVar, tv3: TyVar, f1: Term, f2: Term): Term = App(App(FunctCompose(tv1, tv2, tv3), f1), f2)
    def unapply(tm: Term): Option[(TyVar, TyVar, TyVar, Term, Term)] =
        tm match
            case App(App(FunctCompose(tv1, tv2, tv3), f1), f2) => Some((tv1, tv2, tv3, f1, f2))
            case _                                             => None

object Identity:
    def apply(tv: TyVar): Term = Const("id", FunctionTy(tv, tv))
    def unapply(tm: Term): Option[TyVar] =
        tm match
            case Const("id", FunctionTy(tv1 @ TyVar(_), tv2 @ TyVar(_))) if tv1 == tv2 => Some(tv1)
            case _                                                                     => None
