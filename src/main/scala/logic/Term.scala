package Prover

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
                // assert(!fv(t2).contains(y)) // WARINING: we leave it to the user to avoid free name capture
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
    def apply(): Term = Const("TrueProp", Prop())
    def unapply(tm: Term): Boolean =
        tm match
            case Const("TrueProp", Prop()) => true
            case _                         => false

object FalseProp:
    def apply(): Term = Const("FalseProp", Prop())
    def unapply(tm: Term): Boolean =
        tm match
            case Const("FalseProp", Prop()) => true
            case _                          => false

object TrueBool:
    def apply(): Term = Const("TrueBool", Bool())
    def unapply(tm: Term): Boolean =
        tm match
            case Const("TrueBool", Bool()) => true
            case _                         => false

object FalseBool:
    def apply(): Term = Const("FalseBool", Bool())
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
    def apply(tv: TyVar, cond: Term, thn: Term, els: Term): Term = App(App(App(IfThenElseConst(tv), cond), thn), els)
    def unapply(tm: Term): Option[(TyVar, Term, Term, Term)] =
        tm match
            case App(App(App(IfThenElseConst(tv), cond), thn), els) => Some((tv, cond, thn, els))
            case _                                                  => None

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

object Binop:
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

object Quantifier:
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
