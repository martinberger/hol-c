package Prover

sealed trait Ty
case class TyVar(name: String)                extends Ty { override def toString: String = s"${name}"    }
case class TyFormer(name: String, kind: Kind) extends Ty { override def toString: String = s""           } //[${name}:${kind.toString}]" }
case class TyApp(l: Ty, r: Ty)                extends Ty { override def toString: String = s"(${l}${r})" }

given CanEqual[Ty, Ty] = CanEqual.derived

object Ty:

    def ftv(ty: Ty): Set[TyVar] =
        ty match
            case tv @ TyVar(name) => Set(tv)
            case TyFormer(_, _)   => Set.empty
            case TyApp(l, r)      => ftv(l) ++ ftv(r)

    def subst(ty: Ty, ty2: Ty, x: TyVar): Ty =
        ty match
            case y @ TyVar(_)   => if x == y then ty2 else ty
            case TyFormer(_, _) => ty
            case TyApp(l, r)    => TyApp(subst(l, ty2, x), subst(r, ty2, x))

    def check(ty: Ty, kind: Kind): Boolean =
        (ty, kind) match
            case (TyVar(_), TyKind)         => true
            case (TyFormer(name, kind2), _) => (kind == kind2)
            case (TyApp(l, r), _)           => { check(l, ConstructorKind(kind)) && check(r, TyKind) }
            case _                          => false

object FunctionTy:
    def apply(ty1: Ty, ty2: Ty): Ty =
        TyApp(TyApp(TyFormer("->", BinaryTyFunctionKind()), ty1), ty2)
    def unapply(ty: Ty): Option[(Ty, Ty)] =
        ty match
            case TyApp(TyApp(TyFormer("->", BinaryTyFunctionKind()), ty1), ty2) => Some((ty1, ty2))
            case _                                                              => None

object Prop:
    def apply(): Ty = TyFormer("Prop", TyKind)
    def unapply(ty: Ty): Boolean =
        ty match
            case TyFormer("Prop", TyKind) => true
            case _                        => false

object Bool:
    def apply(): Ty = TyFormer("Bool", TyKind)
    def unapply(ty: Ty): Boolean =
        ty match
            case TyFormer("Bool", TyKind) => true
            case _                        => false

object UnaryPredicateTy:
    def apply(ty: Ty): Ty = FunctionTy(ty, Prop())
    def unapply(ty: Ty): Option[Ty] =
        ty match
            case FunctionTy(src, Prop()) => Some(src)
            case _                       => None

object QuantifierTy:
    def apply(ty: Ty): Ty = UnaryPredicateTy(UnaryPredicateTy(ty))
    def unapply(ty: Ty): Option[Ty] =
        ty match
            case UnaryPredicateTy(UnaryPredicateTy(src)) => Some(src)
            case _                                       => None

object BinaryPredicateTy:
    def apply(ty1: Ty, ty2: Ty): Ty = FunctionTy(ty1, FunctionTy(ty2, Prop()))
    def unapply(ty: Ty): Option[(Ty, Ty)] =
        ty match
            case FunctionTy(src1, FunctionTy(src2, Prop())) => Some((src1, src2))
            case _                                          => None

object FunctionTyPropProp:
    def apply(): Ty = UnaryPredicateTy(Prop())
    def unapply(ty: Ty): Boolean =
        ty match
            case UnaryPredicateTy(Prop()) => true
            case _                        => false

object FunctionTyPropPropProp:
    def apply(): Ty = BinaryPredicateTy(Prop(), Prop())
    def unapply(ty: Ty): Boolean =
        ty match
            case BinaryPredicateTy(Prop(), Prop()) => true
            case _                                 => false

object SetTy:
    def apply(ty: Ty): Ty = FunctionTy(ty, Prop())
    def unapply(ty: Ty): Option[Ty] =
        ty match
            case FunctionTy(src, Prop()) => Some(src)
            case _                       => None

object FunctionTyVarSetProp:
    def apply(tv: TyVar): Ty = BinaryPredicateTy(tv, SetTy(tv))
    def unapply(ty: Ty): Option[TyVar] =
        ty match
            case BinaryPredicateTy(ty @ TyVar(tv1), SetTy(TyVar(tv2))) if tv1 == tv2 => Some(ty)
            case _                                                                   => None

object TernaryFunctionTy:
    def apply(ty1: Ty, ty2: Ty, ty3: Ty, ty4: Ty): Ty = FunctionTy(ty1, FunctionTy(ty2, FunctionTy(ty3, ty4)))
    def unapply(ty: Ty): Option[(Ty, Ty, Ty, Ty)] =
        ty match
            case FunctionTy(ty1, FunctionTy(ty2, FunctionTy(ty3, ty4))) => Some((ty1, ty2, ty3, ty4))
            case _                                                      => None

object IfThenElseTy:
    def apply(ty: Ty): Ty = TernaryFunctionTy(Bool(), ty, ty, ty)
    def unapply(ty: Ty): Option[Ty] =
        ty match
            case TernaryFunctionTy(Bool(), ty1, ty2, ty3) if ty1 == ty2 && ty2 == ty3 => Some(ty1)
            case _                                                                    => None
