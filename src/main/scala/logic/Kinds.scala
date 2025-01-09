package Prover

sealed trait Kind derives CanEqual
case object TyKind                  extends Kind
case class ConstructorKind(k: Kind) extends Kind

object TyFunctionKind:
    def apply(): Kind = ConstructorKind(TyKind)
    def unapply(kind: Kind): Boolean =
        kind match
            case ConstructorKind(TyKind) => true
            case _                       => false

object BinaryTyFunctionKind:
    def apply(): Kind = ConstructorKind(ConstructorKind(TyKind))
    def unapply(kind: Kind): Boolean =
        kind match
            case ConstructorKind(ConstructorKind(TyKind)) => true
            case _                                        => false
