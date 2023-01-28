package Prover

sealed trait Kind
case object TyKind                  extends Kind
case class ConstructorKind(k: Kind) extends Kind

given CanEqual[Kind, Kind] = CanEqual.derived // TODO: check this defines the right equality

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
