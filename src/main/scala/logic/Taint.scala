package Prover

sealed trait Taint
case object I  extends Taint
case object W  extends Taint
case object C  extends Taint
case object CH extends Taint
// case object E   extends Taint // Not used in current version of paper
// case object CE  extends Taint // Not used in current version of paper
// case object CC  extends Taint // Not used in current version of paper
// case object CCE extends Taint // Not used in current version of paper

given CanEqual[Taint, Taint] = CanEqual.derived

// Taint semilattice has this order:
//
//   CH
//    |
//    C
//    |
//    W
//    |
//    I

object TaintLattice extends JoinSemilattice:
    type T = Taint

    val bot = I
    val top = CH

    def eq(t1: T, t2: T): Boolean = t1 == t2
    def lub(t1: T, t2: T): T =
        (t1, t2) match
            case (t1, t2) if t1 == t2 => t1
            case (I, t)               => t
            case (t, I)               => t
            case (W, t)               => t
            case (t, W)               => t
            case (C, t)               => t
            case (t, C)               => t
            case (_, _)               => CH
