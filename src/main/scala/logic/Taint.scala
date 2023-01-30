package Prover

sealed trait Taint
case object I   extends Taint
case object E   extends Taint
case object C   extends Taint
case object CE  extends Taint
case object CC  extends Taint
case object CCE extends Taint
case object W   extends Taint // TODO: Add ordering relations. CURRENTLY WRONG
case object CH  extends Taint // TODO: Add ordering relations. CURRENTLY WRONG

given CanEqual[Taint, Taint] = CanEqual.derived

// Taint semilattice has this order:
//
//        CCE
//        /\
//      CE  CC
//     / \ /
//    E   C
//     \ /
//      I

object TaintLattice extends JoinSemilattice:
    type T = Taint

    val bot = I
    val top = CCE

    def eq(t1: T, t2: T): Boolean = t1 == t2
    def lub(t1: T, t2: T): T =
        (t1, t2) match
            case (t1, t2) if t1 == t2 => t1
            case (I, t)               => t
            case (t, I)               => t
            case (E, C) | (C, E)      => CE
            case (E, CC) | (CC, E)    => CCE
            case (E, t)               => t
            case (t, E)               => t
            case (C, t)               => t
            case (t, C)               => t
            case (CE, CC) | (CC, CE)  => CCE
            case _                    => CCE
