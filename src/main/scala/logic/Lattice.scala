package Prover

trait JoinSemilattice:

    type T
    val top: T
    def eq(t1: T, t2: T): Boolean
    def lub(t1: T, t2: T): T

    def lub3(t1: T, t2: T, t3: T): T = lub(t1, lub(t2, t3))
    def leq(t1: T, t2: T): Boolean   = eq(lub(t1, t2), t2)
    // Standard operations are definable from above
    // def lt(t1: T, t2: T): Boolean = { ??? } // TODO: define from lubSkeleton
    // def leq(t1: T, t2: T): Boolean = { ??? } // TODO: define from lubSkeleton
    // def comparable(t1: T, t2: T): Boolean = { leq(t1, t2) || leq(t2, t1) }
