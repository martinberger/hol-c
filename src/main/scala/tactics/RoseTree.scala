package Prover

sealed trait RoseTree[G, T]
case class Hole[G, T](i: Int)                                                        extends RoseTree[G, T]
case class Justif[G, T](prove: List[T] => Option[T], children: List[RoseTree[G, T]]) extends RoseTree[G, T]

object RoseTree:

    def walk[G, T](rt: RoseTree[G, T]): Option[T] =
        rt match
            case Hole(_) => None
            case Justif(proves, children) =>
                for (
                  tmp <- Lib.optionsOut(children.map(walk(_)));
                  res <- proves(tmp)
                ) yield res

    def replace[G, T](rt: RoseTree[G, T], i: Int, justif: Justif[G, T]): RoseTree[G, T] =
        rt match
            case Hole(j)                 => if i == j then justif else rt
            case Justif(prove, children) => Justif(prove, children.map(replace(_, i, justif)))
