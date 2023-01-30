package Prover

sealed trait RoseTree[T]
case class Hole[T](i: Int) extends RoseTree[T] { override def toString(): String = s"[  ${i}  ]"}
case class Justif[T](prove: List[T] => Option[T], children: List[RoseTree[T]]) extends RoseTree[T] { override def toString(): String = s"Justif(..., ${children})" }

object RoseTree:

    def walk[T](rt: RoseTree[T], pad: String = ""): Option[T] =
        rt match
            case Hole(_) =>                 None
            case Justif(proves, children) =>
                val pad2 = s"   ${pad}"
                for (
                  tmp <- Lib.optionsOut(children.map(walk(_, pad2)));
                  res <- proves(tmp)
                ) yield res

    def replace[T](rt: RoseTree[T], i: Int, justif: Justif[T]): RoseTree[T] =
        rt match
            case Hole(j) =>                if i == j then justif else rt
            case Justif(prove, children) => Justif(prove, children.map(replace(_, i, justif)))
