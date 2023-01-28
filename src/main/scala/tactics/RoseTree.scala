package Prover

sealed trait RoseTree[T]
case class Hole[T](i: Int)                                                     extends RoseTree[T]
case class Justif[T](prove: List[T] => Option[T], children: List[RoseTree[T]]) extends RoseTree[T]

object RoseTree:

    def walk[T](rt: RoseTree[T], pad: String = ""): Option[T] =
        // println(rt)
        rt match
            case Hole(_) => { /*println(s"${pad}rosetree NONE");*/
                None
            }
            case Justif(proves, children) =>
                // println(s"${pad}rosetree Justif, found ${children.size} children")
                val pad2 = s"   ${pad}"
                for (
                  tmp <- Lib.optionsOut(children.map(walk(_, pad2)));
                  res <- proves(tmp)
                ) yield res

    def replace[T](rt: RoseTree[T], i: Int, justif: Justif[T]): RoseTree[T] =
        // println(s"      replace(${rt}, ${i}, ${justif})")
        rt match
            case Hole(j) =>
                if i == j then justif
                else rt
            case Justif(proves, l) => Justif(proves, l.map(subRT => replace(subRT, i, justif)))
