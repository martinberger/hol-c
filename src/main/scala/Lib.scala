package Prover

object Lib:

    private var global = -1

    def gensym(): Int = { global += 1; global }

    def reset(): Unit = { global = -1 } // TODO remove this

    def fresh(s: Set[String]): String =
        var x     = ""
        var found = false
        while !found do
            x = s"x${gensym().toInt}"
            if !s.contains(x) then found = true
        return x

    def freshVar(xs: Set[Var], ty: Ty): Var =
        Var(fresh(xs.map(_.name)), ty)

    def optionsOut[T](l: List[Option[T]]): Option[List[T]] =
        l match
            case List()    => Some(List())
            case None :: _ => None
            case Some(t) :: rest =>
                optionsOut(rest) match
                    case None         => None
                    case Some(result) => Some(t :: result)

    def sandwichMerge[A](empty: A, add: (A, A) => A)(between: A)(l: Seq[A]): A = {
        import scala.annotation.tailrec
        @tailrec def aux(accu: A)(l: Seq[A]): A = {
            l match { // WARNING, the below is false, since it only matches on LISTS what if this is not a list?
                case Seq()          => accu
                case Seq(a)         => add(accu, a)
                case a :: b :: rest => aux(add(add(accu, a), between))(b :: rest)
            }
        }
        (aux(empty)(l))
    }

    def sandwichMerge(between: String)(l: Seq[String]): String = {
        def add(s1: String, s2: String): String = { s"${s1}${s2}" }
        sandwichMerge("", add _)(between)(l)
    }

    def sandwich[A](between: A)(l: List[A]): List[A] = {
        import scala.annotation.tailrec
        @tailrec def aux(accu: List[A])(l: List[A]): List[A] = {
            l match { // WARNING, the below is false, since it only matches on LISTS what if this is not a list?
                case List()         => accu
                case List(_)        => accu ++ l
                case a :: b :: rest => aux(accu ++ List(a, between))(b :: rest)
            }
        }
        (aux(List())(l))
    }

    def saturate[A](between: A)(l: List[A]): List[A] =
        between :: (sandwich(between)(l)) ++ List(between)
