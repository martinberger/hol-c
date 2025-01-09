package Prover

object Lib:

    def fail[T](loc: String)(msg: String): T =
        throw new Exception(s"[${loc}] ${msg}")

    private var global = -1

    def gensym(): Int = { global += 1; global }

    def reset(): Unit = { global = -1 } // Needed b/c we don't have a fully functional gensym

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

    def sandwichMerge[A](empty: A, add: (A, A) => A)(between: A)(l: List[A]): A =
        import scala.annotation.tailrec
        @tailrec def aux(accu: A)(l: List[A]): A =
            l match
                case List()         => accu
                case List(a)        => add(accu, a)
                case a :: b :: rest => aux(add(add(accu, a), between))(b :: rest)
        (aux(empty)(l))

    def sandwichMerge(between: String)(l: List[String]): String =
        def add(s1: String, s2: String): String = { s"${s1}${s2}" }
        sandwichMerge("", add)(between)(l)

    def sandwich[A](between: A)(l: List[A]): List[A] =
        import scala.annotation.tailrec
        @tailrec def aux(accu: List[A])(l: List[A]): List[A] =
            l match
                case List()         => accu
                case List(_)        => accu ++ l
                case a :: b :: rest => aux(accu ++ List(a, between))(b :: rest)
        (aux(List())(l))

    def saturate[A](between: A)(l: List[A]): List[A] =
        between :: (sandwich(between)(l)) ++ List(between)

    def map2[A, B](l: List[A])(f: (A, A) => B): List[B] =
        l match
            case Nil                      => List()
            case List(a)                  => List(f(a, a))
            case List(a1, a2)             => List(f(a1, a2))
            case a1 :: (rest @ (a2 :: _)) => f(a1, a2) :: (map2(rest)(f))
