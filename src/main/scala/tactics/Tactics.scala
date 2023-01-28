package Prover

sealed trait Tactic
case class Apply(preTac: PreTactic)           extends Tactic
case class AndThen(fst: Tactic, snd: Tactic)  extends Tactic
case class Id()                               extends Tactic
case class FailWith(msg: String)              extends Tactic
case class Try(tac: Tactic)                   extends Tactic
case class OrElse(fst: Tactic, snd: Tactic)   extends Tactic
case class Repeat(tac: Tactic)                extends Tactic
case class Select(subgoals: List[String])     extends Tactic
case class PrintState(active: Boolean = true) extends Tactic
case class SelectLast()                       extends Tactic // TODO Experimental, if it works can be unified with Select(l) above

object Tactic:
    def AndThenList(l: List[Tactic]): Tactic =
        // println(s"[AndThenList] found ${l.size}") TODO remove junk
        l match
            case List()      => Id()
            case fst :: rest => AndThen(fst, AndThenList(rest))

    def makeGeneric(l: List[PreTactic], printState: Boolean = false): List[Tactic] =
        val l1 = l.map(Apply(_))
        val l2 = Lib.sandwich(SelectLast())(l1)
        if printState then Lib.saturate(PrintState(true))(l2) else l2
