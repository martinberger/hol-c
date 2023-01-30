package Prover

import ThmClass._
import scala.collection.immutable.Queue
import Context._

import ProofState.{HoleID, Goal}

case class GoalContext(
    val goal: Goal, // type Goal = (Context, Term, Taint) defined below
    val goalName: String
) {
    override def toString(): String = s"${goal._1} |- ${goal._2} : ${goal._3}"
}

class ProofState(
    val subgoals: Map[HoleID, GoalContext],
    val justificationTree: RoseTree[Goal],
    val selected: List[HoleID]
) {
    override def toString(): String = s"""
        +++++++++++++++++++++++++++++
        subgoals = \n${ProofState.subgoalToString(subgoals)}
        selected = ${selected} (as names: ${ProofState.selectedGoalNames(this)})    
        all holeIDs = ${subgoals.keySet}
        +++++++++++++++++++++++++++++
    """
}

object ProofState:

    type Goal = (Context, Term, Taint) // TODO make this opaque later and why not use Thm?
    // TODO make this into class for easier pretty printing and better code readability
    type HoleID = Int // TODO make opaque

    def subgoalToString(subgoals: Map[HoleID, GoalContext]): String =
        val l = subgoals.toList.map(t => s"   ${t._1} -> ${t._2}")
        Lib.sandwichMerge("\n   ")(l)

    def nameToHoleID(ps: ProofState)(s: String): Option[HoleID] =
        val l = ps.subgoals.toList.filter(_._2.goalName == s)
        if l.size != 1 then None else Some(l(0)._1)

    def holeIDtoName(ps: ProofState)(i: HoleID): String =
        ps.subgoals(i).goalName

    def allHoleIDs(ps: ProofState): Set[HoleID] = ps.subgoals.keySet

    def allGoalNames(ps: ProofState): Set[String] = ps.subgoals.keySet.map(holeIDtoName(ps))

    def selectedGoalNames(ps: ProofState): List[String] = ps.selected.map(holeIDtoName(ps))

    def mkFreshNamed(goal: Goal, name: String): ProofState =
        Lib.reset() // Needed because we don't have a fully functional architecture.
        val holeID            = Lib.gensym()
        val justificationTree = Hole[Thm](holeID)
        ProofState(Map(holeID -> GoalContext(goal, name)), justificationTree, List())

    def mkFresh(goal: Goal): ProofState = // Do we need this?>
        mkFreshNamed(goal, s"goal_{ Lib.gensym() }")

    def insert(ps: ProofState)(holeID: HoleID, preGoals: PreTactic.PreGoals): ProofState =
        val (newSubgoals, justif) = preGoals
        val newHoles              = newSubgoals.map(goal => { val hid = Lib.gensym(); (hid, goal, new Hole[Thm](hid)) })
        val newChildren           = newHoles.map(_._3)
        val newJustificationTree  = RoseTree.replace(ps.justificationTree, holeID, Justif[Thm](justif, newChildren))
        val remainingSubgoals     = ps.subgoals.filter(_._1 != holeID)
        val allNewSubgoals        = remainingSubgoals ++ newHoles.map(t => (t._1, GoalContext(t._2, s"goal_${t._1}"))).toMap
        ProofState(allNewSubgoals, newJustificationTree, List())

    def getSelectedSubgoals(ps: ProofState): Map[HoleID, GoalContext] =
        ps.subgoals.filter(gc => ps.selected.contains(gc._1))

    def act(proofState: ProofState)(tac: Tactic): Option[ProofState] =
        tac match
            case Apply(preTac) =>
                proofState.selected match
                    case List() => None
                    case holeID :: rest =>
                        assert(rest.size < 1) // TODO this is not true in general, but true for all tactics implemented.
                        val selectedGoalContext = proofState.subgoals(holeID)
                        PreTactic.apply(preTac)(selectedGoalContext.goal) match
                            case None           => None
                            case Some(preGoals) => Some(insert(proofState)(holeID, preGoals))
            case AndThen(fst, snd) =>
                for (
                  tmp <- act(proofState)(fst);
                  res <- act(tmp)(snd)
                ) yield res
            case Id() => Some(proofState)
            case FailWith(msg) => println(msg); None
            // Note: passing on error message.
            // requires replacing Option[ProofState] with something
            // more sophisticated like Either[String, ProofState]
            case Try(tac) =>
                act(proofState)(tac) match
                    case res @ Some(_) => res
                    case None          => Some(proofState)
            case OrElse(fst, snd) =>
                act(proofState)(fst) match
                    case None              => act(proofState)(snd)
                    case success @ Some(_) => success
            case Repeat(tac) => Lib.fail("ProofState.scala")("Repeat tactic not implemented, because, not useful with current proof system")
            case Select(selectedSubgoals) => // NOTE: invalid names are simply not selected.
                val selectedHoleID = selectedSubgoals.map(nameToHoleID(proofState)).flatten
                val newSelection   = selectedSubgoals :: (proofState.selected.filter(i => !selectedSubgoals.contains(i)))
                Some(ProofState(proofState.subgoals, proofState.justificationTree, selectedHoleID))
            case SelectLast() => // NOTE Experimental, if it works can be unified with Select(l) above
                val hids = proofState.subgoals.keySet
                if hids.isEmpty then return None // NOTE very strict for this experiment. We may also return old proof state
                Some(ProofState(proofState.subgoals, proofState.justificationTree, List(hids.max)))
            // Note we assume that goal names are monotonically increasing!
            case PrintState(active) =>
                if active then println(proofState)
                Some(proofState)

    def qed(ps: ProofState): Option[Thm] =
        if ps.subgoals.size > 0 then return None
        val res = RoseTree.walk(ps.justificationTree)
        res
