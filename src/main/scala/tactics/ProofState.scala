package Prover

import Thm._
import Context._
import ProofState.{HoleID, Goal}

case class GoalContext(val goal: Goal, val goalName: String):
    override def toString(): String = s"${goal._1} |- ${goal._2} : ${goal._3}"

class ProofState(
    val subgoals: Map[HoleID, GoalContext],
    val justificationTree: RoseTree[Goal, Thm],
    val selected: List[HoleID]
):
    override def toString(): String = s"""
        +++++++++++++++++++++++++++++
        subgoals = \n${ProofState.subgoalToString(subgoals)}
        selected = ${selected} (as names: ${ProofState.selectedGoalNames(this)})    
        all holeIDs = ${subgoals.keySet}
        +++++++++++++++++++++++++++++
    """

object ProofState:

    type Goal   = (Context, Term, Taint) // Possible enhancement: make Goal opaque
    type HoleID = Int                    // Possible enhancement: make HoleID opaque

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
        val justificationTree = Hole[Goal, Thm](holeID)
        ProofState(Map(holeID -> GoalContext(goal, name)), justificationTree, List(holeID))

    def mkFresh(goal: Goal): ProofState =
        mkFreshNamed(goal, s"goal_{ Lib.gensym() }")

    def insert(ps: ProofState)(holeID: HoleID, preGoals: PreTactic.PreGoals): ProofState =
        val (newSubgoals, justif) = preGoals
        val newHoles              = newSubgoals.map(goal => { val hid = Lib.gensym(); (hid, goal, new Hole[Goal, Thm](hid)) })
        val newChildren           = newHoles.map(_._3)
        val newJustificationTree  = RoseTree.replace(ps.justificationTree, holeID, Justif[Goal, Thm](justif, newChildren))
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
                        assert(rest.size < 1) // NOTE: this is not true in general, but true for all tactics currently implemented.
                        val selectedGoalContext = proofState.subgoals(holeID)
                        PreTactic.apply(preTac)(selectedGoalContext.goal) match
                            case None => None
                            case Some(preGoals) =>
                                val newPS        = insert(proofState)(holeID, preGoals)
                                val hids         = newPS.subgoals.keySet
                                val nextSelected = if hids.isEmpty then List() else List(hids.max)
                                Some(ProofState(newPS.subgoals, newPS.justificationTree, nextSelected))
            case AndThen(fst, snd) =>
                for (
                  tmp <- act(proofState)(fst);
                  res <- act(tmp)(snd)
                ) yield res
            case Id() => Some(proofState)
            case FailWith(msg) => println(msg); None
            // NOTE: passing on error message in a more principled way
            // requires replacing Option[ProofState] with something
            // more sophisticated like Either[String, ProofState]
            // See Github Issue https://github.com/martinberger/hol-c/issues/4
            case Try(tac) =>
                act(proofState)(tac) match
                    case res @ Some(_) => res
                    case None          => Some(proofState)
            case OrElse(fst, snd) =>
                act(proofState)(fst) match
                    case None              => act(proofState)(snd)
                    case success @ Some(_) => success
            case Repeat(tac)              => Lib.fail("ProofState.scala")("Repeat tactic not implemented: not useful with current proof system")
            case Select(selectedSubgoals) =>
                // NOTE: invalid names are simply not selected.
                // NOTE: this will throw away what is currently selected
                val selectedHoleID = selectedSubgoals.map(nameToHoleID(proofState)).flatten
                val newSelection   = selectedSubgoals :: (proofState.selected.filter(i => !selectedSubgoals.contains(i)))
                Some(ProofState(proofState.subgoals, proofState.justificationTree, selectedHoleID))
            case PrintState() =>
                println(proofState)
                Some(proofState)

    def qed(ps: ProofState): Option[Thm] =
        if ps.subgoals.size > 0 then return None
        RoseTree.walk(ps.justificationTree)
