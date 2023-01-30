package Prover

import Context._
import TaintLattice._

trait ProofSystem:

    type Thm

    def init(gamma: Context, phi: Term): Option[Thm]
    def refl(gamma: Context, tm: Term, ty: Ty): Option[Thm]
    def sym(thm: Thm): Option[Thm]
    def trans(thm1: Thm, thm2: Thm): Option[Thm]
    def lcong(thm: Thm, x: Var): Option[Thm]
    def acong(thm1: Thm, thm2: Thm): Option[Thm]
    def lift(thm: Thm, bigTaint: Taint): Option[Thm]
    def beta(gamma: Context, lam: Lam, src: Ty, target: Ty, tm: Term): Option[Thm]
    def tysubst(thm: Thm, ty: Ty, tv: TyVar): Option[Thm]
    def subst(thm: Thm, tm: Term, ty: Ty, x: Var): Option[Thm]
    def iffE1(thm1: Thm, thm2: Thm): Option[Thm]
    def iffE2(thm1: Thm, thm2: Thm): Option[Thm]
    def iffI(thm1: Thm, thm2: Thm): Option[Thm]
    def trueI(gamma: Context): Option[Thm]
    def falseE(thm: Thm, phi: Term): Option[Thm]
    def conjI(thm1: Thm, thm2: Thm): Option[Thm]
    def conjE1(thm: Thm): Option[Thm]
    def conjE2(thm: Thm): Option[Thm]
    def disjI1(thm: Thm, tm2: Term): Option[Thm]
    def disjI2(thm: Thm, tm1: Term): Option[Thm]
    def disjE(thm1: Thm, thm2: Thm, thm3: Thm): Option[Thm]
    def impI(thm: Thm, tm1: Term): Option[Thm]
    def impE(thm1: Thm, thm2: Thm): Option[Thm]
    def negI(thm: Thm, phi: Term): Option[Thm]
    def negE(thm1: Thm, thm2: Thm): Option[Thm]
    def allE(thm: Thm, tm: Term): Option[Thm]
    def allI(thm: Thm, x: Var): Option[Thm]
    def exI(thm: Thm, phi: Term, x: Var, tm: Term): Option[Thm]
    def exE(thm1: Thm, thm2: Thm, name: String): Option[Thm]
    def eta(gamma: Context, tm: Term, ty: Ty): Option[Thm]
    def lem(gamma: Context, tm: Term): Option[Thm]
    def raa(thm: Thm, tm: Term): Option[Thm]
    def wk(thm: Thm, tm: Term): Option[Thm]

    def show(thm: Thm): (Context, Term, Taint)
