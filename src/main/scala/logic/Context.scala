package Prover

object Context:

    type Context = List[Term] // Note: this is not a set to make tactics
    // easier, see https://github.com/DominicPM/subclassical/issues/16
    // In the paper, contexts are sets

    def valid(gamma: Context): Boolean             = gamma.forall(tm => { Term.check(tm, Prop()) })
    def fv(gamma: Context): Set[Var]               = gamma.toList.foldLeft(Set.empty)((accu, tm) => accu ++ Term.fv(tm))
    def tySubst(gamma: Context, ty: Ty, tv: TyVar) = gamma.toList.map(Term.tySubst(_, ty, tv))
    def subst(gamma: Context, tm: Term, x: Var)    = gamma.toList.map(Term.subst(_, tm, x))
    def remove(gamma: Context, tm: Term): Context  = gamma.diff(List(tm))
