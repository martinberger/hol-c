package Prover

object Context:

    type Context = List[Term]

    def valid(gamma: Context): Boolean             = gamma.forall(Term.check(_, Prop()))
    def fv(gamma: Context): Set[Var]               = gamma.foldLeft(Set.empty)((accu, tm) => accu ++ Term.fv(tm))
    def tySubst(gamma: Context, ty: Ty, tv: TyVar) = gamma.map(Term.tySubst(_, ty, tv))
    def subst(gamma: Context, tm: Term, x: Var)    = gamma.map(Term.subst(_, tm, x))
    def remove(gamma: Context, tm: Term): Context  = gamma.diff(List(tm))
