# miniKanren-coq
A certified semantics for miniKanren with disequality constraints workout.

The folder 'src' contains the formalization of the system and all the proofs:

- Unify.v -- preliminaries from unification theory (terms, substitutions, computation of the most general unifier)
- Stream.v -- (possibly infinite) streams and their properties 
- MiniKanrenSyntax.v -- base language ('Prog' axiom here is an arbitrary correct program)
- DenotationalSem.v -- denotational semantics
- OperationalSem.v -- abstract constraint store definition and parametrized operational semantics
- OpSemSoundness.v -- soundness of the interleaving search under conditions
- OpSemCompleteness.v -- completeness of the interleaving search under conditions
- ObviousDisequality.v -- obvious concrete implementation of constraint stores

The folder 'extracted' contains reference interpreters:

- obvious_diseq_interpreter.hs -- the code extracted from operational semantics instantiated with the obvious constraint stores implementation (from ObviousDisequality.v)
- obvious_diseq_interpreter_wrapped.hs -- the code from obvious_diseq_interpreter.hs appended with primitives for more convenient use and some tests
