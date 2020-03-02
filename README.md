# miniKanren-coq
A certified semantics for miniKanren with disequality constraints workout.

The folder 'src' contains the formalization of the system and all the proofs:

- Unify.v -- preliminaries from unification theory (terms, substitutions, computation of the most general unifier)
- Stream.v -- (possibly infinite) streams and their properties 
- MiniKanrenSyntax.v -- base language ('Prog' axiom here is an arbitrary correct program)
- DenotationalSem.v -- denotational semantics
- OperationalSem.v -- operational semantics for the interleaving search
- OpSemSoundness.v -- soundness of the interleaving search
- OpSemCompleteness.v -- completeness of the interleaving search

The folder 'extracted' contains reference interpreters:

- interpreter.hs -- the code extracted from interleaving search semantics (from OperationalSem.v)
- interpreter_wrapped.hs -- the code from interpreter_wrapped.hs appended with primitives for more convenient use and some tests
- sld_interpreter.hs -- the code extracted from SLD search semantics (from OperationalSemSLD.v)
- sld_interpreter_wrapped.hs -- the code from sld_interpreter_wrapped.hs appended with primitives for more convenient use (including the Prolog to MiniKanren translation) and some tests
