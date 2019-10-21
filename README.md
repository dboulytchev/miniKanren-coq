# miniKanren-coq
A certified semantics for relational programming workout.

The folder 'src' contains the formalization of the system and all the proofs:

- Unify.v -- preliminaries from unification theory (terms, substitutions, computation of the most general unifier)
- Stream.v -- (possibly infinite) streams and their properties 
- MiniKanrenSyntax.v -- base language ('Prog' axiom here is an arbitrary correct program)
- DenotationalSem.v -- denotational semantics
- OperationalSem.v -- operational semantics for the interleaving search
- OpSemSoundness.v -- soundness of the interleaving search
- OpSemCompleteness.v -- completeness of the interleaving search
- OperationalSemSLD.v -- operational semantics for the SLD search (with cuts)
- OpSemSLDSoundness.v -- soundness of the SLD search (with cuts)

The folder 'extracted' contains reference interpreters:

- interpreter.hs -- the code extracted from interleaving search semantics (from OperationalSem.v)
- interpreter_wrapped.hs -- the code from interpreter_wrapped.hs appended with primitives for more convenient use and some tests
- sld_interpreter.hs -- the code extracted from interleaving search semantics (from OperationalSem.v)
- sld_interpreter_wrapped.hs -- the code from sld_interpreter_wrapped.hs appended with primitives for more convenient use (including the Prolog to MiniKanren translation) and some tests
