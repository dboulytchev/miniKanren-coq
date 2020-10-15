A certified semantics for relational programming workout.

`make` command will build and verify everything, and extract code from the Coq specification

The folder 'src' contains the specification of the semantics and all the proofs in Coq:

- The subfolder 'src/Preliminaries' contains the specification of premilinary notions used in the semantics:
    - Unification.v -- notions from unification theory (terms, substitutions, computation of the most general unifier)
    - Streams.v -- (possibly infinite) streams and their properties 
- The subfolder 'src/Syntax' contains the specification of syntax of conventional miniKanren:
    - Language.v -- base language ('Prog' axiom here is an arbitrary correct program)
- The subfolder 'src/InterleavingSearch' contains the specification of syntax and semantics of miniKanren language with canonical interleaving search:
    - DenotationalSem.v -- denotational semantics
    - OperationalSem.v -- operational semantics for interleaving search
    - Soundness.v -- soundness of interleaving search
    - Completeness.v -- completeness of interleaving search
- The subfolder 'src/SLDSearch' contains the specification of syntax and semantics of miniKanren language with SLD resolution with cuts (it repeats the specification of interleaving search with minor modifications):
    - LanguageSLD.v -- base language extended with ''cut'' constructs ('Prog' axiom here is an arbitrary correct program)
    - DenotationalSemSLD.v -- denotational semantics
    - OperationalSemSLD.v -- operational semantics for SLD resolution with cuts
    - SoundnessSLD.v -- soundness of SLD resolution with cuts
- The subfolder 'src/FairConjunction' contains the specification of semantics for fair conjunction:
    - AngelicSemantics.c -- angelic semantics
    
The folder 'extracted' contains reference interpreters extracted from the Coq specification:

- interleaving_interpreter.hs -- the code extracted from interleaving search semantics (from src/InterleavingSearch/OperationalSem.v)
- interleaving_interpreter_wrapped.hs -- the code from interleaving_interpreter.hs appended with primitives for more convenient use and some tests
- sld_interpreter.hs -- the code extracted from SLD resolution with cuts semantics (from src/SLDSearch/OperationalSem.v)
- sld_interpreter_wrapped.hs -- the code from sld_interpreter.hs appended with primitives for more convenient use (including the Prolog to MiniKanren translation) and some tests
