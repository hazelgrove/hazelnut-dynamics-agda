# hazelnut-polymorphism-agda
This repository is the De Bruijn version of the mechanization of the work described in our TFP24 paper.

# Where To Find Each Theorm

The main syntctic categories and judgements are found in [core-type.agda](core-type.agda), [core-exp.agda](core-exp.agda), and [core.agda](core.agda). De Bruijn index operations and substitutions are defined in [core-subst.agda](core-subst.agda).

The proofs of each part of Theorem 5 can be found in:

- [elaborability.agda](elaborability.agda)
- [elaboration-generality.agda](elaboration-generality.agda)
- [elaboration-unicity.agda](elaboration-unicity.agda)
- [typed-elaboration.agda](typed-elaboration.agda)
- [type-assignment-unicity.agda](type-assignment-unicity.agda)

The proofs of each part of Theorem 1 (Type Safety) can be found in:

- [preservation.agda](preservation.agda)
- [progress.agda](progress.agda)

The proofs of each part of Theorem 6 can be found in:

- [complete-elaboration.agda](complete-elaboration.agda)
- [complete-preservation.agda](complete-preservation.agda)
- [complete-progress.agda](complete-progress.agda)

The proof of Theorem 2 can be found in:

- [parametricity.agda](parametricity.agda)

The proof of Theorem 3 and Corollary 2 can be found in:

- [parametricity2.agda](parametricity.agda)
  - Lemma 1: [parametricity2-lemmas1.agda](parametricity2-lemmas1.agda)
  - Lemma 2: [parametricity2-lemmas2.agda](parametricity2-lemmas2.agda)

The proof of Theorem 4 (the Static Gradual Guarantee) can be found in:

- [graduality.agda](graduality.agda)
