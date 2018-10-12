# hazelnut-dynamics-agda
This repository is the mechanization of the work described in our [POPL19
paper](https://github.com/hazelgrove/hazelnut-dynamics). It includes the
full definitions of all the judgements and metafunctions and proofs of the
theorems up through Section 3.

# How To Check These Proofs

These proofs are known to check under `Agda 2.5.1.1`. The most direct, if
not easiest, option to check the proofs is to install that version of Agda,
or one compatible with it, and run `agda all.agda` at the command line.

Alternatively, we have provided a [Docker file](Dockerfile) to make it
easier to build that environment and check the proofs. To use it, first
install [Docker](https://www.docker.com/products/docker-desktop) and clone
this repository to your local machine. Then, at a command line inside that
clone, run `docker build -t hazel-popl19 .`. This may take a fair amount of
time. When it finishes, run `docker run hazel-popl19`. This should take
less than a minute, output a lot of lines that begin with `Finished .. ` or
`Checking ..`, and end with the line `Finished all.` to indicate success.

# Where To Find Each Theorem

All of the judgements defined in the paper are given in
[core.agda](core.agda). The syntax is meant to mirror the on-paper notation
as closely as possible, with some small variations because of the
limitations of the language.

For easy reference, the proofs for the theorems in order of appearance in
the paper text can be found as follows:

- Theorem 3.1, _Typed Expansion_, is in [typed-expansion.agda](typed-expansion.agda)
- Theorem 3.2, _Type Assignment Unicity_, is in [type-assignment-unicity.agda](type-assignment-unicity.agda)
- Theorem 3.3, _Expandability_, is in [expandability.agda](expandability.agda )
- Theorem 3.4, _Expansion Generality_, is in [expansion-generality.agda](expansion-generality.agda)
- Definition 3.5, _Identity Substitution_, is in [core.agda](core.agda) on
  line 31 TODO CHECK THIS BEFORE SUBMISSION
- Definition 3.6, _Substitution Typing_, is in [core.agda](core.agda) on
  line 251 TODO CHECK THIS BEFORE SUBMISSION
- Theorem 3.7, _Finality_, is in [finality.agda](finality.agda)
- Lemma 3.8, _Grounding_, is in [grounding.agda](grounding.agda)
- Theorem 3.9, _Preservation_, is in [preservation.agda](preservation.agda)
- Theorem 3.10, _Progress_, is in [progress.agda](progress.agda)
- Theorem 3.11, _Complete Expansion_, is in [complete-expansion.agda](complete-expansion.agda)
- Theorem 3.12, _Complete Preservation_, is in [complete-preservation.agda](complete-preservation.agda)
- Theorem 3.13, _Complete Progress_, is in [complete-progress.agda](complete-progress.agda)

# Description of Agda Files

The theorems do not quite tell the whole story: they all rely on a variety
of lemmas and smaller claims or observations that aren't explicitly
mentioned in the paper text. What follows is a rough description of what to
expect from each source file; more detail is provided in the comments
inside each.

## Prelude and Datatypes

These files give definitions and syntactic sugar for common elements of
type theory (sum types, products, sigmas, etc.) and data structures
(natural numbers and lists) that are used pervasively throughout the rest
of the development.

- [List.agda](List.agda)
- [Nat.agda](Nat.agda)
- [Prelude.agda](Prelude.agda)

## Core Definitions

- [contexts.agda](contexts.agda) defines contexts as functions from natural
  numbers to possible contents and proves the relevant properties needed to
  make this definition usable.
- [core.agda](core.agda)

## Meta Concerns
- [all.agda](all.agda) is morally a make file: it includes every module in
  every other file, so running `$ agda all.agda` on a clean clone of this
  repository will recheck every proof from scratch. It is known to load
  cleanly with `Agda version 2.5.1.1`; we have not tested it on any other
  version.
- [structural-assumptions.agda](structural-assumptions.agda) is a file of
  postulates for standard structural properties about contexts and
  judgements that we have not yet proven. This will not be included in the
  final version of this mechanization, but it's helpful to have one place
  to look to know exactly what is being taken on faith and what's really
  proven. In a conservative sense, you can think of the rest of the
  theorems as being implied by in the postulates taken here rather than in
  their full form.

## Lemmas

These files contain small technical lemmas for the corresponding judgement
or theorem. They are generally not surprising once stated, although it's
perhaps not immediately why they're needed, and tend to obfuscate the actual
proof text. They are corralled into their own modules in an effort to aid
readability.

- [focus-formation.agda](focus-formation.agda)
- [ground-decidable.agda](ground-decidable.agda)
- [htype-decidable.agda](htype-decidable.agda)
- [lemmas-consistency.agda](lemmas-consistency.agda)
- [lemmas-ground.agda](lemmas-ground.agda)
- [lemmas-matching.agda](lemmas-matching.agda)
- [lemmas-progress-checks.agda](lemmas-progress-checks.agda)
- [lemmas-subst-ta.agda](lemmas-subst-ta.agda)
- [matched-ground-invariant.agda](matched-ground-invariant.agda)
- [synth-unicity.agda](synth-unicity.agda) argues that the synthesis
  judgement produces at most one type for a term.
- [finality.agda](finality.agda) argues that a final expression only steps
  to itself.

## Theorems

### Canonical Forms

Together, these files give the canonical forms lemma for the language. They
are broken down in a slightly more explicit way than in the paper text,
each type getting its own theorem, for usability later.

- [canonical-boxed-forms.agda](canonical-boxed-forms.agda)
- [canonical-indeterminate-forms.agda](canonical-indeterminate-forms.agda)
- [canonical-value-forms.agda](canonical-value-forms.agda)

### Metatheory of Type Assignment

- [type-assignment-unicity.agda](type-assignment-unicity.agda) argues that
  the type assignment system assigns at most one type to any term.

### Metatheory of Expansion

- [expansion-generality.agda](expansion-generality.agda) argues that the expansion
  judgements respect the bidirectional typing system.
- [expandability.agda](expandability.agda) argues that any well typed
  external term can be expanded to a internal term.
- [expansion-unicity.agda](expansion-unicity.agda) argues that expansion
  produces at most one result.
- [typed-expansion.agda](typed-expansion.agda) argues that the expansion
  respects the type assignment system.

### Type Safety

These first three files contain proofs of type safety for the core
language, where terms and types may both have holes in them and still step.

- [progress.agda](progress.agda) argues that any `dhexp` that gets assigned
  a type either steps, is a boxed value, or is indeterminate
- [progress-checks.agda](progress-checks.agda) argues that the clauses in
  progress are disjoint---that is to say that no expression both steps and
  is a boxed value, etc.
- [preservation.agda](preservation.agda) argues that stepping preserves
  type assignment.

We also argue that our dynamics is a conservative extension in the sense
that if you use it to evaluate terms in the calculus that have no holes in
them, you get the same type safety theorems you might expect for the
restricted fragment without holes.

- [complete-expansion.agda](complete-expansion.agda) argues that the
  expansion of a complete external term into the internal language produces
  another complete term.
- [complete-preservation.agda](complete-preservation.agda) argues that
  stepping a complete term produces a complete term that is assigned the
  same type
- [complete-progress.agda](complete-progress.agda) argues that complete
  terms are either a value or step.


### Metatheory of Instantiation

- [commutativity.agda](commutativity.agda) argues that stepping respects
  hole instantiation.
- [instantiation.agda](instantiation.agda) argues that hole instantiation
  respects type assignment
