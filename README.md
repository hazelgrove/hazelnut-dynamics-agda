# hazelnut-dynamics-agda
This repository is the mechanization of the work described in our
[POPL19 paper](https://arxiv.org/pdf/1805.00155). It includes all of the
definitions and proofs from Section 3, as claimed in Sec. 3.4 (Agda
Mechanization).

# How To Check These Proofs

These proofs are known to check under `Agda 2.5.1.1`. The most direct, if
not the easiest, option to check the proofs is to install that version of
Agda or one compatible with it, download the code in this repo, and run
`agda all.agda` at the command line.

Alternatively, we have provided a [Docker file](Dockerfile) to make it
easier to build that environment and check the proofs. To use it, first
install [Docker](https://www.docker.com/products/docker-desktop), make sure
the Docker daemon is running, and clone this repository to your local
machine. Then, at a command line inside that clone, run

```
docker build -t hazel-popl19 .
```

This may take a fair amount of time. When it finishes, run

```
docker run hazel-popl19
```

This should take less than a minute, output a lot of lines that begin with
`Finished` or `Checking`, and end with the line `Finished all.` to indicate
success.

Most text editors that support Agda can be configured to use the version
instead a Docker container instead of your host machine, so you can
experiment with or evolve this code without making too much of a mess. For
some example instructions, see [the docker-agda
repo](https://github.com/banacorn/docker-agda).

# Where To Find Each Theorem

All of the judgements defined in the paper are given in
[core.agda](core.agda). The syntax is meant to mirror the on-paper notation
as closely as possible, with some small variations because of the
limitations of Agda syntax.

For easy reference, the proofs for the theorems in order of appearance in
the paper text can be found as follows:

- Theorem 3.1, _Typed Elaboration_, is in
  [typed-elaboration.agda](typed-elaboration.agda).
- Theorem 3.2, _Type Assignment Unicity_, is in
  [type-assignment-unicity.agda](type-assignment-unicity.agda).
- Theorem 3.3, _Elaborability_, is in
  [elaborability.agda](elaborability.agda).
- Theorem 3.4, _Elaboration Generality_, is in
  [elaboration-generality.agda](elaboration-generality.agda).
- Theorem 3.5, _Elaboration Unicity_, is in
  [elaboration-unicity.agda](elaboration-unicity.agda).
- Definition 3.6, _Identity Substitution_, is in [core.agda](core.agda) on
  line 31.
- Definition 3.7, _Substitution Typing_, is in [core.agda](core.agda) on
  line 252.
- Theorem 3.8, _Finality_, is in [finality.agda](finality.agda).
- Lemma 3.9, _Grounding_, is in [grounding.agda](grounding.agda).
- Theorem 3.10, _Preservation_, is in
  [preservation.agda](preservation.agda).
- Theorem 3.11, _Progress_, is in [progress.agda](progress.agda).
- Theorem 3.12, _Complete Elaboration_, is in
  [complete-elaboration.agda](complete-elaboration.agda).
- Theorem 3.13, _Complete Preservation_, is in
  [complete-preservation.agda](complete-preservation.agda).
- Theorem 3.14, _Complete Progress_, is in
  [complete-progress.agda](complete-progress.agda).
- Proposition 3.15, _Sensibility_, is taken as a postulate in
  [continuity.agda](continuity.agda). Sensibility for a slightly different
  and richer language is proven in the mechanization of our
  [POPL17](https://arxiv.org/pdf/1607.04180) work.
-  Corollary 3.16, _Continuity_, is in
  [continuity.agda](continuity.agda). Though we did not explicitly claim a
  mechanization of this claim, we give a proof is given in terms of a few
  postulates encoding the results from Omar et al., POPL 2017.

The extended paper with an appendix goes into more detail for some lemmas
and definitions omitted from the main paper, some of which have been
mechanized as well. Those can be found as follows:

- A.1, _Substitution_, is defined in [core.agda](core.agda) at line 294, as
  `[_/_]_` for terms and `apply-env` for substitutions `σ`.
- Lemma A.1, _Substitution_ is in
  [lemmas-subst-ta.agda](lemmas-subst-ta.agda).
- Lemma A.2, _Canonical Value Forms_, is in
  [canonical-value-forms.agda](canonical-value-forms.agda).
- Lemma A.3, _Canonical Boxed Forms_, is in
  [canonical-boxed-forms.agda](canonical-value-forms.agda).
- Lemma A.4, _Canonical Indeterminate Forms_, is in
  [canonical-indeterminate-forms.agda](canonical-value-forms.agda).
- A.3, _Complete Programs_, is defined in [core.agda](core.agda) at line
  160.
- Definition A.5, _Typing Context Completeness_, is defined in
  [core.agda](core.agda) at line 183.
- Lemma A.6, _Complete Consistency_, is in
  [lemmas-complete.agda](lemmas-complete.agda) as `complete-consistency` on
  line 19.
- Lemma A.7, _Complete Casts_, is in [cast-inert.agda](cast-inert.agda) as
  `complete-casts` on line 31.
- A.4, _Multiple Steps_, is defined in [core.agda](core.agda) on line 470.

# Description of Agda Files

The theorem statements rely on a variety of lemmas and smaller claims or
observations that aren't explicitly mentioned in the paper text. What
follows is a rough description of what to expect from each source file;
more detail is provided in the comments inside each.

On paper, we typically take it for granted that we can silently α-rename
terms to equivalent terms whenever a collision of bound names is
inconvenient. In a mechanization, we do not have that luxury and instead
must be explicit in our treatment of binders in one way or another. In our
development here, we assume that all terms are in an α-normal form where
binders are globally not reused.

That manifests in this development where we have chosen to add premises
that binders are unique within a term or disjoint between terms when
needed. These premises are fairly benign, since α-equivalence tells us they
can always be satisfied without changing the meaning of the term in
question. Other standard approaches include using de Bruijn indices,
Abstract Binding Trees, HOAS, or PHOAS to actually rewrite the terms when
needed. We have chosen not to use these techniques because _almost all_ of
the theory we're interested in does not need them and their overhead
quickly becomes pervasive, obfuscating the actual points of interest.

Similarly, we make explicit some premises about disjointness of contexts or
variables being apart from contexts in some of the premises of some rules
that would typically be taken as read in an on-paper presentation. This is
a slightly generalized version of Barendrecht's convention (Barendregt,
1984), which we also used in our [POPL17
mechanization](https://github.com/hazelgrove/agda-popl17) for the same
reason.

Since the type system for external terms is bidirectional, the judgments
defining it are mutually recursive. That means that anything type-directed
is very likely to also be mutually recursive. The grammar of internal
expressions is also mutually recursive with the definition of substitution
environments. All told, a fair number of theorems are mutually recursive as
this percolates through. We try to name things in a suggestive way, using
`x-synth` and `x-ana` for the two halves of a theorem named `x`.

Both hole and type contexts are encoded as Agda functions from natural
numbers to optional contents. In practice these mappings are always
finite. We represent finite substitutions and substitution environments
explicitly as inductive datatypes, `_,_⊢_:s:_`and `env` from
[core.agda](core.agda) respectively, taking advantage of the fact that the
base case in our semantics is always the identity substitution. This allows
us to reason about substitutions in a well-founded way that passes the Agda
termination checker.

## Postulates

We have benign postulates in two places:

- First, we postulate function extensionality in
[Prelude.agda](Prelude.agda), because it is known to be independent from
Agda and we use it to reason about contexts.

- Second, in [continuity.agda](continuity.agda), we postulate some
  judgemental forms and theorems from our POPL17 mechanization in order to
  demonstrate the connections to it described in the paper. We also
  postulate some glue code that allows us to use those theorems in this
  work.

There are no other postulates in this development.

## Meta
- [all.agda](all.agda) is morally a make file: it includes every module in
  every other file, so running `$ agda all.agda` on a clean clone of this
  repository will recheck every proof from scratch. It is known to load
  cleanly with `Agda version 2.5.1.1`; we have not tested it on any other
  version.

## Prelude and Datatypes

These files give definitions and syntactic sugar for common elements of
type theory (sum types, products, sigmas, etc.) and natural numbers that
are used pervasively throughout the rest of the development.

- [Nat.agda](Nat.agda)
- [Prelude.agda](Prelude.agda)

## Core Definitions

- [contexts.agda](contexts.agda) defines contexts as functions from natural
  numbers to possible contents and proves a collection of lemmas that makes
  this definition practical.
- [core.agda](core.agda) gives the definitions of all the grammars and
  judgements in the order presented in the paper as types and metafunctions
  in Agda. It also includes the definition of the judgements that are used
  implicitly on paper but need to be made explicit in a mechanization.

## Structural Properties

- [contraction.agda](contraction.agda) argues that contexts are the same up
  to contraction, and therefore that every judgement that uses them enjoys
  the contraction property. Note that this proof is given for any sort of
  context, so it establishes contraction in both the type and hole contexts
  for those judgements that have both.
- [exchange.agda](exchange.agda) argues that contexts are the same up to
  exchange, and therefore that every judgement that uses the enjoys the
  exchange property. As above, this proof establishes exchange in both the
  type and hole contexts for those jugements that have both.
- [weakening.agda](weakening.agda) argues the weakening properties for
  those judgements where we needed it in the other proofs. This is not
  every weakening property for every judgement, and indeed some of them _do
  not_ enjoy weakening in every argument.

  For example, the elaborations do not support weakening in the typing
  context because the rule for substitution typing requires that the lowest
  substitution be exactly the identity, not something that can be weakened
  to the identity. (See the definition of `STAId` on line 254 of
  [core.agda](core.agda).) In practice, this is not a problem because you
  wouldn't want to add anything there just to weaken it away, and allowing
  imprecision here would break the [unicity of
  elaboration](elaboration-unicity.agda).

## Theorems

### Canonical Forms

Together, these files give the canonical forms lemma for the language.

- [canonical-boxed-forms.agda](canonical-boxed-forms.agda)
- [canonical-indeterminate-forms.agda](canonical-indeterminate-forms.agda)
- [canonical-value-forms.agda](canonical-value-forms.agda)

### Metatheory of Type Assignment

- [type-assignment-unicity.agda](type-assignment-unicity.agda) argues that
  the type assignment system assigns at most one type to any term.

### Metatheory of Elaboration

- [elaboration-generality.agda](elaboration-generality.agda) argues that
  the elaboration judgements respect the bidirectional typing system.
- [elaborability.agda](elaborability.agda) argues that any well typed
  external term can be elaborated to a internal term.
- [elaboration-unicity.agda](elaboration-unicity.agda) argues that
  elaboration produces at most one result.
- [typed-elaboration.agda](typed-elaboration.agda) argues that the
  elaboration respects the type assignment system.

### Type Safety

These files contain proofs of type safety for the internal language. Note
that we only give a dynamic semantics for the internal language, which is
related to the external language through elaboration.

- [progress.agda](progress.agda) argues that any well typed internal
  expression either steps, is a boxed value, or is indeterminate.
- [progress-checks.agda](progress-checks.agda) argues that the clauses in
  the conclusion of progress are pairwise disjoint---i.e. that no
  expression both steps and is a boxed value, and so on.
- [preservation.agda](preservation.agda) argues that stepping preserves
  type assignment.

  This is the main place that our assumption about α-normal terms appears:
  the statement of preservation makes explicit the standard on-paper
  convention that binders not be reused in its argument.

We also argue that our dynamics is a conservative extension in the sense
that if you use it to evaluate terms that happen to have no holes in them,
you get the standard type safety theorems you might expect for the
restricted fragment without holes.

- [complete-elaboration.agda](complete-elaboration.agda) argues that the
  elaboration of a complete external term produces a complete internal
  term.
- [complete-preservation.agda](complete-preservation.agda) argues that
  stepping a complete term produces a complete term that is assigned the
  same type, again with an explicit assumption about binder uniqueness.
- [complete-progress.agda](complete-progress.agda) argues that complete
  terms are either a value or step.

### Metatheory of Continuity

- [continuity.agda](continuity.agda) includes a sketch of a proof of
  continuity. This is built on postulates of a result from our POPL17 work
  and a few properties that would need to be proven about the expression
  forms from that work and the α-normal requirement we have in this work.

## Lemmas and Smaller Claims


These files each establish smaller claims that are either not mentioned in
the paper or mentioned only in passing. In terms of complexity and
importance, they're somewhere between a lemma and a theorem.

- [binders-disjoint-checks.agda](binders-disjoint-checks.agda) contains
  some proofs that demonstrate that `binders-disjoint` acts as
  expected. That judgement is defined inductively only on its left
  argument; since Agda datatypes do not define functions, explicit lemmas
  are needed to get the expected reduction behaivour in the right argument.
- [cast-inert.agda](cast-inert.agda) gives a judgemental removal of
  identity casts and argues that doing so does not change the type of the
  expression. It would also be possible to argue that removing the identity
  casts produces a term that evaluates in the same way---but identity cast
  removal is a syntactic operation that goes under binders while our
  evaluation semantics does not. To establish that result, we'd need to
  also give an equational theory of evaluation compatible with the given
  one.
- [disjointness.agda](disjointness.agda) characterizes the output hole
  contexts produced in elaboration, including disjointness guarantees
  needed in the proofs of [Elaborability](elaborability.agda) and
  [Elaboration Generality](elaboration-generality.agda).
- [dom-eq.agda](dom-eq.agda) defines when two contexts have the same
  domain, regardless of the range type or contents, and some operations
  that preserve that property. This is used in the proofs in
  [disjointness.agda](disjointness.agda).
- [finality.agda](finality.agda) argues that a final expression doesn't
  step, and only multi-steps to itself. More properties of this nature are
  proven in [progress-checks.agda](progress-checks.agda) but not called out
  explicitly in the paper.
- [focus-formation.agda](focus-formation.agda) argues that every `ε` is an
  evaluation context. As noted in [core.agda](core.agda), because we elide
  the boxed-in-red finality premises from the stepping rules, every `ε` is
  trivially an evaluation context, so this proof is extremely immediate; it
  would be slightly more involved if those premises were in place.
- [ground-decidable.agda](ground-decidable.agda) argues that every type is
  either ground or not.
- [grounding.agda](grounding.agda) argues the grounding property.
- [holes-disjoint-checks.agda](holes-disjoint-checks.agda) contains some
  checks on and lemmas for using the `holes-disjoint` judgement. Like
  `binders-disjoint`, `holes-disjoint` is defined inductively on only its
  left argument, so there's similar overhead.
- [htype-decidable.agda](htype-decidable.agda) argues that every pair of
  types are either equal or not.
- [synth-unicity.agda](synth-unicity.agda) argues that the synthesis
  judgement produces at most one type for a term.

These files contain technical lemmas for the corresponding judgement or
theorem. They are generally not surprising once stated, although it's
perhaps not immediate why they're needed, and they tend to obfuscate the
actual proof text. They are corralled into their own modules in an effort
to aid readability.

- [lemmas-complete.agda](lemmas-complete.agda)
- [lemmas-consistency.agda](lemmas-consistency.agda)
- [lemmas-disjointness.agda](lemmas-disjointness.agda)
- [lemmas-freshness.agda](lemmas-freshness.agda)
- [lemmas-gcomplete.agda](lemmas-gcomplete.agda)
- [lemmas-ground.agda](lemmas-ground.agda)
- [lemmas-matching.agda](lemmas-matching.agda)
- [lemmas-progress-checks.agda](lemmas-progress-checks.agda)
- [lemmas-subst-ta.agda](lemmas-subst-ta.agda)
