# Sumcheck in tot

A standalone formalization of the algebraic core of the LFKN sumcheck
protocol. The first milestone is checked: honest transcripts satisfy every
round consistency equation and the final evaluation equation, for every
finite challenge sequence.
The finite-carrier foundation is also checked: enumerations carry
exhaustiveness and uniqueness proofs, and decidable predicate counts are
bounded by the carrier's cardinality.
List products and challenge-word enumerations now have checked size formulas
`|xs| * |ys|` and `|alphabet|^n`, with a predicate-count bound for words.

## Check

```sh
python3 test/check.py
```

Run from this directory. The runner uses the checker named by `TOT` when
that variable is set. Otherwise it uses the sibling checkout at
`../tot/_build/default/bin/tot.exe` and stops with a message when that
file is absent. The runner concatenates the foundation and proof sources
in temporary files and checks with `--no-prelude --no-axioms`. It prints the
checker SHA-256 so validation identifies the binary actually used. No
compiler rebuild is required when a built checker exists.

## What is proved

- `scOneRoundCompleteness`: the two endpoint evaluations of the honest
  marginal sum to the current hypercube sum.
- `scHonestCompleteness`: for every carrier `F`, addition operation,
  distinguished endpoints, challenge list, and function `g : List F -> F`,
  the honest transcript satisfies `scAccept` for the true initial sum.
  The proof is structural induction on the challenge list.
- `ScFinite`: a carrier packaged with an exhaustive, duplicate-free list
  and decidable equality. `scEnumerates` and `scEnumerationUnique` expose
  its evidence; `scDecEq` exposes its equality decision procedure.
- `scBitFinite`: a concrete two-element carrier with checked enumeration
  evidence. `scDuplicateImpossible` refutes adjacent duplicate entries in
  any enumeration satisfying `scNoDup`.
- `scCountBound` and `scFiniteCountBound`: counting a decidable predicate
  never exceeds the list length or finite-carrier cardinality, respectively.
  Counts use proof-carrying decisions. The bound is proved by structural
  induction, using the inductive natural order `ScLe`.
- `scAddZeroRight`, `scAddAssoc`, `scLeRefl`, and `scLeWeaken`: basic natural
  arithmetic and order lemmas for subsequent counting arguments.
- `scAppendLength`, `scMapLength`, and `scExpandLength`: append adds lengths,
  map preserves length, and concatenating equal-sized blocks multiplies length.
- `scProductLength`: the Cartesian-product list has length `|xs| * |ys|`.
- `scWordsLength`: recursively prepending alphabet entries produces a list
  of size `|alphabet|^n`. At zero rounds it contains the empty word, even
  for an empty alphabet, so the counting convention is `0^0 = 1`.
- `scWordCountBound`: any decidable predicate holds at most `|alphabet|^n`
  times in that list. With `scElements F finite`, the bound is `|F|^n`.

`scAccept` is defined independently for arbitrary transcripts. A round
requires `message(lo) + message(hi) = claim`, then checks the remaining
transcript with claim `message(r)` and the restricted function `g(r :: xs)`.
The terminal check requires `claim = g([])` after all restrictions.
Thus the terminal value is the original function evaluated at the ordered
challenge sequence. The number of rounds in the completeness theorem is
the length of that sequence. For `n = 0`, acceptance is just the terminal
equality.

No algebraic laws are needed for these equations: recursive hypercube
summation fixes the parenthesization and endpoint order. The usual field
interpretation specializes the endpoints to zero and one. Lists represent
assignments; for an n-round instance only length-n assignments are queried.

## Scope and trust

This is **algebraic consistency completeness**, not yet full polynomial
sumcheck completeness or soundness. Round messages are functions rather
than bounded-degree polynomials. There is currently no degree check,
adaptive strategy definition, probability model, or soundness theorem.
Arbitrary transcripts also do not yet carry an externally enforced round
count; the honest construction uses exactly the supplied challenges.

The standalone foundation declares `Nat`, `List`, `Pair`, and indexed
propositional `Eq`. The finite and counting modules add empty and unit types,
disjunction, decisions, finite-carrier evidence, a two-element carrier, and
natural order. There are no postulates, admitted proofs, or placeholder
theorems. Checking trusts tot's current elaborator and kernel; this project
does not establish their metatheoretic soundness. The default prelude is
excluded, including its unrelated IO-law axioms.

## Validation

On 2026-09-06, all seventeen checks passed with checker SHA-256
`30c4524d57f6723e39ba117097222f3ab8ef3e899a8a4af8b7e60c68337842bf`, built
from tot commit `8cf0b8b` with a clean tree. Build that commit to reproduce
the reference checker. To select an existing build explicitly, run
`TOT=/absolute/path/to/tot.exe python3 test/check.py`.

The seventeen checks:

- All generic proofs check without a prelude or axioms.
- Product and word sizes and exact contents check, including empty factors,
  zero rounds over an empty alphabet, positive rounds over an empty alphabet,
  and the word predicate-count bound.
- An incorrect product size is rejected.
- An incorrect two-round word count is rejected.
- A zero count for zero-round words over an empty alphabet is rejected.
- Finite-carrier and counting proofs check, including empty-carrier
  cardinality, two-element cardinality, empty-list counts, all/none counts,
  each singleton predicate, and a concrete count bound.
- A membership proof for an omitted element is rejected.
- A forged uniqueness proof for duplicate entries is rejected.
- A false equality decision is rejected.
- An incorrect predicate count is rejected.
- A false natural-order bound is rejected.
- For `g(x,y) = x+y` over naturals, the Boolean-cube sum is four and the
  honest transcript for challenges `[2,1]` is accepted.
- The completeness proof term is rejected at initial claim zero. The type
  mismatch is four against zero.
- A one-round message with round sum two is rejected against claim zero.
  Its terminal evaluation is consistent, so this control exercises the
  round-sum equation alone. Without it, a trivial round-sum conjunct in
  `scAccept` passes every other check.
- An incorrect terminal evaluation is rejected. The type mismatch is zero
  against one.
- A forged zero message with a consistent zero round sum fails the final
  check against the constant-one function.
- A user axiom is rejected.

The negative controls show that specific proof terms are rejected. They do
not show that the false statements are unprovable.

Run `python3 test/mutations.py` with the same `TOT` selection to rerun the
suite and check six deliberate mutations in memory. All six were caught:
incorrect multiplication and power base cases, dropped append entries,
missing zero-round words, omitted challenges, and doubled challenges.
The last two preserve enumeration cardinality and are caught by the exact
word-content regression rather than the generic size proofs.

Naturals in the concrete regression example test the algebraic equations;
they are not presented as a finite field.
The two-element carrier likewise has no field structure yet. Empty carriers
are permitted by `ScFinite`; a uniform probability interpretation will need
nonemptiness. Product and word size formulas count list entries with
multiplicity. Packaging these lists as exhaustive, duplicate-free finite
carriers, proving every generated word has the requested length, and
enumeration independence of counts remain future work. The word count bound
is a bound on arbitrary predicates, not a sumcheck soundness theorem.

## Next milestones

1. Extend product/word enumerations with exhaustiveness, uniqueness, and
   word-length proofs; establish enumeration independence and the remaining
   arithmetic needed for soundness.
2. Define polynomial messages, evaluation, restriction, degree bounds, and
   field operations with explicit laws. Prove honest marginals preserve
   the required degree bound, then extend acceptance and completeness.
3. Prove the univariate root bound and the agreement bound for distinct
   bounded-degree polynomials.
4. Define adaptive strategies whose messages depend only on past
   challenges, enforce the input round count, and count accepting challenge
   vectors for false claims by induction. Target
   `|F| * acceptingCount <= n * d * |F|^n` for individual degree at most d.
5. Interpret that count under independent uniform challenges to obtain
   soundness error at most `n*d/|F|`. If intermediate results take a root
   bound as a hypothesis, label them conditional until it is discharged.

Sources: `src/Foundation.tot`, `src/Completeness.tot`, `src/Finite.tot`,
`src/Counting.tot`, `src/Products.tot`.

## License

Dual MIT OR Apache-2.0. Both texts ship with the repository: MIT in
`LICENSE-MIT` and Apache-2.0 in `LICENSE-APACHE`. You choose either licence.
