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
Every generated word has the requested length, and every word whose entries
belong to the alphabet occurs in the enumeration at its length.
Products preserve membership, and products and challenge-word enumerations
are duplicate-free when their input enumerations are duplicate-free.
Finite products now package this evidence together with decidable pair equality
and a checked product cardinality.
Fixed-length vectors now form finite carriers with decidable equality and
cardinality `|F|^n`. Their list conversion preserves length and is injective;
every list converts to a vector at its own length and back unchanged.
Converting the full vector enumeration gives exactly the challenge-word list,
in the same order. Predicate counts agree under this conversion.

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
- `scAllMember`, `scAllAppend`, `scAllMap`, and `scAllExpand`: pointwise
  evidence can be extracted by membership and preserved through list operations.
- `scWordsAllLengths` and `scWordLength`: every member of `scWords A alphabet n`
  has length `n`, including when the alphabet is empty or contains duplicates.
- `scWordsComplete`: every word with alphabet-membership evidence for each
  entry occurs in the enumeration at its own length. `scWordsCompleteAt`
  accepts an explicit round count with a proof that it equals the word length.
- `scFiniteWordsComplete`: every word over a packaged finite carrier occurs
  in the challenge enumeration at its length.
- `scMemberAppendSplit`, `scMemberMapElim`, and `scMemberExpandElim`: membership
  in a constructed enumeration can be traced back to its source entries.
- `scNoDupAppend`, `scNoDupMap`, and `scNoDupExpand`: uniqueness is preserved by
  disjoint append, injective map, and expansion into unique blocks whose
  overlapping entries imply equal source labels. `scGridUnique` specializes
  these lemmas to encodings that preserve both coordinates.
- `scProductComplete` and `scProductUnique`: every pair of members occurs in
  the product, and unique input lists produce a unique product enumeration.
- `scWordsUnique` and `scFiniteWordsUnique`: every fixed-length challenge-word
  enumeration over a duplicate-free alphabet is duplicate-free. The proof
  includes zero rounds and empty alphabets, without requiring nonemptiness
  or decidable equality.

- `scPairCong` and `scPairDecEq`: coordinate equalities construct pair equality,
  and coordinate decisions give a decision for pair equality. Either unequal
  coordinate supplies a refutation through the corresponding projection.
- `scProductFinite`: two finite carriers give a finite pair carrier with complete,
  unique enumeration and decidable equality, including empty factors.
- `scProductCardinality` and `scProductCountBound`: the packaged product has
  cardinality `|A| * |B|`, which bounds every decidable predicate count.
- `ScVector A n` represents exactly `n` entries as iterated pairs ending in
  `ScUnit`. `scVectorFinite` packages its complete, unique enumeration and
  decidable equality using finite products. No equality proof fields or
  proof-irrelevance principle are needed.
- `scVectorCardinality` and `scVectorCountBound`: the vector carrier has
  cardinality `|A|^n`, which bounds every decidable predicate count. Zero
  rounds give one vector even over an empty carrier; positive rounds over
  an empty carrier give none.
- `scVectorList`, `scVectorLength`, and `scVectorListInjective`: vectors
  convert to length-`n` lists, and equal converted lists imply equal vectors.
  `scListVector` converts each list to a vector indexed by its length;
  `scListVectorRoundTrip` proves converting it back yields the original list.
- `scVectorWordMember`: each converted vector belongs to the existing
  `scWords` enumeration at the vector's specified round count.

- `scMapAppend`, `scMapCompose`, and `scMapExpand`: mapping distributes over
  append, composes, and preserves expansion under pointwise block equality.
  These proofs require no function extensionality.
- `scVectorEnumeration`: mapping `scVectorList` over the packaged vector
  enumeration equals `scWords` at the specified round count, preserving
  order and multiplicity, including zero rounds and empty carriers.
- `scCountMap`: counting a predicate after a map equals counting its pullback
  before the map, using the same decision procedure.
- `scVectorWordCount`: finite vector counts of a list predicate pulled back
  through `scVectorList` equal its challenge-word counts.

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

On 2026-09-06, all thirty-nine checks passed with checker SHA-256
`30c4524d57f6723e39ba117097222f3ab8ef3e899a8a4af8b7e60c68337842bf`, built
from tot commit `8cf0b8b` with a clean tree. Build that commit to reproduce
the reference checker. To select an existing build explicitly, run
`TOT=/absolute/path/to/tot.exe python3 test/check.py`.

The thirty-nine checks:

- All generic proofs check without a prelude or axioms.
- Enumeration conversion and count equality check at abstract arguments,
  alongside the three generic map lemmas and count-map lemma. Concrete
  instances cover two-bit vectors, empty carriers at zero and two rounds,
  and all/none/head-high predicates.
- Count equality used with different predicates on its two sides is rejected.
- Enumeration equality used at the wrong round count is rejected.
- Finite vectors check cardinality, membership, uniqueness, exact list
  conversions, round trips, injectivity, length, word membership, and
  all/none/singleton counts with a count bound. Empty carriers at zero and
  two rounds and all sixteen equality decisions on two-bit vectors check.
  Injectivity, the round trip, and word membership also check at abstract
  arguments.
- A vector missing a coordinate is rejected.
- A vector cardinality theorem used with an incorrect size is rejected.
- Vector word-membership evidence used at the wrong round count is rejected.
- Vector injectivity supplied with forged list equality is rejected.
- Finite product packaging checks membership, uniqueness, cardinality, empty
  factors, all/none/singleton predicate counts, and a product count bound.
  All sixteen equality decisions on pairs of bits compute the expected tally.
- An incorrect packaged product cardinality is rejected.
- Forged pair equality ignoring the second coordinate is rejected.
- Forged pair equality ignoring the first coordinate is rejected.
- An incorrect packaged product predicate count is rejected.
- Product membership and uniqueness, word uniqueness, empty product factors,
  empty alphabets at zero and positive rounds, and extraction of a usable
  nonmembership refutation from word uniqueness check.
- Forged uniqueness evidence omitting the head's nonmembership is rejected.
- Forged uniqueness evidence omitting the tail's uniqueness is rejected.
- A constant map supplied with a forged injectivity proof is rejected.
- Overlapping lists supplied with a forged disjointness proof are rejected.
- Word membership and length evidence checks for a two-round word, the empty
  word over an empty alphabet, and an alphabet with repeated entries.
- Word membership evidence supplied at the wrong round count is rejected.
- Forged pointwise evidence omitting an entry's alphabet membership is rejected.
- Forged pointwise evidence omitting the tail's obligations is rejected.
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
suite and check twenty-nine deliberate mutations in memory. All twenty-nine were caught.
Three new mutations consistently trivialize the enumeration, count-map, and
vector-word-count statements. Their consumers catch the first two; the
abstract count-equality regression catches the third. The existing controls cover:
incorrect multiplication and power base cases, dropped append entries,
missing zero-round words, omitted challenges, doubled challenges, and dropped
head or tail obligations in pointwise evidence, dropped head or tail
uniqueness obligations, weakened map injectivity, and weakened block
separation, pair decisions ignoring either coordinate, and pair congruence
with a weakened second-coordinate equality. The added controls change the
zero-round vector carrier, drop a vector coordinate, drop or reverse converted
list entries, weaken the injectivity premise, remove reducibility from
the vector package, product package, or pair decision procedure, and
trivialize the round trip, injectivity, and word-membership statements. All
are caught by generic proofs except the opaque pair decision, which fails the
concrete vector counting checks, and the three trivialized statements, which
pass every concrete instance and fail only the abstract-argument vector
checks. Omitting or doubling challenges preserves enumeration cardinality,
but now fails the word-length proof; exact word-content regressions also remain.

Naturals in the concrete regression example test the algebraic equations;
they are not presented as a finite field.
The two-element carrier likewise has no field structure yet. Empty carriers
are permitted by `ScFinite`; a uniform probability interpretation will need
nonemptiness. Product and word size formulas count list entries with
multiplicity for arbitrary input lists. For duplicate-free inputs, the
uniqueness theorems now justify interpreting the entries as distinct outcomes.
Fixed-length words are packaged through `ScVector`, rather than the type
of all lists. Vector predicate counts now equal the corresponding list-word counts for
predicates pulled back through the conversion. Independence from the choice
of finite enumeration remains future work.
The word count bound
is a bound on arbitrary predicates, not a sumcheck soundness theorem.

## Next milestones

1. Establish enumeration independence and prove the remaining arithmetic
   needed for soundness.
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
`src/Counting.tot`, `src/Products.tot`, `src/WordEnumeration.tot`,
`src/EnumerationUnique.tot`, `src/FiniteProducts.tot`, `src/FiniteVectors.tot`, `src/VectorEnumeration.tot`.

## License

Dual MIT OR Apache-2.0. Both texts ship with the repository: MIT in
`LICENSE-MIT` and Apache-2.0 in `LICENSE-APACHE`. You choose either licence.
