# Sumcheck in tot

A standalone formalization of the algebraic core of the LFKN sumcheck
protocol. The first milestone is checked: honest transcripts satisfy every
round consistency equation and the final evaluation equation, for every
finite challenge sequence.

## Check

```sh
python3 test/check.py
```

Run from this directory. The runner uses the checker named by `TOT` when
that variable is set. Otherwise it uses the sibling checkout at
`../tot/_build/default/bin/tot.exe` and stops with a message when that
file is absent. The runner concatenates the foundation and proof source
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

The standalone foundation declares only `Nat`, `List`, `Pair`, and indexed
propositional `Eq`. There are no postulates, admitted proofs, or placeholder
theorems. Checking trusts tot's current elaborator and kernel; this project
does not establish their metatheoretic soundness. The default prelude is
excluded, including its unrelated IO-law axioms.

## Validation

On 2026-09-06, all seven checks passed with checker SHA-256
`30c4524d57f6723e39ba117097222f3ab8ef3e899a8a4af8b7e60c68337842bf`, built
from tot commit `8cf0b8b` with a clean tree. Build that commit to reproduce
the reference checker. The checks also pass on current tot builds from
uncommitted working trees. Those hashes are not recorded here, because no
commit reproduces them.

The seven checks:

- Generic completeness checks without a prelude or axioms.
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

Naturals in the concrete regression example test the algebraic equations;
they are not presented as a finite field.

## Next milestones

1. Define finite carriers with exhaustive, duplicate-free enumeration,
   decidable equality, arithmetic and order lemmas for finite counts.
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

Sources: `src/Foundation.tot`, `src/Completeness.tot`.

## License

Dual MIT OR Apache-2.0. Both texts ship with the repository: MIT in
`LICENSE-MIT` and Apache-2.0 in `LICENSE-APACHE`. You choose either licence.
