"""Check that enumeration and counting proofs catch deliberate source mutations."""
import tempfile

import check


# Replacements apply to the in-memory concatenation, never to source files.
# Challenge mutations preserve enumeration cardinality but corrupt word contents.
# Trivialized statements survive every concrete instance; the abstract-argument
# vector checks are what reject them.
MUTATIONS = [
    ("round-trip-trivialized", """def rec scListVectorRoundTrip : (0 A : Type 0) -> (xs : List A) ->
    Eq (List A) (scVectorList A (scLength A xs) (scListVector A xs)) xs :=
  fun A xs => match xs as ys return
      Eq (List A) (scVectorList A (scLength A ys) (scListVector A ys)) ys with
  | nil => refl (List A) (nil A)
  | cons x rest => scCong (List A) (List A) (fun tail => cons A x tail)
      (scVectorList A (scLength A rest) (scListVector A rest)) rest
      (scListVectorRoundTrip A rest)
  end

""",
     """def scListVectorRoundTrip : (0 A : Type 0) -> (xs : List A) ->
    Eq (List A) xs xs :=
  fun A xs => refl (List A) xs

""", 1),
    ("injectivity-conclusion-trivialized", """def rec scVectorListInjective : (0 A : Type 0) -> (n : Nat) ->
    (v : ScVector A n) -> (w : ScVector A n) ->
    Eq (List A) (scVectorList A n v) (scVectorList A n w) -> Eq (ScVector A n) v w :=
  fun A n => match n as k return (v : ScVector A k) -> (w : ScVector A k) ->
      Eq (List A) (scVectorList A k v) (scVectorList A k w) -> Eq (ScVector A k) v w with
  | zero => fun v w => match v as a return
      Eq (List A) (scVectorList A zero a) (scVectorList A zero w) -> Eq ScUnit a w with
    | scUnit => match w as b return
        Eq (List A) (nil A) (scVectorList A zero b) -> Eq ScUnit scUnit b with
      | scUnit => fun equal => refl ScUnit scUnit
      end
    end
  | succ k => fun v w => match v as a return
      Eq (List A) (scVectorList A (succ k) a) (scVectorList A (succ k) w) ->
        Eq (ScVector A (succ k)) a w with
    | pair x xs => match w as b return
        Eq (List A) (cons A x (scVectorList A k xs)) (scVectorList A (succ k) b) ->
          Eq (ScVector A (succ k)) (pair A (ScVector A k) x xs) b with
      | pair y ys => fun equal => scPairCong A (ScVector A k) x y xs ys
          (scCong (List A) A (scHeadOr A x)
            (cons A x (scVectorList A k xs)) (cons A y (scVectorList A k ys)) equal)
          (scVectorListInjective A k xs ys
            (scCong (List A) (List A) (scTail A)
              (cons A x (scVectorList A k xs)) (cons A y (scVectorList A k ys)) equal))
      end
    end
  end

""",
     """def scVectorListInjective : (0 A : Type 0) -> (n : Nat) ->
    (v : ScVector A n) -> (w : ScVector A n) ->
    Eq (List A) (scVectorList A n v) (scVectorList A n w) -> Eq (ScVector A n) v v :=
  fun A n v w equal => refl (ScVector A n) v

""", 1),
    ("word-member-at-own-length", """    scMember (List A) (scVectorList A n v) (scWords A (scElements A finite) n) :=
  fun A finite n v => scTransport Nat (scLength A (scVectorList A n v)) n
    (fun k => scMember (List A) (scVectorList A n v) (scWords A (scElements A finite) k))
    (scVectorLength A n v) (scFiniteWordsComplete A finite (scVectorList A n v))

""",
     """    scMember (List A) (scVectorList A n v)
      (scWords A (scElements A finite) (scLength A (scVectorList A n v))) :=
  fun A finite n v => scFiniteWordsComplete A finite (scVectorList A n v)

""", 1),
    ("vector-zero-carrier-empty", "| zero => ScUnit\n  | succ k => Pair A (ScVector A k)",
     "| zero => ScEmpty\n  | succ k => Pair A (ScVector A k)", 1),
    ("vector-successor-drops-coordinate", "| succ k => Pair A (ScVector A k)",
     "| succ k => ScVector A k", 1),
    ("vector-list-drops-coordinate", "cons A x (scVectorList A k rest)",
     "scVectorList A k rest", 1),
    ("vector-list-reverses-order", "cons A x (scVectorList A k rest)",
     "scAppend A (scVectorList A k rest) (cons A x (nil A))", 1),
    ("vector-package-opaque", "reducible def rec scVectorFinite :",
     "def rec scVectorFinite :", 1),
    ("vector-injectivity-loses-input",
     "(scVectorList A k v) (scVectorList A k w) -> Eq (ScVector A k) v w with",
     "(scVectorList A k v) (scVectorList A k v) -> Eq (ScVector A k) v w with", 1),
    ("product-package-opaque", "reducible def scProductFinite :",
     "def scProductFinite :", 1),
    ("pair-decision-opaque", "reducible def scPairDecEq :",
     "def scPairDecEq :", 1),
    ("pair-decision-ignores-first", "match decideA x y with",
     "match decideA x x with", 1),
    ("pair-decision-ignores-second", "match decideB u v with",
     "match decideB u u with", 1),
    ("pair-congruence-drops-second-equality", "Eq A x y -> Eq B u v ->",
     "Eq A x y -> Eq B u u ->", 1),
    ("multiplication-base", "| zero => zero | succ k => scAdd m (scMul k m) end",
     "| zero => m | succ k => scAdd m (scMul k m) end", 1),
    ("power-base", "| zero => succ zero | succ k => scMul base (scPow base k) end",
     "| zero => zero | succ k => scMul base (scPow base k) end", 1),
    ("append-drops-left", "cons A x (scAppend A rest ys)",
     "scAppend A rest ys", 1),
    ("zero-round-has-no-word", "cons (List A) (nil A) (nil (List A))",
     "nil (List A)", 1),
    ("words-omit-challenge", "fun word => cons A x word", "fun word => word", 6),
    ("words-double-challenge", "fun word => cons A x word",
     "fun word => cons A x (cons A x word)", 6),
    ("all-drops-head-evidence", "Pair (P x) (scAll A P rest)",
     "Pair ScUnit (scAll A P rest)", 1),
    ("all-drops-tail-evidence", "Pair (P x) (scAll A P rest)",
     "Pair (P x) ScUnit", 1),
    ("unique-drops-head-obligation",
     "Pair (scMember A x rest -> ScEmpty) (scNoDup A rest)",
     "Pair ScUnit (scNoDup A rest)", 1),
    ("unique-drops-tail-obligation",
     "Pair (scMember A x rest -> ScEmpty) (scNoDup A rest)",
     "Pair (scMember A x rest -> ScEmpty) ScUnit", 1),
    ("map-injectivity-weakened", "Eq B (f x) (f y) -> Eq A x y",
     "Eq B (f x) (f y) -> Eq A x x", 1),
    ("block-separation-weakened",
     "scMember B z (block x) -> scMember B z (block y) -> Eq A x y",
     "scMember B z (block x) -> scMember B z (block y) -> Eq A x x", 1),
]

# Removing a refutation function first fails when an existing proof applies it.
MUTATION_DIAGNOSTICS = {"unique-drops-head-obligation": "not a function type: scunit"}


def main():
    check.main()
    original = check.BASE
    try:
        with tempfile.TemporaryDirectory(prefix="sumcheck-mutants-") as directory:
            for name, before, after, occurrences in MUTATIONS:
                if original.count(before) != occurrences:
                    raise SystemExit(f"stale mutation: {name}")
                check.BASE = original.replace(before, after)
                for case, extra, expected in check.CASES:
                    result = check.run_case(directory, case, extra)
                    if not check.accepted(result, expected):
                        diagnostic = (result.stdout + result.stderr).lower()
                        wanted = MUTATION_DIAGNOSTICS.get(name, "mismatch")
                        if expected is not None or result.returncode != 1 or wanted not in diagnostic:
                            raise SystemExit(f"unexpected mutant failure {name}/{case}:\n"
                                             f"{result.stdout}\n{result.stderr}")
                        print(f"CAUGHT {name}: {case}")
                        break
                else:
                    raise SystemExit(f"SURVIVED {name}")
    finally:
        check.BASE = original
    print(f"PASS {len(MUTATIONS)} of {len(MUTATIONS)} mutations caught")


if __name__ == "__main__":
    main()
