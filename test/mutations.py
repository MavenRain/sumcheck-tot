"""Check that product and word regressions catch deliberate source mutations."""
import tempfile

import check


# Replacements apply to the in-memory concatenation, never to source files.
# The last two preserve enumeration cardinality but corrupt word contents.
MUTATIONS = [
    ("multiplication-base", "| zero => zero | succ k => scAdd m (scMul k m) end",
     "| zero => m | succ k => scAdd m (scMul k m) end", 1),
    ("power-base", "| zero => succ zero | succ k => scMul base (scPow base k) end",
     "| zero => zero | succ k => scMul base (scPow base k) end", 1),
    ("append-drops-left", "cons A x (scAppend A rest ys)",
     "scAppend A rest ys", 1),
    ("zero-round-has-no-word", "cons (List A) (nil A) (nil (List A))",
     "nil (List A)", 1),
    ("words-omit-challenge", "fun word => cons A x word", "fun word => word", 4),
    ("words-double-challenge", "fun word => cons A x word",
     "fun word => cons A x (cons A x word)", 4),
]


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
                        if expected is not None or result.returncode != 1 or "mismatch" not in diagnostic:
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
