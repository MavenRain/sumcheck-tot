"""Check proofs and rejection controls using an existing tot executable."""
from pathlib import Path
import hashlib
import os
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]
DEFAULT_TOT = ROOT.parent / "tot" / "_build" / "default" / "bin" / "tot.exe"
TOT = Path(os.environ.get("TOT", DEFAULT_TOT))
BASE = "\n".join((ROOT / "src" / name).read_text() for name in
                 ("Foundation.tot", "Completeness.tot"))
EXAMPLE = """
reducible def rec plusN : Nat -> Nat -> Nat := fun a b => match a with
| zero => b | succ k => succ (plusN k b) end
reducible def oneN : Nat := succ zero
reducible def twoN : Nat := succ oneN
reducible def fourN : Nat := succ (succ twoN)
reducible def rec sumInputs : List Nat -> Nat := fun xs => match xs with
| nil => zero | cons x rest => plusN x (sumInputs rest) end
reducible def challengesN : List Nat := cons Nat twoN (cons Nat oneN (nil Nat))
reducible def honestN : ScTrace Nat :=
  scHonestTrace Nat plusN zero oneN challengesN sumInputs
"""
# A case is (name, source appended to BASE, expected diagnostic).
# None: the checker must accept. A string: the checker must exit with
# status 1 and print that string in its diagnostic.
CASES = [
    ("generic-completeness", "", None),
    ("two-variable-sum", EXAMPLE + """
def sumIsFour : Eq Nat (scSum Nat plusN zero oneN twoN sumInputs) fourN :=
  refl Nat fourN
def concreteAccepts : scAccept Nat plusN zero oneN honestN sumInputs fourN :=
  scHonestCompleteness Nat plusN zero oneN challengesN sumInputs
""", None),
    ("wrong-initial-claim", EXAMPLE + """
def wrongClaim : scAccept Nat plusN zero oneN honestN sumInputs zero :=
  scHonestCompleteness Nat plusN zero oneN challengesN sumInputs
""", "mismatch"),
    ("wrong-round-sum", EXAMPLE + """
def badRoundSum : scAccept Nat plusN zero oneN
    (scStep Nat (fun r => oneN) zero (scDone Nat))
    (fun xs => oneN) zero := pair _ _ (refl Nat zero) (refl Nat oneN)
""", "mismatch"),
    ("wrong-terminal-evaluation", EXAMPLE + """
def wrongTerminal : scAccept Nat plusN zero oneN (scDone Nat)
    (fun xs => oneN) zero := refl Nat zero
""", "mismatch"),
    ("consistent-message-fails-final-check", EXAMPLE + """
def forged : scAccept Nat plusN zero oneN
    (scStep Nat (fun r => zero) zero (scDone Nat))
    (fun xs => oneN) zero := pair _ _ (refl Nat zero) (refl Nat zero)
""", "mismatch"),
    ("axiom-rejected", "axiom fake : Eq Nat zero (succ zero)\n", "axiom"),
]

def run_case(directory, name, extra):
    path = Path(directory) / f"{name}.tot"
    path.write_text(BASE + "\n" + extra)
    return subprocess.run(
        [str(TOT), "check", "--no-prelude", "--no-axioms", str(path)],
        text=True, capture_output=True, timeout=30)

def accepted(result, expected):
    if expected is None:
        return result.returncode == 0
    diagnostic = (result.stdout + result.stderr).lower()
    return result.returncode == 1 and expected in diagnostic

def main():
    if not TOT.is_file():
        raise SystemExit(f"checker not found: {TOT}\n"
                         "Set TOT=/absolute/path/to/tot.exe")
    print(f"checker: {TOT}")
    print(f"checker sha256: {hashlib.sha256(TOT.read_bytes()).hexdigest()}")
    with tempfile.TemporaryDirectory(prefix="sumcheck-tot-") as directory:
        for name, extra, expected in CASES:
            result = run_case(directory, name, extra)
            if not accepted(result, expected):
                raise SystemExit(f"FAIL {name}: exit {result.returncode}\n"
                                 f"{result.stdout}\n{result.stderr}")
            print(f"PASS {name}")
    print(f"PASS {len(CASES)} of {len(CASES)} cases")

if __name__ == "__main__":
    main()
