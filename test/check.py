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
                 ("Foundation.tot", "Completeness.tot", "Finite.tot", "Counting.tot",
                  "Products.tot", "WordEnumeration.tot", "EnumerationUnique.tot",
                  "FiniteProducts.tot", "FiniteVectors.tot", "VectorEnumeration.tot",
                  "CountingAlgebra.tot", "FiberCounting.tot", "Arithmetic.tot",
                  "Recurrence.tot", "Strategies.tot", "AcceptanceCounting.tot",
                  "EnumerationIndependent.tot", "RoundBounds.tot", "ConditionalSoundness.tot"))
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
PRODUCT_EXAMPLE = EXAMPLE + """
reducible def bitProduct : ScFinite (Pair ScBit ScBit) :=
  scProductFinite ScBit ScBit scBitFinite scBitFinite
reducible def emptyProductFactor : ScFinite ScEmpty :=
  scFinite ScEmpty (nil ScEmpty) (fun x => match x with end) scUnit
    (fun x y => match x with end)
reducible def targetPair : Pair ScBit ScBit := pair ScBit ScBit scHigh scLow
"""
PRODUCT_CHECKS = PRODUCT_EXAMPLE + """
def packagedCardinality : Eq Nat (scCardinality (Pair ScBit ScBit) bitProduct) fourN :=
  scProductCardinality ScBit ScBit scBitFinite scBitFinite
def packagedMember : scMember (Pair ScBit ScBit) targetPair
    (scElements (Pair ScBit ScBit) bitProduct) :=
  scEnumerates (Pair ScBit ScBit) bitProduct targetPair
def packagedUnique : scNoDup (Pair ScBit ScBit) (scElements (Pair ScBit ScBit) bitProduct) :=
  scEnumerationUnique (Pair ScBit ScBit) bitProduct
def leftEmptyCardinality : Eq Nat (scCardinality (Pair ScEmpty ScBit)
    (scProductFinite ScEmpty ScBit emptyProductFactor scBitFinite)) zero :=
  scProductCardinality ScEmpty ScBit emptyProductFactor scBitFinite
def rightEmptyCardinality : Eq Nat (scCardinality (Pair ScBit ScEmpty)
    (scProductFinite ScBit ScEmpty scBitFinite emptyProductFactor)) zero :=
  scProductCardinality ScBit ScEmpty scBitFinite emptyProductFactor
def singletonPairCount : Eq Nat (scFiniteCount (Pair ScBit ScBit)
    (fun p => Eq (Pair ScBit ScBit) p targetPair)
    (fun p => scDecEq (Pair ScBit ScBit) bitProduct p targetPair) bitProduct) oneN :=
  refl Nat oneN
def productAllCount : Eq Nat (scFiniteCount (Pair ScBit ScBit)
    (fun p => ScUnit) (fun p => scYes ScUnit scUnit) bitProduct) fourN := refl Nat fourN
def productNoneCount : Eq Nat (scFiniteCount (Pair ScBit ScBit)
    (fun p => ScEmpty) (fun p => scNo ScEmpty (fun h => h)) bitProduct) zero := refl Nat zero
def packagedCountBound : ScLe (scFiniteCount (Pair ScBit ScBit)
    (fun p => Eq (Pair ScBit ScBit) p targetPair)
    (fun p => scDecEq (Pair ScBit ScBit) bitProduct p targetPair) bitProduct) fourN :=
  scProductCountBound ScBit ScBit (fun p => Eq (Pair ScBit ScBit) p targetPair)
    (fun p => scDecEq (Pair ScBit ScBit) bitProduct p targetPair) scBitFinite scBitFinite
"""
# Exhaust every equality branch through the packaged decision procedure.
for i, (x, u) in enumerate((a, b) for a in ("scLow", "scHigh") for b in ("scLow", "scHigh")):
    for j, (y, v) in enumerate((a, b) for a in ("scLow", "scHigh") for b in ("scLow", "scHigh")):
        left, right = f"(pair ScBit ScBit {x} {u})", f"(pair ScBit ScBit {y} {v})"
        expected = "oneN" if i == j else "zero"
        PRODUCT_CHECKS += f"""
def pairDecision{i}{j} : Eq Nat
    (scTally (Eq (Pair ScBit ScBit) {left} {right})
      (scDecEq (Pair ScBit ScBit) bitProduct {left} {right}) zero) {expected} :=
  refl Nat {expected}
"""

# A case is (name, source appended to BASE, expected diagnostic).
# None: the checker must accept. A string: the checker must exit with
# status 1 and print that string in its diagnostic.
VECTOR_EXAMPLE = PRODUCT_EXAMPLE + """
reducible def vectorHL : ScVector ScBit twoN :=
  pair ScBit (ScVector ScBit oneN) scHigh (pair ScBit ScUnit scLow scUnit)
reducible def vectorWord : List ScBit := cons ScBit scHigh (cons ScBit scLow (nil ScBit))
reducible def bitVectors : ScFinite (ScVector ScBit twoN) := scVectorFinite ScBit scBitFinite twoN
"""
VECTOR_CHECKS = VECTOR_EXAMPLE + """
def vectorCardinality : Eq Nat (scCardinality (ScVector ScBit twoN) bitVectors) fourN :=
  scVectorCardinality ScBit scBitFinite twoN
def vectorMember : scMember (ScVector ScBit twoN) vectorHL
    (scElements (ScVector ScBit twoN) bitVectors) :=
  scEnumerates (ScVector ScBit twoN) bitVectors vectorHL
def vectorUnique : scNoDup (ScVector ScBit twoN) (scElements (ScVector ScBit twoN) bitVectors) :=
  scEnumerationUnique (ScVector ScBit twoN) bitVectors
def vectorToList : Eq (List ScBit) (scVectorList ScBit twoN vectorHL) vectorWord :=
  refl (List ScBit) vectorWord
def listToVector : Eq (ScVector ScBit twoN) (scListVector ScBit vectorWord) vectorHL :=
  refl (ScVector ScBit twoN) vectorHL
def listRoundTrip : Eq (List ScBit)
    (scVectorList ScBit twoN (scListVector ScBit vectorWord)) vectorWord :=
  scListVectorRoundTrip ScBit vectorWord
def vectorLength : Eq Nat (scLength ScBit (scVectorList ScBit twoN vectorHL)) twoN :=
  scVectorLength ScBit twoN vectorHL
def vectorInWords : scMember (List ScBit) vectorWord (scWords ScBit scBits twoN) :=
  scVectorWordMember ScBit scBitFinite twoN vectorHL
def vectorInjective : Eq (ScVector ScBit twoN) vectorHL (scListVector ScBit vectorWord) :=
  scVectorListInjective ScBit twoN vectorHL (scListVector ScBit vectorWord)
    (refl (List ScBit) vectorWord)
def emptyZeroCardinality : Eq Nat (scCardinality (ScVector ScEmpty zero)
    (scVectorFinite ScEmpty emptyProductFactor zero)) oneN :=
  scVectorCardinality ScEmpty emptyProductFactor zero
def emptyTwoCardinality : Eq Nat (scCardinality (ScVector ScEmpty twoN)
    (scVectorFinite ScEmpty emptyProductFactor twoN)) zero :=
  scVectorCardinality ScEmpty emptyProductFactor twoN
def emptyVectorMember : scMember ScUnit scUnit
    (scElements ScUnit (scVectorFinite ScEmpty emptyProductFactor zero)) :=
  scEnumerates ScUnit (scVectorFinite ScEmpty emptyProductFactor zero) scUnit
def emptyVectorWord : scMember (List ScEmpty) (nil ScEmpty) (scWords ScEmpty (nil ScEmpty) zero) :=
  scVectorWordMember ScEmpty emptyProductFactor zero scUnit
def emptyRoundTrip : Eq (List ScEmpty)
    (scVectorList ScEmpty zero (scListVector ScEmpty (nil ScEmpty))) (nil ScEmpty) :=
  scListVectorRoundTrip ScEmpty (nil ScEmpty)
def vectorAllCount : Eq Nat (scFiniteCount (ScVector ScBit twoN)
    (fun v => ScUnit) (fun v => scYes ScUnit scUnit) bitVectors) fourN := refl Nat fourN
def vectorNoneCount : Eq Nat (scFiniteCount (ScVector ScBit twoN)
    (fun v => ScEmpty) (fun v => scNo ScEmpty (fun h => h)) bitVectors) zero := refl Nat zero
def vectorSingletonCount : Eq Nat (scFiniteCount (ScVector ScBit twoN)
    (fun v => Eq (ScVector ScBit twoN) v vectorHL)
    (fun v => scDecEq (ScVector ScBit twoN) bitVectors v vectorHL) bitVectors) oneN := refl Nat oneN
def vectorBound : ScLe (scFiniteCount (ScVector ScBit twoN)
    (fun v => Eq (ScVector ScBit twoN) v vectorHL)
    (fun v => scDecEq (ScVector ScBit twoN) bitVectors v vectorHL) bitVectors) fourN :=
  scVectorCountBound ScBit scBitFinite twoN (fun v => Eq (ScVector ScBit twoN) v vectorHL)
    (fun v => scDecEq (ScVector ScBit twoN) bitVectors v vectorHL)
-- Abstract arguments pin statements that concrete instances normalize away.
def vectorInjectiveAt : (v : ScVector ScBit twoN) -> (w : ScVector ScBit twoN) ->
    Eq (List ScBit) (scVectorList ScBit twoN v) (scVectorList ScBit twoN w) ->
    Eq (ScVector ScBit twoN) v w :=
  fun v w equal => scVectorListInjective ScBit twoN v w equal
def roundTripAt : (xs : List ScBit) ->
    Eq (List ScBit) (scVectorList ScBit (scLength ScBit xs) (scListVector ScBit xs)) xs :=
  fun xs => scListVectorRoundTrip ScBit xs
def vectorWordAt : (n : Nat) -> (v : ScVector ScBit n) ->
    scMember (List ScBit) (scVectorList ScBit n v) (scWords ScBit scBits n) :=
  fun n v => scVectorWordMember ScBit scBitFinite n v
"""
BIT_VECTORS = tuple(
    f"(pair ScBit (ScVector ScBit oneN) {x} (pair ScBit ScUnit {y} scUnit))"
    for x in ("scLow", "scHigh") for y in ("scLow", "scHigh")
)
VECTOR_CHECKS += "\n".join(
    f"def vectorDecision{i}_{j} : Eq Nat (scTally (Eq (ScVector ScBit twoN) {v} {w}) "
    f"(scDecEq (ScVector ScBit twoN) bitVectors {v} {w}) zero) "
    f"{'oneN' if i == j else 'zero'} := refl Nat {'oneN' if i == j else 'zero'}"
    for i, v in enumerate(BIT_VECTORS) for j, w in enumerate(BIT_VECTORS)
)

COUNTING_ALGEBRA_CHECKS = """
def scCountMonoAt : (0 A : Type 0) -> (0 P : A -> Type 0) ->
    (0 Q : A -> Type 0) -> ((x : A) -> P x -> Q x) ->
    (dp : (x : A) -> ScDec (P x)) -> (dq : (x : A) -> ScDec (Q x)) ->
    (xs : List A) -> ScLe (scCount A P dp xs) (scCount A Q dq xs) :=
  fun A P Q implies dp dq xs => scCountMono A P Q implies dp dq xs

def scCountEquivalentAt : (0 A : Type 0) -> (0 P : A -> Type 0) ->
    (0 Q : A -> Type 0) -> ((x : A) -> P x -> Q x) ->
    ((x : A) -> Q x -> P x) -> (dp : (x : A) -> ScDec (P x)) ->
    (dq : (x : A) -> ScDec (Q x)) -> (xs : List A) ->
    Eq Nat (scCount A P dp xs) (scCount A Q dq xs) :=
  fun A P Q forward backward dp dq xs => scCountEquivalent A P Q forward backward dp dq xs

def scCountDecisionIndependentAt : (0 A : Type 0) -> (0 P : A -> Type 0) ->
    (dp : (x : A) -> ScDec (P x)) -> (dq : (x : A) -> ScDec (P x)) ->
    (xs : List A) -> Eq Nat (scCount A P dp xs) (scCount A P dq xs) :=
  fun A P dp dq xs => scCountDecisionIndependent A P dp dq xs

def scCountAppendAt : (0 A : Type 0) -> (0 P : A -> Type 0) ->
    (decide : (x : A) -> ScDec (P x)) -> (xs : List A) -> (ys : List A) ->
    Eq Nat (scCount A P decide (scAppend A xs ys))
      (scAdd (scCount A P decide xs) (scCount A P decide ys)) :=
  fun A P decide xs ys => scCountAppend A P decide xs ys

def scCountUnionBoundAt : (0 A : Type 0) -> (0 P : A -> Type 0) ->
    (0 Q : A -> Type 0) -> (dp : (x : A) -> ScDec (P x)) ->
    (dq : (x : A) -> ScDec (Q x)) -> (xs : List A) ->
    ScLe (scCount A (fun x => ScEither (P x) (Q x))
        (fun x => scEitherDec (P x) (Q x) (dp x) (dq x)) xs)
      (scAdd (scCount A P dp xs) (scCount A Q dq xs)) :=
  fun A P Q dp dq xs => scCountUnionBound A P Q dp dq xs
"""

COUNTING_ALGEBRA_EXAMPLES = EXAMPLE + """

def unionNeither : Eq Nat (scTally (ScEither ScEmpty ScEmpty)
    (scEitherDec ScEmpty ScEmpty (scNo ScEmpty (fun h => h))
      (scNo ScEmpty (fun h => h))) zero) zero := refl Nat zero
def unionLeft : Eq Nat (scTally (ScEither ScUnit ScEmpty)
    (scEitherDec ScUnit ScEmpty (scYes ScUnit scUnit)
      (scNo ScEmpty (fun h => h))) zero) oneN := refl Nat oneN
def unionRight : Eq Nat (scTally (ScEither ScEmpty ScUnit)
    (scEitherDec ScEmpty ScUnit (scNo ScEmpty (fun h => h))
      (scYes ScUnit scUnit)) zero) oneN := refl Nat oneN
def unionBoth : Eq Nat (scTally (ScEither ScUnit ScUnit)
    (scEitherDec ScUnit ScUnit (scYes ScUnit scUnit)
      (scYes ScUnit scUnit)) zero) oneN := refl Nat oneN
reducible def repeatedBits : List ScBit := cons ScBit scHigh scBits
def appendRepeatedCount : Eq Nat
    (scCount ScBit (fun x => ScUnit) (fun x => scYes ScUnit scUnit)
      (scAppend ScBit repeatedBits scBits)) (scAdd (succ twoN) twoN) :=
  scCountAppend ScBit (fun x => ScUnit) (fun x => scYes ScUnit scUnit)
    repeatedBits scBits
def overlappingUnionBound : ScLe
    (scCount ScBit (fun x => ScEither ScUnit ScUnit)
      (fun x => scEitherDec ScUnit ScUnit (scYes ScUnit scUnit)
        (scYes ScUnit scUnit)) scBits) fourN :=
  scCountUnionBound ScBit (fun x => ScUnit) (fun x => ScUnit)
    (fun x => scYes ScUnit scUnit) (fun x => scYes ScUnit scUnit) scBits
def emptyUnionBound : ScLe zero zero :=
  scCountUnionBound ScBit (fun x => ScUnit) (fun x => ScUnit)
    (fun x => scYes ScUnit scUnit) (fun x => scYes ScUnit scUnit) (nil ScBit)
"""

FIBER_CHECKS = """
def scSumOverCongAt : (0 A : Type 0) -> (f : A -> Nat) -> (g : A -> Nat) ->
    ((x : A) -> Eq Nat (f x) (g x)) -> (xs : List A) ->
    Eq Nat (scSumOver A f xs) (scSumOver A g xs) :=
  fun A f g equal xs => scSumOverCong A f g equal xs

def scSumOverBoundAt : (0 A : Type 0) -> (weight : A -> Nat) -> (d : Nat) ->
    ((x : A) -> ScLe (weight x) d) -> (xs : List A) ->
    ScLe (scSumOver A weight xs) (scMul (scLength A xs) d) :=
  fun A weight d bounded xs => scSumOverBound A weight d bounded xs

def scCountExpandAt : (0 A : Type 0) -> (0 B : Type 0) ->
    (block : A -> List B) -> (0 P : B -> Type 0) ->
    (decide : (y : B) -> ScDec (P y)) -> (xs : List A) ->
    Eq Nat (scCount B P decide (scExpand A B block xs))
      (scSumOver A (fun x => scCount B P decide (block x)) xs) :=
  fun A B block P decide xs => scCountExpand A B block P decide xs

def scCountExpandBoundAt : (0 A : Type 0) -> (0 B : Type 0) ->
    (block : A -> List B) -> (0 P : B -> Type 0) ->
    (decide : (y : B) -> ScDec (P y)) -> (d : Nat) ->
    ((x : A) -> ScLe (scCount B P decide (block x)) d) -> (xs : List A) ->
    ScLe (scCount B P decide (scExpand A B block xs)) (scMul (scLength A xs) d) :=
  fun A B block P decide d bounded xs => scCountExpandBound A B block P decide d bounded xs

def scCountProductAt : (0 A : Type 0) -> (0 B : Type 0) ->
    (0 P : Pair A B -> Type 0) -> (decide : (p : Pair A B) -> ScDec (P p)) ->
    (xs : List A) -> (ys : List B) ->
    Eq Nat (scCount (Pair A B) P decide (scProduct A B xs ys))
      (scSumOver A (fun x => scCount B (fun y => P (pair A B x y))
        (fun y => decide (pair A B x y)) ys) xs) :=
  fun A B P decide xs ys => scCountProduct A B P decide xs ys

def scFiniteProductFiberBoundAt : (0 A : Type 0) -> (0 B : Type 0) ->
    (0 P : Pair A B -> Type 0) -> (decide : (p : Pair A B) -> ScDec (P p)) ->
    (fa : ScFinite A) -> (fb : ScFinite B) -> (d : Nat) ->
    ((x : A) -> ScLe (scFiniteCount B (fun y => P (pair A B x y))
      (fun y => decide (pair A B x y)) fb) d) ->
    ScLe (scFiniteCount (Pair A B) P decide (scProductFinite A B fa fb))
      (scMul (scCardinality A fa) d) :=
  fun A B P decide fa fb d bounded => scFiniteProductFiberBound A B P decide fa fb d bounded
"""

FIBER_EXAMPLES = PRODUCT_EXAMPLE + """
reducible def fiberBlock : ScBit -> List ScBit := fun x => match x with
  | scLow => nil ScBit
  | scHigh => cons ScBit scHigh (cons ScBit scHigh (cons ScBit scLow (nil ScBit)))
  end
reducible def fiberHigh : ScBit -> Type 0 := fun x => Eq ScBit x scHigh
reducible def fiberDec : (x : ScBit) -> ScDec (fiberHigh x) :=
  fun x => scBitDecEq x scHigh
reducible def fiberRepeated : List ScBit :=
  cons ScBit scHigh (cons ScBit scLow (cons ScBit scHigh (nil ScBit)))
def fiberExact : Eq Nat (scCount ScBit fiberHigh fiberDec
    (scExpand ScBit ScBit fiberBlock fiberRepeated)) fourN := refl Nat fourN
def fiberSumExact : Eq Nat (scSumOver ScBit
    (fun x => scCount ScBit fiberHigh fiberDec (fiberBlock x)) fiberRepeated) fourN :=
  scEqTrans Nat
    (scSumOver ScBit (fun x => scCount ScBit fiberHigh fiberDec (fiberBlock x))
      fiberRepeated) fourN fourN
    (scEqSym Nat fourN fourN
      (scCountExpand ScBit ScBit fiberBlock fiberHigh fiberDec fiberRepeated))
    (refl Nat fourN)
def fiberBlockBound : (x : ScBit) ->
    ScLe (scCount ScBit fiberHigh fiberDec (fiberBlock x)) twoN :=
  fun x => match x as y return
      ScLe (scCount ScBit fiberHigh fiberDec (fiberBlock y)) twoN with
  | scLow => scLeZero twoN
  | scHigh => scLeRefl twoN
  end
def fiberRepeatedBound : ScLe fourN (scMul (succ twoN) twoN) :=
  scCountExpandBound ScBit ScBit fiberBlock fiberHigh fiberDec twoN
    fiberBlockBound fiberRepeated
def fiberEmptyBound : ScLe zero zero :=
  scCountExpandBound ScBit ScBit fiberBlock fiberHigh fiberDec twoN
    fiberBlockBound (nil ScBit)
reducible def fiberPairHigh : Pair ScBit ScBit -> Type 0 :=
  fun p => fiberHigh (scSecond ScBit ScBit p)
reducible def fiberPairDec : (p : Pair ScBit ScBit) -> ScDec (fiberPairHigh p) :=
  fun p => fiberDec (scSecond ScBit ScBit p)
def fiberProductSharp : ScLe twoN twoN :=
  scFiniteProductFiberBound ScBit ScBit fiberPairHigh fiberPairDec
    scBitFinite scBitFinite oneN (fun x => scLeRefl oneN)
def fiberProductExact : Eq Nat
    (scCount (Pair ScBit ScBit) fiberPairHigh fiberPairDec
      (scProduct ScBit ScBit scBits scBits)) twoN :=
  scCountProduct ScBit ScBit fiberPairHigh fiberPairDec scBits scBits
def fiberEmptyRight : ScLe zero zero :=
  scFiniteProductFiberBound ScBit ScEmpty (fun p => ScUnit)
    (fun p => scYes ScUnit scUnit) scBitFinite emptyProductFactor zero
    (fun x => scLeZero zero)
def fiberEmptyLeft : ScLe zero zero :=
  scFiniteProductFiberBound ScEmpty ScBit (fun p => ScUnit)
    (fun p => scYes ScUnit scUnit) emptyProductFactor scBitFinite zero
    (fun x => match x with end)
"""

ARITHMETIC_CHECKS = """
def scMulZeroRightAt : (n : Nat) -> Eq Nat (scMul n zero) zero :=
  fun n => scMulZeroRight n
def scAddMulAt : (n : Nat) -> (m : Nat) -> (k : Nat) ->
    Eq Nat (scMul (scAdd n m) k) (scAdd (scMul n k) (scMul m k)) :=
  fun n m k => scAddMul n m k
def scMulAssocAt : (n : Nat) -> (m : Nat) -> (k : Nat) ->
    Eq Nat (scMul (scMul n m) k) (scMul n (scMul m k)) :=
  fun n m k => scMulAssoc n m k
def scLeTransAt : (n : Nat) -> (m : Nat) -> ScLe n m ->
    (k : Nat) -> ScLe m k -> ScLe n k :=
  fun n m first k second => scLeTrans n m first k second
def scMulMonoLeftAt : (k : Nat) -> (n : Nat) -> (m : Nat) -> ScLe n m ->
    ScLe (scMul k n) (scMul k m) :=
  fun k n m bound => scMulMonoLeft k n m bound
def scMulMonoRightAt : (n : Nat) -> (m : Nat) -> ScLe n m -> (k : Nat) ->
    ScLe (scMul n k) (scMul m k) :=
  fun n m bound k => scMulMonoRight n m bound k
def scMulMonoAt : (n : Nat) -> (m : Nat) -> ScLe n m ->
    (k : Nat) -> (l : Nat) -> ScLe k l -> ScLe (scMul n k) (scMul m l) :=
  fun n m first k l second => scMulMono n m first k l second
def scPowAddAt : (q : Nat) -> (n : Nat) -> (m : Nat) ->
    Eq Nat (scPow q (scAdd n m)) (scMul (scPow q n) (scPow q m)) :=
  fun q n m => scPowAdd q n m
"""

ARITHMETIC_EXAMPLES = EXAMPLE + """
def arithmeticZero : Eq Nat (scMul twoN zero) zero := scMulZeroRight twoN
def arithmeticDistribution : Eq Nat
    (scMul (scAdd oneN twoN) twoN) (scAdd twoN fourN) := scAddMul oneN twoN twoN
def arithmeticAssoc : Eq Nat (scMul (scMul twoN oneN) twoN) fourN :=
  scMulAssoc twoN oneN twoN
def arithmeticTrans : ScLe oneN fourN :=
  scLeTrans oneN twoN (scLeWeaken oneN oneN (scLeRefl oneN))
    fourN (scLeSucc oneN (succ twoN) (scLeSucc zero twoN (scLeZero twoN)))
def arithmeticLeftSlack : ScLe twoN fourN :=
  scMulMonoLeft twoN oneN twoN (scLeWeaken oneN oneN (scLeRefl oneN))
def arithmeticRightSlack : ScLe twoN fourN :=
  scMulMonoRight oneN twoN (scLeWeaken oneN oneN (scLeRefl oneN)) twoN
def arithmeticBothSlack : ScLe oneN fourN :=
  scMulMono oneN twoN (scLeWeaken oneN oneN (scLeRefl oneN))
    oneN twoN (scLeWeaken oneN oneN (scLeRefl oneN))
def arithmeticLeftZero : ScLe zero zero :=
  scMulMonoLeft zero oneN twoN (scLeWeaken oneN oneN (scLeRefl oneN))
def arithmeticRightZero : ScLe zero zero :=
  scMulMonoRight oneN twoN (scLeWeaken oneN oneN (scLeRefl oneN)) zero
def arithmeticEmptyLower : ScLe zero fourN :=
  scMulMonoRight zero twoN (scLeZero twoN) twoN
def arithmeticZeroPower : Eq Nat (scPow zero (scAdd zero zero)) oneN :=
  scPowAdd zero zero zero
def arithmeticEmptyPower : Eq Nat (scPow zero (scAdd zero twoN)) zero :=
  scPowAdd zero zero twoN
def arithmeticPower : Eq Nat (scPow twoN (scAdd oneN oneN)) fourN :=
  scPowAdd twoN oneN oneN
"""

RECURRENCE_CHECKS = """
def addCommAt : (n : Nat) -> (m : Nat) ->
    Eq Nat (scAdd n m) (scAdd m n) := scAddComm
def addSwapAt : (a : Nat) -> (b : Nat) -> (c : Nat) ->
    Eq Nat (scAdd a (scAdd b c)) (scAdd b (scAdd a c)) := scAddSwap
def mulSuccRightAt : (n : Nat) -> (m : Nat) ->
    Eq Nat (scMul n (succ m)) (scAdd n (scMul n m)) := scMulSuccRight
def mulCommAt : (n : Nat) -> (m : Nat) ->
    Eq Nat (scMul n m) (scMul m n) := scMulComm
def mulSwapAt : (a : Nat) -> (b : Nat) -> (c : Nat) ->
    Eq Nat (scMul a (scMul b c)) (scMul b (scMul a c)) := scMulSwap
def budgetScaledAt : (q : Nat) -> (d : Nat) -> (n : Nat) ->
    Eq Nat (scMul q (scErrorBudget q d n)) (scMul (scMul n d) (scPow q n)) :=
  scErrorBudgetScaled
def budgetSuccessorAt : (q : Nat) -> (d : Nat) -> (n : Nat) ->
    Eq Nat (scErrorBudget q d (succ n)) (scMul (scMul (succ n) d) (scPow q n)) :=
  scErrorBudgetSuccessor
def recurrenceBoundAt : (q : Nat) -> (d : Nat) -> (f : Nat -> Nat) ->
    ScLe (f zero) zero ->
    ((k : Nat) -> ScLe (f (succ k))
      (scAdd (scMul d (scPow q k)) (scMul q (f k)))) -> (n : Nat) ->
    ScLe (f n) (scErrorBudget q d n) := scRecurrenceBound
def recurrenceScaledBoundAt : (q : Nat) -> (d : Nat) -> (f : Nat -> Nat) ->
    ScLe (f zero) zero ->
    ((k : Nat) -> ScLe (f (succ k))
      (scAdd (scMul d (scPow q k)) (scMul q (f k)))) -> (n : Nat) ->
    ScLe (scMul q (f n)) (scMul (scMul n d) (scPow q n)) := scRecurrenceScaledBound
"""
RECURRENCE_EXAMPLES = EXAMPLE + """
def budgetZeroRounds : Eq Nat (scErrorBudget twoN oneN zero) zero := refl Nat zero
def budgetOneRound : Eq Nat (scErrorBudget twoN oneN oneN) oneN := refl Nat oneN
def budgetTwoRounds : Eq Nat (scErrorBudget twoN oneN twoN) fourN := refl Nat fourN
def budgetThreeRounds : Eq Nat (scErrorBudget twoN oneN (succ twoN))
    (scMul (succ twoN) fourN) := refl Nat (scMul (succ twoN) fourN)
def budgetZeroCarrierOne : Eq Nat (scErrorBudget zero twoN oneN) twoN := refl Nat twoN
def budgetZeroCarrierTwo : Eq Nat (scErrorBudget zero twoN twoN) zero := refl Nat zero
def budgetZeroDegree : Eq Nat (scErrorBudget twoN zero twoN) zero := refl Nat zero
def budgetUnitCarrier : Eq Nat (scErrorBudget oneN twoN twoN) fourN := refl Nat fourN
def budgetScaledConcrete : Eq Nat (scMul twoN (scErrorBudget twoN oneN twoN))
    (scMul twoN fourN) := scErrorBudgetScaled twoN oneN twoN
def budgetSuccessorConcrete : Eq Nat (scErrorBudget twoN oneN (succ twoN))
    (scMul (succ twoN) fourN) := scErrorBudgetSuccessor twoN oneN twoN
def recurrenceSharp : ScLe (scErrorBudget twoN oneN twoN) fourN :=
  scRecurrenceBound twoN oneN (scErrorBudget twoN oneN) (scLeZero zero)
    (fun k => scLeRefl (scErrorBudget twoN oneN (succ k))) twoN
def recurrenceSlack : ScLe zero (scMul twoN fourN) :=
  scRecurrenceScaledBound twoN oneN (fun k => zero) (scLeZero zero)
    (fun k => scLeZero (scAdd (scMul oneN (scPow twoN k)) (scMul twoN zero))) twoN
def commuteConcrete : Eq Nat (scMul twoN (succ twoN)) (scMul (succ twoN) twoN) :=
  scMulComm twoN (succ twoN)
"""

STRATEGY_CHECKS = """
def scRunStrategyLengthAt : (0 F : Type 0) -> (n : Nat) ->
    (strategy : ScStrategy F n) -> (v : ScVector F n) ->
    Eq Nat (scTraceLength F (scRunStrategy F n strategy v)) n :=
  fun F n strategy v => scRunStrategyLength F n strategy v

def scRunStrategyChallengesAt : (0 F : Type 0) -> (n : Nat) ->
    (strategy : ScStrategy F n) -> (v : ScVector F n) ->
    Eq (List F) (scTraceChallenges F (scRunStrategy F n strategy v))
      (scVectorList F n v) :=
  fun F n strategy v => scRunStrategyChallenges F n strategy v

def scHonestStrategyTraceAt : (0 F : Type 0) -> (plus : F -> F -> F) ->
    (lo : F) -> (hi : F) -> (cs : List F) -> (g : List F -> F) ->
    Eq (ScTrace F)
      (scRunStrategy F (scLength F cs)
        (scHonestStrategy F plus lo hi (scLength F cs) g) (scListVector F cs))
      (scHonestTrace F plus lo hi cs g) :=
  fun F plus lo hi cs g => scHonestStrategyTrace F plus lo hi cs g

def scHonestStrategyCompletenessAt : (0 F : Type 0) -> (plus : F -> F -> F) ->
    (lo : F) -> (hi : F) -> (n : Nat) -> (v : ScVector F n) ->
    (g : List F -> F) ->
    scAccept F plus lo hi
      (scRunStrategy F n (scHonestStrategy F plus lo hi n g) v) g
      (scSum F plus lo hi n g) :=
  fun F plus lo hi n v g => scHonestStrategyCompleteness F plus lo hi n v g

"""

ACCEPTANCE_CHECKS = """
def scCountSatisfiedAt : (0 A : Type 0) -> (0 P : A -> Type 0) ->
    (decide : (x : A) -> ScDec (P x)) -> ((x : A) -> P x) -> (xs : List A) ->
    Eq Nat (scCount A P decide xs) (scLength A xs) :=
  fun A P decide holds xs => scCountSatisfied A P decide holds xs

def scCountRefutedAt : (0 A : Type 0) -> (0 P : A -> Type 0) ->
    (decide : (x : A) -> ScDec (P x)) -> ((x : A) -> P x -> ScEmpty) ->
    (xs : List A) -> Eq Nat (scCount A P decide xs) zero :=
  fun A P decide refutes xs => scCountRefuted A P decide refutes xs

def scAcceptingCountBoundAt : (0 F : Type 0) -> (finite : ScFinite F) ->
    (plus : F -> F -> F) -> (lo : F) -> (hi : F) -> (n : Nat) ->
    (strategy : ScStrategy F n) -> (g : List F -> F) -> (claim : F) ->
    ScLe (scAcceptingCount F finite plus lo hi n strategy g claim)
      (scPow (scCardinality F finite) n) :=
  fun F finite plus lo hi n strategy g claim =>
    scAcceptingCountBound F finite plus lo hi n strategy g claim

def scHonestAcceptingCountAt : (0 F : Type 0) -> (finite : ScFinite F) ->
    (plus : F -> F -> F) -> (lo : F) -> (hi : F) -> (n : Nat) -> (g : List F -> F) ->
    Eq Nat (scAcceptingCount F finite plus lo hi n
      (scHonestStrategy F plus lo hi n g) g (scSum F plus lo hi n g))
      (scPow (scCardinality F finite) n) :=
  fun F finite plus lo hi n g => scHonestAcceptingCount F finite plus lo hi n g

def scFalseZeroAcceptingCountAt : (0 F : Type 0) -> (finite : ScFinite F) ->
    (plus : F -> F -> F) -> (lo : F) -> (hi : F) ->
    (strategy : ScStrategy F zero) -> (g : List F -> F) -> (claim : F) ->
    (Eq F claim (g (nil F)) -> ScEmpty) ->
    Eq Nat (scAcceptingCount F finite plus lo hi zero strategy g claim) zero :=
  fun F finite plus lo hi strategy g claim different =>
    scFalseZeroAcceptingCount F finite plus lo hi strategy g claim different

def scAcceptingCountStepAt : (0 F : Type 0) -> (finite : ScFinite F) ->
    (plus : F -> F -> F) -> (lo : F) -> (hi : F) -> (n : Nat) ->
    (message : F -> F) -> (next : F -> ScStrategy F n) ->
    (g : List F -> F) -> (claim : F) ->
    Eq F (plus (message lo) (message hi)) claim ->
    Eq Nat (scAcceptingCount F finite plus lo hi (succ n)
      (pair (F -> F) (F -> ScStrategy F n) message next) g claim)
      (scSumOver F (fun r => scAcceptingCount F finite plus lo hi n
        (next r) (scRestrict F g r) (message r)) (scElements F finite)) :=
  fun F finite plus lo hi n message next g claim valid =>
    scAcceptingCountStep F finite plus lo hi n message next g claim valid

def scRejectedRoundCountAt : (0 F : Type 0) -> (finite : ScFinite F) ->
    (plus : F -> F -> F) -> (lo : F) -> (hi : F) -> (n : Nat) ->
    (message : F -> F) -> (next : F -> ScStrategy F n) ->
    (g : List F -> F) -> (claim : F) ->
    (Eq F (plus (message lo) (message hi)) claim -> ScEmpty) ->
    Eq Nat (scAcceptingCount F finite plus lo hi (succ n)
      (pair (F -> F) (F -> ScStrategy F n) message next) g claim) zero :=
  fun F finite plus lo hi n message next g claim invalid =>
    scRejectedRoundCount F finite plus lo hi n message next g claim invalid
"""

ACCEPTANCE_EXAMPLE = EXAMPLE + """
reducible def bitPlus : ScBit -> ScBit -> ScBit := fun x y => x
reducible def bitGoal : List ScBit -> ScBit := fun xs => scLow
reducible def adaptiveBits : ScStrategy ScBit twoN :=
  pair (ScBit -> ScBit) (ScBit -> ScStrategy ScBit oneN) (fun r => r)
    (fun r => pair (ScBit -> ScBit) (ScBit -> ScUnit)
      (fun s => scLow) (fun s => scUnit))
reducible def bitAcceptCount : ScBit -> Nat := fun claim =>
  scAcceptingCount ScBit scBitFinite bitPlus scLow scHigh twoN adaptiveBits bitGoal claim
"""

ENUMERATION_CHECKS = """
def scSumOverZeroAt : (0 A : Type 0) -> (xs : List A) ->
    Eq Nat (scSumOver A (fun x => zero) xs) zero :=
  scSumOverZero
def scSumOverAddAt : (0 A : Type 0) -> (f : A -> Nat) -> (g : A -> Nat) ->
    (xs : List A) -> Eq Nat (scSumOver A (fun x => scAdd (f x) (g x)) xs)
      (scAdd (scSumOver A f xs) (scSumOver A g xs)) :=
  scSumOverAdd
def scSumOverSwapAt : (0 A : Type 0) -> (0 B : Type 0) ->
    (weight : A -> B -> Nat) -> (xs : List A) -> (ys : List B) ->
    Eq Nat (scSumOver A (fun x => scSumOver B (weight x) ys) xs)
      (scSumOver B (fun y => scSumOver A (fun x => weight x y) xs) ys) :=
  scSumOverSwap
def scDiagonalSymAt : (0 A : Type 0) ->
    (equal : (x : A) -> (y : A) -> ScDec (Eq A x y)) ->
    (weight : A -> Nat) -> (x : A) -> (y : A) ->
    Eq Nat (scDiagonalWeight A equal weight x y) (scDiagonalWeight A equal weight y x) :=
  scDiagonalSym
def scDiagonalAbsentAt : (0 A : Type 0) ->
    (equal : (x : A) -> (y : A) -> ScDec (Eq A x y)) ->
    (weight : A -> Nat) -> (x : A) -> (xs : List A) ->
    (scMember A x xs -> ScEmpty) ->
    Eq Nat (scSumOver A (scDiagonalWeight A equal weight x) xs) zero :=
  scDiagonalAbsent
def scDiagonalPresentAt : (0 A : Type 0) ->
    (equal : (x : A) -> (y : A) -> ScDec (Eq A x y)) ->
    (weight : A -> Nat) -> (x : A) -> (xs : List A) ->
    scNoDup A xs -> scMember A x xs ->
    Eq Nat (scSumOver A (scDiagonalWeight A equal weight x) xs) (weight x) :=
  scDiagonalPresent
def scFiniteSumIndependentAt : (0 A : Type 0) -> (weight : A -> Nat) ->
    (fa : ScFinite A) -> (fb : ScFinite A) ->
    Eq Nat (scSumOver A weight (scElements A fa))
      (scSumOver A weight (scElements A fb)) :=
  scFiniteSumIndependent
def scCountAsSumAt : (0 A : Type 0) -> (0 P : A -> Type 0) ->
    (decide : (x : A) -> ScDec (P x)) -> (xs : List A) ->
    Eq Nat (scCount A P decide xs)
      (scSumOver A (fun x => scTally (P x) (decide x) zero) xs) :=
  scCountAsSum
def scFiniteCountIndependentAt : (0 A : Type 0) -> (0 P : A -> Type 0) ->
    (dp : (x : A) -> ScDec (P x)) -> (dq : (x : A) -> ScDec (P x)) ->
    (fa : ScFinite A) -> (fb : ScFinite A) ->
    Eq Nat (scFiniteCount A P dp fa) (scFiniteCount A P dq fb) :=
  scFiniteCountIndependent
def scCardinalityIndependentAt : (0 A : Type 0) -> (fa : ScFinite A) ->
    (fb : ScFinite A) -> Eq Nat (scCardinality A fa) (scCardinality A fb) :=
  scCardinalityIndependent
def scAcceptingCountIndependentAt : (0 F : Type 0) ->
    (fa : ScFinite F) -> (fb : ScFinite F) -> (plus : F -> F -> F) ->
    (lo : F) -> (hi : F) -> (n : Nat) -> (strategy : ScStrategy F n) ->
    (g : List F -> F) -> (claim : F) ->
    Eq Nat (scAcceptingCount F fa plus lo hi n strategy g claim)
      (scAcceptingCount F fb plus lo hi n strategy g claim) :=
  scAcceptingCountIndependent
"""

ENUMERATION_EXAMPLE = ACCEPTANCE_EXAMPLE + """
reducible def enumerationEmpty : ScFinite ScEmpty :=
  scFinite ScEmpty (nil ScEmpty) (fun x => match x with end) scUnit
    (fun x y => match x with end)

reducible def reversedBits : List ScBit :=
  cons ScBit scHigh (cons ScBit scLow (nil ScBit))
def reversedComplete : (x : ScBit) -> scMember ScBit x reversedBits :=
  fun x => match x as y return scMember ScBit y reversedBits with
  | scLow => scRight (Eq ScBit scLow scHigh)
      (scMember ScBit scLow (cons ScBit scLow (nil ScBit)))
      (scLeft (Eq ScBit scLow scLow) ScEmpty (refl ScBit scLow))
  | scHigh => scLeft (Eq ScBit scHigh scHigh)
      (scMember ScBit scHigh (cons ScBit scLow (nil ScBit))) (refl ScBit scHigh)
  end
def reversedUnique : scNoDup ScBit reversedBits :=
  pair (scMember ScBit scHigh (cons ScBit scLow (nil ScBit)) -> ScEmpty)
    (scNoDup ScBit (cons ScBit scLow (nil ScBit)))
    (fun member => match member with
    | scLeft same => scHighNeLow same | scRight impossible => impossible end)
    (pair (ScEmpty -> ScEmpty) ScUnit (fun impossible => impossible) scUnit)
reducible def reversedDecision : (x : ScBit) -> (y : ScBit) -> ScDec (Eq ScBit x y) :=
  fun x y => match scBitDecEq y x with
  | scYes same => scYes (Eq ScBit x y) (scEqSym ScBit y x same)
  | scNo different => scNo (Eq ScBit x y)
      (fun same => different (scEqSym ScBit x y same))
  end
reducible def reversedFinite : ScFinite ScBit :=
  scFinite ScBit reversedBits reversedComplete reversedUnique reversedDecision
reducible def bitWeight : ScBit -> Nat := fun x => match x with
  | scLow => oneN | scHigh => twoN end
def reversedSum : Eq Nat (scSumOver ScBit bitWeight scBits)
    (scSumOver ScBit bitWeight reversedBits) :=
  scFiniteSumIndependent ScBit bitWeight scBitFinite reversedFinite
def weightedTotal : Eq Nat (scSumOver ScBit bitWeight reversedBits) (succ twoN) :=
  refl Nat (succ twoN)
def reversedCardinality : Eq Nat (scCardinality ScBit scBitFinite)
    (scCardinality ScBit reversedFinite) :=
  scCardinalityIndependent ScBit scBitFinite reversedFinite
def reversedCount : Eq Nat
    (scFiniteCount ScBit (fun x => Eq ScBit x scHigh)
      (fun x => scBitDecEq x scHigh) scBitFinite)
    (scFiniteCount ScBit (fun x => Eq ScBit x scHigh)
      (fun x => reversedDecision x scHigh) reversedFinite) :=
  scFiniteCountIndependent ScBit (fun x => Eq ScBit x scHigh)
    (fun x => scBitDecEq x scHigh) (fun x => reversedDecision x scHigh)
    scBitFinite reversedFinite
def reversedAcceptingCount : Eq Nat (bitAcceptCount scLow)
    (scAcceptingCount ScBit reversedFinite bitPlus scLow scHigh twoN
      adaptiveBits bitGoal scLow) :=
  scAcceptingCountIndependent ScBit scBitFinite reversedFinite bitPlus scLow scHigh
    twoN adaptiveBits bitGoal scLow
def reversedAcceptingTotal : Eq Nat
    (scAcceptingCount ScBit reversedFinite bitPlus scLow scHigh twoN
      adaptiveBits bitGoal scLow) twoN := refl Nat twoN
def emptySumIndependent : Eq Nat
    (scSumOver ScEmpty (fun x => zero) (scElements ScEmpty enumerationEmpty))
    (scSumOver ScEmpty (fun x => zero) (scElements ScEmpty enumerationEmpty)) :=
  scFiniteSumIndependent ScEmpty (fun x => zero) enumerationEmpty enumerationEmpty
def duplicateSum : Eq Nat
    (scSumOver ScBit bitWeight (cons ScBit scHigh reversedBits)) (succ fourN) :=
  refl Nat (succ fourN)
def absentWeight : Eq Nat (scSumOver ScBit
    (scDiagonalWeight ScBit scBitDecEq bitWeight scHigh)
    (cons ScBit scLow (nil ScBit))) zero :=
  scDiagonalAbsent ScBit scBitDecEq bitWeight scHigh (cons ScBit scLow (nil ScBit))
    (fun member => match member with
    | scLeft same => scHighNeLow same | scRight impossible => impossible end)
def presentWeight : Eq Nat (scSumOver ScBit
    (scDiagonalWeight ScBit scBitDecEq bitWeight scHigh) scBits) twoN :=
  scDiagonalPresent ScBit scBitDecEq bitWeight scHigh scBits
    scBitsUnique (scBitsComplete scHigh)
def zeroRoundIndependent : Eq Nat
    (scAcceptingCount ScBit scBitFinite bitPlus scLow scHigh zero scUnit bitGoal scLow)
    (scAcceptingCount ScBit reversedFinite bitPlus scLow scHigh zero scUnit bitGoal scLow) :=
  scAcceptingCountIndependent ScBit scBitFinite reversedFinite bitPlus scLow scHigh
    zero scUnit bitGoal scLow
"""

ROUND_BOUND_CHECKS = """
def scSumOverMonoAt : (0 A : Type 0) -> (f : A -> Nat) -> (g : A -> Nat) ->
    ((x : A) -> ScLe (f x) (g x)) -> (xs : List A) ->
    ScLe (scSumOver A f xs) (scSumOver A g xs) :=
  scSumOverMono
def scSumOverConstantAt : (0 A : Type 0) -> (b : Nat) -> (xs : List A) ->
    Eq Nat (scSumOver A (fun x => b) xs) (scMul (scLength A xs) b) :=
  scSumOverConstant
def scExceptionAllowanceSumAt : (0 A : Type 0) -> (0 P : A -> Type 0) ->
    (decide : (x : A) -> ScDec (P x)) -> (cap : Nat) -> (xs : List A) ->
    Eq Nat (scSumOver A (fun x => scExceptionAllowance (P x) (decide x) cap) xs)
      (scMul (scCount A P decide xs) cap) :=
  scExceptionAllowanceSum
def scExceptionPointBoundAt : (0 P : Type 0) -> (decision : ScDec P) ->
    (weight : Nat) -> (cap : Nat) -> (b : Nat) -> ScLe weight cap ->
    ((P -> ScEmpty) -> ScLe weight b) ->
    ScLe weight (scAdd b (scExceptionAllowance P decision cap)) :=
  scExceptionPointBound
def scSumOverExceptionalBoundAt : (0 A : Type 0) -> (0 P : A -> Type 0) ->
    (decide : (x : A) -> ScDec (P x)) -> (weight : A -> Nat) ->
    (cap : Nat) -> (b : Nat) -> ((x : A) -> ScLe (weight x) cap) ->
    ((x : A) -> (P x -> ScEmpty) -> ScLe (weight x) b) -> (xs : List A) ->
    ScLe (scSumOver A weight xs)
      (scAdd (scMul (scCount A P decide xs) cap) (scMul (scLength A xs) b)) :=
  scSumOverExceptionalBound
def scAcceptingRoundBoundAt : (0 F : Type 0) -> (finite : ScFinite F) ->
    (plus : F -> F -> F) -> (lo : F) -> (hi : F) -> (n : Nat) ->
    (message : F -> F) -> (next : F -> ScStrategy F n) ->
    (g : List F -> F) -> (claim : F) -> (0 P : F -> Type 0) ->
    (decide : (r : F) -> ScDec (P r)) -> (d : Nat) -> (b : Nat) ->
    ScLe (scFiniteCount F P decide finite) d ->
    ((r : F) -> (P r -> ScEmpty) ->
      ScLe (scAcceptingCount F finite plus lo hi n (next r)
        (scRestrict F g r) (message r)) b) ->
    ScLe (scAcceptingCount F finite plus lo hi (succ n)
      (pair (F -> F) (F -> ScStrategy F n) message next) g claim)
      (scAdd (scMul d (scPow (scCardinality F finite) n))
        (scMul (scCardinality F finite) b)) :=
  scAcceptingRoundBound
"""

CONDITIONAL_SOUNDNESS_CHECKS = """
def scConditionalSoundnessAt : (0 F : Type 0) -> (finite : ScFinite F) ->
    (plus : F -> F -> F) -> (lo : F) -> (hi : F) -> (d : Nat) -> (n : Nat) ->
    (strategy : ScStrategy F n) -> (g : List F -> F) -> (claim : F) ->
    ScAgreementTree F finite plus lo hi d n strategy g claim ->
    (Eq F claim (scSum F plus lo hi n g) -> ScEmpty) ->
    ScLe (scAcceptingCount F finite plus lo hi n strategy g claim)
      (scErrorBudget (scCardinality F finite) d n) :=
  scConditionalSoundness
def scConditionalSoundnessScaledAt : (0 F : Type 0) -> (finite : ScFinite F) ->
    (plus : F -> F -> F) -> (lo : F) -> (hi : F) -> (d : Nat) -> (n : Nat) ->
    (strategy : ScStrategy F n) -> (g : List F -> F) -> (claim : F) ->
    ScAgreementTree F finite plus lo hi d n strategy g claim ->
    (Eq F claim (scSum F plus lo hi n g) -> ScEmpty) ->
    ScLe (scMul (scCardinality F finite)
      (scAcceptingCount F finite plus lo hi n strategy g claim))
      (scMul (scMul n d) (scPow (scCardinality F finite) n)) :=
  scConditionalSoundnessScaled
"""

CONDITIONAL_SOUNDNESS_EXAMPLE = EXAMPLE + """
reducible def soundPlus : ScBit -> ScBit -> ScBit := fun x y => x
reducible def soundGoal : List ScBit -> ScBit := fun xs => scLow
reducible def soundMessage : ScBit -> ScBit := fun r => match r with
| scLow => scHigh | scHigh => scLow end
reducible def soundOne : ScStrategy ScBit oneN :=
  pair (ScBit -> ScBit) (ScBit -> ScStrategy ScBit zero) soundMessage (fun r => scUnit)
def soundOneTree : ScAgreementTree ScBit scBitFinite soundPlus scLow scHigh
    oneN oneN soundOne soundGoal scHigh :=
  pair (Eq ScBit (soundPlus (soundMessage scLow) (soundMessage scHigh)) scHigh ->
    (Eq ScBit scHigh (scSum ScBit soundPlus scLow scHigh oneN soundGoal) -> ScEmpty) ->
    ScLe (scFiniteCount ScBit
      (fun r => Eq ScBit (soundMessage r) (scMarginal ScBit soundPlus scLow scHigh zero soundGoal r))
      (fun r => scBitDecEq (soundMessage r)
        (scMarginal ScBit soundPlus scLow scHigh zero soundGoal r)) scBitFinite) oneN) (ScBit -> ScUnit)
    (fun valid different => scLeRefl oneN) (fun r => scUnit)
reducible def soundTwo : ScStrategy ScBit twoN :=
  pair (ScBit -> ScBit) (ScBit -> ScStrategy ScBit oneN) soundMessage (fun r => match r with
    | scLow => soundOne
    | scHigh => scHonestStrategy ScBit soundPlus scLow scHigh oneN soundGoal
    end)
def soundTwoTree : ScAgreementTree ScBit scBitFinite soundPlus scLow scHigh
    oneN twoN soundTwo soundGoal scHigh :=
  pair (Eq ScBit (soundPlus (soundMessage scLow) (soundMessage scHigh)) scHigh ->
    (Eq ScBit scHigh (scSum ScBit soundPlus scLow scHigh twoN soundGoal) -> ScEmpty) ->
    ScLe (scFiniteCount ScBit
      (fun r => Eq ScBit (soundMessage r) (scMarginal ScBit soundPlus scLow scHigh oneN soundGoal r))
      (fun r => scBitDecEq (soundMessage r)
        (scMarginal ScBit soundPlus scLow scHigh oneN soundGoal r)) scBitFinite) oneN) ((r : ScBit) ->
      ScAgreementTree ScBit scBitFinite soundPlus scLow scHigh oneN oneN
        (match r with | scLow => soundOne
         | scHigh => scHonestStrategy ScBit soundPlus scLow scHigh oneN soundGoal end)
        (scRestrict ScBit soundGoal r) (soundMessage r))
    (fun valid different => scLeRefl oneN)
    (fun r => match r as x return ScAgreementTree ScBit scBitFinite
        soundPlus scLow scHigh oneN oneN
        (match x with | scLow => soundOne
         | scHigh => scHonestStrategy ScBit soundPlus scLow scHigh oneN soundGoal end)
        (scRestrict ScBit soundGoal x) (soundMessage x) with
    | scLow => soundOneTree
    | scHigh => pair
        (Eq ScBit scLow scLow -> (Eq ScBit scLow scLow -> ScEmpty) -> ScLe twoN oneN)
        (ScBit -> ScUnit)
        (fun valid different => match different (refl ScBit scLow) with end)
        (fun r => scUnit)
    end)
reducible def soundRejected : ScStrategy ScBit oneN :=
  scHonestStrategy ScBit soundPlus scLow scHigh oneN soundGoal
def soundRejectedTree : ScAgreementTree ScBit scBitFinite soundPlus scLow scHigh
    zero oneN soundRejected soundGoal scHigh :=
  pair (Eq ScBit scLow scHigh -> (Eq ScBit scHigh scLow -> ScEmpty) -> ScLe twoN zero)
    (ScBit -> ScUnit)
    (fun valid different => match scLowNeHigh valid with end) (fun r => scUnit)
"""

CONDITIONAL_SOUNDNESS_EXAMPLES = CONDITIONAL_SOUNDNESS_EXAMPLE + """
def sharpSoundness : ScLe
    (scAcceptingCount ScBit scBitFinite soundPlus scLow scHigh oneN
      soundOne soundGoal scHigh) oneN :=
  scConditionalSoundness ScBit scBitFinite soundPlus scLow scHigh oneN oneN
    soundOne soundGoal scHigh soundOneTree scHighNeLow
def sharpCount : Eq Nat
    (scAcceptingCount ScBit scBitFinite soundPlus scLow scHigh oneN
      soundOne soundGoal scHigh) oneN := refl Nat oneN
def adaptiveSoundness : ScLe
    (scAcceptingCount ScBit scBitFinite soundPlus scLow scHigh twoN
      soundTwo soundGoal scHigh) fourN :=
  scConditionalSoundness ScBit scBitFinite soundPlus scLow scHigh oneN twoN
    soundTwo soundGoal scHigh soundTwoTree scHighNeLow
def adaptiveCount : Eq Nat
    (scAcceptingCount ScBit scBitFinite soundPlus scLow scHigh twoN
      soundTwo soundGoal scHigh) (succ twoN) := refl Nat (succ twoN)
def scaledSoundness : ScLe
    (scMul twoN (scAcceptingCount ScBit scBitFinite soundPlus scLow scHigh twoN
      soundTwo soundGoal scHigh)) (scMul fourN twoN) :=
  scConditionalSoundnessScaled ScBit scBitFinite soundPlus scLow scHigh oneN twoN
    soundTwo soundGoal scHigh soundTwoTree scHighNeLow
def terminalSoundness : ScLe
    (scAcceptingCount ScBit scBitFinite soundPlus scLow scHigh zero
      scUnit soundGoal scHigh) zero :=
  scConditionalSoundness ScBit scBitFinite soundPlus scLow scHigh zero zero
    scUnit soundGoal scHigh scUnit scHighNeLow
def rejectedSoundness : ScLe
    (scAcceptingCount ScBit scBitFinite soundPlus scLow scHigh oneN
      soundRejected soundGoal scHigh) zero :=
  scConditionalSoundness ScBit scBitFinite soundPlus scLow scHigh zero oneN
    soundRejected soundGoal scHigh soundRejectedTree scHighNeLow
"""

CASES = [
    ("generic-proofs", "", None),
    ("conditional-soundness", CONDITIONAL_SOUNDNESS_CHECKS, None),
    ("conditional-soundness-examples", CONDITIONAL_SOUNDNESS_EXAMPLES, None),
    ("soundness-missing-tree", CONDITIONAL_SOUNDNESS_EXAMPLE + """
def missingTree : ScLe
    (scAcceptingCount ScBit scBitFinite soundPlus scLow scHigh oneN
      soundOne soundGoal scHigh) oneN :=
  scConditionalSoundness ScBit scBitFinite soundPlus scLow scHigh oneN oneN
    soundOne soundGoal scHigh scUnit scHighNeLow
""", "mismatch"),
    ("soundness-missing-falsity", CONDITIONAL_SOUNDNESS_EXAMPLE + """
def missingFalsity : ScLe
    (scAcceptingCount ScBit scBitFinite soundPlus scLow scHigh oneN
      soundOne soundGoal scHigh) oneN :=
  scConditionalSoundness ScBit scBitFinite soundPlus scLow scHigh oneN oneN
    soundOne soundGoal scHigh soundOneTree
""", "mismatch"),
    ("soundness-tree-missing-rarity", CONDITIONAL_SOUNDNESS_EXAMPLE + """
def missingRarity : ScAgreementTree ScBit scBitFinite soundPlus scLow scHigh
    oneN oneN soundOne soundGoal scHigh :=
  pair (Eq ScBit (soundPlus (soundMessage scLow) (soundMessage scHigh)) scHigh ->
    (Eq ScBit scHigh (scSum ScBit soundPlus scLow scHigh oneN soundGoal) -> ScEmpty) ->
    ScLe (scFiniteCount ScBit
      (fun r => Eq ScBit (soundMessage r) (scMarginal ScBit soundPlus scLow scHigh zero soundGoal r))
      (fun r => scBitDecEq (soundMessage r)
        (scMarginal ScBit soundPlus scLow scHigh zero soundGoal r)) scBitFinite) oneN) (ScBit -> ScUnit) scUnit (fun r => scUnit)
""", "mismatch"),
    ("soundness-tree-missing-children", CONDITIONAL_SOUNDNESS_EXAMPLE + """
def missingChildren : ScAgreementTree ScBit scBitFinite soundPlus scLow scHigh
    oneN twoN soundTwo soundGoal scHigh :=
  pair (Eq ScBit (soundPlus (soundMessage scLow) (soundMessage scHigh)) scHigh ->
    (Eq ScBit scHigh (scSum ScBit soundPlus scLow scHigh twoN soundGoal) -> ScEmpty) ->
    ScLe (scFiniteCount ScBit
      (fun r => Eq ScBit (soundMessage r) (scMarginal ScBit soundPlus scLow scHigh oneN soundGoal r))
      (fun r => scBitDecEq (soundMessage r)
        (scMarginal ScBit soundPlus scLow scHigh oneN soundGoal r)) scBitFinite) oneN) ((r : ScBit) ->
      ScAgreementTree ScBit scBitFinite soundPlus scLow scHigh oneN oneN
        (match r with | scLow => soundOne
         | scHigh => scHonestStrategy ScBit soundPlus scLow scHigh oneN soundGoal end)
        (scRestrict ScBit soundGoal r) (soundMessage r))
    (fun valid different => scLeRefl oneN) (fun r => scUnit)
""", "mismatch"),
    ("round-bounds", ROUND_BOUND_CHECKS, None),
    ("exceptional-sum-examples", EXAMPLE + """
reducible def lowException : ScBit -> Type 0 := fun r => Eq ScBit r scLow
reducible def lowDecision : (r : ScBit) -> ScDec (lowException r) :=
  fun r => scBitDecEq r scLow
reducible def mixedWeight : ScBit -> Nat := fun r => match r with
  | scLow => twoN | scHigh => oneN end
def mixedCap : (r : ScBit) -> ScLe (mixedWeight r) twoN :=
  fun r => match r as s return ScLe (mixedWeight s) twoN with
  | scLow => scLeRefl twoN
  | scHigh => scLeSucc zero oneN (scLeZero oneN)
  end
def mixedOutside : (r : ScBit) -> (lowException r -> ScEmpty) ->
    ScLe (mixedWeight r) oneN :=
  fun r => match r as s return (lowException s -> ScEmpty) ->
      ScLe (mixedWeight s) oneN with
  | scLow => fun refute => match refute (refl ScBit scLow) with end
  | scHigh => fun refute => scLeRefl oneN
  end
def mixedBound : ScLe (scSumOver ScBit mixedWeight scBits) fourN :=
  scSumOverExceptionalBound ScBit lowException lowDecision mixedWeight
    twoN oneN mixedCap mixedOutside scBits
def mixedTotal : Eq Nat (scSumOver ScBit mixedWeight scBits) (succ twoN) :=
  refl Nat (succ twoN)
def emptyBound : ScLe zero zero :=
  scSumOverExceptionalBound ScBit lowException lowDecision mixedWeight
    twoN oneN mixedCap mixedOutside (nil ScBit)
def duplicateAllowance : Eq Nat
    (scSumOver ScBit (fun r => scExceptionAllowance (lowException r)
      (lowDecision r) twoN) (cons ScBit scLow (cons ScBit scLow (nil ScBit))))
    fourN := scExceptionAllowanceSum ScBit lowException lowDecision twoN
      (cons ScBit scLow (cons ScBit scLow (nil ScBit)))
def noExceptions : Eq Nat
    (scSumOver ScBit (fun r => scExceptionAllowance ScEmpty
      (scNo ScEmpty (fun h => h)) twoN) scBits) zero :=
  scExceptionAllowanceSum ScBit (fun r => ScEmpty)
    (fun r => scNo ScEmpty (fun h => h)) twoN scBits
def zeroCap : Eq Nat
    (scSumOver ScBit (fun r => scExceptionAllowance (lowException r)
      (lowDecision r) zero) scBits) zero :=
  scExceptionAllowanceSum ScBit lowException lowDecision zero scBits
""", None),
    ("round-bound-examples", ACCEPTANCE_EXAMPLE + """
reducible def nextBit : ScBit -> ScStrategy ScBit oneN :=
  fun r => pair (ScBit -> ScBit) (ScBit -> ScUnit)
    (fun s => scLow) (fun s => scUnit)
def outsideLow : (r : ScBit) -> (Eq ScBit r scLow -> ScEmpty) ->
    ScLe (scAcceptingCount ScBit scBitFinite bitPlus scLow scHigh oneN
      (nextBit r) (scRestrict ScBit bitGoal r) r) zero :=
  fun r => match r as s return (Eq ScBit s scLow -> ScEmpty) ->
      ScLe (scAcceptingCount ScBit scBitFinite bitPlus scLow scHigh oneN
        (nextBit s) (scRestrict ScBit bitGoal s) s) zero with
  | scLow => fun refute => match refute (refl ScBit scLow) with end
  | scHigh => fun refute => scLeZero zero
  end
def adaptiveBound : ScLe (bitAcceptCount scLow) twoN :=
  scAcceptingRoundBound ScBit scBitFinite bitPlus scLow scHigh oneN
    (fun r => r) nextBit bitGoal scLow (fun r => Eq ScBit r scLow)
    (fun r => scBitDecEq r scLow) oneN zero (scLeRefl oneN) outsideLow
def rejectedBound : ScLe (bitAcceptCount scHigh) twoN :=
  scAcceptingRoundBound ScBit scBitFinite bitPlus scLow scHigh oneN
    (fun r => r) nextBit bitGoal scHigh (fun r => Eq ScBit r scLow)
    (fun r => scBitDecEq r scLow) oneN zero (scLeRefl oneN) outsideLow
def terminalOutside : (r : ScBit) -> (Eq ScBit r scLow -> ScEmpty) ->
    ScLe (scAcceptingCount ScBit scBitFinite bitPlus scLow scHigh zero
      scUnit (scRestrict ScBit bitGoal r) r) zero :=
  fun r refute => scTransport Nat zero
    (scAcceptingCount ScBit scBitFinite bitPlus scLow scHigh zero
      scUnit (scRestrict ScBit bitGoal r) r) (fun total => ScLe total zero)
    (scEqSym Nat (scAcceptingCount ScBit scBitFinite bitPlus scLow scHigh zero
      scUnit (scRestrict ScBit bitGoal r) r) zero
      (scFalseZeroAcceptingCount ScBit scBitFinite bitPlus scLow scHigh
        scUnit (scRestrict ScBit bitGoal r) r refute)) (scLeZero zero)
def lastRoundBound : ScLe (scAcceptingCount ScBit scBitFinite bitPlus scLow
    scHigh oneN (pair (ScBit -> ScBit) (ScBit -> ScUnit)
      (fun r => r) (fun r => scUnit)) bitGoal scLow) oneN :=
  scAcceptingRoundBound ScBit scBitFinite bitPlus scLow scHigh zero
    (fun r => r) (fun r => scUnit) bitGoal scLow (fun r => Eq ScBit r scLow)
    (fun r => scBitDecEq r scLow) oneN zero (scLeRefl oneN) terminalOutside
""", None),
    ("exception-missing-cap", """
def scSumOverExceptionalBoundAt : (0 A : Type 0) -> (0 P : A -> Type 0) ->
    (decide : (x : A) -> ScDec (P x)) -> (weight : A -> Nat) ->
    (cap : Nat) -> (b : Nat) ->
    ((x : A) -> (P x -> ScEmpty) -> ScLe (weight x) b) -> (xs : List A) ->
    ScLe (scSumOver A weight xs)
      (scAdd (scMul (scCount A P decide xs) cap) (scMul (scLength A xs) b)) :=
  scSumOverExceptionalBound
""", "mismatch"),
    ("exception-missing-outside", """
def scSumOverExceptionalBoundAt : (0 A : Type 0) -> (0 P : A -> Type 0) ->
    (decide : (x : A) -> ScDec (P x)) -> (weight : A -> Nat) ->
    (cap : Nat) -> (b : Nat) -> ((x : A) -> ScLe (weight x) cap) ->
     (xs : List A) ->
    ScLe (scSumOver A weight xs)
      (scAdd (scMul (scCount A P decide xs) cap) (scMul (scLength A xs) b)) :=
  scSumOverExceptionalBound
""", "mismatch"),
    ("round-missing-exception-count", """
def scAcceptingRoundBoundAt : (0 F : Type 0) -> (finite : ScFinite F) ->
    (plus : F -> F -> F) -> (lo : F) -> (hi : F) -> (n : Nat) ->
    (message : F -> F) -> (next : F -> ScStrategy F n) ->
    (g : List F -> F) -> (claim : F) -> (0 P : F -> Type 0) ->
    (decide : (r : F) -> ScDec (P r)) -> (d : Nat) -> (b : Nat) ->

    ((r : F) -> (P r -> ScEmpty) ->
      ScLe (scAcceptingCount F finite plus lo hi n (next r)
        (scRestrict F g r) (message r)) b) ->
    ScLe (scAcceptingCount F finite plus lo hi (succ n)
      (pair (F -> F) (F -> ScStrategy F n) message next) g claim)
      (scAdd (scMul d (scPow (scCardinality F finite) n))
        (scMul (scCardinality F finite) b)) :=
  scAcceptingRoundBound
""", "mismatch"),
    ("round-missing-continuation-bound", """
def scAcceptingRoundBoundAt : (0 F : Type 0) -> (finite : ScFinite F) ->
    (plus : F -> F -> F) -> (lo : F) -> (hi : F) -> (n : Nat) ->
    (message : F -> F) -> (next : F -> ScStrategy F n) ->
    (g : List F -> F) -> (claim : F) -> (0 P : F -> Type 0) ->
    (decide : (r : F) -> ScDec (P r)) -> (d : Nat) -> (b : Nat) ->
    ScLe (scFiniteCount F P decide finite) d ->
    ScLe (scAcceptingCount F finite plus lo hi (succ n)
      (pair (F -> F) (F -> ScStrategy F n) message next) g claim)
      (scAdd (scMul d (scPow (scCardinality F finite) n))
        (scMul (scCardinality F finite) b)) :=
  scAcceptingRoundBound
""", "mismatch"),

    ("enumeration-independent", ENUMERATION_CHECKS, None),
    ("enumeration-independent-examples", ENUMERATION_EXAMPLE, None),
    ("diagonal-missing-uniqueness", """
def missingUnique : (0 A : Type 0) ->
    (equal : (x : A) -> (y : A) -> ScDec (Eq A x y)) ->
    (weight : A -> Nat) -> (x : A) -> (xs : List A) ->
    scMember A x xs ->
    Eq Nat (scSumOver A (scDiagonalWeight A equal weight x) xs) (weight x) :=
  scDiagonalPresent
""", "mismatch"),
    ("diagonal-missing-membership", """
def missingMember : (0 A : Type 0) ->
    (equal : (x : A) -> (y : A) -> ScDec (Eq A x y)) ->
    (weight : A -> Nat) -> (x : A) -> (xs : List A) -> scNoDup A xs ->
    Eq Nat (scSumOver A (scDiagonalWeight A equal weight x) xs) (weight x) :=
  scDiagonalPresent
""", "mismatch"),
    ("diagonal-missing-absence", """
def missingAbsent : (0 A : Type 0) ->
    (equal : (x : A) -> (y : A) -> ScDec (Eq A x y)) ->
    (weight : A -> Nat) -> (x : A) -> (xs : List A) ->
    Eq Nat (scSumOver A (scDiagonalWeight A equal weight x) xs) zero :=
  scDiagonalAbsent
""", "mismatch"),
    ("enumeration-different-predicates", """
def differentPredicates : (0 A : Type 0) -> (0 P : A -> Type 0) ->
    (0 Q : A -> Type 0) -> (dp : (x : A) -> ScDec (P x)) ->
    (dq : (x : A) -> ScDec (Q x)) -> (fa : ScFinite A) -> (fb : ScFinite A) ->
    Eq Nat (scFiniteCount A P dp fa) (scFiniteCount A Q dq fb) :=
  fun A P Q dp dq fa fb => scFiniteCountIndependent A P dp dq fa fb
""", "mismatch"),
    ("enumeration-duplicates-change-sum", ENUMERATION_EXAMPLE + """
def duplicatesIgnored : Eq Nat
    (scSumOver ScBit bitWeight (cons ScBit scHigh reversedBits))
    (scSumOver ScBit bitWeight scBits) := reversedSum
""", "mismatch"),
    ("acceptance-counting", ACCEPTANCE_CHECKS, None),
    ("acceptance-count-examples", ACCEPTANCE_EXAMPLE + """
def adaptiveHalf : Eq Nat (bitAcceptCount scLow) twoN := refl Nat twoN
def rejectedHead : Eq Nat (bitAcceptCount scHigh) zero := refl Nat zero
def honestAll : Eq Nat (scAcceptingCount ScBit scBitFinite bitPlus scLow scHigh twoN
    (scHonestStrategy ScBit bitPlus scLow scHigh twoN bitGoal) bitGoal scLow) fourN :=
  scHonestAcceptingCount ScBit scBitFinite bitPlus scLow scHigh twoN bitGoal
def terminalTrue : Eq Nat (scAcceptingCount ScBit scBitFinite bitPlus scLow scHigh
    zero scUnit bitGoal scLow) oneN := refl Nat oneN
def terminalFalse : Eq Nat (scAcceptingCount ScBit scBitFinite bitPlus scLow scHigh
    zero scUnit bitGoal scHigh) zero := refl Nat zero
def restrictionAndClaim : Eq Nat (scAcceptingCount ScBit scBitFinite bitPlus
    scLow scHigh oneN
    (pair (ScBit -> ScBit) (ScBit -> ScUnit) (fun r => r) (fun r => scUnit))
    (scHeadOr ScBit scLow) scLow) twoN := refl Nat twoN
def splitAdaptive : Eq Nat (bitAcceptCount scLow)
    (scSumOver ScBit (fun r => scAcceptingCount ScBit scBitFinite bitPlus scLow scHigh
      oneN (pair (ScBit -> ScBit) (ScBit -> ScUnit) (fun s => scLow) (fun s => scUnit))
      (scRestrict ScBit bitGoal r) r) scBits) :=
  scAcceptingCountStep ScBit scBitFinite bitPlus scLow scHigh oneN (fun r => r)
    (fun r => pair (ScBit -> ScBit) (ScBit -> ScUnit)
      (fun s => scLow) (fun s => scUnit)) bitGoal scLow (refl ScBit scLow)
""", None),
    ("acceptance-step-missing-round-check", """
def missingRound : (0 F : Type 0) -> (finite : ScFinite F) ->
    (plus : F -> F -> F) -> (lo : F) -> (hi : F) -> (n : Nat) ->
    (message : F -> F) -> (next : F -> ScStrategy F n) ->
    (g : List F -> F) -> (claim : F) ->
    Eq Nat (scAcceptingCount F finite plus lo hi (succ n)
      (pair (F -> F) (F -> ScStrategy F n) message next) g claim)
      (scSumOver F (fun r => scAcceptingCount F finite plus lo hi n
        (next r) (scRestrict F g r) (message r)) (scElements F finite)) :=
  fun F finite plus lo hi n message next g claim =>
    scAcceptingCountStep F finite plus lo hi n message next g claim
""", "mismatch"),
    ("acceptance-rejected-round-missing-refutation", """
def missingRefutation : (0 F : Type 0) -> (finite : ScFinite F) ->
    (plus : F -> F -> F) -> (lo : F) -> (hi : F) -> (n : Nat) ->
    (message : F -> F) -> (next : F -> ScStrategy F n) ->
    (g : List F -> F) -> (claim : F) ->
    Eq Nat (scAcceptingCount F finite plus lo hi (succ n)
      (pair (F -> F) (F -> ScStrategy F n) message next) g claim) zero :=
  fun F finite plus lo hi n message next g claim =>
    scRejectedRoundCount F finite plus lo hi n message next g claim
""", "mismatch"),
    ("acceptance-zero-missing-falsity", """
def missingFalsity : (0 F : Type 0) -> (finite : ScFinite F) ->
    (plus : F -> F -> F) -> (lo : F) -> (hi : F) ->
    (strategy : ScStrategy F zero) -> (g : List F -> F) -> (claim : F) ->
    Eq Nat (scAcceptingCount F finite plus lo hi zero strategy g claim) zero :=
  fun F finite plus lo hi strategy g claim =>
    scFalseZeroAcceptingCount F finite plus lo hi strategy g claim
""", "mismatch"),
    ("acceptance-honest-wrong-claim", """
def wrongHonestCount : (0 F : Type 0) -> (finite : ScFinite F) ->
    (plus : F -> F -> F) -> (lo : F) -> (hi : F) -> (n : Nat) ->
    (g : List F -> F) -> (claim : F) ->
    Eq Nat (scAcceptingCount F finite plus lo hi n
      (scHonestStrategy F plus lo hi n g) g claim) (scPow (scCardinality F finite) n) :=
  fun F finite plus lo hi n g claim => scHonestAcceptingCount F finite plus lo hi n g
""", "mismatch"),
    ("acceptance-tail-cannot-be-ignored", ACCEPTANCE_EXAMPLE + """
def ignoresTail : Eq Nat (bitAcceptCount scLow) fourN := refl Nat fourN
""", "mismatch"),
    ("strategies", STRATEGY_CHECKS, None),
    ("strategy-examples", EXAMPLE + """
reducible def adaptiveN : ScStrategy Nat twoN :=
  pair (Nat -> Nat) (Nat -> ScStrategy Nat oneN) (fun x => zero)
    (fun r => pair (Nat -> Nat) (Nat -> ScStrategy Nat zero)
      (fun x => r) (fun x => scUnit))
reducible def vectorN : ScVector Nat twoN := scListVector Nat challengesN
reducible def alternateN : ScVector Nat twoN :=
  pair Nat (ScVector Nat oneN) oneN (pair Nat ScUnit twoN scUnit)
def adaptiveFirst : Eq (ScTrace Nat) (scRunStrategy Nat twoN adaptiveN vectorN)
    (scStep Nat (fun x => zero) twoN
      (scStep Nat (fun x => twoN) oneN (scDone Nat))) :=
  refl (ScTrace Nat) (scStep Nat (fun x => zero) twoN
    (scStep Nat (fun x => twoN) oneN (scDone Nat)))
def adaptiveAlternate : Eq (ScTrace Nat) (scRunStrategy Nat twoN adaptiveN alternateN)
    (scStep Nat (fun x => zero) oneN
      (scStep Nat (fun x => oneN) twoN (scDone Nat))) :=
  refl (ScTrace Nat) (scStep Nat (fun x => zero) oneN
    (scStep Nat (fun x => oneN) twoN (scDone Nat)))
def strategyLength : Eq Nat (scTraceLength Nat
    (scRunStrategy Nat twoN adaptiveN vectorN)) twoN :=
  scRunStrategyLength Nat twoN adaptiveN vectorN
def strategyChallenges : Eq (List Nat) (scTraceChallenges Nat
    (scRunStrategy Nat twoN adaptiveN vectorN)) challengesN :=
  scRunStrategyChallenges Nat twoN adaptiveN vectorN
def honestStrategyAgrees : Eq (ScTrace Nat)
    (scRunStrategy Nat twoN (scHonestStrategy Nat plusN zero oneN twoN sumInputs)
      vectorN) honestN :=
  scHonestStrategyTrace Nat plusN zero oneN challengesN sumInputs
def honestStrategyAccepts : scAccept Nat plusN zero oneN
    (scRunStrategy Nat twoN (scHonestStrategy Nat plusN zero oneN twoN sumInputs)
      vectorN) sumInputs fourN :=
  scHonestStrategyCompleteness Nat plusN zero oneN twoN vectorN sumInputs
def noRounds : Eq (ScTrace ScEmpty)
    (scRunStrategy ScEmpty zero scUnit scUnit) (scDone ScEmpty) :=
  refl (ScTrace ScEmpty) (scDone ScEmpty)
def zeroRoundAccepts : scAccept Nat plusN zero oneN
    (scRunStrategy Nat zero (scHonestStrategy Nat plusN zero oneN zero sumInputs)
      scUnit) sumInputs zero :=
  scHonestStrategyCompleteness Nat plusN zero oneN zero scUnit sumInputs
""", None),
    ("strategy-wrong-rounds", """
def wrongStrategyLength : (0 F : Type 0) -> (n : Nat) ->
    (s : ScStrategy F n) -> (v : ScVector F n) ->
    Eq Nat (scTraceLength F (scRunStrategy F n s v)) (succ n) :=
  fun F n s v => scRunStrategyLength F n s v
""", "mismatch"),
    ("strategy-wrong-challenges", """
def wrongStrategyChallenges : (0 F : Type 0) -> (n : Nat) ->
    (s : ScStrategy F n) -> (v : ScVector F n) -> (w : ScVector F n) ->
    Eq (List F) (scTraceChallenges F (scRunStrategy F n s v))
      (scVectorList F n w) :=
  fun F n s v w => scRunStrategyChallenges F n s v
""", "mismatch"),
    ("strategy-wrong-claim", """
def wrongStrategyClaim : (0 F : Type 0) -> (plus : F -> F -> F) ->
    (lo : F) -> (hi : F) -> (n : Nat) -> (v : ScVector F n) ->
    (g : List F -> F) -> (claim : F) -> scAccept F plus lo hi
      (scRunStrategy F n (scHonestStrategy F plus lo hi n g) v) g claim :=
  fun F plus lo hi n v g claim => scHonestStrategyCompleteness F plus lo hi n v g
""", "mismatch"),
    ("strategy-early-stop", """
def earlyStop : (0 F : Type 0) -> ScStrategy F (succ zero) :=
  fun F => scUnit
""", "mismatch"),
    ("recurrence", RECURRENCE_CHECKS, None),
    ("recurrence-examples", RECURRENCE_EXAMPLES, None),
    ("recurrence-missing-initial", """
def missingInitial : (q : Nat) -> (d : Nat) -> (f : Nat -> Nat) ->
    ((k : Nat) -> ScLe (f (succ k))
      (scAdd (scMul d (scPow q k)) (scMul q (f k)))) -> (n : Nat) ->
    ScLe (f n) (scErrorBudget q d n) :=
  fun q d f step n => scRecurrenceBound q d f (scLeRefl (f zero)) step n
""", "mismatch"),
    ("recurrence-missing-step", """
def missingStep : (q : Nat) -> (d : Nat) -> (f : Nat -> Nat) ->
    ScLe (f zero) zero -> (n : Nat) -> ScLe (f n) (scErrorBudget q d n) :=
  fun q d f initial n => scRecurrenceBound q d f initial
    (fun k => scLeRefl (f (succ k))) n
""", "mismatch"),
    ("recurrence-wrong-exponent", """
def wrongExponent : (q : Nat) -> (d : Nat) -> (n : Nat) ->
    Eq Nat (scErrorBudget q d (succ n))
      (scMul (scMul (succ n) d) (scPow q (succ n))) := scErrorBudgetSuccessor
""", "mismatch"),
    ("recurrence-omits-scale", """
def omittedScale : (q : Nat) -> (d : Nat) -> (f : Nat -> Nat) ->
    ScLe (f zero) zero ->
    ((k : Nat) -> ScLe (f (succ k))
      (scAdd (scMul d (scPow q k)) (scMul q (f k)))) -> (n : Nat) ->
    ScLe (f n) (scMul (scMul n d) (scPow q n)) := scRecurrenceScaledBound
""", "mismatch"),
    ('arithmetic', ARITHMETIC_CHECKS, None),
    ('arithmetic-examples', ARITHMETIC_EXAMPLES, None),
    ('order-transitivity-reversed', """
def badTrans : (n : Nat) -> (m : Nat) -> ScLe n m ->
    (k : Nat) -> ScLe m k -> ScLe k n :=
  fun n m first k second => scLeTrans n m first k second
""", "mismatch"),
    ('multiplication-omits-factor', """
def badMul : (n : Nat) -> (m : Nat) -> ScLe n m -> (k : Nat) ->
    ScLe (scMul n k) m :=
  fun n m bound k => scMulMonoRight n m bound k
""", "mismatch"),
    ('multiplication-reversed-bound', """
def badMul : (k : Nat) -> (n : Nat) -> (m : Nat) -> ScLe n m ->
    ScLe (scMul k m) (scMul k n) :=
  fun k n m bound => scMulMonoLeft k n m bound
""", "mismatch"),
    ('power-add-wrong-exponent', """
def badPow : (q : Nat) -> (n : Nat) -> (m : Nat) ->
    Eq Nat (scPow q (scAdd n m)) (scMul (scPow q n) (scPow q n)) :=
  fun q n m => scPowAdd q n m
""", "mismatch"),
    ('fiber-counting', FIBER_CHECKS, None),
    ('fiber-examples', FIBER_EXAMPLES, None),
    ('fiber-bound-missing-hypothesis', """
def badFiber : (0 A : Type 0) -> (weight : A -> Nat) -> (d : Nat) ->
    (xs : List A) -> ScLe (scSumOver A weight xs) (scMul (scLength A xs) d) :=
  fun A weight d xs => scSumOverBound A weight d (fun x => scLeRefl d) xs
""", "mismatch"),
    ('fiber-bound-omits-block-count', """
def badFiber : (0 A : Type 0) -> (0 B : Type 0) ->
    (block : A -> List B) -> (0 P : B -> Type 0) ->
    (decide : (y : B) -> ScDec (P y)) -> (d : Nat) ->
    ((x : A) -> ScLe (scCount B P decide (block x)) d) -> (xs : List A) ->
    ScLe (scCount B P decide (scExpand A B block xs)) d :=
  fun A B block P decide d bounded xs =>
    scCountExpandBound A B block P decide d bounded xs
""", "mismatch"),
    ('fiber-product-wrong-coordinate', """
def badFiber : (0 A : Type 0) -> (0 P : Pair A A -> Type 0) ->
    (decide : (p : Pair A A) -> ScDec (P p)) -> (xs : List A) -> (ys : List A) ->
    Eq Nat (scCount (Pair A A) P decide (scProduct A A xs ys))
      (scSumOver A (fun x => scCount A (fun y => P (pair A A y x))
        (fun y => decide (pair A A y x)) ys) xs) :=
  fun A P decide xs ys => scCountProduct A A P decide xs ys
""", "mismatch"),
    ('counting-algebra', COUNTING_ALGEBRA_CHECKS, None),
    ('counting-algebra-examples', COUNTING_ALGEBRA_EXAMPLES, None),
    ("count-mono-reversed", """def badMono : (0 A : Type 0) -> (0 P : A -> Type 0) ->
    (0 Q : A -> Type 0) -> ((x : A) -> P x -> Q x) ->
    (dp : (x : A) -> ScDec (P x)) -> (dq : (x : A) -> ScDec (Q x)) ->
    (xs : List A) -> ScLe (scCount A Q dq xs) (scCount A P dp xs) :=
  fun A P Q implies dp dq xs => scCountMono A P Q implies dp dq xs
""", "mismatch"),
    ("count-equivalence-missing-reverse", """def badEquivalent : (0 A : Type 0) -> (0 P : A -> Type 0) ->
    (0 Q : A -> Type 0) -> ((x : A) -> P x -> Q x) ->
    ((x : A) -> P x -> Q x) -> (dp : (x : A) -> ScDec (P x)) ->
    (dq : (x : A) -> ScDec (Q x)) -> (xs : List A) ->
    Eq Nat (scCount A P dp xs) (scCount A Q dq xs) :=
  fun A P Q forward backward dp dq xs => scCountEquivalent A P Q forward backward dp dq xs
""", "mismatch"),
    ("union-bound-omits-right-count", """def badUnion : (0 A : Type 0) -> (0 P : A -> Type 0) ->
    (0 Q : A -> Type 0) -> (dp : (x : A) -> ScDec (P x)) ->
    (dq : (x : A) -> ScDec (Q x)) -> (xs : List A) ->
    ScLe (scCount A (fun x => ScEither (P x) (Q x))
        (fun x => scEitherDec (P x) (Q x) (dp x) (dq x)) xs)
      (scCount A P dp xs) :=
  fun A P Q dp dq xs => scCountUnionBound A P Q dp dq xs
""", "mismatch"),
    ('vector-word-counts', PRODUCT_EXAMPLE + """def scMapAppendAt : (0 A : Type 0) -> (0 B : Type 0) -> (f : A -> B) ->
    (xs : List A) -> (ys : List A) ->
    Eq (List B) (scMap A B f (scAppend A xs ys))
      (scAppend B (scMap A B f xs) (scMap A B f ys)) :=
  fun A B f xs ys => scMapAppend A B f xs ys

def scMapComposeAt : (0 A : Type 0) -> (0 B : Type 0) -> (0 C : Type 0) ->
    (f : A -> B) -> (g : B -> C) -> (xs : List A) ->
    Eq (List C) (scMap B C g (scMap A B f xs))
      (scMap A C (fun x => g (f x)) xs) :=
  fun A B C f g xs => scMapCompose A B C f g xs

def scMapExpandAt : (0 A : Type 0) -> (0 B : Type 0) -> (0 C : Type 0) ->
    (f : B -> C) -> (block : A -> List B) -> (target : A -> List C) ->
    ((x : A) -> Eq (List C) (scMap B C f (block x)) (target x)) ->
    (xs : List A) -> Eq (List C) (scMap B C f (scExpand A B block xs))
      (scExpand A C target xs) :=
  fun A B C f block target equal xs => scMapExpand A B C f block target equal xs

def scVectorEnumerationAt : (0 A : Type 0) -> (finite : ScFinite A) -> (n : Nat) ->
    Eq (List (List A))
      (scMap (ScVector A n) (List A) (scVectorList A n)
        (scElements (ScVector A n) (scVectorFinite A finite n)))
      (scWords A (scElements A finite) n) :=
  fun A finite n => scVectorEnumeration A finite n

def scCountMapAt : (0 A : Type 0) -> (0 B : Type 0) -> (f : A -> B) ->
    (0 P : B -> Type 0) -> (decide : (y : B) -> ScDec (P y)) -> (xs : List A) ->
    Eq Nat (scCount A (fun x => P (f x)) (fun x => decide (f x)) xs)
      (scCount B P decide (scMap A B f xs)) :=
  fun A B f P decide xs => scCountMap A B f P decide xs

def scVectorWordCountAt : (0 A : Type 0) -> (finite : ScFinite A) -> (n : Nat) ->
    (0 P : List A -> Type 0) -> (decide : (xs : List A) -> ScDec (P xs)) ->
    Eq Nat
      (scFiniteCount (ScVector A n) (fun v => P (scVectorList A n v))
        (fun v => decide (scVectorList A n v)) (scVectorFinite A finite n))
      (scCount (List A) P decide (scWords A (scElements A finite) n)) :=
  fun A finite n P decide => scVectorWordCount A finite n P decide

def enumBits : Eq (List (List ScBit))
    (scMap (ScVector ScBit twoN) (List ScBit) (scVectorList ScBit twoN)
      (scElements (ScVector ScBit twoN) (scVectorFinite ScBit scBitFinite twoN)))
    (scWords ScBit scBits twoN) := scVectorEnumeration ScBit scBitFinite twoN
def enumEmptyZero : Eq (List (List ScEmpty))
    (scMap (ScVector ScEmpty zero) (List ScEmpty) (scVectorList ScEmpty zero)
      (scElements (ScVector ScEmpty zero) (scVectorFinite ScEmpty emptyProductFactor zero)))
    (cons (List ScEmpty) (nil ScEmpty) (nil (List ScEmpty))) :=
  scVectorEnumeration ScEmpty emptyProductFactor zero
def enumEmptyTwo : Eq (List (List ScEmpty))
    (scMap (ScVector ScEmpty twoN) (List ScEmpty) (scVectorList ScEmpty twoN)
      (scElements (ScVector ScEmpty twoN) (scVectorFinite ScEmpty emptyProductFactor twoN)))
    (nil (List ScEmpty)) := scVectorEnumeration ScEmpty emptyProductFactor twoN

def allWordCount : Eq Nat
    (scFiniteCount (ScVector ScBit twoN) (fun v => ScUnit)
      (fun v => scYes ScUnit scUnit) (scVectorFinite ScBit scBitFinite twoN))
    (scCount (List ScBit) (fun xs => ScUnit) (fun xs => scYes ScUnit scUnit) (scWords ScBit scBits twoN)) :=
  scVectorWordCount ScBit scBitFinite twoN (fun xs => ScUnit) (fun xs => scYes ScUnit scUnit)

def noneWordCount : Eq Nat
    (scFiniteCount (ScVector ScBit twoN) (fun v => ScEmpty)
      (fun v => scNo ScEmpty (fun h => h)) (scVectorFinite ScBit scBitFinite twoN))
    (scCount (List ScBit) (fun xs => ScEmpty) (fun xs => scNo ScEmpty (fun h => h)) (scWords ScBit scBits twoN)) :=
  scVectorWordCount ScBit scBitFinite twoN (fun xs => ScEmpty) (fun xs => scNo ScEmpty (fun h => h))

def headHighWordCount : Eq Nat
    (scFiniteCount (ScVector ScBit twoN) (fun v => Eq ScBit (scHeadOr ScBit scLow (scVectorList ScBit twoN v)) scHigh)
      (fun v => scBitDecEq (scHeadOr ScBit scLow (scVectorList ScBit twoN v)) scHigh) (scVectorFinite ScBit scBitFinite twoN))
    (scCount (List ScBit) (fun xs => Eq ScBit (scHeadOr ScBit scLow xs) scHigh) (fun xs => scBitDecEq (scHeadOr ScBit scLow xs) scHigh) (scWords ScBit scBits twoN)) :=
  scVectorWordCount ScBit scBitFinite twoN (fun xs => Eq ScBit (scHeadOr ScBit scLow xs) scHigh) (fun xs => scBitDecEq (scHeadOr ScBit scLow xs) scHigh)
""", None),
    ('vector-word-count-wrong-predicate', PRODUCT_EXAMPLE + """
def wrongPredicate : Eq Nat
    (scFiniteCount (ScVector ScBit twoN) (fun v => ScUnit)
      (fun v => scYes ScUnit scUnit) (scVectorFinite ScBit scBitFinite twoN))
    (scCount (List ScBit) (fun xs => ScEmpty) (fun xs => scNo ScEmpty (fun h => h))
      (scWords ScBit scBits twoN)) :=
  scVectorWordCount ScBit scBitFinite twoN (fun xs => ScUnit) (fun xs => scYes ScUnit scUnit)
""", 'mismatch'),
    ('vector-enumeration-wrong-rounds', PRODUCT_EXAMPLE + """
def wrongEnumeration : Eq (List (List ScBit))
    (scMap (ScVector ScBit twoN) (List ScBit) (scVectorList ScBit twoN)
      (scElements (ScVector ScBit twoN) (scVectorFinite ScBit scBitFinite twoN)))
    (scWords ScBit scBits oneN) := scVectorEnumeration ScBit scBitFinite twoN
""", 'mismatch'),
    ("finite-vectors", VECTOR_CHECKS, None),
    ("vector-missing-coordinate", VECTOR_EXAMPLE + """
def missingCoordinate : ScVector ScBit twoN := pair ScBit ScUnit scHigh scUnit
""", "mismatch"),
    ("vector-wrong-cardinality", VECTOR_EXAMPLE + """
def wrongVectorSize : Eq Nat (scCardinality (ScVector ScBit twoN) bitVectors) twoN :=
  scVectorCardinality ScBit scBitFinite twoN
""", "mismatch"),
    ("vector-wrong-round-count", VECTOR_EXAMPLE + """
def wrongVectorRound : scMember (List ScBit) vectorWord (scWords ScBit scBits oneN) :=
  scVectorWordMember ScBit scBitFinite twoN vectorHL
""", "mismatch"),
    ("vector-injectivity-forged-input", VECTOR_EXAMPLE + """
def forgedVectorEquality : Eq (ScVector ScBit twoN) vectorHL
    (pair ScBit (ScVector ScBit oneN) scHigh (pair ScBit ScUnit scHigh scUnit)) :=
  scVectorListInjective ScBit twoN vectorHL
    (pair ScBit (ScVector ScBit oneN) scHigh (pair ScBit ScUnit scHigh scUnit))
    (refl (List ScBit) vectorWord)
""", "mismatch"),
    ("finite-products", PRODUCT_CHECKS, None),
    ("product-wrong-cardinality", PRODUCT_EXAMPLE + """
def badCardinality : Eq Nat (scCardinality (Pair ScBit ScBit) bitProduct) twoN :=
  refl Nat twoN
""", "mismatch"),
    ("product-equality-ignores-second", PRODUCT_EXAMPLE + """
def forgedPairEquality : ScDec (Eq (Pair ScBit ScBit)
    (pair ScBit ScBit scLow scLow) (pair ScBit ScBit scLow scHigh)) :=
  scYes _ (refl (Pair ScBit ScBit) (pair ScBit ScBit scLow scLow))
""", "mismatch"),
    ("product-equality-ignores-first", PRODUCT_EXAMPLE + """
def forgedPairEquality : ScDec (Eq (Pair ScBit ScBit)
    (pair ScBit ScBit scLow scLow) (pair ScBit ScBit scHigh scLow)) :=
  scYes _ (refl (Pair ScBit ScBit) (pair ScBit ScBit scLow scLow))
""", "mismatch"),
    ("product-wrong-predicate-count", PRODUCT_EXAMPLE + """
def badPairCount : Eq Nat (scFiniteCount (Pair ScBit ScBit)
    (fun p => Eq (Pair ScBit ScBit) p targetPair)
    (fun p => scDecEq (Pair ScBit ScBit) bitProduct p targetPair) bitProduct) twoN :=
  refl Nat twoN
""", "mismatch"),
    ("enumeration-uniqueness", EXAMPLE + """
def productMember : scMember (Pair ScBit ScBit) (pair ScBit ScBit scHigh scLow)
    (scProduct ScBit ScBit scBits scBits) :=
  scProductComplete ScBit ScBit scBits scBits scHigh scLow
    (scBitsComplete scHigh) (scBitsComplete scLow)
def productUnique : scNoDup (Pair ScBit ScBit) (scProduct ScBit ScBit scBits scBits) :=
  scProductUnique ScBit ScBit scBits scBits scBitsUnique scBitsUnique
def emptyLeftUnique : scNoDup (Pair ScEmpty ScBit)
    (scProduct ScEmpty ScBit (nil ScEmpty) scBits) :=
  scProductUnique ScEmpty ScBit (nil ScEmpty) scBits scUnit scBitsUnique
def emptyRightUnique : scNoDup (Pair ScBit ScEmpty)
    (scProduct ScBit ScEmpty scBits (nil ScEmpty)) :=
  scProductUnique ScBit ScEmpty scBits (nil ScEmpty) scBitsUnique scUnit
def wordsUnique : scNoDup (List ScBit) (scWords ScBit scBits twoN) :=
  scFiniteWordsUnique ScBit scBitFinite twoN
def zeroWordsUnique : scNoDup (List ScEmpty) (scWords ScEmpty (nil ScEmpty) zero) :=
  scWordsUnique ScEmpty (nil ScEmpty) scUnit zero
def emptyWordsUnique : scNoDup (List ScEmpty) (scWords ScEmpty (nil ScEmpty) twoN) :=
  scWordsUnique ScEmpty (nil ScEmpty) scUnit twoN
-- Uniqueness exposes a usable refutation, including nonadjacent duplicates.
def lowLowNotInTail : scMember (List ScBit)
    (cons ScBit scLow (cons ScBit scLow (nil ScBit)))
    (scTail (List ScBit) (scWords ScBit scBits twoN)) -> ScEmpty :=
  scFirst
    (scMember (List ScBit) (cons ScBit scLow (cons ScBit scLow (nil ScBit)))
      (scTail (List ScBit) (scWords ScBit scBits twoN)) -> ScEmpty)
    (scNoDup (List ScBit) (scTail (List ScBit) (scWords ScBit scBits twoN))) wordsUnique
""", None),
    ("uniqueness-missing-head-obligation", """
def forgedUnique : scNoDup ScBit scBits :=
  pair ScUnit (scNoDup ScBit (cons ScBit scHigh (nil ScBit))) scUnit
    (pair (ScEmpty -> ScEmpty) ScUnit (fun impossible => impossible) scUnit)
""", "mismatch"),
    ("uniqueness-missing-tail-obligation", """
def forgedUniqueTail : scNoDup ScBit scBits :=
  pair (scMember ScBit scLow (cons ScBit scHigh (nil ScBit)) -> ScEmpty) ScUnit
    (fun member => match member with
      | scLeft h => scLowNeHigh h | scRight impossible => impossible end) scUnit
""", "mismatch"),
    ("map-noninjective", """
def forgedMapUnique : scNoDup ScBit (scMap ScBit ScBit (fun x => scLow) scBits) :=
  scNoDupMap ScBit ScBit (fun x => scLow)
    (fun x y h => refl ScBit x) scBits scBitsUnique
""", "mismatch"),
    ("append-overlapping", """
def forgedAppendUnique : scNoDup ScBit (scAppend ScBit scBits scBits) :=
  scNoDupAppend ScBit scBits scBits scBitsUnique scBitsUnique
    (fun x left right => scUnit)
""", "mismatch"),
    ("word-enumeration-evidence", EXAMPLE + """
reducible def highLow : List ScBit := cons ScBit scHigh (cons ScBit scLow (nil ScBit))
def highLowMember : scMember (List ScBit) highLow (scWords ScBit scBits twoN) :=
  scFiniteWordsComplete ScBit scBitFinite highLow
def highLowLength : Eq Nat (scLength ScBit highLow) twoN :=
  scWordLength ScBit scBits twoN highLow highLowMember
def emptyWordMember : scMember (List ScEmpty) (nil ScEmpty)
    (scWords ScEmpty (nil ScEmpty) zero) :=
  scWordsComplete ScEmpty (nil ScEmpty) (nil ScEmpty) scUnit
reducible def repeatedAlphabet : List ScBit :=
  cons ScBit scHigh (cons ScBit scHigh (nil ScBit))
reducible def highOnly : List ScBit := cons ScBit scHigh (nil ScBit)
def repeatedMember : scMember (List ScBit) highOnly
    (scWords ScBit repeatedAlphabet oneN) :=
  scWordsCompleteAt ScBit repeatedAlphabet oneN highOnly (refl Nat oneN)
    (pair (scMember ScBit scHigh repeatedAlphabet) ScUnit
      (scLeft (Eq ScBit scHigh scHigh)
        (scMember ScBit scHigh (cons ScBit scHigh (nil ScBit))) (refl ScBit scHigh)) scUnit)
def repeatedLength : Eq Nat (scLength ScBit highOnly) oneN :=
  scWordLength ScBit repeatedAlphabet oneN highOnly repeatedMember
def emptyWordLength : Eq Nat (scLength ScEmpty (nil ScEmpty)) zero :=
  scWordLength ScEmpty (nil ScEmpty) zero (nil ScEmpty) emptyWordMember
-- Membership in the tail exercises equality transport and recursive evidence.
def tailLength : Eq Nat (scLength ScBit highLow) twoN :=
  scAllMember (List ScBit) (fun w => Eq Nat (scLength ScBit w) twoN)
    (cons (List ScBit) highLow (cons (List ScBit) highLow (nil (List ScBit))))
    (pair (Eq Nat twoN twoN) (Pair (Eq Nat twoN twoN) ScUnit)
      (refl Nat twoN) (pair (Eq Nat twoN twoN) ScUnit (refl Nat twoN) scUnit))
    highLow (scRight (Eq (List ScBit) highLow highLow)
      (ScEither (Eq (List ScBit) highLow highLow) ScEmpty)
      (scLeft (Eq (List ScBit) highLow highLow) ScEmpty (refl (List ScBit) highLow)))
""", None),
    ("word-wrong-round-count", EXAMPLE + """
def wrongRoundMember : scMember (List ScBit) (cons ScBit scHigh (nil ScBit))
    (scWords ScBit scBits twoN) :=
  scFiniteWordsComplete ScBit scBitFinite (cons ScBit scHigh (nil ScBit))
""", "mismatch"),
    ("word-missing-alphabet-evidence", """
def forgedAlphabetEvidence : scAll ScBit (fun x => scMember ScBit x (nil ScBit))
    (cons ScBit scHigh (nil ScBit)) := pair ScUnit ScUnit scUnit scUnit
""", "mismatch"),
    ("word-missing-tail-evidence", """
def forgedTailEvidence : scAll ScBit (fun x => Eq ScBit x scHigh)
    (cons ScBit scHigh (cons ScBit scLow (nil ScBit))) :=
  pair (Eq ScBit scHigh scHigh) ScUnit (refl ScBit scHigh) scUnit
""", "mismatch"),
    ("products-and-words", EXAMPLE + """
def bitProductSize : Eq Nat
    (scLength (Pair ScBit ScBit) (scProduct ScBit ScBit scBits scBits)) fourN :=
  scProductLength ScBit ScBit scBits scBits
def emptyLeftProduct : Eq Nat
    (scLength (Pair ScBit ScBit) (scProduct ScBit ScBit (nil ScBit) scBits)) zero :=
  scProductLength ScBit ScBit (nil ScBit) scBits
def emptyRightProduct : Eq Nat
    (scLength (Pair ScBit ScBit) (scProduct ScBit ScBit scBits (nil ScBit))) zero :=
  scProductLength ScBit ScBit scBits (nil ScBit)
def productContents : Eq (List (Pair ScBit ScBit))
    (scProduct ScBit ScBit scBits (cons ScBit scHigh (nil ScBit)))
    (cons (Pair ScBit ScBit) (pair ScBit ScBit scLow scHigh)
      (cons (Pair ScBit ScBit) (pair ScBit ScBit scHigh scHigh)
        (nil (Pair ScBit ScBit)))) :=
  refl (List (Pair ScBit ScBit))
    (cons (Pair ScBit ScBit) (pair ScBit ScBit scLow scHigh)
      (cons (Pair ScBit ScBit) (pair ScBit ScBit scHigh scHigh)
        (nil (Pair ScBit ScBit))))
reducible def bitWord : ScBit -> ScBit -> List ScBit :=
  fun x y => cons ScBit x (cons ScBit y (nil ScBit))
reducible def expectedWords : List (List ScBit) :=
  cons (List ScBit) (bitWord scLow scLow)
    (cons (List ScBit) (bitWord scLow scHigh)
      (cons (List ScBit) (bitWord scHigh scLow)
        (cons (List ScBit) (bitWord scHigh scHigh) (nil (List ScBit)))))
def wordContents : Eq (List (List ScBit)) (scWords ScBit scBits twoN) expectedWords :=
  refl (List (List ScBit)) expectedWords
def bitWordSize : Eq Nat (scLength (List ScBit) (scWords ScBit scBits twoN)) fourN :=
  scWordsLength ScBit scBits twoN
def zeroRoundEmptyAlphabet : Eq Nat
    (scLength (List ScEmpty) (scWords ScEmpty (nil ScEmpty) zero)) oneN :=
  scWordsLength ScEmpty (nil ScEmpty) zero
def positiveRoundsEmptyAlphabet : Eq Nat
    (scLength (List ScEmpty) (scWords ScEmpty (nil ScEmpty) twoN)) zero :=
  scWordsLength ScEmpty (nil ScEmpty) twoN
def allWordCount : Eq Nat
    (scCount (List ScBit) (fun word => ScUnit) (fun word => scYes ScUnit scUnit)
      (scWords ScBit scBits twoN)) fourN := refl Nat fourN
def wordCountBound : ScLe
    (scCount (List ScBit) (fun word => ScUnit) (fun word => scYes ScUnit scUnit)
      (scWords ScBit scBits twoN)) (scPow (scCardinality ScBit scBitFinite) twoN) :=
  scWordCountBound ScBit (fun word => ScUnit) (fun word => scYes ScUnit scUnit)
    (scElements ScBit scBitFinite) twoN
""", None),
    ("wrong-product-size", EXAMPLE + """
def wrongProductSize : Eq Nat
    (scLength (Pair ScBit ScBit) (scProduct ScBit ScBit scBits scBits)) twoN :=
  refl Nat twoN
""", "mismatch"),
    ("wrong-word-size", EXAMPLE + """
def wrongWordSize : Eq Nat (scLength (List ScBit) (scWords ScBit scBits twoN)) twoN :=
  refl Nat twoN
""", "mismatch"),
    ("wrong-zero-round-size", """
def wrongZeroRoundSize : Eq Nat
    (scLength (List ScEmpty) (scWords ScEmpty (nil ScEmpty) zero)) zero := refl Nat zero
""", "mismatch"),
    ("finite-counts", """
reducible def emptyFinite : ScFinite ScEmpty :=
  scFinite ScEmpty (nil ScEmpty)
    (fun x => match x with end) scUnit
    (fun x y => match x with end)
def emptyCardinality : Eq Nat (scCardinality ScEmpty emptyFinite) zero :=
  refl Nat zero
def bitCardinality : Eq Nat (scCardinality ScBit scBitFinite) (succ (succ zero)) :=
  refl Nat (succ (succ zero))
def emptyCount : Eq Nat
    (scCount ScBit (fun x => ScUnit) (fun x => scYes ScUnit scUnit) (nil ScBit))
    zero := refl Nat zero
def allCount : Eq Nat
    (scFiniteCount ScBit (fun x => ScUnit) (fun x => scYes ScUnit scUnit) scBitFinite)
    (succ (succ zero)) := refl Nat (succ (succ zero))
def noneCount : Eq Nat
    (scFiniteCount ScBit (fun x => ScEmpty)
      (fun x => scNo ScEmpty (fun impossible => impossible)) scBitFinite)
    zero := refl Nat zero
def highCount : Eq Nat
    (scFiniteCount ScBit (fun x => Eq ScBit x scHigh)
      (fun x => scBitDecEq x scHigh) scBitFinite)
    (succ zero) := refl Nat (succ zero)
def lowCount : Eq Nat
    (scFiniteCount ScBit (fun x => Eq ScBit x scLow)
      (fun x => scDecEq ScBit scBitFinite x scLow) scBitFinite)
    (succ zero) := refl Nat (succ zero)
def concreteCountBound : ScLe
    (scFiniteCount ScBit (fun x => Eq ScBit x scHigh)
      (fun x => scBitDecEq x scHigh) scBitFinite)
    (scCardinality ScBit scBitFinite) :=
  scFiniteCountBound ScBit (fun x => Eq ScBit x scHigh)
    (fun x => scBitDecEq x scHigh) scBitFinite
""", None),
    ("missing-element", """
def missingHigh : scMember ScBit scHigh (cons ScBit scLow (nil ScBit)) :=
  scLeft (Eq ScBit scHigh scLow) ScEmpty (refl ScBit scHigh)
""", "mismatch"),
    ("duplicate-enumeration", """
def duplicateUnique : scNoDup ScBit
    (cons ScBit scLow (cons ScBit scLow (nil ScBit))) :=
  pair (scMember ScBit scLow (cons ScBit scLow (nil ScBit)) -> ScEmpty)
    (scNoDup ScBit (cons ScBit scLow (nil ScBit)))
    (fun member => match member with
      | scLeft h => scLowNeHigh h | scRight impossible => impossible end)
    (pair (ScEmpty -> ScEmpty) ScUnit (fun impossible => impossible) scUnit)
""", "mismatch"),
    ("false-equality-decision", """
def falseDecision : ScDec (Eq ScBit scLow scHigh) :=
  scYes (Eq ScBit scLow scHigh) (refl ScBit scLow)
""", "mismatch"),
    ("wrong-count", """
def wrongCount : Eq Nat
    (scFiniteCount ScBit (fun x => Eq ScBit x scHigh)
      (fun x => scBitDecEq x scHigh) scBitFinite)
    zero := refl Nat zero
""", "mismatch"),
    ("false-order-bound", """
def falseBound : ScLe (succ zero) zero := scLeZero zero
""", "mismatch"),
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
