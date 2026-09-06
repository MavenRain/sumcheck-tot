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
                  "Recurrence.tot"))
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

CASES = [
    ("generic-proofs", "", None),
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
