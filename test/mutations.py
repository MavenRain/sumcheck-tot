"""Check that enumeration and counting proofs catch deliberate source mutations."""
import tempfile

import check


# Replacements apply to the in-memory concatenation, never to source files.
# Challenge mutations preserve enumeration cardinality but corrupt word contents.
# Abstract-argument checks pin statements without generic consumers;
# other weakened statements are rejected by downstream proofs.
MUTATIONS = [
    ('scSumOverMono-trivialized', """def rec scSumOverMono : (0 A : Type 0) -> (f : A -> Nat) -> (g : A -> Nat) ->
    ((x : A) -> ScLe (f x) (g x)) -> (xs : List A) ->
    ScLe (scSumOver A f xs) (scSumOver A g xs) :=
  fun A f g bounded xs => match xs as ys return
      ScLe (scSumOver A f ys) (scSumOver A g ys) with
  | nil => scLeZero zero
  | cons x rest => scAddLe (f x) (g x) (bounded x)
      (scSumOver A f rest) (scSumOver A g rest)
      (scSumOverMono A f g bounded rest)
  end""",
     """def scSumOverMono : (0 A : Type 0) -> (f : A -> Nat) -> (g : A -> Nat) ->
    ((x : A) -> ScLe (f x) (g x)) -> (xs : List A) ->
    ScLe zero zero :=
  fun A f g bounded xs => scLeZero zero""", 1),
    ('scSumOverConstant-trivialized', """def rec scSumOverConstant : (0 A : Type 0) -> (b : Nat) -> (xs : List A) ->
    Eq Nat (scSumOver A (fun x => b) xs) (scMul (scLength A xs) b) :=
  fun A b xs => match xs as ys return
      Eq Nat (scSumOver A (fun x => b) ys) (scMul (scLength A ys) b) with
  | nil => refl Nat zero
  | cons x rest => scCong Nat Nat (scAdd b)
      (scSumOver A (fun x => b) rest) (scMul (scLength A rest) b)
      (scSumOverConstant A b rest)
  end""",
     """def scSumOverConstant : (0 A : Type 0) -> (b : Nat) -> (xs : List A) ->
    Eq Nat zero zero :=
  fun A b xs => refl Nat zero""", 1),
    ('scExceptionAllowanceSum-trivialized', """def rec scExceptionAllowanceSum : (0 A : Type 0) -> (0 P : A -> Type 0) ->
    (decide : (x : A) -> ScDec (P x)) -> (cap : Nat) -> (xs : List A) ->
    Eq Nat (scSumOver A (fun x => scExceptionAllowance (P x) (decide x) cap) xs)
      (scMul (scCount A P decide xs) cap) :=
  fun A P decide cap xs => match xs as ys return
      Eq Nat (scSumOver A (fun x => scExceptionAllowance (P x) (decide x) cap) ys)
        (scMul (scCount A P decide ys) cap) with
  | nil => refl Nat zero
  | cons x rest => match decide x as d return
      Eq Nat (scAdd (scExceptionAllowance (P x) d cap)
        (scSumOver A (fun y => scExceptionAllowance (P y) (decide y) cap) rest))
        (scMul (scTally (P x) d (scCount A P decide rest)) cap) with
    | scYes proof => scCong Nat Nat (scAdd cap)
        (scSumOver A (fun y => scExceptionAllowance (P y) (decide y) cap) rest)
        (scMul (scCount A P decide rest) cap)
        (scExceptionAllowanceSum A P decide cap rest)
    | scNo refute => scExceptionAllowanceSum A P decide cap rest
    end
  end""",
     """def scExceptionAllowanceSum : (0 A : Type 0) -> (0 P : A -> Type 0) ->
    (decide : (x : A) -> ScDec (P x)) -> (cap : Nat) -> (xs : List A) ->
    Eq Nat zero zero :=
  fun A P decide cap xs => refl Nat zero""", 1),
    ('scExceptionPointBound-trivialized', """def scExceptionPointBound : (0 P : Type 0) -> (decision : ScDec P) ->
    (weight : Nat) -> (cap : Nat) -> (b : Nat) -> ScLe weight cap ->
    ((P -> ScEmpty) -> ScLe weight b) ->
    ScLe weight (scAdd b (scExceptionAllowance P decision cap)) :=
  fun P decision weight cap b bounded outside => match decision as d return
      ScLe weight (scAdd b (scExceptionAllowance P d cap)) with
  | scYes proof => scLeAddLeft b weight cap bounded
  | scNo refute => scTransport Nat b (scAdd b zero) (fun upper => ScLe weight upper)
      (scEqSym Nat (scAdd b zero) b (scAddZeroRight b)) (outside refute)
  end""",
     """def scExceptionPointBound : (0 P : Type 0) -> (decision : ScDec P) ->
    (weight : Nat) -> (cap : Nat) -> (b : Nat) -> ScLe weight cap ->
    ((P -> ScEmpty) -> ScLe weight b) ->
    ScLe zero zero :=
  fun P decision weight cap b bounded outside => scLeZero zero""", 1),
    ('scSumOverExceptionalBound-trivialized', """def scSumOverExceptionalBound : (0 A : Type 0) -> (0 P : A -> Type 0) ->
    (decide : (x : A) -> ScDec (P x)) -> (weight : A -> Nat) ->
    (cap : Nat) -> (b : Nat) -> ((x : A) -> ScLe (weight x) cap) ->
    ((x : A) -> (P x -> ScEmpty) -> ScLe (weight x) b) -> (xs : List A) ->
    ScLe (scSumOver A weight xs)
      (scAdd (scMul (scCount A P decide xs) cap) (scMul (scLength A xs) b)) :=
  fun A P decide weight cap b bounded outside xs => scTransport Nat
    (scSumOver A (fun x => scAdd b (scExceptionAllowance (P x) (decide x) cap)) xs)
    (scAdd (scMul (scCount A P decide xs) cap) (scMul (scLength A xs) b))
    (fun upper => ScLe (scSumOver A weight xs) upper)
    (scEqTrans Nat
      (scSumOver A (fun x => scAdd b (scExceptionAllowance (P x) (decide x) cap)) xs)
      (scAdd (scSumOver A (fun x => b) xs)
        (scSumOver A (fun x => scExceptionAllowance (P x) (decide x) cap) xs))
      (scAdd (scMul (scCount A P decide xs) cap) (scMul (scLength A xs) b))
      (scSumOverAdd A (fun x => b)
        (fun x => scExceptionAllowance (P x) (decide x) cap) xs)
      (scEqTrans Nat
        (scAdd (scSumOver A (fun x => b) xs)
          (scSumOver A (fun x => scExceptionAllowance (P x) (decide x) cap) xs))
        (scAdd (scMul (scLength A xs) b) (scMul (scCount A P decide xs) cap))
        (scAdd (scMul (scCount A P decide xs) cap) (scMul (scLength A xs) b))
        (scEqTrans Nat
          (scAdd (scSumOver A (fun x => b) xs)
            (scSumOver A (fun x => scExceptionAllowance (P x) (decide x) cap) xs))
          (scAdd (scMul (scLength A xs) b)
            (scSumOver A (fun x => scExceptionAllowance (P x) (decide x) cap) xs))
          (scAdd (scMul (scLength A xs) b) (scMul (scCount A P decide xs) cap))
          (scCong Nat Nat
            (fun total => scAdd total
              (scSumOver A (fun x => scExceptionAllowance (P x) (decide x) cap) xs))
            (scSumOver A (fun x => b) xs) (scMul (scLength A xs) b)
            (scSumOverConstant A b xs))
          (scCong Nat Nat (scAdd (scMul (scLength A xs) b))
            (scSumOver A (fun x => scExceptionAllowance (P x) (decide x) cap) xs)
            (scMul (scCount A P decide xs) cap)
            (scExceptionAllowanceSum A P decide cap xs)))
        (scAddComm (scMul (scLength A xs) b) (scMul (scCount A P decide xs) cap))))
    (scSumOverMono A weight
      (fun x => scAdd b (scExceptionAllowance (P x) (decide x) cap))
      (fun x => scExceptionPointBound (P x) (decide x) (weight x) cap b
        (bounded x) (outside x)) xs)""",
     """def scSumOverExceptionalBound : (0 A : Type 0) -> (0 P : A -> Type 0) ->
    (decide : (x : A) -> ScDec (P x)) -> (weight : A -> Nat) ->
    (cap : Nat) -> (b : Nat) -> ((x : A) -> ScLe (weight x) cap) ->
    ((x : A) -> (P x -> ScEmpty) -> ScLe (weight x) b) -> (xs : List A) ->
    ScLe zero zero :=
  fun A P decide weight cap b bounded outside xs => scLeZero zero""", 1),
    ('scAcceptingRoundBound-trivialized', """def scAcceptingRoundBound : (0 F : Type 0) -> (finite : ScFinite F) ->
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
  fun F finite plus lo hi n message next g claim P decide d b rare outside =>
    match scDecEq F finite (plus (message lo) (message hi)) claim with
    | scYes valid => scTransport Nat
        (scSumOver F (fun r => scAcceptingCount F finite plus lo hi n
          (next r) (scRestrict F g r) (message r)) (scElements F finite))
        (scAcceptingCount F finite plus lo hi (succ n)
          (pair (F -> F) (F -> ScStrategy F n) message next) g claim)
        (fun total => ScLe total
          (scAdd (scMul d (scPow (scCardinality F finite) n))
            (scMul (scCardinality F finite) b)))
        (scEqSym Nat (scAcceptingCount F finite plus lo hi (succ n)
          (pair (F -> F) (F -> ScStrategy F n) message next) g claim)
          (scSumOver F (fun r => scAcceptingCount F finite plus lo hi n
            (next r) (scRestrict F g r) (message r)) (scElements F finite))
          (scAcceptingCountStep F finite plus lo hi n message next g claim valid))
        (scLeTrans
          (scSumOver F (fun r => scAcceptingCount F finite plus lo hi n
            (next r) (scRestrict F g r) (message r)) (scElements F finite))
          (scAdd (scMul (scFiniteCount F P decide finite)
            (scPow (scCardinality F finite) n)) (scMul (scCardinality F finite) b))
          (scSumOverExceptionalBound F P decide
            (fun r => scAcceptingCount F finite plus lo hi n
              (next r) (scRestrict F g r) (message r))
            (scPow (scCardinality F finite) n) b
            (fun r => scAcceptingCountBound F finite plus lo hi n
              (next r) (scRestrict F g r) (message r)) outside (scElements F finite))
          (scAdd (scMul d (scPow (scCardinality F finite) n))
            (scMul (scCardinality F finite) b))
          (scAddLe
            (scMul (scFiniteCount F P decide finite) (scPow (scCardinality F finite) n))
            (scMul d (scPow (scCardinality F finite) n))
            (scMulMonoRight (scFiniteCount F P decide finite) d rare
              (scPow (scCardinality F finite) n))
            (scMul (scCardinality F finite) b) (scMul (scCardinality F finite) b)
            (scLeRefl (scMul (scCardinality F finite) b))))
    | scNo invalid => scTransport Nat zero
        (scAcceptingCount F finite plus lo hi (succ n)
          (pair (F -> F) (F -> ScStrategy F n) message next) g claim)
        (fun total => ScLe total
          (scAdd (scMul d (scPow (scCardinality F finite) n))
            (scMul (scCardinality F finite) b)))
        (scEqSym Nat (scAcceptingCount F finite plus lo hi (succ n)
          (pair (F -> F) (F -> ScStrategy F n) message next) g claim) zero
          (scRejectedRoundCount F finite plus lo hi n message next g claim invalid))
        (scLeZero (scAdd (scMul d (scPow (scCardinality F finite) n))
          (scMul (scCardinality F finite) b)))
    end""",
     """def scAcceptingRoundBound : (0 F : Type 0) -> (finite : ScFinite F) ->
    (plus : F -> F -> F) -> (lo : F) -> (hi : F) -> (n : Nat) ->
    (message : F -> F) -> (next : F -> ScStrategy F n) ->
    (g : List F -> F) -> (claim : F) -> (0 P : F -> Type 0) ->
    (decide : (r : F) -> ScDec (P r)) -> (d : Nat) -> (b : Nat) ->
    ScLe (scFiniteCount F P decide finite) d ->
    ((r : F) -> (P r -> ScEmpty) ->
      ScLe (scAcceptingCount F finite plus lo hi n (next r)
        (scRestrict F g r) (message r)) b) ->
    ScLe zero zero :=
  fun F finite plus lo hi n message next g claim P decide d b rare outside => scLeZero zero""", 1),
    ("scSumOverZero-trivialized", """def rec scSumOverZero : (0 A : Type 0) -> (xs : List A) ->
    Eq Nat (scSumOver A (fun x => zero) xs) zero :=
  fun A xs => match xs as ys return
      Eq Nat (scSumOver A (fun x => zero) ys) zero with
  | nil => refl Nat zero
  | cons x rest => scSumOverZero A rest
  end""",
     """def scSumOverZero : (0 A : Type 0) -> (xs : List A) ->
    Eq Nat zero zero :=
  fun A xs => refl Nat zero""", 1),
    ("scSumOverAdd-trivialized", """def rec scSumOverAdd : (0 A : Type 0) -> (f : A -> Nat) -> (g : A -> Nat) ->
    (xs : List A) -> Eq Nat (scSumOver A (fun x => scAdd (f x) (g x)) xs)
      (scAdd (scSumOver A f xs) (scSumOver A g xs)) :=
  fun A f g xs => match xs as ys return
      Eq Nat (scSumOver A (fun x => scAdd (f x) (g x)) ys)
        (scAdd (scSumOver A f ys) (scSumOver A g ys)) with
  | nil => refl Nat zero
  | cons x rest => (scEqTrans Nat (scAdd (scAdd (f x) (g x)) (scSumOver A (fun x => scAdd (f x) (g
      x)) rest)) (scAdd (f x) (scAdd (scSumOver A f rest) (scAdd (g x) (scSumOver A g rest))))
      (scAdd (scAdd (f x) (scSumOver A f rest)) (scAdd (g x) (scSumOver A g rest))) (scEqTrans Nat
      (scAdd (scAdd (f x) (g x)) (scSumOver A (fun x => scAdd (f x) (g x)) rest)) (scAdd (f x)
      (scAdd (g x) (scAdd (scSumOver A f rest) (scSumOver A g rest)))) (scAdd (f x) (scAdd
      (scSumOver A f rest) (scAdd (g x) (scSumOver A g rest)))) (scEqTrans Nat (scAdd (scAdd (f x)
      (g x)) (scSumOver A (fun x => scAdd (f x) (g x)) rest)) (scAdd (scAdd (f x) (g x)) (scAdd
      (scSumOver A f rest) (scSumOver A g rest))) (scAdd (f x) (scAdd (g x) (scAdd (scSumOver A f
      rest) (scSumOver A g rest)))) (scCong Nat Nat (scAdd (scAdd (f x) (g x))) (scSumOver A (fun
      x => scAdd (f x) (g x)) rest) (scAdd (scSumOver A f rest) (scSumOver A g rest))
      (scSumOverAdd A f g rest)) (scAddAssoc (f x) (g x) (scAdd (scSumOver A f rest) (scSumOver A
      g rest)))) (scCong Nat Nat (scAdd (f x)) (scAdd (g x) (scAdd (scSumOver A f rest) (scSumOver
      A g rest))) (scAdd (scSumOver A f rest) (scAdd (g x) (scSumOver A g rest))) (scAddSwap (g x)
      (scSumOver A f rest) (scSumOver A g rest)))) (scEqSym Nat (scAdd (scAdd (f x) (scSumOver A f
      rest)) (scAdd (g x) (scSumOver A g rest))) (scAdd (f x) (scAdd (scSumOver A f rest) (scAdd
      (g x) (scSumOver A g rest)))) (scAddAssoc (f x) (scSumOver A f rest) (scAdd (g x) (scSumOver
      A g rest)))))
  end""",
     """def scSumOverAdd : (0 A : Type 0) -> (f : A -> Nat) -> (g : A -> Nat) ->
    (xs : List A) ->
    Eq Nat (scAdd (scSumOver A f xs) (scSumOver A g xs)) (scAdd (scSumOver A f xs) (scSumOver A g xs)) :=
  fun A f g xs => refl Nat (scAdd (scSumOver A f xs) (scSumOver A g xs))""", 1),
    ("scSumOverSwap-trivialized", """def rec scSumOverSwap : (0 A : Type 0) -> (0 B : Type 0) ->
    (weight : A -> B -> Nat) -> (xs : List A) -> (ys : List B) ->
    Eq Nat (scSumOver A (fun x => scSumOver B (weight x) ys) xs)
      (scSumOver B (fun y => scSumOver A (fun x => weight x y) xs) ys) :=
  fun A B weight xs ys => match xs as zs return
      Eq Nat (scSumOver A (fun x => scSumOver B (weight x) ys) zs)
        (scSumOver B (fun y => scSumOver A (fun x => weight x y) zs) ys) with
  | nil => scEqSym Nat (scSumOver B (fun y => zero) ys) zero (scSumOverZero B ys)
  | cons x rest => scEqTrans Nat (scAdd (scSumOver B (weight x) ys) (scSumOver A (fun x =>
      scSumOver B (weight x) ys) rest)) (scAdd (scSumOver B (weight x) ys) (scSumOver B (fun y =>
      scSumOver A (fun x => weight x y) rest) ys)) (scSumOver B (fun y => scAdd (weight x y)
      (scSumOver A (fun x => weight x y) rest)) ys)
      (scCong Nat Nat (scAdd (scSumOver B (weight x) ys)) (scSumOver A (fun x => scSumOver B
          (weight x) ys) rest) (scSumOver B (fun y => scSumOver A (fun x => weight x y) rest) ys)
        (scSumOverSwap A B weight rest ys))
      (scEqSym Nat (scSumOver B (fun y => scAdd (weight x y) (scSumOver A (fun x => weight x y)
          rest)) ys) (scAdd (scSumOver B (weight x) ys) (scSumOver B (fun y => scSumOver A (fun x
          => weight x y) rest) ys))
        (scSumOverAdd B (weight x) (fun y => scSumOver A (fun z => weight z y) rest) ys))
  end""",
     """def scSumOverSwap : (0 A : Type 0) -> (0 B : Type 0) ->
    (weight : A -> B -> Nat) -> (xs : List A) -> (ys : List B) ->
    Eq Nat (scSumOver B (fun y => scSumOver A (fun x => weight x y) xs) ys) (scSumOver B (fun y => scSumOver A (fun x => weight x y) xs) ys) :=
  fun A B weight xs ys => refl Nat (scSumOver B (fun y => scSumOver A (fun x => weight x y) xs) ys)""", 1),
    ("scDiagonalSym-trivialized", """def scDiagonalSym : (0 A : Type 0) ->
    (equal : (x : A) -> (y : A) -> ScDec (Eq A x y)) ->
    (weight : A -> Nat) -> (x : A) -> (y : A) ->
    Eq Nat (scDiagonalWeight A equal weight x y) (scDiagonalWeight A equal weight y x) :=
  fun A equal weight x y => match equal x y as d return
      Eq Nat (match d with | scYes same => weight x | scNo different => zero end)
        (scDiagonalWeight A equal weight y x) with
  | scYes same => match equal y x as e return Eq Nat (weight x)
      (match e with | scYes same => weight y | scNo different => zero end) with
    | scYes reverse => scCong A Nat weight x y same
    | scNo different => match different (scEqSym A x y same) with end
    end
  | scNo different => match equal y x as e return Eq Nat zero
      (match e with | scYes same => weight y | scNo different => zero end) with
    | scYes reverse => match different (scEqSym A y x reverse) with end
    | scNo reject => refl Nat zero
    end
  end""",
     """def scDiagonalSym : (0 A : Type 0) ->
    (equal : (x : A) -> (y : A) -> ScDec (Eq A x y)) ->
    (weight : A -> Nat) -> (x : A) -> (y : A) ->
    Eq Nat (scDiagonalWeight A equal weight y x) (scDiagonalWeight A equal weight y x) :=
  fun A equal weight x y => refl Nat (scDiagonalWeight A equal weight y x)""", 1),
    ("scDiagonalAbsent-trivialized", """def rec scDiagonalAbsent : (0 A : Type 0) ->
    (equal : (x : A) -> (y : A) -> ScDec (Eq A x y)) ->
    (weight : A -> Nat) -> (x : A) -> (xs : List A) ->
    (scMember A x xs -> ScEmpty) ->
    Eq Nat (scSumOver A (scDiagonalWeight A equal weight x) xs) zero :=
  fun A equal weight x xs => match xs as ys return
      (scMember A x ys -> ScEmpty) ->
      Eq Nat (scSumOver A (scDiagonalWeight A equal weight x) ys) zero with
  | nil => fun absent => refl Nat zero
  | cons y rest => fun absent => match equal x y as d return
      Eq Nat (scAdd
        (match d with | scYes same => weight x | scNo different => zero end)
        (scSumOver A (scDiagonalWeight A equal weight x) rest)) zero with
    | scYes same => match absent (scLeft (Eq A x y) (scMember A x rest) same) with end
    | scNo different => scDiagonalAbsent A equal weight x rest
        (fun member => absent (scRight (Eq A x y) (scMember A x rest) member))
    end
  end""",
     """def scDiagonalAbsent : (0 A : Type 0) ->
    (equal : (x : A) -> (y : A) -> ScDec (Eq A x y)) ->
    (weight : A -> Nat) -> (x : A) -> (xs : List A) ->
    (scMember A x xs -> ScEmpty) ->
    Eq Nat zero zero :=
  fun A equal weight x xs absent => refl Nat zero""", 1),
    ("scDiagonalPresent-trivialized", """def rec scDiagonalPresent : (0 A : Type 0) ->
    (equal : (x : A) -> (y : A) -> ScDec (Eq A x y)) ->
    (weight : A -> Nat) -> (x : A) -> (xs : List A) ->
    scNoDup A xs -> scMember A x xs ->
    Eq Nat (scSumOver A (scDiagonalWeight A equal weight x) xs) (weight x) :=
  fun A equal weight x xs => match xs as ys return
      scNoDup A ys -> scMember A x ys ->
      Eq Nat (scSumOver A (scDiagonalWeight A equal weight x) ys) (weight x) with
  | nil => fun unique impossible => match impossible with end
  | cons y rest => fun unique member => match unique with
    | pair absent tail => match equal x y as d return
        Eq Nat (scAdd
          (match d with | scYes same => weight x | scNo different => zero end)
          (scSumOver A (scDiagonalWeight A equal weight x) rest)) (weight x) with
      | scYes same => scEqTrans Nat (scAdd (weight x) (scSumOver A (scDiagonalWeight A equal
          weight x) rest))
          (scAdd (weight x) zero) (weight x)
          (scCong Nat Nat (scAdd (weight x)) (scSumOver A (scDiagonalWeight A equal weight x)
              rest) zero
            (scDiagonalAbsent A equal weight x rest
              (fun inside => absent
                (scTransport A x y (fun z => scMember A z rest) same inside))))
          (scAddZeroRight (weight x))
      | scNo different => scDiagonalPresent A equal weight x rest tail
          (match member with
          | scLeft same => match different same with end
          | scRight inside => inside
          end)
      end
    end
  end""",
     """def scDiagonalPresent : (0 A : Type 0) ->
    (equal : (x : A) -> (y : A) -> ScDec (Eq A x y)) ->
    (weight : A -> Nat) -> (x : A) -> (xs : List A) ->
    scNoDup A xs -> scMember A x xs ->
    Eq Nat (weight x) (weight x) :=
  fun A equal weight x xs unique member => refl Nat (weight x)""", 1),
    ("scFiniteSumIndependent-trivialized", """def scFiniteSumIndependent : (0 A : Type 0) -> (weight : A -> Nat) ->
    (fa : ScFinite A) -> (fb : ScFinite A) ->
    Eq Nat (scSumOver A weight (scElements A fa))
      (scSumOver A weight (scElements A fb)) :=
  fun A weight fa fb => scEqTrans Nat (scSumOver A weight (scElements A fa)) (scSumOver A (fun x
      => scSumOver A (scDiagonalWeight A (scDecEq A fa) weight x) (scElements A fb)) (scElements A
      fa)) (scSumOver A weight (scElements A fb))
    (scEqSym Nat (scSumOver A (fun x => scSumOver A (scDiagonalWeight A (scDecEq A fa) weight x)
        (scElements A fb)) (scElements A fa)) (scSumOver A weight (scElements A fa))
        (scSumOverCong A (fun x => scSumOver A (scDiagonalWeight A (scDecEq A fa) weight x)
        (scElements A fb)) weight
      (fun x => scDiagonalPresent A (scDecEq A fa) weight x (scElements A fb)
        (scEnumerationUnique A fb) (scEnumerates A fb x)) (scElements A fa)))
    (scEqTrans Nat (scSumOver A (fun x => scSumOver A (scDiagonalWeight A (scDecEq A fa) weight x)
        (scElements A fb)) (scElements A fa)) (scSumOver A (fun y => scSumOver A (fun x =>
        scDiagonalWeight A (scDecEq A fa) weight x y) (scElements A fa)) (scElements A fb))
        (scSumOver A weight (scElements A fb))
      (scSumOverSwap A A (scDiagonalWeight A (scDecEq A fa) weight) (scElements A fa) (scElements
          A fb))
      (scSumOverCong A (fun y => scSumOver A (fun x => scDiagonalWeight A (scDecEq A fa) weight x
          y) (scElements A fa)) weight
        (fun y => scEqTrans Nat (scSumOver A (fun x => scDiagonalWeight A (scDecEq A fa) weight x
            y) (scElements A fa)) (scSumOver A (scDiagonalWeight A (scDecEq A fa) weight y)
            (scElements A fa)) (weight y)
          (scSumOverCong A (fun x => scDiagonalWeight A (scDecEq A fa) weight x y)
            (scDiagonalWeight A (scDecEq A fa) weight y)
            (fun x => scDiagonalSym A (scDecEq A fa) weight x y) (scElements A fa))
          (scDiagonalPresent A (scDecEq A fa) weight y (scElements A fa)
            (scEnumerationUnique A fa) (scEnumerates A fa y))) (scElements A fb)))""",
     """def scFiniteSumIndependent : (0 A : Type 0) -> (weight : A -> Nat) ->
    (fa : ScFinite A) -> (fb : ScFinite A) ->
    Eq Nat (scSumOver A weight (scElements A fb)) (scSumOver A weight (scElements A fb)) :=
  fun A weight fa fb => refl Nat (scSumOver A weight (scElements A fb))""", 1),
    ("scCountAsSum-trivialized", """def rec scCountAsSum : (0 A : Type 0) -> (0 P : A -> Type 0) ->
    (decide : (x : A) -> ScDec (P x)) -> (xs : List A) ->
    Eq Nat (scCount A P decide xs)
      (scSumOver A (fun x => scTally (P x) (decide x) zero) xs) :=
  fun A P decide xs => match xs as ys return
      Eq Nat (scCount A P decide ys)
        (scSumOver A (fun x => scTally (P x) (decide x) zero) ys) with
  | nil => refl Nat zero
  | cons x rest => scEqTrans Nat
      (scTally (P x) (decide x) (scCount A P decide rest)) (scTally (P x) (decide x) (scSumOver A
          (fun y => scTally (P y) (decide y) zero) rest))
      (scAdd (scTally (P x) (decide x) zero) (scSumOver A (fun y => scTally (P y) (decide y) zero)
          rest))
      (scCong Nat Nat (scTally (P x) (decide x)) (scCount A P decide rest) (scSumOver A (fun y =>
          scTally (P y) (decide y) zero) rest)
        (scCountAsSum A P decide rest))
      (scTallyAdd (P x) (decide x) zero (scSumOver A (fun y => scTally (P y) (decide y) zero)
          rest))
  end""",
     """def scCountAsSum : (0 A : Type 0) -> (0 P : A -> Type 0) ->
    (decide : (x : A) -> ScDec (P x)) -> (xs : List A) ->
    Eq Nat (scSumOver A (fun x => scTally (P x) (decide x) zero) xs) (scSumOver A (fun x => scTally (P x) (decide x) zero) xs) :=
  fun A P decide xs => refl Nat (scSumOver A (fun x => scTally (P x) (decide x) zero) xs)""", 1),
    ("scFiniteCountIndependent-trivialized", """def scFiniteCountIndependent : (0 A : Type 0) -> (0 P : A -> Type 0) ->
    (dp : (x : A) -> ScDec (P x)) -> (dq : (x : A) -> ScDec (P x)) ->
    (fa : ScFinite A) -> (fb : ScFinite A) ->
    Eq Nat (scFiniteCount A P dp fa) (scFiniteCount A P dq fb) :=
  fun A P dp dq fa fb => scEqTrans Nat (scFiniteCount A P dp fa) (scSumOver A (fun x => scTally (P
      x) (dp x) zero) (scElements A fa)) (scFiniteCount A P dq fb)
    (scCountAsSum A P dp (scElements A fa))
    (scEqTrans Nat (scSumOver A (fun x => scTally (P x) (dp x) zero) (scElements A fa)) (scSumOver
        A (fun x => scTally (P x) (dp x) zero) (scElements A fb)) (scFiniteCount A P dq fb)
      (scFiniteSumIndependent A (fun x => scTally (P x) (dp x) zero) fa fb)
      (scEqTrans Nat (scSumOver A (fun x => scTally (P x) (dp x) zero) (scElements A fb))
          (scFiniteCount A P dp fb) (scFiniteCount A P dq fb)
        (scEqSym Nat (scFiniteCount A P dp fb) (scSumOver A (fun x => scTally (P x) (dp x) zero)
            (scElements A fb)) (scCountAsSum A P dp (scElements A fb)))
        (scCountDecisionIndependent A P dp dq (scElements A fb))))""",
     """def scFiniteCountIndependent : (0 A : Type 0) -> (0 P : A -> Type 0) ->
    (dp : (x : A) -> ScDec (P x)) -> (dq : (x : A) -> ScDec (P x)) ->
    (fa : ScFinite A) -> (fb : ScFinite A) ->
    Eq Nat (scFiniteCount A P dq fb) (scFiniteCount A P dq fb) :=
  fun A P dp dq fa fb => refl Nat (scFiniteCount A P dq fb)""", 1),
    ("scCardinalityIndependent-trivialized", """def scCardinalityIndependent : (0 A : Type 0) -> (fa : ScFinite A) ->
    (fb : ScFinite A) -> Eq Nat (scCardinality A fa) (scCardinality A fb) :=
  fun A fa fb => scEqTrans Nat (scCardinality A fa) (scFiniteCount A (fun x => ScUnit) (fun x =>
      scYes ScUnit scUnit) fa) (scCardinality A fb)
    (scEqSym Nat (scFiniteCount A (fun x => ScUnit) (fun x => scYes ScUnit scUnit) fa)
        (scCardinality A fa) (scCountSatisfied A (fun x => ScUnit)
      (fun x => scYes ScUnit scUnit) (fun x => scUnit) (scElements A fa)))
    (scEqTrans Nat (scFiniteCount A (fun x => ScUnit) (fun x => scYes ScUnit scUnit) fa)
        (scFiniteCount A (fun x => ScUnit) (fun x => scYes ScUnit scUnit) fb) (scCardinality A fb)
      (scFiniteCountIndependent A (fun x => ScUnit)
        (fun x => scYes ScUnit scUnit) (fun x => scYes ScUnit scUnit) fa fb)
      (scCountSatisfied A (fun x => ScUnit)
        (fun x => scYes ScUnit scUnit) (fun x => scUnit) (scElements A fb)))""",
     """def scCardinalityIndependent : (0 A : Type 0) -> (fa : ScFinite A) ->
    (fb : ScFinite A) ->
    Eq Nat (scCardinality A fb) (scCardinality A fb) :=
  fun A fa fb => refl Nat (scCardinality A fb)""", 1),
    ("scAcceptingCountIndependent-trivialized", """def scAcceptingCountIndependent : (0 F : Type 0) ->
    (fa : ScFinite F) -> (fb : ScFinite F) -> (plus : F -> F -> F) ->
    (lo : F) -> (hi : F) -> (n : Nat) -> (strategy : ScStrategy F n) ->
    (g : List F -> F) -> (claim : F) ->
    Eq Nat (scAcceptingCount F fa plus lo hi n strategy g claim)
      (scAcceptingCount F fb plus lo hi n strategy g claim) :=
  fun F fa fb plus lo hi n strategy g claim =>
    scFiniteCountIndependent (ScVector F n)
      (scStrategyAccept F plus lo hi n strategy g claim)
      (scStrategyAcceptDec F fa plus lo hi n strategy g claim)
      (scStrategyAcceptDec F fb plus lo hi n strategy g claim)
      (scVectorFinite F fa n) (scVectorFinite F fb n)""",
     """def scAcceptingCountIndependent : (0 F : Type 0) ->
    (fa : ScFinite F) -> (fb : ScFinite F) -> (plus : F -> F -> F) ->
    (lo : F) -> (hi : F) -> (n : Nat) -> (strategy : ScStrategy F n) ->
    (g : List F -> F) -> (claim : F) ->
    Eq Nat (scAcceptingCount F fb plus lo hi n strategy g claim) (scAcceptingCount F fb plus lo hi n strategy g claim) :=
  fun F fa fb plus lo hi n strategy g claim => refl Nat (scAcceptingCount F fb plus lo hi n strategy g claim)""", 1),
    ("scCountSatisfied-trivialized", """def rec scCountSatisfied : (0 A : Type 0) -> (0 P : A -> Type 0) ->
    (decide : (x : A) -> ScDec (P x)) -> ((x : A) -> P x) -> (xs : List A) ->
    Eq Nat (scCount A P decide xs) (scLength A xs) :=
  fun A P decide holds xs => match xs as ys return
      Eq Nat (scCount A P decide ys) (scLength A ys) with
  | nil => refl Nat zero
  | cons x rest => match decide x as d return
      Eq Nat (scTally (P x) d (scCount A P decide rest)) (succ (scLength A rest)) with
    | scYes p => scSuccCong (scCount A P decide rest) (scLength A rest)
        (scCountSatisfied A P decide holds rest)
    | scNo refute => match refute (holds x) with end
    end
  end""",
     """def scCountSatisfied : (0 A : Type 0) -> (0 P : A -> Type 0) ->
    (decide : (x : A) -> ScDec (P x)) -> ((x : A) -> P x) -> (xs : List A) ->
    Eq Nat (scLength A xs) (scLength A xs) :=
  fun A P decide holds xs => refl Nat (scLength A xs)""", 1),
    ("scCountRefuted-trivialized", """def rec scCountRefuted : (0 A : Type 0) -> (0 P : A -> Type 0) ->
    (decide : (x : A) -> ScDec (P x)) -> ((x : A) -> P x -> ScEmpty) ->
    (xs : List A) -> Eq Nat (scCount A P decide xs) zero :=
  fun A P decide refutes xs => match xs as ys return
      Eq Nat (scCount A P decide ys) zero with
  | nil => refl Nat zero
  | cons x rest => match decide x as d return
      Eq Nat (scTally (P x) d (scCount A P decide rest)) zero with
    | scYes p => match refutes x p with end
    | scNo reject => scCountRefuted A P decide refutes rest
    end
  end""",
     """def scCountRefuted : (0 A : Type 0) -> (0 P : A -> Type 0) ->
    (decide : (x : A) -> ScDec (P x)) -> ((x : A) -> P x -> ScEmpty) ->
    (xs : List A) -> Eq Nat (zero) (zero) :=
  fun A P decide refutes xs => refl Nat (zero)""", 1),
    ("scAcceptingCountBound-trivialized", """def scAcceptingCountBound : (0 F : Type 0) -> (finite : ScFinite F) ->
    (plus : F -> F -> F) -> (lo : F) -> (hi : F) -> (n : Nat) ->
    (strategy : ScStrategy F n) -> (g : List F -> F) -> (claim : F) ->
    ScLe (scAcceptingCount F finite plus lo hi n strategy g claim)
      (scPow (scCardinality F finite) n) :=
  fun F finite plus lo hi n strategy g claim => scVectorCountBound F finite n
    (scStrategyAccept F plus lo hi n strategy g claim)
    (scStrategyAcceptDec F finite plus lo hi n strategy g claim)""",
     """def scAcceptingCountBound : (0 F : Type 0) -> (finite : ScFinite F) ->
    (plus : F -> F -> F) -> (lo : F) -> (hi : F) -> (n : Nat) ->
    (strategy : ScStrategy F n) -> (g : List F -> F) -> (claim : F) ->
    ScLe (scPow (scCardinality F finite) n) (scPow (scCardinality F finite) n) :=
  fun F finite plus lo hi n strategy g claim => scLeRefl (scPow (scCardinality F finite) n)""", 1),
    ("scHonestAcceptingCount-trivialized", """def scHonestAcceptingCount : (0 F : Type 0) -> (finite : ScFinite F) ->
    (plus : F -> F -> F) -> (lo : F) -> (hi : F) -> (n : Nat) -> (g : List F -> F) ->
    Eq Nat (scAcceptingCount F finite plus lo hi n
      (scHonestStrategy F plus lo hi n g) g (scSum F plus lo hi n g))
      (scPow (scCardinality F finite) n) :=
  fun F finite plus lo hi n g => scEqTrans Nat
    (scAcceptingCount F finite plus lo hi n
      (scHonestStrategy F plus lo hi n g) g (scSum F plus lo hi n g))
    (scCardinality (ScVector F n) (scVectorFinite F finite n))
    (scPow (scCardinality F finite) n)
    (scCountSatisfied (ScVector F n)
      (scStrategyAccept F plus lo hi n (scHonestStrategy F plus lo hi n g) g
        (scSum F plus lo hi n g))
      (scStrategyAcceptDec F finite plus lo hi n (scHonestStrategy F plus lo hi n g) g
        (scSum F plus lo hi n g))
      (fun v => scHonestStrategyCompleteness F plus lo hi n v g)
      (scElements (ScVector F n) (scVectorFinite F finite n)))
    (scVectorCardinality F finite n)""",
     """def scHonestAcceptingCount : (0 F : Type 0) -> (finite : ScFinite F) ->
    (plus : F -> F -> F) -> (lo : F) -> (hi : F) -> (n : Nat) -> (g : List F -> F) ->
    Eq Nat (scPow (scCardinality F finite) n) (scPow (scCardinality F finite) n) :=
  fun F finite plus lo hi n g => refl Nat (scPow (scCardinality F finite) n)""", 1),
    ("scFalseZeroAcceptingCount-trivialized", """def scFalseZeroAcceptingCount : (0 F : Type 0) -> (finite : ScFinite F) ->
    (plus : F -> F -> F) -> (lo : F) -> (hi : F) ->
    (strategy : ScStrategy F zero) -> (g : List F -> F) -> (claim : F) ->
    (Eq F claim (g (nil F)) -> ScEmpty) ->
    Eq Nat (scAcceptingCount F finite plus lo hi zero strategy g claim) zero :=
  fun F finite plus lo hi strategy g claim different => scCountRefuted ScUnit
    (scStrategyAccept F plus lo hi zero strategy g claim)
    (scStrategyAcceptDec F finite plus lo hi zero strategy g claim)
    (fun v accepted => different accepted) (scElements ScUnit scUnitFinite)""",
     """def scFalseZeroAcceptingCount : (0 F : Type 0) -> (finite : ScFinite F) ->
    (plus : F -> F -> F) -> (lo : F) -> (hi : F) ->
    (strategy : ScStrategy F zero) -> (g : List F -> F) -> (claim : F) ->
    (Eq F claim (g (nil F)) -> ScEmpty) ->
    Eq Nat (zero) (zero) :=
  fun F finite plus lo hi strategy g claim different => refl Nat (zero)""", 1),
    ("scAcceptingCountStep-trivialized", """def scAcceptingCountStep : (0 F : Type 0) -> (finite : ScFinite F) ->
    (plus : F -> F -> F) -> (lo : F) -> (hi : F) -> (n : Nat) ->
    (message : F -> F) -> (next : F -> ScStrategy F n) ->
    (g : List F -> F) -> (claim : F) ->
    Eq F (plus (message lo) (message hi)) claim ->
    Eq Nat (scAcceptingCount F finite plus lo hi (succ n)
      (pair (F -> F) (F -> ScStrategy F n) message next) g claim)
      (scSumOver F (fun r => scAcceptingCount F finite plus lo hi n
        (next r) (scRestrict F g r) (message r)) (scElements F finite)) :=
  fun F finite plus lo hi n message next g claim valid => scEqTrans Nat
    (scAcceptingCount F finite plus lo hi (succ n)
      (pair (F -> F) (F -> ScStrategy F n) message next) g claim)
    (scSumOver F (fun r => scFiniteCount (ScVector F n)
      (fun v => Pair (Eq F (plus (message lo) (message hi)) claim)
        (scStrategyAccept F plus lo hi n (next r) (scRestrict F g r) (message r) v))
      (fun v => scStrategyAcceptDec F finite plus lo hi (succ n)
        (pair (F -> F) (F -> ScStrategy F n) message next) g claim
        (pair F (ScVector F n) r v)) (scVectorFinite F finite n)) (scElements F finite))
    (scSumOver F (fun r => scAcceptingCount F finite plus lo hi n
      (next r) (scRestrict F g r) (message r)) (scElements F finite))
    (scCountProduct F (ScVector F n)
      (scStrategyAccept F plus lo hi (succ n)
        (pair (F -> F) (F -> ScStrategy F n) message next) g claim)
      (scStrategyAcceptDec F finite plus lo hi (succ n)
        (pair (F -> F) (F -> ScStrategy F n) message next) g claim)
      (scElements F finite) (scElements (ScVector F n) (scVectorFinite F finite n)))
    (scSumOverCong F
      (fun r => scFiniteCount (ScVector F n)
        (fun v => Pair (Eq F (plus (message lo) (message hi)) claim)
          (scStrategyAccept F plus lo hi n (next r) (scRestrict F g r) (message r) v))
        (fun v => scStrategyAcceptDec F finite plus lo hi (succ n)
          (pair (F -> F) (F -> ScStrategy F n) message next) g claim
          (pair F (ScVector F n) r v)) (scVectorFinite F finite n))
      (fun r => scAcceptingCount F finite plus lo hi n
        (next r) (scRestrict F g r) (message r))
      (fun r => scCountEquivalent (ScVector F n)
      (fun v => Pair (Eq F (plus (message lo) (message hi)) claim)
        (scStrategyAccept F plus lo hi n (next r) (scRestrict F g r) (message r) v))
      (scStrategyAccept F plus lo hi n (next r) (scRestrict F g r) (message r))
      (fun v accepted => scSecond (Eq F (plus (message lo) (message hi)) claim)
        (scStrategyAccept F plus lo hi n (next r) (scRestrict F g r) (message r) v) accepted)
      (fun v accepted => pair (Eq F (plus (message lo) (message hi)) claim)
        (scStrategyAccept F plus lo hi n (next r) (scRestrict F g r) (message r) v)
        valid accepted)
      (fun v => scStrategyAcceptDec F finite plus lo hi (succ n)
        (pair (F -> F) (F -> ScStrategy F n) message next) g claim
        (pair F (ScVector F n) r v))
      (scStrategyAcceptDec F finite plus lo hi n (next r) (scRestrict F g r) (message r))
      (scElements (ScVector F n) (scVectorFinite F finite n))) (scElements F finite))""",
     """def scAcceptingCountStep : (0 F : Type 0) -> (finite : ScFinite F) ->
    (plus : F -> F -> F) -> (lo : F) -> (hi : F) -> (n : Nat) ->
    (message : F -> F) -> (next : F -> ScStrategy F n) ->
    (g : List F -> F) -> (claim : F) ->
    Eq F (plus (message lo) (message hi)) claim ->
    Eq Nat (scSumOver F (fun r => scAcceptingCount F finite plus lo hi n
        (next r) (scRestrict F g r) (message r)) (scElements F finite)) (scSumOver F (fun r => scAcceptingCount F finite plus lo hi n
        (next r) (scRestrict F g r) (message r)) (scElements F finite)) :=
  fun F finite plus lo hi n message next g claim valid => refl Nat (scSumOver F (fun r => scAcceptingCount F finite plus lo hi n
        (next r) (scRestrict F g r) (message r)) (scElements F finite))""", 1),
    ("scRejectedRoundCount-trivialized", """def scRejectedRoundCount : (0 F : Type 0) -> (finite : ScFinite F) ->
    (plus : F -> F -> F) -> (lo : F) -> (hi : F) -> (n : Nat) ->
    (message : F -> F) -> (next : F -> ScStrategy F n) ->
    (g : List F -> F) -> (claim : F) ->
    (Eq F (plus (message lo) (message hi)) claim -> ScEmpty) ->
    Eq Nat (scAcceptingCount F finite plus lo hi (succ n)
      (pair (F -> F) (F -> ScStrategy F n) message next) g claim) zero :=
  fun F finite plus lo hi n message next g claim invalid =>
    scCountRefuted (ScVector F (succ n))
      (scStrategyAccept F plus lo hi (succ n)
        (pair (F -> F) (F -> ScStrategy F n) message next) g claim)
      (scStrategyAcceptDec F finite plus lo hi (succ n)
        (pair (F -> F) (F -> ScStrategy F n) message next) g claim)
      (fun v => match v as w return scStrategyAccept F plus lo hi (succ n)
          (pair (F -> F) (F -> ScStrategy F n) message next) g claim w -> ScEmpty with
        | pair r rest => fun accepted => invalid
            (scFirst (Eq F (plus (message lo) (message hi)) claim)
              (scStrategyAccept F plus lo hi n (next r) (scRestrict F g r)
                (message r) rest) accepted)
        end)
      (scElements (ScVector F (succ n)) (scVectorFinite F finite (succ n)))""",
     """def scRejectedRoundCount : (0 F : Type 0) -> (finite : ScFinite F) ->
    (plus : F -> F -> F) -> (lo : F) -> (hi : F) -> (n : Nat) ->
    (message : F -> F) -> (next : F -> ScStrategy F n) ->
    (g : List F -> F) -> (claim : F) ->
    (Eq F (plus (message lo) (message hi)) claim -> ScEmpty) ->
    Eq Nat (zero) (zero) :=
  fun F finite plus lo hi n message next g claim invalid => refl Nat (zero)""", 1),
    ("scRunStrategyLength-trivialized", """def rec scRunStrategyLength : (0 F : Type 0) -> (n : Nat) ->
    (strategy : ScStrategy F n) -> (v : ScVector F n) ->
    Eq Nat (scTraceLength F (scRunStrategy F n strategy v)) n :=
  fun F n => match n as k return (strategy : ScStrategy F k) ->
      (v : ScVector F k) ->
      Eq Nat (scTraceLength F (scRunStrategy F k strategy v)) k with
  | zero => fun strategy v => refl Nat zero
  | succ k => fun strategy v => match strategy as s return
      Eq Nat (scTraceLength F (scRunStrategy F (succ k) s v)) (succ k) with
    | pair message next => match v as w return Eq Nat
        (scTraceLength F (scRunStrategy F (succ k)
          (pair (F -> F) (F -> ScStrategy F k) message next) w))
        (succ k) with
      | pair r rest => scSuccCong
          (scTraceLength F (scRunStrategy F k (next r) rest)) k
          (scRunStrategyLength F k (next r) rest)
      end
    end
  end""",
     """def scRunStrategyLength : (0 F : Type 0) -> (n : Nat) ->
    (strategy : ScStrategy F n) -> (v : ScVector F n) ->
    Eq Nat n n :=
  fun F n strategy v => refl Nat n""", 1),
    ("scRunStrategyChallenges-trivialized", """def rec scRunStrategyChallenges : (0 F : Type 0) -> (n : Nat) ->
    (strategy : ScStrategy F n) -> (v : ScVector F n) ->
    Eq (List F) (scTraceChallenges F (scRunStrategy F n strategy v))
      (scVectorList F n v) :=
  fun F n => match n as k return (strategy : ScStrategy F k) ->
      (v : ScVector F k) ->
      Eq (List F) (scTraceChallenges F (scRunStrategy F k strategy v))
        (scVectorList F k v) with
  | zero => fun strategy v => refl (List F) (nil F)
  | succ k => fun strategy v => match strategy as s return Eq (List F)
      (scTraceChallenges F (scRunStrategy F (succ k) s v))
      (scVectorList F (succ k) v) with
    | pair message next => match v as w return Eq (List F)
        (scTraceChallenges F (scRunStrategy F (succ k)
          (pair (F -> F) (F -> ScStrategy F k) message next) w))
        (scVectorList F (succ k) w) with
      | pair r rest => scCong (List F) (List F) (fun xs => cons F r xs)
          (scTraceChallenges F (scRunStrategy F k (next r) rest))
          (scVectorList F k rest) (scRunStrategyChallenges F k (next r) rest)
      end
    end
  end""",
     """def scRunStrategyChallenges : (0 F : Type 0) -> (n : Nat) ->
    (strategy : ScStrategy F n) -> (v : ScVector F n) ->
    Eq (List F) (scVectorList F n v) (scVectorList F n v) :=
  fun F n strategy v => refl (List F) (scVectorList F n v)""", 1),
    ("scHonestStrategyTrace-trivialized", """def rec scHonestStrategyTrace : (0 F : Type 0) -> (plus : F -> F -> F) ->
    (lo : F) -> (hi : F) -> (cs : List F) -> (g : List F -> F) ->
    Eq (ScTrace F)
      (scRunStrategy F (scLength F cs)
        (scHonestStrategy F plus lo hi (scLength F cs) g) (scListVector F cs))
      (scHonestTrace F plus lo hi cs g) :=
  fun F plus lo hi cs => match cs as xs return (g : List F -> F) ->
      Eq (ScTrace F)
        (scRunStrategy F (scLength F xs)
          (scHonestStrategy F plus lo hi (scLength F xs) g) (scListVector F xs))
        (scHonestTrace F plus lo hi xs g) with
  | nil => fun g => refl (ScTrace F) (scDone F)
  | cons r rest => fun g => scCong (ScTrace F) (ScTrace F)
      (fun tail => scStep F (scMarginal F plus lo hi (scLength F rest) g) r tail)
      (scRunStrategy F (scLength F rest)
        (scHonestStrategy F plus lo hi (scLength F rest) (scRestrict F g r))
        (scListVector F rest))
      (scHonestTrace F plus lo hi rest (scRestrict F g r))
      (scHonestStrategyTrace F plus lo hi rest (scRestrict F g r))
  end""",
     """def scHonestStrategyTrace : (0 F : Type 0) -> (plus : F -> F -> F) ->
    (lo : F) -> (hi : F) -> (cs : List F) -> (g : List F -> F) ->
    Eq (ScTrace F) (scHonestTrace F plus lo hi cs g)
      (scHonestTrace F plus lo hi cs g) :=
  fun F plus lo hi cs g => refl (ScTrace F) (scHonestTrace F plus lo hi cs g)""", 1),
    ("scHonestStrategyCompleteness-trivialized", """def rec scHonestStrategyCompleteness : (0 F : Type 0) -> (plus : F -> F -> F) ->
    (lo : F) -> (hi : F) -> (n : Nat) -> (v : ScVector F n) ->
    (g : List F -> F) ->
    scAccept F plus lo hi
      (scRunStrategy F n (scHonestStrategy F plus lo hi n g) v) g
      (scSum F plus lo hi n g) :=
  fun F plus lo hi n => match n as k return (v : ScVector F k) ->
      (g : List F -> F) -> scAccept F plus lo hi
        (scRunStrategy F k (scHonestStrategy F plus lo hi k g) v) g
        (scSum F plus lo hi k g) with
  | zero => fun v g => refl F (g (nil F))
  | succ k => fun v => match v as w return (g : List F -> F) ->
      scAccept F plus lo hi
        (scRunStrategy F (succ k) (scHonestStrategy F plus lo hi (succ k) g) w) g
        (scSum F plus lo hi (succ k) g) with
    | pair r rest => fun g => pair _ _ (scOneRoundCompleteness F plus lo hi k g)
        (scHonestStrategyCompleteness F plus lo hi k rest (scRestrict F g r))
    end
  end""",
     """def scHonestStrategyCompleteness : (0 F : Type 0) -> (plus : F -> F -> F) ->
    (lo : F) -> (hi : F) -> (n : Nat) -> (v : ScVector F n) ->
    (g : List F -> F) ->
    ScUnit :=
  fun F plus lo hi n v g => scUnit""", 1),
    ("strategy-drops-round", """scStep F message r (scRunStrategy F k (next r) rest)""",
     """scRunStrategy F k (next r) rest""", 1),
    ("strategy-branches-on-evaluation", """scStep F message r (scRunStrategy F k (next r) rest)""",
     """scStep F message r (scRunStrategy F k (next (message r)) rest)""", 1),
    ("strategy-records-evaluation", """scStep F message r (scRunStrategy F k (next r) rest)""",
     """scStep F message (message r) (scRunStrategy F k (next r) rest)""", 1),
    ("scAddComm-trivialized", """def rec scAddComm : (n : Nat) -> (m : Nat) ->
    Eq Nat (scAdd n m) (scAdd m n) :=
  fun n m => match n as a return Eq Nat (scAdd a m) (scAdd m a) with
  | zero => scEqSym Nat (scAdd m zero) m (scAddZeroRight m)
  | succ a => scEqTrans Nat (succ (scAdd a m)) (succ (scAdd m a))
      (scAdd m (succ a)) (scSuccCong (scAdd a m) (scAdd m a) (scAddComm a m))
      (scEqSym Nat (scAdd m (succ a)) (succ (scAdd m a)) (scAddSuccRight m a))
  end""",
     """def scAddComm : (n : Nat) -> (m : Nat) ->
    Eq Nat (scAdd n m) (scAdd n m) :=
  fun n m => refl Nat (scAdd n m)""", 1),
    ("scAddSwap-trivialized", """def scAddSwap : (a : Nat) -> (b : Nat) -> (c : Nat) ->
    Eq Nat (scAdd a (scAdd b c)) (scAdd b (scAdd a c)) :=
  fun a b c => scEqTrans Nat (scAdd a (scAdd b c)) (scAdd (scAdd a b) c)
    (scAdd b (scAdd a c))
    (scEqSym Nat (scAdd (scAdd a b) c) (scAdd a (scAdd b c)) (scAddAssoc a b c))
    (scEqTrans Nat (scAdd (scAdd a b) c) (scAdd (scAdd b a) c)
      (scAdd b (scAdd a c))
      (scCong Nat Nat (fun x => scAdd x c) (scAdd a b) (scAdd b a) (scAddComm a b))
      (scAddAssoc b a c))""",
     """def scAddSwap : (a : Nat) -> (b : Nat) -> (c : Nat) ->
    Eq Nat (scAdd a (scAdd b c)) (scAdd a (scAdd b c)) :=
  fun a b c => refl Nat (scAdd a (scAdd b c))""", 1),
    ("scMulSuccRight-trivialized", """def rec scMulSuccRight : (n : Nat) -> (m : Nat) ->
    Eq Nat (scMul n (succ m)) (scAdd n (scMul n m)) :=
  fun n m => match n as a return
      Eq Nat (scMul a (succ m)) (scAdd a (scMul a m)) with
  | zero => refl Nat zero
  | succ a => scSuccCong (scAdd m (scMul a (succ m)))
      (scAdd a (scAdd m (scMul a m)))
      (scEqTrans Nat (scAdd m (scMul a (succ m)))
        (scAdd m (scAdd a (scMul a m))) (scAdd a (scAdd m (scMul a m)))
        (scCong Nat Nat (scAdd m) (scMul a (succ m)) (scAdd a (scMul a m))
          (scMulSuccRight a m)) (scAddSwap m a (scMul a m)))
  end""",
     """def scMulSuccRight : (n : Nat) -> (m : Nat) ->
    Eq Nat (scMul n (succ m)) (scMul n (succ m)) :=
  fun n m => refl Nat (scMul n (succ m))""", 1),
    ("scMulComm-trivialized", """def rec scMulComm : (n : Nat) -> (m : Nat) ->
    Eq Nat (scMul n m) (scMul m n) :=
  fun n m => match n as a return Eq Nat (scMul a m) (scMul m a) with
  | zero => scEqSym Nat (scMul m zero) zero (scMulZeroRight m)
  | succ a => scEqTrans Nat (scAdd m (scMul a m)) (scAdd m (scMul m a))
      (scMul m (succ a))
      (scCong Nat Nat (scAdd m) (scMul a m) (scMul m a) (scMulComm a m))
      (scEqSym Nat (scMul m (succ a)) (scAdd m (scMul m a)) (scMulSuccRight m a))
  end""",
     """def scMulComm : (n : Nat) -> (m : Nat) ->
    Eq Nat (scMul n m) (scMul n m) :=
  fun n m => refl Nat (scMul n m)""", 1),
    ("scMulSwap-trivialized", """def scMulSwap : (a : Nat) -> (b : Nat) -> (c : Nat) ->
    Eq Nat (scMul a (scMul b c)) (scMul b (scMul a c)) :=
  fun a b c => scEqTrans Nat (scMul a (scMul b c)) (scMul (scMul a b) c)
    (scMul b (scMul a c))
    (scEqSym Nat (scMul (scMul a b) c) (scMul a (scMul b c)) (scMulAssoc a b c))
    (scEqTrans Nat (scMul (scMul a b) c) (scMul (scMul b a) c)
      (scMul b (scMul a c))
      (scCong Nat Nat (fun x => scMul x c) (scMul a b) (scMul b a) (scMulComm a b))
      (scMulAssoc b a c))""",
     """def scMulSwap : (a : Nat) -> (b : Nat) -> (c : Nat) ->
    Eq Nat (scMul a (scMul b c)) (scMul a (scMul b c)) :=
  fun a b c => refl Nat (scMul a (scMul b c))""", 1),
    ("scErrorBudgetScaled-trivialized", """def rec scErrorBudgetScaled : (q : Nat) -> (d : Nat) -> (n : Nat) ->
    Eq Nat (scMul q (scErrorBudget q d n)) (scMul (scMul n d) (scPow q n)) :=
  fun q d n => match n as k return
      Eq Nat (scMul q (scErrorBudget q d k)) (scMul (scMul k d) (scPow q k)) with
  | zero => scMulZeroRight q
  | succ k => scEqTrans Nat (scMul q (scErrorBudget q d (succ k)))
      (scMul q (scMul (scMul (succ k) d) (scPow q k)))
      (scMul (scMul (succ k) d) (scPow q (succ k)))
      (scCong Nat Nat (scMul q) (scErrorBudget q d (succ k))
        (scMul (scMul (succ k) d) (scPow q k))
        (scEqTrans Nat (scErrorBudget q d (succ k))
          (scAdd (scMul d (scPow q k)) (scMul (scMul k d) (scPow q k)))
          (scMul (scMul (succ k) d) (scPow q k))
          (scCong Nat Nat (scAdd (scMul d (scPow q k)))
            (scMul q (scErrorBudget q d k)) (scMul (scMul k d) (scPow q k))
            (scErrorBudgetScaled q d k))
          (scEqSym Nat (scMul (scAdd d (scMul k d)) (scPow q k))
            (scAdd (scMul d (scPow q k)) (scMul (scMul k d) (scPow q k)))
            (scAddMul d (scMul k d) (scPow q k)))))
      (scMulSwap q (scMul (succ k) d) (scPow q k))
  end""",
     """def scErrorBudgetScaled : (q : Nat) -> (d : Nat) -> (n : Nat) ->
    Eq Nat (scMul q (scErrorBudget q d n)) (scMul q (scErrorBudget q d n)) :=
  fun q d n => refl Nat (scMul q (scErrorBudget q d n))""", 1),
    ("scErrorBudgetSuccessor-trivialized", """def scErrorBudgetSuccessor : (q : Nat) -> (d : Nat) -> (n : Nat) ->
    Eq Nat (scErrorBudget q d (succ n)) (scMul (scMul (succ n) d) (scPow q n)) :=
  fun q d n => scEqTrans Nat (scErrorBudget q d (succ n))
    (scAdd (scMul d (scPow q n)) (scMul (scMul n d) (scPow q n)))
    (scMul (scMul (succ n) d) (scPow q n))
    (scCong Nat Nat (scAdd (scMul d (scPow q n)))
      (scMul q (scErrorBudget q d n)) (scMul (scMul n d) (scPow q n))
      (scErrorBudgetScaled q d n))
    (scEqSym Nat (scMul (scAdd d (scMul n d)) (scPow q n))
      (scAdd (scMul d (scPow q n)) (scMul (scMul n d) (scPow q n)))
      (scAddMul d (scMul n d) (scPow q n)))""",
     """def scErrorBudgetSuccessor : (q : Nat) -> (d : Nat) -> (n : Nat) ->
    Eq Nat (scErrorBudget q d (succ n)) (scErrorBudget q d (succ n)) :=
  fun q d n => refl Nat (scErrorBudget q d (succ n))""", 1),
    ("scRecurrenceBound-trivialized", """def rec scRecurrenceBound : (q : Nat) -> (d : Nat) -> (f : Nat -> Nat) ->
    ScLe (f zero) zero ->
    ((k : Nat) -> ScLe (f (succ k))
      (scAdd (scMul d (scPow q k)) (scMul q (f k)))) -> (n : Nat) ->
    ScLe (f n) (scErrorBudget q d n) :=
  fun q d f initial step n => match n as k return
      ScLe (f k) (scErrorBudget q d k) with
  | zero => initial
  | succ k => scLeTrans (f (succ k))
      (scAdd (scMul d (scPow q k)) (scMul q (f k))) (step k)
      (scErrorBudget q d (succ k))
      (scAddLe (scMul d (scPow q k)) (scMul d (scPow q k))
        (scLeRefl (scMul d (scPow q k)))
        (scMul q (f k)) (scMul q (scErrorBudget q d k))
        (scMulMonoLeft q (f k) (scErrorBudget q d k)
          (scRecurrenceBound q d f initial step k)))
  end""",
     """def scRecurrenceBound : (q : Nat) -> (d : Nat) -> (f : Nat -> Nat) ->
    ScLe (f zero) zero ->
    ((k : Nat) -> ScLe (f (succ k))
      (scAdd (scMul d (scPow q k)) (scMul q (f k)))) -> (n : Nat) ->
    ScLe (f n) (f n) :=
  fun q d f initial step n => scLeRefl (f n)""", 1),
    ("scRecurrenceScaledBound-trivialized", """def scRecurrenceScaledBound : (q : Nat) -> (d : Nat) -> (f : Nat -> Nat) ->
    ScLe (f zero) zero ->
    ((k : Nat) -> ScLe (f (succ k))
      (scAdd (scMul d (scPow q k)) (scMul q (f k)))) -> (n : Nat) ->
    ScLe (scMul q (f n)) (scMul (scMul n d) (scPow q n)) :=
  fun q d f initial step n => scTransport Nat
    (scMul q (scErrorBudget q d n)) (scMul (scMul n d) (scPow q n))
    (fun upper => ScLe (scMul q (f n)) upper) (scErrorBudgetScaled q d n)
    (scMulMonoLeft q (f n) (scErrorBudget q d n)
      (scRecurrenceBound q d f initial step n))""",
     """def scRecurrenceScaledBound : (q : Nat) -> (d : Nat) -> (f : Nat -> Nat) ->
    ScLe (f zero) zero ->
    ((k : Nat) -> ScLe (f (succ k))
      (scAdd (scMul d (scPow q k)) (scMul q (f k)))) -> (n : Nat) ->
    ScLe (scMul q (f n)) (scMul q (f n)) :=
  fun q d f initial step n => scLeRefl (scMul q (f n))""", 1),
    ("budget-nonzero-base", """reducible def rec scErrorBudget : Nat -> Nat -> Nat -> Nat :=
  fun q d n => match n with
  | zero => zero
  | succ k => scAdd (scMul d (scPow q k)) (scMul q (scErrorBudget q d k))
  end""",
     """reducible def rec scErrorBudget : Nat -> Nat -> Nat -> Nat :=
  fun q d n => match n with
  | zero => succ zero
  | succ k => scAdd (scMul d (scPow q k)) (scMul q (scErrorBudget q d k))
  end""", 1),
    ("budget-omits-local", """reducible def rec scErrorBudget : Nat -> Nat -> Nat -> Nat :=
  fun q d n => match n with
  | zero => zero
  | succ k => scAdd (scMul d (scPow q k)) (scMul q (scErrorBudget q d k))
  end""",
     """reducible def rec scErrorBudget : Nat -> Nat -> Nat -> Nat :=
  fun q d n => match n with
  | zero => zero
  | succ k => scMul q (scErrorBudget q d k)
  end""", 1),
    ("budget-omits-carry-factor", """reducible def rec scErrorBudget : Nat -> Nat -> Nat -> Nat :=
  fun q d n => match n with
  | zero => zero
  | succ k => scAdd (scMul d (scPow q k)) (scMul q (scErrorBudget q d k))
  end""",
     """reducible def rec scErrorBudget : Nat -> Nat -> Nat -> Nat :=
  fun q d n => match n with
  | zero => zero
  | succ k => scAdd (scMul d (scPow q k)) (scErrorBudget q d k)
  end""", 1),
    ("scMulZeroRight-trivialized", """def rec scMulZeroRight : (n : Nat) -> Eq Nat (scMul n zero) zero :=
  fun n => match n as a return Eq Nat (scMul a zero) zero with
  | zero => refl Nat zero
  | succ a => scMulZeroRight a
  end""",
     """def scMulZeroRight : (n : Nat) -> Eq Nat (scMul n zero) (scMul n zero) :=
  fun n => refl Nat (scMul n zero)""", 1),
    ("scAddMul-trivialized", """def rec scAddMul : (n : Nat) -> (m : Nat) -> (k : Nat) ->
    Eq Nat (scMul (scAdd n m) k) (scAdd (scMul n k) (scMul m k)) :=
  fun n m k => match n as a return
      Eq Nat (scMul (scAdd a m) k) (scAdd (scMul a k) (scMul m k)) with
  | zero => refl Nat (scMul m k)
  | succ a => scEqTrans Nat
      (scAdd k (scMul (scAdd a m) k))
      (scAdd k (scAdd (scMul a k) (scMul m k)))
      (scAdd (scAdd k (scMul a k)) (scMul m k))
      (scCong Nat Nat (scAdd k) (scMul (scAdd a m) k)
        (scAdd (scMul a k) (scMul m k)) (scAddMul a m k))
      (scEqSym Nat (scAdd (scAdd k (scMul a k)) (scMul m k))
        (scAdd k (scAdd (scMul a k) (scMul m k)))
        (scAddAssoc k (scMul a k) (scMul m k)))
  end""",
     """def scAddMul : (n : Nat) -> (m : Nat) -> (k : Nat) ->
    Eq Nat (scMul (scAdd n m) k) (scMul (scAdd n m) k) :=
  fun n m k => refl Nat (scMul (scAdd n m) k)""", 1),
    ("scMulAssoc-trivialized", """def rec scMulAssoc : (n : Nat) -> (m : Nat) -> (k : Nat) ->
    Eq Nat (scMul (scMul n m) k) (scMul n (scMul m k)) :=
  fun n m k => match n as a return
      Eq Nat (scMul (scMul a m) k) (scMul a (scMul m k)) with
  | zero => refl Nat zero
  | succ a => scEqTrans Nat
      (scMul (scAdd m (scMul a m)) k)
      (scAdd (scMul m k) (scMul (scMul a m) k))
      (scAdd (scMul m k) (scMul a (scMul m k)))
      (scAddMul m (scMul a m) k)
      (scCong Nat Nat (scAdd (scMul m k))
        (scMul (scMul a m) k) (scMul a (scMul m k)) (scMulAssoc a m k))
  end""",
     """def scMulAssoc : (n : Nat) -> (m : Nat) -> (k : Nat) ->
    Eq Nat (scMul (scMul n m) k) (scMul (scMul n m) k) :=
  fun n m k => refl Nat (scMul (scMul n m) k)""", 1),
    ("scLeTrans-trivialized", """def rec scLeTrans : (n : Nat) -> (m : Nat) -> ScLe n m ->
    (k : Nat) -> ScLe m k -> ScLe n k :=
  fun n => match n as a return (m : Nat) -> ScLe a m ->
      (k : Nat) -> ScLe m k -> ScLe a k with
  | zero => fun m first k second => scLeZero k
  | succ a => fun m => match m as b return ScLe (succ a) b ->
      (k : Nat) -> ScLe b k -> ScLe (succ a) k with
    | zero => fun first k second => match scLeSuccZeroAbsurd a first with end
    | succ b => fun first k => match k as c return
        ScLe (succ b) c -> ScLe (succ a) c with
      | zero => fun second => match scLeSuccZeroAbsurd b second with end
      | succ c => fun second => scLeSucc a c
          (scLeTrans a b (scLePred (succ a) (succ b) first) c
            (scLePred (succ b) (succ c) second))
      end
    end
  end""",
     """def scLeTrans : (n : Nat) -> (m : Nat) -> ScLe n m ->
    (k : Nat) -> ScLe m k -> ScLe n n :=
  fun n m first k second => scLeRefl n""", 1),
    ("scMulMonoLeft-trivialized", """def rec scMulMonoLeft : (k : Nat) -> (n : Nat) -> (m : Nat) -> ScLe n m ->
    ScLe (scMul k n) (scMul k m) :=
  fun k n m bound => match k as a return ScLe (scMul a n) (scMul a m) with
  | zero => scLeZero zero
  | succ a => scAddLe n m bound (scMul a n) (scMul a m)
      (scMulMonoLeft a n m bound)
  end""",
     """def scMulMonoLeft : (k : Nat) -> (n : Nat) -> (m : Nat) -> ScLe n m ->
    ScLe (scMul k n) (scMul k n) :=
  fun k n m bound => scLeRefl (scMul k n)""", 1),
    ("scMulMonoRight-trivialized", """def rec scMulMonoRight : (n : Nat) -> (m : Nat) -> ScLe n m -> (k : Nat) ->
    ScLe (scMul n k) (scMul m k) :=
  fun n => match n as a return (m : Nat) -> ScLe a m -> (k : Nat) ->
      ScLe (scMul a k) (scMul m k) with
  | zero => fun m bound k => scLeZero (scMul m k)
  | succ a => fun m => match m as b return ScLe (succ a) b -> (k : Nat) ->
        ScLe (scMul (succ a) k) (scMul b k) with
    | zero => fun bound k => match scLeSuccZeroAbsurd a bound with end
    | succ b => fun bound k => scAddLe k k (scLeRefl k)
        (scMul a k) (scMul b k)
        (scMulMonoRight a b (scLePred (succ a) (succ b) bound) k)
    end
  end""",
     """def scMulMonoRight : (n : Nat) -> (m : Nat) -> ScLe n m -> (k : Nat) ->
    ScLe (scMul n k) (scMul n k) :=
  fun n m bound k => scLeRefl (scMul n k)""", 1),
    ("scMulMono-trivialized", """def scMulMono : (n : Nat) -> (m : Nat) -> ScLe n m ->
    (k : Nat) -> (l : Nat) -> ScLe k l -> ScLe (scMul n k) (scMul m l) :=
  fun n m first k l second => scLeTrans
    (scMul n k) (scMul m k) (scMulMonoRight n m first k)
    (scMul m l) (scMulMonoLeft m k l second)""",
     """def scMulMono : (n : Nat) -> (m : Nat) -> ScLe n m ->
    (k : Nat) -> (l : Nat) -> ScLe k l -> ScLe (scMul n k) (scMul n k) :=
  fun n m first k l second => scLeRefl (scMul n k)""", 1),
    ("scPowAdd-trivialized", """def rec scPowAdd : (q : Nat) -> (n : Nat) -> (m : Nat) ->
    Eq Nat (scPow q (scAdd n m)) (scMul (scPow q n) (scPow q m)) :=
  fun q n m => match n as a return
      Eq Nat (scPow q (scAdd a m)) (scMul (scPow q a) (scPow q m)) with
  | zero => scEqSym Nat (scAdd (scPow q m) zero) (scPow q m)
      (scAddZeroRight (scPow q m))
  | succ a => scEqTrans Nat
      (scMul q (scPow q (scAdd a m)))
      (scMul q (scMul (scPow q a) (scPow q m)))
      (scMul (scMul q (scPow q a)) (scPow q m))
      (scCong Nat Nat (scMul q) (scPow q (scAdd a m))
        (scMul (scPow q a) (scPow q m)) (scPowAdd q a m))
      (scEqSym Nat (scMul (scMul q (scPow q a)) (scPow q m))
        (scMul q (scMul (scPow q a) (scPow q m)))
        (scMulAssoc q (scPow q a) (scPow q m)))
  end""",
     """def scPowAdd : (q : Nat) -> (n : Nat) -> (m : Nat) ->
    Eq Nat (scPow q (scAdd n m)) (scPow q (scAdd n m)) :=
  fun q n m => refl Nat (scPow q (scAdd n m))""", 1),
    ("scSumOverCong-trivialized", """def rec scSumOverCong : (0 A : Type 0) -> (f : A -> Nat) -> (g : A -> Nat) ->
    ((x : A) -> Eq Nat (f x) (g x)) -> (xs : List A) ->
    Eq Nat (scSumOver A f xs) (scSumOver A g xs) :=
  fun A f g equal xs => match xs as ys return
      Eq Nat (scSumOver A f ys) (scSumOver A g ys) with
  | nil => refl Nat zero
  | cons x rest => scEqTrans Nat
      (scAdd (f x) (scSumOver A f rest)) (scAdd (g x) (scSumOver A f rest))
      (scAdd (g x) (scSumOver A g rest))
      (scCong Nat Nat (fun n => scAdd n (scSumOver A f rest)) (f x) (g x) (equal x))
      (scCong Nat Nat (scAdd (g x)) (scSumOver A f rest) (scSumOver A g rest)
        (scSumOverCong A f g equal rest))
  end""",
     """def scSumOverCong : (0 A : Type 0) -> (f : A -> Nat) -> (g : A -> Nat) ->
    ((x : A) -> Eq Nat (f x) (g x)) -> (xs : List A) ->
    Eq Nat (scSumOver A f xs) (scSumOver A f xs) :=
  fun A f g equal xs => refl Nat (scSumOver A f xs)""", 1),
    ("scSumOverBound-trivialized", """def rec scSumOverBound : (0 A : Type 0) -> (weight : A -> Nat) -> (d : Nat) ->
    ((x : A) -> ScLe (weight x) d) -> (xs : List A) ->
    ScLe (scSumOver A weight xs) (scMul (scLength A xs) d) :=
  fun A weight d bounded xs => match xs as ys return
      ScLe (scSumOver A weight ys) (scMul (scLength A ys) d) with
  | nil => scLeZero zero
  | cons x rest => scAddLe (weight x) d (bounded x)
      (scSumOver A weight rest) (scMul (scLength A rest) d)
      (scSumOverBound A weight d bounded rest)
  end""",
     """def scSumOverBound : (0 A : Type 0) -> (weight : A -> Nat) -> (d : Nat) ->
    ((x : A) -> ScLe (weight x) d) -> (xs : List A) ->
    ScLe (scSumOver A weight xs) (scSumOver A weight xs) :=
  fun A weight d bounded xs => scLeRefl (scSumOver A weight xs)""", 1),
    ("scCountExpand-trivialized", """def rec scCountExpand : (0 A : Type 0) -> (0 B : Type 0) ->
    (block : A -> List B) -> (0 P : B -> Type 0) ->
    (decide : (y : B) -> ScDec (P y)) -> (xs : List A) ->
    Eq Nat (scCount B P decide (scExpand A B block xs))
      (scSumOver A (fun x => scCount B P decide (block x)) xs) :=
  fun A B block P decide xs => match xs as ys return
      Eq Nat (scCount B P decide (scExpand A B block ys))
        (scSumOver A (fun x => scCount B P decide (block x)) ys) with
  | nil => refl Nat zero
  | cons x rest => scEqTrans Nat
      (scCount B P decide (scExpand A B block (cons A x rest)))
      (scAdd (scCount B P decide (block x))
        (scCount B P decide (scExpand A B block rest)))
      (scSumOver A (fun y => scCount B P decide (block y)) (cons A x rest))
      (scCountAppend B P decide (block x) (scExpand A B block rest))
      (scCong Nat Nat (scAdd (scCount B P decide (block x)))
        (scCount B P decide (scExpand A B block rest))
        (scSumOver A (fun y => scCount B P decide (block y)) rest)
        (scCountExpand A B block P decide rest))
  end""",
     """def scCountExpand : (0 A : Type 0) -> (0 B : Type 0) ->
    (block : A -> List B) -> (0 P : B -> Type 0) ->
    (decide : (y : B) -> ScDec (P y)) -> (xs : List A) ->
    Eq Nat (scCount B P decide (scExpand A B block xs))
      (scCount B P decide (scExpand A B block xs)) :=
  fun A B block P decide xs => refl Nat (scCount B P decide (scExpand A B block xs))""", 1),
    ("scCountExpandBound-trivialized", """def scCountExpandBound : (0 A : Type 0) -> (0 B : Type 0) ->
    (block : A -> List B) -> (0 P : B -> Type 0) ->
    (decide : (y : B) -> ScDec (P y)) -> (d : Nat) ->
    ((x : A) -> ScLe (scCount B P decide (block x)) d) -> (xs : List A) ->
    ScLe (scCount B P decide (scExpand A B block xs)) (scMul (scLength A xs) d) :=
  fun A B block P decide d bounded xs => scTransport Nat
    (scSumOver A (fun x => scCount B P decide (block x)) xs)
    (scCount B P decide (scExpand A B block xs))
    (fun total => ScLe total (scMul (scLength A xs) d))
    (scEqSym Nat (scCount B P decide (scExpand A B block xs))
      (scSumOver A (fun x => scCount B P decide (block x)) xs)
      (scCountExpand A B block P decide xs))
    (scSumOverBound A (fun x => scCount B P decide (block x)) d bounded xs)""",
     """def scCountExpandBound : (0 A : Type 0) -> (0 B : Type 0) ->
    (block : A -> List B) -> (0 P : B -> Type 0) ->
    (decide : (y : B) -> ScDec (P y)) -> (d : Nat) ->
    ((x : A) -> ScLe (scCount B P decide (block x)) d) -> (xs : List A) ->
    ScLe (scCount B P decide (scExpand A B block xs))
      (scCount B P decide (scExpand A B block xs)) :=
  fun A B block P decide d bounded xs => scLeRefl (scCount B P decide (scExpand A B block xs))""", 1),
    ("scCountProduct-trivialized", """def scCountProduct : (0 A : Type 0) -> (0 B : Type 0) ->
    (0 P : Pair A B -> Type 0) -> (decide : (p : Pair A B) -> ScDec (P p)) ->
    (xs : List A) -> (ys : List B) ->
    Eq Nat (scCount (Pair A B) P decide (scProduct A B xs ys))
      (scSumOver A (fun x => scCount B (fun y => P (pair A B x y))
        (fun y => decide (pair A B x y)) ys) xs) :=
  fun A B P decide xs ys => scEqTrans Nat
    (scCount (Pair A B) P decide (scProduct A B xs ys))
    (scSumOver A (fun x => scCount (Pair A B) P decide
      (scMap B (Pair A B) (fun y => pair A B x y) ys)) xs)
    (scSumOver A (fun x => scCount B (fun y => P (pair A B x y))
      (fun y => decide (pair A B x y)) ys) xs)
    (scCountExpand A (Pair A B)
      (fun x => scMap B (Pair A B) (fun y => pair A B x y) ys) P decide xs)
    (scSumOverCong A
      (fun x => scCount (Pair A B) P decide
        (scMap B (Pair A B) (fun y => pair A B x y) ys))
      (fun x => scCount B (fun y => P (pair A B x y))
        (fun y => decide (pair A B x y)) ys)
      (fun x => scEqSym Nat
        (scCount B (fun y => P (pair A B x y)) (fun y => decide (pair A B x y)) ys)
        (scCount (Pair A B) P decide (scMap B (Pair A B) (fun y => pair A B x y) ys))
        (scCountMap B (Pair A B) (fun y => pair A B x y) P decide ys)) xs)""",
     """def scCountProduct : (0 A : Type 0) -> (0 B : Type 0) ->
    (0 P : Pair A B -> Type 0) -> (decide : (p : Pair A B) -> ScDec (P p)) ->
    (xs : List A) -> (ys : List B) ->
    Eq Nat (scCount (Pair A B) P decide (scProduct A B xs ys))
      (scCount (Pair A B) P decide (scProduct A B xs ys)) :=
  fun A B P decide xs ys => refl Nat (scCount (Pair A B) P decide (scProduct A B xs ys))""", 1),
    ("scFiniteProductFiberBound-trivialized", """def scFiniteProductFiberBound : (0 A : Type 0) -> (0 B : Type 0) ->
    (0 P : Pair A B -> Type 0) -> (decide : (p : Pair A B) -> ScDec (P p)) ->
    (fa : ScFinite A) -> (fb : ScFinite B) -> (d : Nat) ->
    ((x : A) -> ScLe (scFiniteCount B (fun y => P (pair A B x y))
      (fun y => decide (pair A B x y)) fb) d) ->
    ScLe (scFiniteCount (Pair A B) P decide (scProductFinite A B fa fb))
      (scMul (scCardinality A fa) d) :=
  fun A B P decide fa fb d bounded => scTransport Nat
    (scSumOver A (fun x => scFiniteCount B (fun y => P (pair A B x y))
      (fun y => decide (pair A B x y)) fb) (scElements A fa))
    (scFiniteCount (Pair A B) P decide (scProductFinite A B fa fb))
    (fun total => ScLe total (scMul (scCardinality A fa) d))
    (scEqSym Nat (scFiniteCount (Pair A B) P decide (scProductFinite A B fa fb))
      (scSumOver A (fun x => scFiniteCount B (fun y => P (pair A B x y))
        (fun y => decide (pair A B x y)) fb) (scElements A fa))
      (scCountProduct A B P decide (scElements A fa) (scElements B fb)))
    (scSumOverBound A (fun x => scFiniteCount B (fun y => P (pair A B x y))
      (fun y => decide (pair A B x y)) fb) d bounded (scElements A fa))""",
     """def scFiniteProductFiberBound : (0 A : Type 0) -> (0 B : Type 0) ->
    (0 P : Pair A B -> Type 0) -> (decide : (p : Pair A B) -> ScDec (P p)) ->
    (fa : ScFinite A) -> (fb : ScFinite B) -> (d : Nat) ->
    ((x : A) -> ScLe (scFiniteCount B (fun y => P (pair A B x y))
      (fun y => decide (pair A B x y)) fb) d) ->
    ScLe (scFiniteCount (Pair A B) P decide (scProductFinite A B fa fb))
      (scFiniteCount (Pair A B) P decide (scProductFinite A B fa fb)) :=
  fun A B P decide fa fb d bounded => scLeRefl (scFiniteCount (Pair A B) P decide (scProductFinite A B fa fb))""", 1),

    ("scCountMono-trivialized", """def rec scCountMono : (0 A : Type 0) -> (0 P : A -> Type 0) ->
    (0 Q : A -> Type 0) -> ((x : A) -> P x -> Q x) ->
    (dp : (x : A) -> ScDec (P x)) -> (dq : (x : A) -> ScDec (Q x)) ->
    (xs : List A) -> ScLe (scCount A P dp xs) (scCount A Q dq xs) :=
  fun A P Q implies dp dq xs => match xs as ys return
      ScLe (scCount A P dp ys) (scCount A Q dq ys) with
  | nil => scLeZero zero
  | cons x rest => scTallyMono (P x) (Q x) (implies x) (dp x) (dq x)
      (scCount A P dp rest) (scCount A Q dq rest)
      (scCountMono A P Q implies dp dq rest)
  end""", """def scCountMono : (0 A : Type 0) -> (0 P : A -> Type 0) ->
    (0 Q : A -> Type 0) -> ((x : A) -> P x -> Q x) ->
    (dp : (x : A) -> ScDec (P x)) -> (dq : (x : A) -> ScDec (Q x)) ->
    (xs : List A) -> ScLe (scCount A P dp xs) (scCount A P dp xs) :=
  fun A P Q implies dp dq xs => scLeRefl (scCount A P dp xs)""", 1),
    ("scCountEquivalent-trivialized", """def rec scCountEquivalent : (0 A : Type 0) -> (0 P : A -> Type 0) ->
    (0 Q : A -> Type 0) -> ((x : A) -> P x -> Q x) ->
    ((x : A) -> Q x -> P x) -> (dp : (x : A) -> ScDec (P x)) ->
    (dq : (x : A) -> ScDec (Q x)) -> (xs : List A) ->
    Eq Nat (scCount A P dp xs) (scCount A Q dq xs) :=
  fun A P Q forward backward dp dq xs => match xs as ys return
      Eq Nat (scCount A P dp ys) (scCount A Q dq ys) with
  | nil => refl Nat zero
  | cons x rest => scTallyEquivalent (P x) (Q x) (forward x) (backward x)
      (dp x) (dq x) (scCount A P dp rest) (scCount A Q dq rest)
      (scCountEquivalent A P Q forward backward dp dq rest)
  end""", """def scCountEquivalent : (0 A : Type 0) -> (0 P : A -> Type 0) ->
    (0 Q : A -> Type 0) -> ((x : A) -> P x -> Q x) ->
    ((x : A) -> Q x -> P x) -> (dp : (x : A) -> ScDec (P x)) ->
    (dq : (x : A) -> ScDec (Q x)) -> (xs : List A) ->
    Eq Nat (scCount A P dp xs) (scCount A P dp xs) :=
  fun A P Q forward backward dp dq xs => refl Nat (scCount A P dp xs)""", 1),
    ("scCountDecisionIndependent-trivialized", """def scCountDecisionIndependent : (0 A : Type 0) -> (0 P : A -> Type 0) ->
    (dp : (x : A) -> ScDec (P x)) -> (dq : (x : A) -> ScDec (P x)) ->
    (xs : List A) -> Eq Nat (scCount A P dp xs) (scCount A P dq xs) :=
  fun A P dp dq xs => scCountEquivalent A P P (fun x p => p)
    (fun x p => p) dp dq xs""", """def scCountDecisionIndependent : (0 A : Type 0) -> (0 P : A -> Type 0) ->
    (dp : (x : A) -> ScDec (P x)) -> (dq : (x : A) -> ScDec (P x)) ->
    (xs : List A) -> Eq Nat (scCount A P dp xs) (scCount A P dp xs) :=
  fun A P dp dq xs => refl Nat (scCount A P dp xs)""", 1),
    ("scCountAppend-trivialized", """def rec scCountAppend : (0 A : Type 0) -> (0 P : A -> Type 0) ->
    (decide : (x : A) -> ScDec (P x)) -> (xs : List A) -> (ys : List A) ->
    Eq Nat (scCount A P decide (scAppend A xs ys))
      (scAdd (scCount A P decide xs) (scCount A P decide ys)) :=
  fun A P decide xs ys => match xs as zs return
      Eq Nat (scCount A P decide (scAppend A zs ys))
        (scAdd (scCount A P decide zs) (scCount A P decide ys)) with
  | nil => refl Nat (scCount A P decide ys)
  | cons x rest => scEqTrans Nat
      (scTally (P x) (decide x) (scCount A P decide (scAppend A rest ys)))
      (scTally (P x) (decide x)
        (scAdd (scCount A P decide rest) (scCount A P decide ys)))
      (scAdd (scTally (P x) (decide x) (scCount A P decide rest))
        (scCount A P decide ys))
      (scCong Nat Nat (scTally (P x) (decide x))
        (scCount A P decide (scAppend A rest ys))
        (scAdd (scCount A P decide rest) (scCount A P decide ys))
        (scCountAppend A P decide rest ys))
      (scTallyAdd (P x) (decide x) (scCount A P decide rest) (scCount A P decide ys))
  end""", """def scCountAppend : (0 A : Type 0) -> (0 P : A -> Type 0) ->
    (decide : (x : A) -> ScDec (P x)) -> (xs : List A) -> (ys : List A) ->
    Eq Nat (scCount A P decide (scAppend A xs ys))
      (scCount A P decide (scAppend A xs ys)) :=
  fun A P decide xs ys => refl Nat (scCount A P decide (scAppend A xs ys))""", 1),
    ("scCountUnionBound-trivialized", """def rec scCountUnionBound : (0 A : Type 0) -> (0 P : A -> Type 0) ->
    (0 Q : A -> Type 0) -> (dp : (x : A) -> ScDec (P x)) ->
    (dq : (x : A) -> ScDec (Q x)) -> (xs : List A) ->
    ScLe (scCount A (fun x => ScEither (P x) (Q x))
        (fun x => scEitherDec (P x) (Q x) (dp x) (dq x)) xs)
      (scAdd (scCount A P dp xs) (scCount A Q dq xs)) :=
  fun A P Q dp dq xs => match xs as ys return
      ScLe (scCount A (fun x => ScEither (P x) (Q x))
          (fun x => scEitherDec (P x) (Q x) (dp x) (dq x)) ys)
        (scAdd (scCount A P dp ys) (scCount A Q dq ys)) with
  | nil => scLeZero zero
  | cons x rest => scTallyUnionBound (P x) (Q x) (dp x) (dq x)
      (scCount A (fun y => ScEither (P y) (Q y))
        (fun y => scEitherDec (P y) (Q y) (dp y) (dq y)) rest)
      (scCount A P dp rest) (scCount A Q dq rest)
      (scCountUnionBound A P Q dp dq rest)
  end""", """def scCountUnionBound : (0 A : Type 0) -> (0 P : A -> Type 0) ->
    (0 Q : A -> Type 0) -> (dp : (x : A) -> ScDec (P x)) ->
    (dq : (x : A) -> ScDec (Q x)) -> (xs : List A) ->
    ScLe (scCount A P dp xs) (scCount A P dp xs) :=
  fun A P Q dp dq xs => scLeRefl (scCount A P dp xs)""", 1),
    ('scVectorEnumeration-trivialized', """def rec scVectorEnumeration : (0 A : Type 0) -> (finite : ScFinite A) -> (n : Nat) ->
    Eq (List (List A))
      (scMap (ScVector A n) (List A) (scVectorList A n)
        (scElements (ScVector A n) (scVectorFinite A finite n)))
      (scWords A (scElements A finite) n) :=
  fun A finite n => match n as k return Eq (List (List A))
      (scMap (ScVector A k) (List A) (scVectorList A k)
        (scElements (ScVector A k) (scVectorFinite A finite k)))
      (scWords A (scElements A finite) k) with
  | zero => refl (List (List A)) (cons (List A) (nil A) (nil (List A)))
  | succ k => scMapExpand A (ScVector A (succ k)) (List A)
      (scVectorList A (succ k))
      (fun x => scMap (ScVector A k) (ScVector A (succ k))
        (fun v => pair A (ScVector A k) x v)
        (scElements (ScVector A k) (scVectorFinite A finite k)))
      (fun x => scMap (List A) (List A) (fun tail => cons A x tail) (scWords A (scElements A finite) k))
      (fun x => scEqTrans (List (List A)) (scMap (ScVector A (succ k)) (List A) (scVectorList A (succ k)) (scMap (ScVector A k) (ScVector A (succ k)) (fun v => pair A (ScVector A k) x v) (scElements (ScVector A k) (scVectorFinite A finite k))))
        (scMap (ScVector A k) (List A) (fun v => cons A x (scVectorList A k v)) (scElements (ScVector A k) (scVectorFinite A finite k))) (scMap (List A) (List A) (fun tail => cons A x tail) (scWords A (scElements A finite) k))
        (scMapCompose (ScVector A k) (ScVector A (succ k)) (List A)
          (fun v => pair A (ScVector A k) x v) (scVectorList A (succ k))
          (scElements (ScVector A k) (scVectorFinite A finite k)))
        (scEqTrans (List (List A)) (scMap (ScVector A k) (List A) (fun v => cons A x (scVectorList A k v)) (scElements (ScVector A k) (scVectorFinite A finite k)))
          (scMap (List A) (List A) (fun tail => cons A x tail) (scMap (ScVector A k) (List A) (scVectorList A k) (scElements (ScVector A k) (scVectorFinite A finite k)))) (scMap (List A) (List A) (fun tail => cons A x tail) (scWords A (scElements A finite) k))
          (scEqSym (List (List A)) (scMap (List A) (List A) (fun tail => cons A x tail) (scMap (ScVector A k) (List A) (scVectorList A k) (scElements (ScVector A k) (scVectorFinite A finite k)))) (scMap (ScVector A k) (List A) (fun v => cons A x (scVectorList A k v)) (scElements (ScVector A k) (scVectorFinite A finite k)))
            (scMapCompose (ScVector A k) (List A) (List A)
              (scVectorList A k) (fun tail => cons A x tail)
              (scElements (ScVector A k) (scVectorFinite A finite k))))
          (scCong (List (List A)) (List (List A)) (scMap (List A) (List A) (fun tail => cons A x tail))
            (scMap (ScVector A k) (List A) (scVectorList A k) (scElements (ScVector A k) (scVectorFinite A finite k)))
            (scWords A (scElements A finite) k) (scVectorEnumeration A finite k))))
      (scElements A finite)
  end""", """def scVectorEnumeration : (0 A : Type 0) -> (finite : ScFinite A) -> (n : Nat) ->
    Eq (List (List A)) (scWords A (scElements A finite) n) (scWords A (scElements A finite) n) :=
  fun A finite n => refl (List (List A)) (scWords A (scElements A finite) n)""", 1),
    ('scCountMap-trivialized', """def rec scCountMap : (0 A : Type 0) -> (0 B : Type 0) -> (f : A -> B) ->
    (0 P : B -> Type 0) -> (decide : (y : B) -> ScDec (P y)) -> (xs : List A) ->
    Eq Nat (scCount A (fun x => P (f x)) (fun x => decide (f x)) xs)
      (scCount B P decide (scMap A B f xs)) :=
  fun A B f P decide xs => match xs as ys return
      Eq Nat (scCount A (fun x => P (f x)) (fun x => decide (f x)) ys)
        (scCount B P decide (scMap A B f ys)) with
  | nil => refl Nat zero
  | cons x rest => scCong Nat Nat (scTally (P (f x)) (decide (f x)))
      (scCount A (fun x => P (f x)) (fun x => decide (f x)) rest)
      (scCount B P decide (scMap A B f rest)) (scCountMap A B f P decide rest)
  end""", """def scCountMap : (0 A : Type 0) -> (0 B : Type 0) -> (f : A -> B) ->
    (0 P : B -> Type 0) -> (decide : (y : B) -> ScDec (P y)) -> (xs : List A) ->
    Eq (Nat) (scCount B P decide (scMap A B f xs)) (scCount B P decide (scMap A B f xs)) :=
  fun A B f P decide xs => refl (Nat) (scCount B P decide (scMap A B f xs))""", 1),
    ('scVectorWordCount-trivialized', """def scVectorWordCount : (0 A : Type 0) -> (finite : ScFinite A) -> (n : Nat) ->
    (0 P : List A -> Type 0) -> (decide : (xs : List A) -> ScDec (P xs)) ->
    Eq Nat
      (scFiniteCount (ScVector A n) (fun v => P (scVectorList A n v))
        (fun v => decide (scVectorList A n v)) (scVectorFinite A finite n))
      (scCount (List A) P decide (scWords A (scElements A finite) n)) :=
  fun A finite n P decide => scEqTrans Nat
    (scFiniteCount (ScVector A n) (fun v => P (scVectorList A n v)) (fun v => decide (scVectorList A n v)) (scVectorFinite A finite n))
    (scCount (List A) P decide (scMap (ScVector A n) (List A) (scVectorList A n) (scElements (ScVector A n) (scVectorFinite A finite n))))
    (scCount (List A) P decide (scWords A (scElements A finite) n))
    (scCountMap (ScVector A n) (List A) (scVectorList A n) P decide
      (scElements (ScVector A n) (scVectorFinite A finite n)))
    (scCong (List (List A)) Nat (scCount (List A) P decide)
      (scMap (ScVector A n) (List A) (scVectorList A n) (scElements (ScVector A n) (scVectorFinite A finite n)))
      (scWords A (scElements A finite) n) (scVectorEnumeration A finite n))""", """def scVectorWordCount : (0 A : Type 0) -> (finite : ScFinite A) -> (n : Nat) ->
    (0 P : List A -> Type 0) -> (decide : (xs : List A) -> ScDec (P xs)) ->
    Eq (Nat) (scCount (List A) P decide (scWords A (scElements A finite) n)) (scCount (List A) P decide (scWords A (scElements A finite) n)) :=
  fun A finite n P decide => refl (Nat) (scCount (List A) P decide (scWords A (scElements A finite) n))""", 1),

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
     "nil (List A)", 2),
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
