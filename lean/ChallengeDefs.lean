/-
  ChallengeDefs.lean — Zero-import, self-contained textbook definitions for the
  balanced 9-variable nonlinearity 242 problem (`nl_bal(9) = 240`).

  Trusted base for `leanprover/comparator`: pure Lean 4.15.0 core (`Init`) only —
  zero Mathlib, zero imports from any proof module. Every definition below can be
  audited in under a minute.
-/

namespace NL242Challenge

/-- Boolean vectors `F_2^n`, represented as standard functions `Fin n → Bool`. -/
abbrev Vec (n : Nat) := Fin n → Bool

/-- Sign encoding of a Boolean value: `false ↦ +1`, `true ↦ -1`. -/
def sign (b : Bool) : Int := if b then -1 else 1

/-- Prepend a Boolean coordinate to a vector in `F_2^n`. -/
def consVec {n : Nat} (b : Bool) (v : Vec n) : Vec (n + 1) :=
  fun i => match i with
    | ⟨0, _⟩ => b
    | ⟨k + 1, h⟩ => v ⟨k, Nat.lt_of_succ_lt_succ h⟩

/-- Drop the first coordinate of a vector in `F_2^(n+1)`. -/
def tailVec {n : Nat} (v : Vec (n + 1)) : Vec n :=
  fun i => v ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩

/-- Sum of an integer-valued function over all `2^n` vectors of `F_2^n`. -/
def sumVecs : {n : Nat} → (Vec n → Int) → Int
  | 0, g => g (fun i => Fin.elim0 i)
  | _ + 1, g =>
    sumVecs (fun v => g (consVec false v)) +
    sumVecs (fun v => g (consVec true v))

/-- Inner product modulo 2 on `F_2^n`. -/
def dot : {n : Nat} → Vec n → Vec n → Bool
  | 0, _, _ => false
  | _ + 1, a, x =>
    xor (a ⟨0, Nat.zero_lt_succ _⟩ && x ⟨0, Nat.zero_lt_succ _⟩)
        (dot (tailVec a) (tailVec x))

/-- Hamming weight `|{x ∈ F_2^n : F(x) = true}|` of a Boolean function. -/
def hammingWeight {n : Nat} (F : Vec n → Bool) : Int :=
  sumVecs (fun x => if F x then 1 else 0)

/-- Hamming distance `|{x ∈ F_2^n : F(x) ≠ G(x)}|` between two Boolean functions. -/
def hammingDist {n : Nat} (F G : Vec n → Bool) : Int :=
  sumVecs (fun x => if F x != G x then 1 else 0)

/-- Affine Boolean function `x ↦ (a · x) ⊕ c` on `F_2^n`. -/
def affine {n : Nat} (a : Vec n) (c : Bool) (x : Vec n) : Bool :=
  xor (dot a x) c

/-- A 9-variable Boolean function is balanced iff it takes `true` on exactly half (`256`)
    of the `2^9 = 512` inputs. -/
def isBalanced9 (F : Vec 9 → Bool) : Prop :=
  hammingWeight F = 256

/-- A 9-variable Boolean function has nonlinearity `≥ d` iff its Hamming distance to every
    affine function `x ↦ (a · x) ⊕ c` on `F_2^9` is at least `d`. -/
def hasNonlinearityAtLeast9 (F : Vec 9 → Bool) (d : Int) : Prop :=
  ∀ (a : Vec 9) (c : Bool), d ≤ hammingDist F (affine a c)

/-- Walsh–Hadamard transform `W_g(a) = ∑_{x ∈ F_2^n} g(x) (-1)^{a · x}`. -/
def walsh {n : Nat} (g : Vec n → Int) (a : Vec n) : Int :=
  sumVecs (fun x => g x * sign (dot a x))

/-- Walsh–Hadamard transform of a Boolean function `F : F_2^n → Bool`. -/
def walshBool {n : Nat} (F : Vec n → Bool) (a : Vec n) : Int :=
  walsh (fun x => sign (F x)) a

/-- Low and high spectral blocks `lo = W_f + W_g`, `hi = W_f - W_g` of two 8-variable halves. -/
def lo8 (f g : Vec 8 → Bool) (a : Vec 8) : Int := walshBool f a + walshBool g a
def hi8 (f g : Vec 8 → Bool) (a : Vec 8) : Int := walshBool f a - walshBool g a

/-- Number of inputs `x ∈ F_2^8` on which two 8-variable halves agree (`t = #{x : f(x) = g(x)}`). -/
def agreements8 (f g : Vec 8 → Bool) : Int :=
  sumVecs (fun x => if f x = g x then 1 else 0)

/-- Adapted balanced-242 halves `(f, g)` (every balanced 9-variable function with
    nonlinearity `≥ 242` reduces unconditionally in Lean to such a pair via a linear
    transvection). -/
def Adapted242 (f g : Vec 8 → Bool) : Prop :=
  (∀ a, hi8 f g a % 8 = 4) ∧
  (∀ a, (hi8 f g a).natAbs ≤ 28) ∧
  lo8 f g (fun _ => false) = 0 ∧
  (∀ a, lo8 f g a % 8 = 0) ∧
  (∀ a, (lo8 f g a).natAbs ≤ 24) ∧
  agreements8 f g % 2 = 0

/-- Complementary ternary pair condition: at every `x`, one entry is `0` and the other is `±1`. -/
def Complementary (v u : Int) : Prop :=
  (v = 0 ∧ (u = 1 ∨ u = -1)) ∨ (u = 0 ∧ (v = 1 ∨ v = -1))

/-- Direct `t = 116, k = 16` endpoint hypothesis (discharged independently by
    `nl242_endpoint_closure.zip` and `nl242_endpoint_crosscheck.zip`). -/
def EndpointK16Direct : Prop :=
  ¬ ∃ (u v : Vec 8 → Int),
      (∀ x, Complementary (v x) (u x)) ∧
      (∀ a, (walsh v a).natAbs = 4 ∨ (walsh v a).natAbs = 12) ∧
      (∀ a, (walsh u a).natAbs = 4 ∨ (walsh u a).natAbs = 12) ∧
      sumVecs (fun a => if (walsh u a).natAbs = 4 then (1 : Int) else 0) = 16

/-- Unrestricted covering-radius bound `ρ(1, 9) < 244`: no 9-variable Boolean function
    (balanced or unbalanced) has nonlinearity `≥ 244` (re-verified in `nl244_verify.zip`). -/
def CoveringRadius244 : Prop :=
  ¬ ∃ F : Vec 9 → Bool, hasNonlinearityAtLeast9 F 244

end NL242Challenge
