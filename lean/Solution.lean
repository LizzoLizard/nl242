/-
  Solution.lean — Complete, zero-`sorry`, zero-`native_decide` proof of every theorem in
  `Challenge.lean`, bridging the pure `Fin n → Bool` Hamming-distance challenge interface
  (`ChallengeDefs`) to the zero-Mathlib `Balanced242Master` formalization in `src/`.
-/
import ChallengeDefs
import Balanced242Master

namespace NL242Challenge

open FrozenShells CandyKnots CollisionLaw SilentRoom
open Balanced242Parents Balanced242Blocks Balanced242Support Balanced242Coord
open Balanced242No244 Balanced242Endpoint Balanced242LowRange
open Balanced242Z64Switch Balanced242T112 Balanced242T114 Balanced242T118
open Balanced242HighSections (complementary)
open Balanced242Reduction (clsA clsC hi_values)

/-! ## Bijection `Vec n ≃ W n` and exact bridge lemmas -/

private def toW : {n : Nat} → Vec n → W n
  | 0, _ => ()
  | _ + 1, v => (v ⟨0, Nat.zero_lt_succ _⟩, toW (tailVec v))

private def ofW : {n : Nat} → W n → Vec n
  | 0, _ => fun i => Fin.elim0 i
  | _ + 1, (b, w) => consVec b (ofW w)

private theorem toW_ofW : {n : Nat} → (w : W n) → toW (ofW w) = w
  | 0, () => rfl
  | _ + 1, (b, w) => by
    change (b, toW (fun i => ofW w i)) = (b, w)
    exact congrArg (b, ·) (toW_ofW w)

private theorem ofW_toW : {n : Nat} → (v : Vec n) → ofW (toW v) = v
  | 0, v => funext (fun i => Fin.elim0 i)
  | n + 1, v => funext fun i => by
    cases i with
    | mk k hk =>
      cases k with
      | zero => rfl
      | succ k =>
        change ofW (toW (tailVec v)) ⟨k, Nat.lt_of_succ_lt_succ hk⟩ = v ⟨k + 1, hk⟩
        rw [ofW_toW (tailVec v)]
        rfl

private theorem toW_zero : {n : Nat} → toW (fun _ : Fin n => false) = zero n
  | 0 => rfl
  | _ + 1 => congrArg (false, ·) toW_zero

private theorem sumVecs_eq_total : {n : Nat} → (g : Vec n → Int) →
    sumVecs g = total n (fun w => g (ofW w))
  | 0, g => by
    change g (fun i => Fin.elim0 i) = g (fun i => Fin.elim0 i)
    rfl
  | _ + 1, g => by
    simp only [sumVecs, total, ofW]
    rw [sumVecs_eq_total, sumVecs_eq_total]

private theorem dot_eq_W : {n : Nat} → (a x : Vec n) →
    dot a x = FrozenShells.dot n (toW a) (toW x)
  | 0, _, _ => rfl
  | _ + 1, a, x => by
    simp only [dot, toW, FrozenShells.dot]
    rw [dot_eq_W (tailVec a) (tailVec x)]

private theorem sign_eq (b : Bool) : NL242Challenge.sign b = CandyKnots.sign b := rfl

private theorem walsh_eq_transform {n : Nat} (g : Vec n → Int) (a : Vec n) :
    walsh g a = transform (fun w => g (ofW w)) (toW a) := by
  unfold walsh transform
  rw [sumVecs_eq_total]
  apply congrArg (total n)
  funext w
  rw [sign_eq, dot_eq_W a (ofW w), toW_ofW w]
  rfl

private theorem walshBool_eq_booleanSpec {n : Nat} (F : Vec n → Bool) (a : Vec n) :
    walshBool F a = booleanSpec (fun w => F (ofW w)) (toW a) := by
  unfold walshBool booleanSpec
  exact walsh_eq_transform (fun x => NL242Challenge.sign (F x)) a

private theorem lo8_eq (f g : Vec 8 → Bool) (a : Vec 8) :
    lo8 f g a = lo (fun w => f (ofW w)) (fun w => g (ofW w)) (toW a) := by
  unfold lo8 lo spec
  rw [walshBool_eq_booleanSpec, walshBool_eq_booleanSpec]
  rfl

private theorem hi8_eq (f g : Vec 8 → Bool) (a : Vec 8) :
    hi8 f g a = hi (fun w => f (ofW w)) (fun w => g (ofW w)) (toW a) := by
  unfold hi8 hi spec
  rw [walshBool_eq_booleanSpec, walshBool_eq_booleanSpec]
  rfl

private theorem agreements8_eq (f g : Vec 8 → Bool) :
    agreements8 f g = agreements (fun w => f (ofW w)) (fun w => g (ofW w)) := by
  unfold agreements8 agreements countPair
  rw [sumVecs_eq_total, ← total_add]
  apply congrArg (total 8)
  funext w
  dsimp only
  cases f (ofW w) <;> cases g (ofW w) <;> decide

/-! ## Exact Hamming-weight / Hamming-distance ↔ Walsh–Hadamard identities on `F_2^9` -/

private theorem total9_const_one : total 9 (fun _ => (1 : Int)) = 512 := by decide

private theorem sum_sign_eq_512_sub_2_weight (F : Vec 9 → Bool) :
    total 9 (fun w => CandyKnots.sign (F (ofW w))) = 512 - 2 * hammingWeight F := by
  unfold hammingWeight
  rw [sumVecs_eq_total, ← total9_const_one, ← total_scale, ← total_sub]
  apply congrArg (total 9)
  funext w
  dsimp only
  cases F (ofW w) <;> decide

private theorem walshBool_affine_dist (F : Vec 9 → Bool) (a : Vec 9) (c : Bool) :
    NL242Challenge.sign c * walshBool F a = 512 - 2 * hammingDist F (affine a c) := by
  unfold walshBool walsh hammingDist affine
  rw [sumVecs_eq_total, sumVecs_eq_total, ← total9_const_one, ← total_scale, ← total_scale, ← total_sub]
  apply congrArg (total 9)
  funext w
  dsimp only
  cases c <;> cases F (ofW w) <;> cases dot a (ofW w) <;> decide

private theorem isBalanced9_to_total (F : Vec 9 → Bool) (hbal : isBalanced9 F) :
    total 9 (fun w => CandyKnots.sign (F (ofW w))) = 0 := by
  rw [sum_sign_eq_512_sub_2_weight, hbal]
  decide

private theorem nl_to_walshCap (F : Vec 9 → Bool) (d : Int) (B : Nat)
    (hB : 512 - 2 * d = (B : Int)) (hnl : hasNonlinearityAtLeast9 F d) :
    ∀ a : Vec 9, (walshBool F a).natAbs ≤ B := by
  intro a
  have h0 := walshBool_affine_dist F a false
  have h1 := walshBool_affine_dist F a true
  have hd0 := hnl a false
  have hd1 := hnl a true
  simp only [NL242Challenge.sign, Bool.false_eq_true, ite_false, ite_true] at h0 h1
  omega

private theorem walshCap_to_nl (F : Vec 9 → Bool) (d : Int) (B : Nat)
    (hB : 512 - 2 * d = (B : Int)) (hcap : ∀ a : Vec 9, (walshBool F a).natAbs ≤ B) :
    hasNonlinearityAtLeast9 F d := by
  intro a c
  have hc := walshBool_affine_dist F a c
  have ha := hcap a
  cases c
  · simp only [NL242Challenge.sign, Bool.false_eq_true, ite_false] at hc
    omega
  · simp only [NL242Challenge.sign, ite_true] at hc
    omega

/-! ## Bridge between `Vec 8` and `W 8` structures -/

private theorem adapted_to_W (f g : Vec 8 → Bool) (had : Adapted242 f g) :
    Balanced242Master.Adapted242 (fun w => f (ofW w)) (fun w => g (ofW w)) := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := had
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a; have := h1 (ofW a); rw [hi8_eq, toW_ofW] at this; exact this
  · intro a; have := h2 (ofW a); rw [hi8_eq, toW_ofW] at this; exact this
  · rw [← toW_zero]; rw [lo8_eq] at h3; exact h3
  · intro a; have := h4 (ofW a); rw [lo8_eq, toW_ofW] at this; exact this
  · intro a; have := h5 (ofW a); rw [lo8_eq, toW_ofW] at this; exact this
  · rw [← agreements8_eq]; exact h6

private theorem adapted_of_W (f g : Half) (had : Balanced242Master.Adapted242 f g) :
    Adapted242 (fun v => f (toW v)) (fun v => g (toW v)) := by
  have hf : (fun w => f (toW (ofW w))) = f := funext fun w => congrArg f (toW_ofW w)
  have hg : (fun w => g (toW (ofW w))) = g := funext fun w => congrArg g (toW_ofW w)
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := had
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a; rw [hi8_eq, hf, hg]; exact h1 (toW a)
  · intro a; rw [hi8_eq, hf, hg]; exact h2 (toW a)
  · rw [lo8_eq, hf, hg, toW_zero]; exact h3
  · intro a; rw [lo8_eq, hf, hg]; exact h4 (toW a)
  · intro a; rw [lo8_eq, hf, hg]; exact h5 (toW a)
  · rw [agreements8_eq, hf, hg]; exact h6

private theorem walshBool_cons9 (f g : Vec 8 → Bool) (b : Bool) (a : Vec 8) :
    walshBool (fun v : Vec 9 => if v ⟨0, by decide⟩ then g (tailVec v) else f (tailVec v))
      (consVec b a) =
    if b then hi8 f g a else lo8 f g a := by
  unfold walshBool walsh sumVecs lo8 hi8
  have h1 : ∀ v : Vec 8,
      NL242Challenge.sign (if consVec false v ⟨0, by decide⟩ then g (tailVec (consVec false v)) else f (tailVec (consVec false v))) *
      NL242Challenge.sign (dot (consVec b a) (consVec false v)) =
      NL242Challenge.sign (f v) * NL242Challenge.sign (dot a v) := by
    intro v
    change NL242Challenge.sign (f v) * NL242Challenge.sign (xor (b && false) (dot a v)) = _
    simp
  have h2 : ∀ v : Vec 8,
      NL242Challenge.sign (if consVec true v ⟨0, by decide⟩ then g (tailVec (consVec true v)) else f (tailVec (consVec true v))) *
      NL242Challenge.sign (dot (consVec b a) (consVec true v)) =
      (if b then -(NL242Challenge.sign (g v) * NL242Challenge.sign (dot a v))
            else  (NL242Challenge.sign (g v) * NL242Challenge.sign (dot a v))) := by
    intro v
    change NL242Challenge.sign (g v) * NL242Challenge.sign (xor (b && true) (dot a v)) = _
    cases b <;> cases dot a v <;> cases g v <;> decide
  simp only [h1, h2]
  cases b
  · rfl
  · simp only [ite_true, walshBool, walsh]
    rw [sumVecs_eq_total, sumVecs_eq_total, sumVecs_eq_total, ← total_add, ← total_sub]
    apply congrArg (total 8); funext w; omega

private theorem coveringRadius_to_W (hcov : CoveringRadius244) :
    Balanced242Z64Switch.CoveringRadius244 := by
  intro ⟨f', g', hcap⟩
  apply hcov
  let f : Vec 8 → Bool := fun v => f' (toW v)
  let g : Vec 8 → Bool := fun v => g' (toW v)
  let F : Vec 9 → Bool := fun v => if v ⟨0, by decide⟩ then g (tailVec v) else f (tailVec v)
  have hf : (fun w => f (ofW w)) = f' := funext fun w => congrArg f' (toW_ofW w)
  have hg : (fun w => g (ofW w)) = g' := funext fun w => congrArg g' (toW_ofW w)
  refine ⟨F, walshCap_to_nl F 244 24 (by decide) fun a => ?_⟩
  have ha : a = consVec (a ⟨0, by decide⟩) (tailVec a) := by
    funext i; cases i with | mk k hk => cases k <;> rfl
  rw [ha, walshBool_cons9]
  cases a ⟨0, by decide⟩
  · simp only [Bool.false_eq_true, ite_false]
    rw [lo8_eq, hf, hg]
    exact (hcap (toW (tailVec a))).1
  · simp only [ite_true]
    rw [hi8_eq, hf, hg]
    exact (hcap (toW (tailVec a))).2

private theorem endpointK16_to_W (h116 : EndpointK16Direct) :
    Balanced242Master.EndpointK16Direct := by
  intro ⟨u, v, hcomp, hv, hu, hcnt⟩
  apply h116
  let u' : Vec 8 → Int := fun x => u (toW x)
  let v' : Vec 8 → Int := fun x => v (toW x)
  have hu_eq : (fun w => u' (ofW w)) = u := funext fun w => congrArg u (toW_ofW w)
  have hv_eq : (fun w => v' (ofW w)) = v := funext fun w => congrArg v (toW_ofW w)
  refine ⟨u', v', ?_, ?_, ?_, ?_⟩
  · intro x; exact hcomp (toW x)
  · intro a; rw [walsh_eq_transform, hv_eq]; exact hv (toW a)
  · intro a; rw [walsh_eq_transform, hu_eq]; exact hu (toW a)
  · rw [sumVecs_eq_total]
    have hpt : (fun w => if (walsh u' (ofW w)).natAbs = 4 then (1 : Int) else 0) =
               (fun w => if (transform u w).natAbs = 4 then (1 : Int) else 0) := by
      funext w; rw [walsh_eq_transform, hu_eq, toW_ofW]
    rw [hpt]; exact hcnt

/-! ## Solutions to all 8 Challenge theorems -/

theorem no_balanced_9var_nl244 (F : Vec 9 → Bool)
    (hbal : isBalanced9 F) (hnl : hasNonlinearityAtLeast9 F 244) : False := by
  let F' : W 9 → Bool := fun w => F (ofW w)
  have hbal' : total 9 (fun x => CandyKnots.sign (F' x)) = 0 := isBalanced9_to_total F hbal
  have hcap := nl_to_walshCap F 244 24 (by decide) hnl
  have hcap' : ∀ a : W 9, (booleanSpec F' a).natAbs ≤ 24 := fun a => by
    have := hcap (ofW a)
    rw [walshBool_eq_booleanSpec, toW_ofW] at this
    exact this
  exact no_balanced_nl244 F' hbal' hcap'

theorem no_adapted_t112 (f g : Vec 8 → Bool)
    (had : Adapted242 f g) (ht : agreements8 f g = 112) : False := by
  obtain ⟨res, hicap, dc, lores, locap, _⟩ := adapted_to_W f g had
  rw [agreements8_eq] at ht
  exact no_t112 _ _ res hicap dc lores locap ht

theorem no_adapted_t114 (f g : Vec 8 → Bool)
    (had : Adapted242 f g) (ht : agreements8 f g = 114) : False := by
  obtain ⟨res, hicap, dc, lores, locap, _⟩ := adapted_to_W f g had
  rw [agreements8_eq] at ht
  exact no_t114 _ _ res hicap dc lores locap ht

theorem no_adapted_t118 (f g : Vec 8 → Bool)
    (had : Adapted242 f g) (ht : agreements8 f g = 118) : False := by
  obtain ⟨_, _, dc, lores, locap, _⟩ := adapted_to_W f g had
  rw [agreements8_eq] at ht
  exact no_t118 _ _ dc lores locap ht

theorem no_adapted_t_ge_120 (f g : Vec 8 → Bool)
    (had : Adapted242 f g) (ht : 120 ≤ agreements8 f g) : False := by
  obtain ⟨_, _, dc, lores, locap, _⟩ := adapted_to_W f g had
  rw [agreements8_eq] at ht
  have hlt := low_agreements_below_120 _ _ dc lores locap
  omega

theorem endpointK16_of_coveringRadius (hcov : CoveringRadius244) : EndpointK16Direct := by
  have hW := Balanced242Master.endpointK16_of_coveringRadius (coveringRadius_to_W hcov)
  intro ⟨u, v, hcomp, hv, hu, hcnt⟩
  apply hW
  let uW : W 8 → Int := fun w => u (ofW w)
  let vW : W 8 → Int := fun w => v (ofW w)
  refine ⟨uW, vW, ?_, ?_, ?_, ?_⟩
  · intro w; exact hcomp (ofW w)
  · intro a; have := hv (ofW a); rw [walsh_eq_transform, toW_ofW] at this; exact this
  · intro a; have := hu (ofW a); rw [walsh_eq_transform, toW_ofW] at this; exact this
  · rw [sumVecs_eq_total] at hcnt
    have hpt : (fun w => if (walsh u (ofW w)).natAbs = 4 then (1 : Int) else 0) =
               (fun w => if (transform uW w).natAbs = 4 then (1 : Int) else 0) := by
      funext w; rw [walsh_eq_transform, toW_ofW]
    rw [← hpt]; exact hcnt

theorem no_balanced_9var_nl242_direct (F : Vec 9 → Bool)
    (hbal : isBalanced9 F)
    (hnl : hasNonlinearityAtLeast9 F 242)
    (h_le_110 : ∀ f g : Vec 8 → Bool, Adapted242 f g → agreements8 f g ≤ 110 → False)
    (h116 : EndpointK16Direct) : False := by
  let F' : W 9 → Bool := fun w => F (ofW w)
  have hbal' : total 9 (fun x => CandyKnots.sign (F' x)) = 0 := isBalanced9_to_total F hbal
  have hcap := nl_to_walshCap F 242 28 (by decide) hnl
  have hcap' : ∀ a : W 9, (booleanSpec F' a).natAbs ≤ 28 := fun a => by
    have := hcap (ofW a)
    rw [walshBool_eq_booleanSpec, toW_ofW] at this
    exact this
  have hs := supportXor_ne_zero_of_cap28 F' hbal' hcap'
  obtain ⟨f, g, haxis, hbal_fg, hlo_m, hhi_m, _⟩ := to_adapted F' hbal' hs
  have hcap_fg : ∀ a, (lo f g a).natAbs ≤ 28 ∧ (hi f g a).natAbs ≤ 28 := fun a => by
    obtain ⟨b1, hb1⟩ := hlo_m a; obtain ⟨b2, hb2⟩ := hhi_m a
    exact ⟨hb1 ▸ hcap' b1, hb2 ▸ hcap' b2⟩
  have split : total 8 (fun x => CandyKnots.sign (f x) + CandyKnots.sign (g x)) = 0 := by
    rw [total_add]; exact hbal_fg
  have dc : lo f g (zero 8) = 0 := by
    simpa [lo, spec, transform, chr, dot_zero, CandyKnots.sign, total_add] using split
  have lores (a : W 8) := (adapted_blocks f g haxis hbal_fg a).1
  have res (a : W 8) := (adapted_blocks f g haxis hbal_fg a).2
  have hicap (a : W 8) := (hcap_fg a).2
  have locap (a : W 8) : (lo f g a).natAbs ≤ 24 := by
    have := (hcap_fg a).1; have := lores a; omega
  have heven : agreements f g % 2 = 0 := agreements_even f g hbal_fg
  have hlt120 : agreements f g < 120 := low_agreements_below_120 f g dc lores locap
  have hadW : Balanced242Master.Adapted242 f g := ⟨res, hicap, dc, lores, locap, heven⟩
  by_cases hle : agreements f g ≤ 110
  · have hV := adapted_of_W f g hadW
    have hf : (fun w => f (toW (ofW w))) = f := funext fun w => congrArg f (toW_ofW w)
    have hg : (fun w => g (toW (ofW w))) = g := funext fun w => congrArg g (toW_ofW w)
    apply h_le_110 (fun v => f (toW v)) (fun v => g (toW v)) hV
    rw [agreements8_eq, hf, hg]; exact hle
  · have ht_cases :
        agreements f g = 112 ∨ agreements f g = 114 ∨
        agreements f g = 116 ∨ agreements f g = 118 := by omega
    rcases ht_cases with ht | ht | ht | ht
    · exact no_t112 f g res hicap dc lores locap ht
    · exact no_t114 f g res hicap dc lores locap ht
    · have hk16 := t116_forces_k16 f g res hicap dc lores locap ht
      obtain ⟨u, v, hcomp_uv, hv_lev, hu_lev⟩ :=
        endpoint_switched_blocks f g res hicap dc lores locap (Or.inr ht)
      apply endpointK16_to_W h116
      refine ⟨u, v, hcomp_uv, hv_lev, ?_, ?_⟩
      · intro a; rw [hu_lev a]; cases clsA f g a || clsC f g a <;> simp
      · have hpt (a : W 8) : (if (transform u a).natAbs = 4 then (1 : Int) else 0) =
            Balanced242Reduction.ind (clsA f g) a + Balanced242Reduction.ind (clsC f g) a := by
          rw [hu_lev a]
          unfold Balanced242Reduction.ind clsA clsC
          rcases hi_values f g res hicap a with h | h | h | h | h | h | h | h <;> rw [h] <;> decide
        rw [funext hpt, total_add]
        exact hk16
    · exact no_t118 f g dc lores locap ht

theorem no_balanced_9var_nl242_covering (F : Vec 9 → Bool)
    (hbal : isBalanced9 F)
    (hnl : hasNonlinearityAtLeast9 F 242)
    (h_le_110 : ∀ f g : Vec 8 → Bool, Adapted242 f g → agreements8 f g ≤ 110 → False)
    (hcov : CoveringRadius244) : False :=
  no_balanced_9var_nl242_direct F hbal hnl h_le_110 (endpointK16_of_coveringRadius hcov)

#print axioms no_balanced_9var_nl244
#print axioms no_adapted_t112
#print axioms no_adapted_t114
#print axioms no_adapted_t118
#print axioms no_adapted_t_ge_120
#print axioms endpointK16_of_coveringRadius
#print axioms no_balanced_9var_nl242_direct
#print axioms no_balanced_9var_nl242_covering

end NL242Challenge
