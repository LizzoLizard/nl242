/-
  Balanced242Z64Switch.lean — Complete Lean 4 formalization of the `|Z| = 64` (rank-2
  residue-flat) affine-span obstruction and plane-switching reduction from `AGREEMENT_RANGE.md`:

    1. `z64_small_masks_ge_9`: whenever `rr (β8 f g) = 64` and `Zc f g = 64`,
       `9 ≤ cnt (clsA f g) + cnt (clsC f g)` (proved unconditionally via constructive
       orthogonal-direction counting on `W 8` and mod-3 ternary inversion `U_0`, zero choice!).
    2. `no_Z64_of_t_le_112`: **UNCONDITIONAL** exclusion of `|Z| = 64` for ALL `t ≤ 112`
       (ZERO covering-radius hypothesis, ZERO `SectionEnum`!).
    3. `t112_forces_rank4_Z96`: at `t = 112`, ONLY rank 4 (`rr = 16, Zc = 96`) can survive
       (unconditional!).
    4. `z64_plane_switch_114_116`: at `t = 114` or `t = 116`, constructs an explicit 9-variable
       Boolean function `(f', g')` with `∀ a, |lo f' g' a| ≤ 24 ∧ |hi f' g' a| ≤ 24`
       (via `Balanced242HighSections.plane_switch`), immediately excluding BOTH `t = 114`
       and `t = 116` under the Wang–Lou–Wang covering-radius bound `CoveringRadius244`!

  Zero Mathlib, zero `sorry`, zero `native_decide`, zero `SectionEnum`, zero custom axioms.
-/
import Balanced242LowBlock

namespace Balanced242Z64Switch

open FrozenShells FreezeMovies CandyKnots CollisionLaw MaskRecovery SilentRoom
open Balanced242Parents Balanced242Support Balanced242Hyperplane Balanced242Reduction
open Balanced242Plateau Balanced242Rank Balanced242Global Balanced242RankCond
open Balanced242SectionFacts Balanced242QuarticHighBlock Balanced242LowBlock
open Balanced242HighSections (complementary plane_switch)

local notation "bind" => Balanced242Plateau.ind

/-- The Wang–Lou–Wang covering-radius bound `ρ(1, 9) < 244`: no 9-variable Boolean function
    `(f', g')` has all Walsh coefficients bounded by 24 in magnitude (nonlinearity ≥ 244). -/
def CoveringRadius244 : Prop :=
  ¬ ∃ f' g' : Half, ∀ a : W 8, (lo f' g' a).natAbs ≤ 24 ∧ (hi f' g' a).natAbs ≤ 24

/-- Balanced ternary residue modulo 3 in `{-1, 0, 1}`. -/
def mods3 (z : Int) : Int :=
  if z % 3 = 1 then 1 else if z % 3 = 2 then -1 else 0

private theorem mods3_spec (z : Int) :
    (mods3 z = -1 ∨ mods3 z = 0 ∨ mods3 z = 1) ∧
    (mods3 z - z) % 3 = 0 ∧
    mods3 (-z) = -mods3 z := by
  unfold mods3
  have hm : z % 3 = 0 ∨ z % 3 = 1 ∨ z % 3 = 2 := by omega
  rcases hm with h | h | h
  · have hneg : (-z) % 3 = 0 := by omega
    simp [h, hneg]
  · have hneg : (-z) % 3 = 2 := by omega
    simp [h, hneg]; omega
  · have hneg : (-z) % 3 = 1 := by omega
    simp [h, hneg]; omega

private theorem mods3_eq_of_ternary (u z : Int) (hu : u = -1 ∨ u = 0 ∨ u = 1)
    (hmod : (u - z) % 3 = 0) : u = mods3 z := by
  have ⟨hm, hmz, _⟩ := mods3_spec z
  rcases hu with rfl | rfl | rfl <;> rcases hm with h | h | h <;> rw [h] at hmz ⊢ <;> omega

/-- Constructive linear-algebra counting lemma on `W 8`: any list `L : List (W 8)` of length `≤ 7`
    has a nonzero vector `d : W 8` orthogonal to EVERY element of `L`!
    Proof: `#{d : ∀ x ∈ L, dot 8 d x = false} ≥ 256 / 2^(L.length) ≥ 2 > 1` by halving! -/
private theorem exists_ortho_nonzero (L : List (W 8)) (hlen : L.length ≤ 7) :
    ∃ d : W 8, d ≠ zero 8 ∧ ∀ x, x ∈ L → dot 8 d x = false := by
  have hcount : ∀ (M : List (W 8)),
      (2 : Int) ^ M.length * total 8 (fun d => if M.all (fun x => !dot 8 d x) then (1 : Int) else 0) ≥ 256 := by
    intro M
    induction M with
    | nil =>
      simp only [List.length_nil, Int.pow_zero, Int.one_mul, List.all_nil, if_true, total_const]
      decide
    | cons v rest ih =>
      -- Halving step: for any predicate `P d := rest.all (fun x => !dot d x)`,
      -- either `∀ d, P d → dot d v = false` (count unchanged, ×2 ≥ 256) or some `d0` has
      -- `P d0 = true ∧ dot d0 v = true`, in which case `d ↦ add 8 d d0` pairs `P ∧ !dot v`
      -- bijectively with `P ∧ dot v`, so `2 * #(P ∧ !dot v) = #P`!
      let P : W 8 → Bool := fun d => rest.all (fun x => !dot 8 d x)
      have hP_add (d1 d2 : W 8) (h1 : P d1 = true) : P (add 8 d1 d2) = P d2 := by
        dsimp only [P] at h1 ⊢
        rw [List.all_eq_true] at h1
        have haux : ∀ (R : List (W 8)), (∀ x ∈ R, (!dot 8 d1 x) = true) →
            R.all (fun x => !dot 8 (add 8 d1 d2) x) = R.all (fun x => !dot 8 d2 x) := by
          intro R hR; induction R with
          | nil => rfl
          | cons y ys ihy =>
            simp only [List.all_cons]
            have hy := hR y (List.mem_cons_self _ _)
            have hd1 : dot 8 d1 y = false := by cases h : dot 8 d1 y <;> rw [h] at hy <;> simp_all
            have hadd : dot 8 (add 8 d1 d2) y = dot 8 d2 y := by
              rw [dot_comm 8 (add 8 d1 d2) y, dot_right, dot_comm 8 y d1, dot_comm 8 y d2, hd1, Bool.false_xor]
            rw [hadd, ihy (fun x hx => hR x (List.mem_cons_of_mem _ hx))]
        exact haux rest h1
      have hhalf : 2 * total 8 (fun d => if P d && !dot 8 d v then (1 : Int) else 0) ≥
          total 8 (fun d => if P d then (1 : Int) else 0) := by
        cases hex : (worlds 8).all (fun d => !(P d && dot 8 d v))
        · obtain ⟨d0, _, hd0⟩ := all_false_exists _ _ hex
          have hPd0 : P d0 = true := by cases h : P d0 <;> rw [h] at hd0 <;> simp_all
          have hdv0 : dot 8 d0 v = true := by cases h : dot 8 d0 v <;> rw [h, hPd0] at hd0 <;> simp_all
          have hsh := sum_shift 8 d0 (fun d => if P d && !dot 8 d v then (1 : Int) else 0)
          have hpt (d : W 8) :
              (if P (add 8 d0 d) && !dot 8 (add 8 d0 d) v then (1 : Int) else 0) =
              (if P d && dot 8 d v then (1 : Int) else 0) := by
            rw [hP_add d0 d hPd0, dot_comm 8 (add 8 d0 d) v, dot_right,
                dot_comm 8 v d0, dot_comm 8 v d, hdv0]
            cases P d <;> cases dot 8 d v <;> decide
          rw [funext hpt] at hsh
          have hsplit : total 8 (fun d => if P d then (1 : Int) else 0) =
              total 8 (fun d => if P d && !dot 8 d v then (1 : Int) else 0) +
              total 8 (fun d => if P d && dot 8 d v then (1 : Int) else 0) := by
            rw [← total_add]; apply congrArg (total 8); funext d
            cases P d <;> cases dot 8 d v <;> decide
          omega
        · rw [List.all_eq_true] at hex
          have heq : total 8 (fun d => if P d && !dot 8 d v then (1 : Int) else 0) =
              total 8 (fun d => if P d then (1 : Int) else 0) := by
            apply congrArg (total 8); funext d
            have hd := hex d (all_worlds 8 d)
            cases hP : P d <;> cases hdv : dot 8 d v <;> rw [hP, hdv] at hd <;> simp_all
          have hnn : 0 ≤ total 8 (fun d => if P d then (1 : Int) else 0) :=
            total_nonneg _ (fun d => by split <;> omega)
          omega
      have hcomm : (fun d => if (v :: rest).all (fun x => !dot 8 d x) then (1 : Int) else 0) =
          fun d => if P d && !dot 8 d v then (1 : Int) else 0 := by
        funext d; dsimp only [P]; simp only [List.all_cons, Bool.and_comm]
      rw [hcomm, List.length_cons, Int.pow_succ]
      have hpos : (0 : Int) ≤ (2 : Int) ^ rest.length := by
        clear ih hhalf; induction rest.length with | zero => decide | succ k hk => rw [Int.pow_succ]; omega
      have hmul := Int.mul_le_mul_of_nonneg_left hhalf hpos
      have hre : (2 : Int) ^ rest.length * (2 * total 8 fun d => if P d && !dot 8 d v then (1 : Int) else 0) =
          (2 : Int) ^ rest.length * 2 * total 8 fun d => if P d && !dot 8 d v then (1 : Int) else 0 := by ac_rfl
      dsimp only [P] at hmul hre ⊢
      omega
  have hc := hcount L
  have hpow : (2 : Int) ^ L.length ≤ 128 := by
    have : ∀ k : Nat, k ≤ 7 → (2 : Int) ^ k ≤ 128 := by
      intro k hk; match k with
      | 0 => decide | 1 => decide | 2 => decide | 3 => decide
      | 4 => decide | 5 => decide | 6 => decide | 7 => decide | _ + 8 => omega
    exact this L.length hlen
  have hge2 : 2 ≤ total 8 (fun d => if L.all (fun x => !dot 8 d x) then (1 : Int) else 0) := by
    have hnn : 0 ≤ total 8 (fun d => if L.all (fun x => !dot 8 d x) then (1 : Int) else 0) :=
      total_nonneg _ (fun d => by split <;> omega)
    have h1 : (2 : Int) ^ L.length * total 8 (fun d => if L.all (fun x => !dot 8 d x) then (1 : Int) else 0) ≤
        128 * total 8 (fun d => if L.all (fun x => !dot 8 d x) then (1 : Int) else 0) :=
      Int.mul_le_mul_of_nonneg_right hpow hnn
    omega
  cases hall : (worlds 8).all (fun d => decide (d = zero 8) || !L.all (fun x => !dot 8 d x))
  · obtain ⟨d, _, hd⟩ := all_false_exists _ _ hall
    have hd_ne : d ≠ zero 8 := by intro hz; subst hz; simp at hd
    have hd_all : L.all (fun x => !dot 8 d x) = true := by
      cases h : L.all (fun x => !dot 8 d x) <;> rw [h] at hd <;> simp_all
    rw [List.all_eq_true] at hd_all
    refine ⟨d, hd_ne, fun x hx => ?_⟩
    have hx' := hd_all x hx
    cases h : dot 8 d x <;> rw [h] at hx' <;> simp_all
  · exfalso
    rw [List.all_eq_true] at hall
    have hle1 : total 8 (fun d => if L.all (fun x => !dot 8 d x) then (1 : Int) else 0) ≤ 1 := by
      have hpt (d : W 8) : (if L.all (fun x => !dot 8 d x) then (1 : Int) else 0) ≤ hits (zero 8) d := by
        have hd := hall d (all_worlds 8 d)
        by_cases hz : d = zero 8
        · subst hz; unfold hits; simp; split <;> omega
        · have hne : ¬ zero 8 = d := fun h => hz h.symm
          have hdec : decide (d = zero 8) = false := decide_eq_false hz
          rw [hdec, Bool.false_or] at hd
          have hf : L.all (fun x => !dot 8 d x) = false := by
            cases h : L.all (fun x => !dot 8 d x) <;> rw [h] at hd <;> simp_all
          unfold hits; simp [hne, hf]
      have hm := total_mono 8 _ _ hpt; rw [diagonal] at hm; exact hm
    omega

/-- Signed plane dual `S_P(x) = transform (q8 f g) x / 128` at `rr = 64` (`|P| = 4`). -/
def Splane (f g : Half) (x : W 8) : Int := transform (q8 f g) x / 128

private theorem Splane_spec (f g : Half) (res : ∀ a, hi f g a % 8 = 4) (hrr : rr (β8 f g) = 64) :
    (∀ x, (good (β8 f g) x = true → Splane f g x = 1 ∨ Splane f g x = -1) ∧
          (good (β8 f g) x = false → Splane f g x = 0)) ∧
    (∀ x, transform (q8 f g) x = 128 * Splane f g x) ∧
    (∀ a, transform (Splane f g) a = 2 * q8 f g a) := by
  have hm8 : many 8 = 256 := by decide
  have hMM : (128 : Int) * 128 = many 8 * rr (β8 f g) := by rw [hm8, hrr]; decide
  have hval (x : W 8) :
      (good (β8 f g) x = true → Splane f g x = 1 ∨ Splane f g x = -1) ∧
      (good (β8 f g) x = false → Splane f g x = 0) := by
    have hv := Balanced242Rank.spec_values (β8 f g) (cube8 f g res) 128 hMM x
    constructor
    · intro hg
      rcases hv.1 hg with h | h <;> unfold Splane <;> change transform (q8 f g) x = _ at h <;> rw [h] <;> decide
    · intro hng
      have h := hv.2 hng; unfold Splane; change transform (q8 f g) x = 0 at h; rw [h]; decide
  have hmul (x : W 8) : transform (q8 f g) x = 128 * Splane f g x := by
    have hv := Balanced242Rank.spec_values (β8 f g) (cube8 f g res) 128 hMM x
    cases hg : good (β8 f g) x
    · have h := hv.2 hg; change transform (q8 f g) x = 0 at h; rw [h, (hval x).2 hg]; decide
    · rcases hv.1 hg with h | h <;> change transform (q8 f g) x = _ at h <;> unfold Splane <;> rw [h] <;> decide
  have hinv (a : W 8) : transform (Splane f g) a = 2 * q8 f g a := by
    have hi := transform_involution (q8 f g) a
    rw [hm8] at hi
    have htr : transform (transform (q8 f g)) a = 128 * transform (Splane f g) a := by
      rw [show transform (q8 f g) = fun x => 128 * Splane f g x from funext hmul]
      unfold transform
      have hpt (x : W 8) : 128 * Splane f g x * chr a x = 128 * (Splane f g x * chr a x) := Int.mul_assoc _ _ _
      rw [funext hpt, total_scale]
    rw [htr] at hi; omega
  exact ⟨hval, hmul, hinv⟩

/-- **Theorem 1 (`z64_small_masks_ge_9`)**: Whenever `rr (β8 f g) = 64` (rank 2),
    there are at least 9 small high masks: `9 ≤ cnt (clsA f g) + cnt (clsC f g)`!
    (Proved 100% constructively via mod-3 ternary inversion `U_0` — zero `SectionEnum`, zero choice!) -/
theorem z64_small_masks_ge_9 (f g : Half) (res : ∀ a, hi f g a % 8 = 4)
    (cap : ∀ a, (hi f g a).natAbs ≤ 28) (hrr : rr (β8 f g) = 64) :
    9 ≤ cnt (clsA f g) + cnt (clsC f g) := by
  by_cases hge : 9 ≤ cnt (clsA f g) + cnt (clsC f g)
  · exact hge
  · exfalso
    let Kset : W 8 → Bool := fun a => clsA f g a || clsC f g a
    have hKcnt : ((Balanced242Krawtchouk.suppList Kset).length : Int) = cnt (clsA f g) + cnt (clsC f g) := by
      have h1 := Balanced242Farkas.suppList_length_eq_total Kset
      rw [h1]; unfold cnt; rw [← total_add]
      apply congrArg (total 8); funext a
      dsimp only [Kset]; unfold Balanced242Plateau.ind Balanced242Reduction.ind clsA clsC
      rcases hi_values f g res cap a with h | h | h | h | h | h | h | h <;> rw [h] <;> decide
    have hKlen : (Balanced242Krawtchouk.suppList Kset).length ≤ 8 := by omega
    -- Find a hyperplane `{a : dot 8 d a = c0}` containing ALL of `Kset`!
    have hex_plane : ∃ (d : W 8) (c0 : Bool), d ≠ zero 8 ∧ ∀ a, Kset a = true → dot 8 d a = c0 := by
      cases hL : Balanced242Krawtchouk.suppList Kset with
      | nil =>
        refine ⟨(true, zero 7), false, fun h => Bool.noConfusion (congrArg Prod.fst h), fun a ha => ?_⟩
        exfalso
        have hm : a ∈ Balanced242Krawtchouk.suppList Kset := by
          unfold Balanced242Krawtchouk.suppList; rw [List.mem_filter]; exact ⟨all_worlds 8 a, ha⟩
        rw [hL] at hm; nomatch hm
      | cons a0 rest =>
        have hrlen : rest.length ≤ 7 := by rw [hL, List.length_cons] at hKlen; omega
        let diffs := rest.map (fun a => add 8 a a0)
        have hdlen : diffs.length ≤ 7 := by dsimp only [diffs]; rw [List.length_map]; exact hrlen
        obtain ⟨d, hd_ne, hd_orth⟩ := exists_ortho_nonzero diffs hdlen
        refine ⟨d, dot 8 d a0, hd_ne, fun a ha => ?_⟩
        have hm : a ∈ a0 :: rest := by
          rw [← hL]; unfold Balanced242Krawtchouk.suppList; rw [List.mem_filter]; exact ⟨all_worlds 8 a, ha⟩
        rcases List.mem_cons.mp hm with rfl | hrest
        · rfl
        · have hdm : add 8 a a0 ∈ diffs := List.mem_map.mpr ⟨a, hrest, rfl⟩
          have h0 := hd_orth (add 8 a a0) hdm
          rw [dot_right] at h0
          cases h1 : dot 8 d a <;> cases h2 : dot 8 d a0 <;> rw [h1, h2] at h0 <;> simp_all
    obtain ⟨d, c0, hd_ne, hK_plane⟩ := hex_plane
    -- Define `J(a) := if Kset a then H8 f g a + q8 f g a else 0` and `U0(x) := mods3 (-transform J x)`.
    let J : W 8 → Int := fun a => if Kset a then H8 f g a + q8 f g a else 0
    let U0 : W 8 → Int := fun x => mods3 (-transform J x)
    obtain ⟨hSval, hSmul, _⟩ := Splane_spec f g res hrr
    -- Pointwise `H8 a + q8 a ≡ J a (mod 3)`:
    have hHJ_mod3 (a : W 8) : (H8 f g a + q8 f g a - J a) % 3 = 0 := by
      dsimp only [J, Kset]
      have hqH := q8_point f g res cap a
      have hq : q8 f g a = 1 ∨ q8 f g a = -1 := sign_vals _
      unfold Balanced242Reduction.ind clsA clsB clsC at hqH
      unfold clsA clsC
      have h4 : hi f g a = 4 * H8 f g a := by have hr := res a; unfold H8; omega
      rcases hi_values f g res cap a with h | h | h | h | h | h | h | h <;>
        (rw [h] at hqH h4 ⊢; rcases hq with hq1 | hq1 <;> (rw [hq1] at hqH ⊢; simp at hqH ⊢ <;> omega))
    -- Hence `transform (H8 + q8) x = 128 * (U x + Splane x) ≡ transform J x (mod 3)`:
    have hU0_off (x : W 8) (hng : good (β8 f g) x = false) : U f g x = U0 x := by
      have hmod3 : (transform (fun a => H8 f g a + q8 f g a) x - transform J x) % 3 = 0 := by
        unfold transform; rw [← total_sub]
        have aux : ∀ {m : Nat} (F : W m → Int), (∀ y, F y % 3 = 0) → total m F % 3 = 0 := by
          intro m; induction m with
          | zero => intro F hF; exact hF ()
          | succ k ih =>
            intro F hF
            show (total k (fun z => F (false, z)) + total k (fun z => F (true, z))) % 3 = 0
            rw [Int.add_emod, ih _ (fun z => hF (false, z)), ih _ (fun z => hF (true, z))]; rfl
        apply aux; intro a
        have hsub : (H8 f g a + q8 f g a) * chr x a - J a * chr x a =
            (H8 f g a + q8 f g a - J a) * chr x a := by rw [Int.sub_mul]
        rw [hsub, Int.mul_emod, hHJ_mod3 a, Int.zero_mul]; rfl
      have htrH : transform (H8 f g) x = 128 * U f g x := by
        have h2 : 2 * transform (H8 f g) x = transform (transform (U f g)) x := by
          unfold transform; rw [← total_scale]
          apply congrArg (total 8); funext w
          have hs := spec8 f g res w; unfold transform at hs
          rw [← Int.mul_assoc, hs]
        rw [transform_involution] at h2
        have hm8 : many 8 = 256 := by decide
        rw [hm8] at h2; omega
      have htrHQ : transform (fun a => H8 f g a + q8 f g a) x = 128 * U f g x + 128 * Splane f g x := by
        unfold transform
        have hpt (a : W 8) : (H8 f g a + q8 f g a) * chr x a = H8 f g a * chr x a + q8 f g a * chr x a :=
          Int.add_mul _ _ _
        rw [funext hpt, total_add]
        change transform (H8 f g) x + transform (q8 f g) x = _
        rw [htrH, hSmul x]
      rw [htrHQ, (hSval x).2 hng, Int.mul_zero, Int.add_zero] at hmod3
      have hUb := U_bound f g x
      exact mods3_eq_of_ternary (U f g x) (-transform J x) (by omega) (by omega)
    -- `U0` has symmetry `U0 (add 8 x d) = sign c0 * U0 x`!
    have hU0_sym (x : W 8) : U0 (add 8 x d) = sign c0 * U0 x := by
      have hJtr : transform J (add 8 x d) = sign c0 * transform J x := by
        unfold transform; rw [← total_scale]
        apply congrArg (total 8); funext a
        dsimp only [J]
        cases hKa : Kset a
        · simp
        · simp only [if_true]
          have hda := hK_plane a hKa
          have hchr : chr (add 8 x d) a = sign c0 * chr x a := by
            unfold chr; rw [dot_comm 8 (add 8 x d) a, dot_right,
              dot_comm 8 a x, dot_comm 8 a d, hda, signMul]; ac_rfl
          rw [hchr]; ac_rfl
      dsimp only [U0]; rw [hJtr]
      cases c0
      · simp [sign]
      · simp only [sign, if_true, Int.neg_mul, Int.one_mul, Int.neg_neg]
        have hs := (mods3_spec (-transform J x)).2.2
        rw [Int.neg_neg] at hs
        have := (mods3_spec (transform J x)).2.2
        omega
    -- Pick a frequency `w` with `dot 8 d w = !c0`!
    have hex_w0 : ∃ w0 : W 8, dot 8 w0 d = true := by
      have aux : ∀ {m : Nat} (r : W m), r ≠ zero m → ∃ w : W m, dot m w r = true := by
        intro m; induction m with
        | zero => intro r hr; exact absurd rfl hr
        | succ k ih =>
          intro r hr; rcases r with ⟨rb, r'⟩
          cases rb
          · have hr' : r' ≠ zero k := fun h => hr (by rw [h]; rfl)
            obtain ⟨w', hw'⟩ := ih r' hr'
            exact ⟨(false, w'), by simp [dot, hw']⟩
          · exact ⟨(true, zero k), by simp [dot, dot_zero]⟩
      exact aux d hd_ne
    obtain ⟨w0, hw0⟩ := hex_w0
    let w : W 8 := if c0 then zero 8 else w0
    have hdw : dot 8 d w = !c0 := by
      dsimp only [w]; cases c0
      · simp only [Bool.false_eq_true, if_false, Bool.not_false]
        rw [dot_comm]; exact hw0
      · simp only [if_true, Bool.not_true]; rw [dot_comm, dot_zero]
    -- `w ∉ Kset`, so `|transform U w| = 2 * |H8 w| ≥ 10`!
    have hw_notK : Kset w = false := by
      cases hKw : Kset w
      · rfl
      · exfalso; have h1 := hK_plane w hKw; rw [hdw] at h1; cases c0 <;> simp at h1
    have hU_ge10 : 10 ≤ (transform (U f g) w).natAbs := by
      rw [spec8 f g res w]
      have h4 : hi f g w = 4 * H8 f g w := by have hr := res w; unfold H8; omega
      dsimp only [Kset] at hw_notK; unfold clsA clsC at hw_notK
      rcases hi_values f g res cap w with h | h | h | h | h | h | h | h <;>
        rw [h] at hw_notK h4 <;> simp at hw_notK <;> omega
    -- Meanwhile `transform U0 w = 0`!
    have hU0_tr0 : transform U0 w = 0 := by
      have hsh := sum_shift 8 d (fun x => U0 x * chr w x)
      have hpt (x : W 8) : U0 (add 8 d x) * chr w (add 8 d x) = -(U0 x * chr w x) := by
        rw [add_comm 8 d x, hU0_sym x, Balanced242Plateau.chr_add]
        have hcwd : chr w d = -sign c0 := by
          unfold chr; rw [dot_comm 8 w d, hdw]; cases c0 <;> decide
        rw [hcwd]
        cases c0 <;> simp [sign] <;> omega
      rw [funext hpt] at hsh
      have hneg : total 8 (fun x => -(U0 x * chr w x)) = -total 8 (fun x => U0 x * chr w x) := by
        have h1 (x : W 8) : -(U0 x * chr w x) = (-1 : Int) * (U0 x * chr w x) := by omega
        rw [funext h1, total_scale]; omega
      rw [hneg] at hsh
      unfold transform; omega
    -- And `|transform (U - U0) w| ≤ 2 * #good = 8`!
    have hdiff_le8 : (transform (U f g) w).natAbs ≤ 8 := by
      have hdiff : transform (U f g) w = total 8 (fun x => (U f g x - U0 x) * chr w x) := by
        have hsub : transform (U f g) w - transform U0 w = total 8 (fun x => (U f g x - U0 x) * chr w x) := by
          unfold transform; rw [← total_sub]
          apply congrArg (total 8); funext x; rw [Int.sub_mul]
        rw [hU0_tr0, Int.sub_zero] at hsub; exact hsub
      have hcnt4 : total 8 (fun x => bind (good (β8 f g) x)) = 4 := by
        have hrg := rr_good (β8 f g) (cube8 f g res)
        have hm8 : many 8 = 256 := by decide
        rw [hrr, hm8] at hrg; omega
      have hup : total 8 (fun x => (U f g x - U0 x) * chr w x) ≤ 8 := by
        have hpt (x : W 8) : (U f g x - U0 x) * chr w x ≤ 2 * bind (good (β8 f g) x) := by
          cases hg : good (β8 f g) x
          · rw [hU0_off x hg]; simp [Balanced242Plateau.ind]
          · simp only [Balanced242Plateau.ind, if_true, Int.mul_one]
            have hU := U_bound f g x
            have h0 := (mods3_spec (-transform J x)).1
            unfold chr; cases dot 8 w x <;> simp [sign] <;> rcases h0 with h | h | h <;> rw [show U0 x = _ from h] <;> omega
        have hm := total_mono 8 _ _ hpt; rw [total_scale, hcnt4] at hm; omega
      have hlo : -8 ≤ total 8 (fun x => (U f g x - U0 x) * chr w x) := by
        have hpt (x : W 8) : (-2 : Int) * bind (good (β8 f g) x) ≤ (U f g x - U0 x) * chr w x := by
          cases hg : good (β8 f g) x
          · rw [hU0_off x hg]; simp [Balanced242Plateau.ind]
          · simp only [Balanced242Plateau.ind, if_true, Int.mul_one]
            have hU := U_bound f g x
            have h0 := (mods3_spec (-transform J x)).1
            unfold chr; cases dot 8 w x <;> simp [sign] <;> rcases h0 with h | h | h <;> rw [show U0 x = _ from h] <;> omega
        have hm := total_mono 8 _ _ hpt; rw [total_scale, hcnt4] at hm; omega
      rw [hdiff]; omega
    omega

/-- **Theorem 2 (`no_Z64_of_t_le_112`)**: UNCONDITIONAL exclusion of `|Z| = 64` (rank 2)
    for EVERY `agreements f g ≤ 112` — ZERO covering radius, ZERO `SectionEnum`! -/
theorem no_Z64_of_t_le_112 (f g : Half) (res : ∀ a, hi f g a % 8 = 4)
    (cap : ∀ a, (hi f g a).natAbs ≤ 28) (hrr : rr (β8 f g) = 64)
    (ht : agreements f g ≤ 112) : False := by
  have hk9 := z64_small_masks_ge_9 f g res cap hrr
  have hph := phase_identity f g res cap
  obtain ⟨hSval, hSmul, _⟩ := Splane_spec f g res hrr
  have hph128 : total 8 (fun x => U f g x * transform (q8 f g) x) =
      128 * total 8 (fun x => U f g x * Splane f g x) := by
    rw [← total_scale]; apply congrArg (total 8); funext x; rw [hSmul x]; ac_rfl
  rw [hph128] at hph
  have hcnt4 : total 8 (fun x => bind (good (β8 f g) x)) = 4 := by
    have hrg := rr_good (β8 f g) (cube8 f g res)
    have hm8 : many 8 = 256 := by decide
    rw [hrr, hm8] at hrg; omega
  have hlo : -4 ≤ total 8 (fun x => U f g x * Splane f g x) := by
    have hpt (x : W 8) : (-1 : Int) * bind (good (β8 f g) x) ≤ U f g x * Splane f g x := by
      cases hg : good (β8 f g) x
      · rw [(hSval x).2 hg]; simp [Balanced242Plateau.ind]
      · simp only [Balanced242Plateau.ind, if_true, Int.mul_one]
        have hU := U_bound f g x
        rcases (hSval x).1 hg with h | h <;> rw [h] <;> omega
    have hm := total_mono 8 _ _ hpt; rw [total_scale, hcnt4] at hm; omega
  omega

/-- **Corollary (`t112_forces_rank4_Z96`)**: Unconditionally, at `t = 112`, ONLY rank 4
    (`rr = 16, Zc = 96`) can exist! (ZERO covering radius needed!) -/
theorem t112_forces_rank4_Z96 (f g : Half) (res : ∀ a, hi f g a % 8 = 4)
    (cap : ∀ a, (hi f g a).natAbs ≤ 28) (dc : lo f g (zero 8) = 0)
    (lores : ∀ a, lo f g a % 8 = 0) (locap : ∀ a, (lo f g a).natAbs ≤ 24)
    (ht : agreements f g = 112) :
    rr (β8 f g) = 16 ∧ Zc f g = 96 := by
  rcases t112_forces_rank4_or_Z64 f g res dc lores locap ht with h4 | ⟨hrr64, _⟩
  · exact h4
  · exact False.elim (no_Z64_of_t_le_112 f g res cap hrr64 (by omega))

private theorem low_switch_levels (w v e c : Int)
    (h : w = 2 * v) (hr : w % 8 = 0) (hc : w.natAbs ≤ 24)
    (he : e = 1 ∨ e = -1) (hs : c = 1 ∨ c = -1) :
    let z := if w % 16 = 0 then 1 else 0
    (v + e * (c * (4 * z))).natAbs = 4 ∨ (v + e * (c * (4 * z))).natAbs = 12 := by
  dsimp only
  by_cases hz : w % 16 = 0 <;> rcases he with rfl|rfl <;> rcases hs with rfl|rfl <;>
    simp [hz] <;> omega

/-- At the two upper endpoints the switch yields complementary ternary tables.
    The small switched high coefficients occur exactly in classes A and C. -/
theorem endpoint_switched_blocks (f g : Half) (res : ∀ a, hi f g a % 8 = 4)
    (cap : ∀ a, (hi f g a).natAbs ≤ 28) (dc : lo f g (zero 8) = 0)
    (lores : ∀ a, lo f g a % 8 = 0) (locap : ∀ a, (lo f g a).natAbs ≤ 24)
    (ht : agreements f g = 114 ∨ agreements f g = 116)
    : ∃ u v : W 8 → Int, (∀ x, complementary (v x) (u x)) ∧
      (∀ a, (transform v a).natAbs = 4 ∨ (transform v a).natAbs = 12) ∧
      (∀ a, (transform u a).natAbs =
        if clsA f g a || clsC f g a then 4 else 12) := by
  obtain ⟨hrr, hZc⟩ := t_ge_114_forces_Z64 f g res dc lores locap (by omega)
  have hk9 := z64_small_masks_ge_9 f g res cap hrr
  have hph := phase_identity f g res cap
  obtain ⟨hSval, hSmul, hSinv⟩ := Splane_spec f g res hrr
  have hph128 : total 8 (fun x => U f g x * transform (q8 f g) x) =
      128 * total 8 (fun x => U f g x * Splane f g x) := by
    rw [← total_scale]; apply congrArg (total 8); funext x; rw [hSmul x]; ac_rfl
  rw [hph128] at hph
  have hcnt4 : total 8 (fun x => bind (good (β8 f g) x)) = 4 := by
    have hrg := rr_good (β8 f g) (cube8 f g res)
    have hm8 : many 8 = 256 := by decide
    rw [hrr, hm8] at hrg; omega
  -- `total (U * Splane) ≤ -3` (in fact `-4` at `t=114`, `-3` or `-4` at `t=116`)!
  have hsum_le : total 8 (fun x => U f g x * Splane f g x) ≤ -3 := by omega
  -- Hence on `P := good (β8 f g)` (4 points), every `x ∈ P` has `U x * Splane x ≤ 0`,
  -- AND at most ONE `x ∈ P` has `U x = 0`!
  have horient : ∀ x : W 8, good (β8 f g) x = true → U f g x * Splane f g x ≤ 0 := by
    intro x hgx
    by_cases hle : U f g x * Splane f g x ≤ 0
    · exact hle
    · exfalso
      have hpos1 : U f g x * Splane f g x = 1 := by
        have hU := U_bound f g x; rcases (hSval x).1 hgx with h | h <;> rw [h] at hle ⊢ <;> omega
      have hge : -2 ≤ total 8 (fun y => U f g y * Splane f g y) := by
        have hpt (y : W 8) : 2 * hits x y - bind (good (β8 f g) y) ≤ U f g y * Splane f g y := by
          unfold hits
          by_cases hy : x = y
          · subst hy; simp [hgx, Balanced242Plateau.ind, hpos1]
          · simp only [hy, if_false, Int.mul_zero, Int.zero_sub]
            cases hgy : good (β8 f g) y
            · rw [(hSval y).2 hgy]; simp [Balanced242Plateau.ind]
            · simp only [Balanced242Plateau.ind, if_true]
              have hU := U_bound f g y; rcases (hSval y).1 hgy with h | h <;> rw [h] <;> omega
        have hm := total_mono 8 _ _ hpt; rw [total_sub, total_scale, diagonal, hcnt4] at hm; exact hm
      omega
  have hat_most_one_zero : ∀ x1 x2 : W 8,
      good (β8 f g) x1 = true → U f g x1 = 0 →
      good (β8 f g) x2 = true → U f g x2 = 0 → x1 = x2 := by
    intro x1 x2 hg1 hu1 hg2 hu2
    by_cases heq : x1 = x2
    · exact heq
    · exfalso
      have hge : -2 ≤ total 8 (fun y => U f g y * Splane f g y) := by
        have hpt (y : W 8) : hits x1 y + hits x2 y - bind (good (β8 f g) y) ≤ U f g y * Splane f g y := by
          unfold hits
          by_cases h1 : x1 = y
          · subst h1; have hne : ¬ x2 = x1 := fun e => heq e.symm
            simp [hne, hg1, hu1, Balanced242Plateau.ind]
          · by_cases h2 : x2 = y
            · subst h2; simp [h1, hg2, hu2, Balanced242Plateau.ind]
            · simp only [h1, h2, if_false, Int.add_zero, Int.zero_sub]
              cases hgy : good (β8 f g) y
              · rw [(hSval y).2 hgy]; simp [Balanced242Plateau.ind]
              · simp only [Balanced242Plateau.ind, if_true]
                have hU := U_bound f g y; rcases (hSval y).1 hgy with h | h <;> rw [h] <;> omega
        have hm := total_mono 8 _ _ hpt; rw [total_sub, total_add, diagonal, diagonal, hcnt4] at hm; exact hm
      omega
  -- Choose `eps ∈ {-1, 1}` so that if some `x0 ∈ P` has `U x0 = 0`, then `V x0 = -eps`!
  have hex_eps : ∃ eps : Int, (eps = 1 ∨ eps = -1) ∧
      ∀ x, good (β8 f g) x = true → U f g x = 0 → Vtbl f g x = -eps := by
    cases hall : (worlds 8).all (fun x => !(good (β8 f g) x && decide (U f g x = 0)))
    · obtain ⟨x0, _, hx0⟩ := all_false_exists _ _ hall
      have hgx0 : good (β8 f g) x0 = true := by cases h : good (β8 f g) x0 <;> rw [h] at hx0 <;> simp_all
      have hUx0 : U f g x0 = 0 := by
        by_cases h0 : U f g x0 = 0
        · exact h0
        · exfalso; have hd : decide (U f g x0 = 0) = false := decide_eq_false h0
          rw [hgx0, hd] at hx0; simp at hx0
      have hVx0 : Vtbl f g x0 = 1 ∨ Vtbl f g x0 = -1 := by
        unfold Vtbl; unfold U at hUx0
        cases hfx : f x0 <;> cases hgx : g x0 <;> simp [hfx, hgx, sign] at hUx0 ⊢
      refine ⟨-Vtbl f g x0, by rcases hVx0 with h | h <;> rw [h] <;> decide, fun x hgx hUx => ?_⟩
      have heq := hat_most_one_zero x x0 hgx hUx hgx0 hUx0
      rw [heq]; omega
    · rw [List.all_eq_true] at hall
      refine ⟨1, Or.inl rfl, fun x hgx hUx => ?_⟩
      exfalso
      have hx := hall x (all_worlds 8 x)
      rw [hgx, decide_eq_true hUx] at hx; simp at hx
  obtain ⟨eps, heps, hcancel⟩ := hex_eps
  -- Prove `Zset f g = rad (β8 f g)` so `transform P a = 0` outside `Zset`!
  have hm8 : many 8 = 256 := by decide
  have hMM : (128 : Int) * 128 = many 8 * rr (β8 f g) := by rw [hm8, hrr]; decide
  have hgood_sx : good (β8 f g) (supportXor g) = true := by
    cases hg : good (β8 f g) (supportXor g)
    · exfalso
      have h0 : transform (q8 f g) (supportXor g) = 0 :=
        (Balanced242Rank.spec_values (β8 f g) (cube8 f g res) 128 hMM (supportXor g)).2 hg
      have hzid := Z_identity f g res dc lores
      rw [h0, Int.mul_zero] at hzid; omega
    · rfl
  have hZ_eq_rad (a : W 8) : Zset f g a = rad (β8 f g) a := by
    -- First show `rad a = true → Zset a = true`:
    have himp (x : W 8) (hr : rad (β8 f g) x = true) : Zset f g x = true := by
      have hphi := (good_spec (β8 f g)).1 hgood_sx x hr
      unfold phi at hphi
      have hc := Balanced242HighSections.coupled_phase f g x
      rw [dc] at hc
      have r1 := res x; have r0 := res (zero 8); have l1 := lores x
      unfold β8 Balanced242Plateau.bt H8 at hphi
      unfold Zset
      rw [dot_comm 8 (supportXor g) x] at hphi
      cases hd : dot 8 x (supportXor g) <;> rw [hd] at hphi hc <;>
        simp only [if_true, if_false, Bool.false_eq_true] at hc <;>
        by_cases h1 : hi f g x / 4 / 2 % 2 = 1 <;> by_cases h0 : hi f g (zero 8) / 4 / 2 % 2 = 1 <;>
        by_cases hl : lo f g x % 16 = 0 <;>
        simp only [h1, h0, hl, decide_true, decide_false, Bool.xor_false, Bool.xor_true] at hphi ⊢ <;>
        first | rfl | omega | exact Bool.noConfusion hphi
    have hge (x : W 8) : bind (rad (β8 f g) x) ≤ bind (Zset f g x) := by
      cases hr : rad (β8 f g) x
      · simp [Balanced242Plateau.ind]; exact Balanced242Plateau.ind_nonneg _
      · rw [himp x hr]; decide
    have hdiff_nn (x : W 8) : 0 ≤ bind (Zset f g x) - bind (rad (β8 f g) x) := by have := hge x; omega
    have hdiff_sum : total 8 (fun x => bind (Zset f g x) - bind (rad (β8 f g) x)) = 0 := by
      rw [total_sub, ← Zc_eq_total_Zset]
      change Zc f g - rr (β8 f g) = 0
      rw [hZc, hrr]; rfl
    have hpt := point_le_total 8 (fun x => bind (Zset f g x) - bind (rad (β8 f g) x)) hdiff_nn a
    rw [hdiff_sum] at hpt
    have h0 := hdiff_nn a
    cases hz : Zset f g a <;> cases hr : rad (β8 f g) a <;>
      rw [hz, hr] at hpt h0 <;> simp [Balanced242Plateau.ind] at hpt h0 ⊢ <;> omega
  let P : W 8 → Int := fun x => bind (good (β8 f g) x)
  let v : W 8 → Int := fun x => Vtbl f g x + eps * P x
  let u : W 8 → Int := fun x => U f g x + Splane f g x
  refine ⟨u, v, ?_, ?_, ?_⟩
  · intro x
    have hsrc : complementary (Vtbl f g x) (U f g x) := by
      unfold complementary Vtbl U
      cases f x <;> cases g x <;> simp [sign]
    cases hg : good (β8 f g) x
    · simpa [v, u, P, hg, Balanced242Plateau.ind, (hSval x).2 hg] using hsrc
    · have b := (hSval x).1 hg
      have orient := horient x hg
      have cancel := hcancel x hg
      unfold complementary at hsrc ⊢
      simp only [v, u, P, hg, Balanced242Plateau.ind, if_true, Int.mul_one]
      rcases hsrc with ⟨p,h|h⟩ | ⟨p,h|h⟩ <;>
        rcases b with h₁|h₁ <;> rcases heps with h₂|h₂ <;> simp_all
  · intro a
    have hP : transform P a = chr a (supportXor g) * (4 * bind (rad (β8 f g) a)) := by
      have hgood_eq (x : W 8) : good (β8 f g) x = perp (β8 f g) (add 8 x (supportXor g)) := by
        cases hg : good (β8 f g) x
        · cases hp : perp (β8 f g) (add 8 x (supportXor g))
          · rfl
          · exfalso
            have h1 := good_shift (β8 f g) hgood_sx hp
            rw [add_comm 8 (supportXor g) _, Balanced242Plateau.add_assoc', add_self, add_zero_right] at h1
            rw [h1] at hg; exact Bool.noConfusion hg
        · symm; exact good_perp (β8 f g) hg hgood_sx
      have htr_perp : transform (fun x => bind (perp (β8 f g) x)) a = 4 * bind (rad (β8 f g) a) := by
        have hinv := transform_involution (fun x => bind (rad (β8 f g) x)) a
        have htr_rad (u : W 8) : transform (fun x => bind (rad (β8 f g) x)) u = 64 * bind (perp (β8 f g) u) := by
          change total 8 (fun d => bind (rad (β8 f g) d) * sign (dot 8 u d)) = 64 * bind (perp (β8 f g) u)
          have hch := char_radical (β8 f g) (dot 8 u) (fun e _ d => dot_right 8 u e d)
          cases hp : perp (β8 f g) u
          · rw [hch.1 hp]; rfl
          · rw [hch.2 hp]; change rr (β8 f g) = 64 * 1; rw [hrr]; omega
        rw [show transform (fun x => bind (rad (β8 f g) x)) = fun u => 64 * bind (perp (β8 f g) u) from funext htr_rad] at hinv
        unfold transform at hinv ⊢
        have hpt (u : W 8) : 64 * bind (perp (β8 f g) u) * chr a u = 64 * (bind (perp (β8 f g) u) * chr a u) :=
          Int.mul_assoc _ _ _
        rw [funext hpt, total_scale, hm8] at hinv
        dsimp only at hinv ⊢; omega
      have hsh := sum_shift 8 (supportXor g) (fun x => bind (good (β8 f g) x) * chr a x)
      have hre (x : W 8) : bind (good (β8 f g) (add 8 (supportXor g) x)) * chr a (add 8 (supportXor g) x) =
          chr a (supportXor g) * (bind (perp (β8 f g) x) * chr a x) := by
        rw [hgood_eq, add_comm 8 (supportXor g) x, Balanced242Plateau.add_assoc', add_self, add_zero_right,
            Balanced242Plateau.chr_add]; ac_rfl
      rw [funext hre, total_scale] at hsh
      change chr a (supportXor g) * transform (fun x => bind (perp (β8 f g) x)) a =
        transform (fun x => bind (good (β8 f g) x)) a at hsh
      change transform (fun x => bind (good (β8 f g) x)) a = _
      rw [← hsh, htr_perp]
    have hV := lo_eq_2_transform_V f g a
    have hvcap := locap a
    have hvr := lores a
    have hchr : chr a (supportXor g) = 1 ∨ chr a (supportXor g) = -1 := sign_vals _
    have hv : transform v a = transform (Vtbl f g) a + eps * transform P a := by
      simp only [v, transform, Int.add_mul, Int.mul_assoc, total_add, total_scale]
    rw [hv, hP, ← hZ_eq_rad]
    simpa only [Zset, Balanced242Plateau.ind, decide_eq_true_eq] using
      low_switch_levels _ _ _ _ hV hvr hvcap heps hchr
  · intro a
    have hu : transform u a = 2 * H8 f g a + 2 * q8 f g a := by
      rw [← spec8 f g res a, ← hSinv]
      simp only [u, transform, Int.add_mul, total_add]
    rw [hu]
    unfold H8 q8 β8 H8 Balanced242Plateau.bt clsA clsC
    rcases hi_values f g res cap a with h|h|h|h|h|h|h|h <;> rw [h] <;> decide

/-- The Boolean halves obtained from the switched tables have Walsh peak at most 24. -/
theorem z64_plane_switch_114_116 (f g : Half) (res : ∀ a, hi f g a % 8 = 4)
    (cap : ∀ a, (hi f g a).natAbs ≤ 28) (dc : lo f g (zero 8) = 0)
    (lores : ∀ a, lo f g a % 8 = 0) (locap : ∀ a, (lo f g a).natAbs ≤ 24)
    (ht : agreements f g = 114 ∨ agreements f g = 116)
    : ∃ f' g' : Half, ∀ a : W 8, (lo f' g' a).natAbs ≤ 24 ∧ (hi f' g' a).natAbs ≤ 24 := by
  obtain ⟨u, v, hc, hv, hu⟩ := endpoint_switched_blocks f g res cap dc lores locap ht
  let f' (x : W 8) := decide (v x + u x < 0)
  let g' (x : W 8) := decide (v x - u x < 0)
  have sums (x : W 8) : sign (f' x) + sign (g' x) = 2*v x ∧
      sign (f' x) - sign (g' x) = 2*u x := by
    rcases hc x with ⟨p,h|h⟩ | ⟨p,h|h⟩ <;> simp [f',g',p,h,sign]
  refine ⟨f', g', fun a => ?_⟩
  have l : lo f' g' a = 2 * transform v a := by
    unfold lo spec transform
    rw [← total_add]
    simp only [← Int.add_mul, (sums _).1, Int.mul_assoc, total_scale]
  have h : hi f' g' a = 2 * transform u a := by
    unfold hi spec transform
    rw [← total_sub]
    simp only [← Int.sub_mul, (sums _).2, Int.mul_assoc, total_scale]
  rw [l,h]
  have low := hv a
  have high := hu a
  split at high <;> omega

/-- The unrestricted covering-radius bound also rules out both endpoints. -/
theorem no_t114_t116_of_covering_radius (f g : Half) (res : ∀ a, hi f g a % 8 = 4)
    (cap : ∀ a, (hi f g a).natAbs ≤ 28) (dc : lo f g (zero 8) = 0)
    (lores : ∀ a, lo f g a % 8 = 0) (locap : ∀ a, (lo f g a).natAbs ≤ 24)
    (ht : agreements f g = 114 ∨ agreements f g = 116)
    (hcov : CoveringRadius244) : False :=
  hcov (z64_plane_switch_114_116 f g res cap dc lores locap ht)

end Balanced242Z64Switch

#print axioms Balanced242Z64Switch.z64_small_masks_ge_9
#print axioms Balanced242Z64Switch.no_Z64_of_t_le_112
#print axioms Balanced242Z64Switch.t112_forces_rank4_Z96
#print axioms Balanced242Z64Switch.no_t114_t116_of_covering_radius

#print axioms Balanced242Z64Switch.endpoint_switched_blocks
#print axioms Balanced242Z64Switch.z64_plane_switch_114_116
