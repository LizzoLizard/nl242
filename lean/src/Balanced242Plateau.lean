/-
  The plateau property of the section phase, proved.

  Let D : W n -> Int with transform D = 2 H and every H value odd.  Write beta(a) for the
  second bit of H(a), so that sign(beta a) = (-1)^((H a - 1)/2) is the phase of H.

  1. Third differences of an integer Walsh transform are divisible by 8, so third differences
     of H are divisible by 4, and the eight phase bits around any cube XOR to zero (`Cube`).
  2. For a cubic-free beta, ell_d(a) = beta a + beta(a+d) + beta 0 + beta d is linear in a, so
     the autocorrelation sum_a q(a) q(a+d) is either 0 or +-2^n, the latter exactly on the
     radical R = {d : ell_d = 0}.
  3. q^(y)^2 = 2^n * sum_{d in R} psi_y(d) with psi_y a character of the subgroup R, so
     q^(y)^2 is 0 or 2^n |R|.  Parseval gives |R| * #support = 2^n.
  4. For n = 7 the only consistent values are |q^| in {16, 32, 64, 128}.

  This discharges the plateau hypothesis of Balanced242Section0320.no_section_0_32_0.
-/
import Balanced242Support
import Balanced242Blocks
import Balanced242Section0320

namespace Balanced242Plateau
open FrozenShells FreezeMovies CandyKnots CollisionLaw MaskRecovery SilentRoom
open Balanced242Support Balanced242Blocks

theorem add_assoc' (n : Nat) (x y z : W n) : add n (add n x y) z = add n x (add n y z) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [add]; rw [Bool.xor_assoc, ih]

theorem add_zero_right (n : Nat) (w : W n) : add n w (zero n) = w := by
  rw [add_comm, add_zero_left]

theorem chr_add {n : Nat} (y a b : W n) : chr y (add n a b) = chr y a * chr y b := by
  simp only [chr, dot_right, signMul]

theorem sign_sq (b : Bool) : sign b * sign b = 1 := by cases b <;> decide

def ind (b : Bool) : Int := if b then 1 else 0

/-- Constructive replacement for `List.all_eq_false` (which uses choice). -/
theorem all_false_exists {α : Type} (p : α → Bool) :
    ∀ l : List α, l.all p = false → ∃ x, x ∈ l ∧ p x = false
  | [], h => by simp at h
  | a :: l, h => by
    cases ha : p a
    · exact ⟨a, List.mem_cons_self a l, ha⟩
    · rw [List.all_cons, ha, Bool.true_and] at h
      obtain ⟨x, hx, hpx⟩ := all_false_exists p l h
      exact ⟨x, List.mem_cons_of_mem a hx, hpx⟩

/-! ## The second bit of an odd number and the cube identity -/

def bt (x : Int) : Bool := decide (x / 2 % 2 = 1)

theorem bt_sub (x y : Int) (h : x % 2 = y % 2) : bt (x - y) = xor (bt x) (bt y) := by
  unfold bt
  cases hx : decide (x / 2 % 2 = 1) <;> cases hy : decide (y / 2 % 2 = 1) <;>
    simp only [decide_eq_true_eq, decide_eq_false_iff_not] at hx hy <;>
    simp only [Bool.xor_true, Bool.xor_false, Bool.not_false, Bool.not_true,
      decide_eq_true_eq, decide_eq_false_iff_not] <;> omega

theorem cube8 (h0 h1 h2 h3 h4 h5 h6 h7 : Int)
    (o0 : h0 % 2 = 1) (o1 : h1 % 2 = 1) (o2 : h2 % 2 = 1) (o3 : h3 % 2 = 1)
    (o4 : h4 % 2 = 1) (o5 : h5 % 2 = 1) (o6 : h6 % 2 = 1) (o7 : h7 % 2 = 1)
    (hd : (4:Int) ∣ ((h7 - h6) - (h5 - h4)) - ((h3 - h2) - (h1 - h0))) :
    xor (xor (xor (bt h7) (bt h6)) (xor (bt h5) (bt h4)))
        (xor (xor (bt h3) (bt h2)) (xor (bt h1) (bt h0))) = false := by
  rw [← bt_sub h7 h6 (by omega), ← bt_sub h5 h4 (by omega), ← bt_sub h3 h2 (by omega),
    ← bt_sub h1 h0 (by omega), ← bt_sub (h7 - h6) (h5 - h4) (by omega),
    ← bt_sub (h3 - h2) (h1 - h0) (by omega),
    ← bt_sub ((h7 - h6) - (h5 - h4)) ((h3 - h2) - (h1 - h0)) (by omega)]
  unfold bt; simp only [decide_eq_false_iff_not]; omega

/-! ## Quadratic phase bits -/

section Quadratic
variable {n : Nat} (β : W n → Bool)

def Cube : Prop := ∀ u v w a : W n,
  xor (xor (xor (β (add n u (add n v (add n w a)))) (β (add n v (add n w a))))
           (xor (β (add n u (add n w a))) (β (add n w a))))
      (xor (xor (β (add n u (add n v a))) (β (add n v a)))
           (xor (β (add n u a)) (β a))) = false

/-- The derivative form: linear in `a` when `β` is cubic-free. -/
def ell (d a : W n) : Bool := xor (xor (β a) (β (add n a d))) (xor (β (zero n)) (β d))

def rad (d : W n) : Bool := (worlds n).all (fun a => !ell β d a)

def phi (y d : W n) : Bool := xor (dot n y d) (xor (β (zero n)) (β d))

theorem rad_spec {d : W n} : rad β d = true ↔ ∀ a, ell β d a = false := by
  unfold rad; rw [List.all_eq_true]; constructor
  · intro h a; have := h a (all_worlds n a); simpa using this
  · intro h a _; simp [h a]

theorem ell_hom (hc : Cube β) (d e a : W n) :
    ell β d (add n e a) = xor (ell β d e) (ell β d a) := by
  have h := hc e a d (zero n)
  simp only [add_zero_right] at h
  unfold ell
  rw [add_assoc']
  revert h
  generalize β (add n e (add n a d)) = p1
  generalize β (add n a d) = p2
  generalize β (add n e d) = p3
  generalize β (add n e a) = p5
  generalize β d = p4
  generalize β a = p6
  generalize β e = p7
  generalize β (zero n) = p8
  revert p1 p2 p3 p4 p5 p6 p7 p8; decide

theorem ell_sum (hc : Cube β) (d : W n) :
    total n (fun a => sign (ell β d a)) = many n * ind (rad β d) := by
  cases hr : rad β d
  · have : ∃ e, ell β d e = true := by
      obtain ⟨e, _, he⟩ := all_false_exists _ _ hr
      exact ⟨e, by revert he; cases ell β d e <;> decide⟩
    obtain ⟨e, he⟩ := this
    have sh := sum_shift n e (fun a => sign (ell β d a))
    simp only [ell_hom β hc, he, signMul] at sh
    rw [total_scale] at sh
    simp only [ind, sign, if_true, Bool.false_eq_true, if_false] at sh ⊢
    omega
  · have h := (rad_spec β).1 hr
    simp only [h, total_const, ind, sign, if_true, Bool.false_eq_true, if_false]

theorem auto (hc : Cube β) (d : W n) :
    total n (fun a => sign (β a) * sign (β (add n a d))) =
      sign (xor (β (zero n)) (β d)) * (many n * ind (rad β d)) := by
  have e (a : W n) : sign (β a) * sign (β (add n a d)) =
      sign (xor (β (zero n)) (β d)) * sign (ell β d a) := by
    rw [← signMul, ← signMul]; congr 1; unfold ell
    generalize β (add n a d) = y
    generalize β a = x
    generalize β (zero n) = z
    generalize β d = w
    revert x y z w; decide
  simp only [e, total_scale, ell_sum β hc]

/-- The squared spectrum is 2^n times a signed count over the radical. -/
theorem spec_sq (hc : Cube β) (y : W n) :
    transform (fun a => sign (β a)) y * transform (fun a => sign (β a)) y =
      many n * total n (fun d => ind (rad β d) * sign (phi β y d)) := by
  let f : W n → Int := fun b => sign (β b) * chr y b
  have hT : transform (fun a => sign (β a)) y = total n f := rfl
  rw [hT]
  have s1 : total n f * total n f = total n (fun a => f a * total n f) := by
    rw [Int.mul_comm, ← total_scale]; apply congrArg (total n); funext a; rw [Int.mul_comm]
  have s2 (a : W n) : f a * total n f =
      total n (fun d => chr y d * (sign (β a) * sign (β (add n a d)))) := by
    rw [← sum_shift n a f, ← total_scale]; apply congrArg (total n); funext d
    simp only [f, chr_add]
    have q := sign_sq (dot n y a)
    simp only [chr] at *
    generalize sign (dot n y a) = ca at q ⊢
    generalize sign (dot n y d) = cd
    generalize sign (β a) = sa
    generalize sign (β (add n a d)) = sb
    have : sa * ca * (sb * (ca * cd)) = (ca * ca) * (cd * (sa * sb)) := by
      simp only [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
    rw [this, q, Int.one_mul]
  rw [s1]; simp only [s2]; rw [swap]
  simp only [total_scale, auto β hc]
  rw [← total_scale]; apply congrArg (total n); funext d
  simp only [phi, signMul, chr]
  generalize sign (dot n y d) = cd
  generalize sign (xor (β (zero n)) (β d)) = s
  cases rad β d <;> simp [ind, Int.mul_comm, Int.mul_left_comm]

theorem rad_shift (e : W n) (he : rad β e = true) (x : W n) :
    β (add n x e) = xor (xor (β x) (β (zero n))) (β e) := by
  have h := (rad_spec β).1 he x
  unfold ell at h
  revert h
  generalize β (add n x e) = q
  generalize β x = p
  generalize β (zero n) = z
  generalize β e = w
  revert p q z w; decide

theorem rad_add (e : W n) (he : rad β e = true) (d : W n) : rad β (add n e d) = rad β d := by
  have key (a : W n) : ell β (add n e d) a = ell β d a := by
    unfold ell
    have r1 : add n a (add n e d) = add n (add n a d) e := by
      rw [add_assoc', add_comm n e d]
    rw [r1, rad_shift β e he (add n a d), add_comm n e d, rad_shift β e he d]
    generalize β (add n a d) = p
    generalize β a = x
    generalize β (zero n) = z
    generalize β e = w
    generalize β d = v
    revert p x z w v; decide
  unfold rad; congr 1; funext a; rw [key a]

theorem phi_add (y e : W n) (he : rad β e = true) (d : W n) :
    phi β y (add n e d) = xor (phi β y e) (phi β y d) := by
  unfold phi
  rw [dot_right, add_comm n e d, rad_shift β e he d]
  generalize dot n y e = a
  generalize dot n y d = b
  generalize β (zero n) = z
  generalize β e = w
  generalize β d = v
  revert a b z w v; decide

theorem signed_radical (y : W n) :
    total n (fun d => ind (rad β d) * sign (phi β y d)) = 0 ∨
    total n (fun d => ind (rad β d) * sign (phi β y d)) = total n (fun d => ind (rad β d)) := by
  cases hb : (worlds n).all (fun e => !(rad β e && phi β y e))
  · left
    obtain ⟨e, _, he⟩ := all_false_exists _ _ hb
    have he : rad β e = true ∧ phi β y e = true := by
      revert he; cases rad β e <;> cases phi β y e <;> decide
    have sh := sum_shift n e (fun d => ind (rad β d) * sign (phi β y d))
    simp only [rad_add β e he.1, phi_add β y e he.1, he.2, signMul] at sh
    have neg (d : W n) : ind (rad β d) * (sign true * sign (phi β y d)) =
        -1 * (ind (rad β d) * sign (phi β y d)) := by
      simp only [sign, if_true]; rw [Int.mul_left_comm]
    simp only [neg, total_scale] at sh
    omega
  · right
    rw [List.all_eq_true] at hb
    apply congrArg (total n); funext d
    have := hb d (all_worlds n d)
    cases h : rad β d
    · simp [ind]
    · rw [h] at this
      simp only [Bool.true_and, Bool.not_eq_true'] at this
      simp [ind, this, sign]

theorem ind_nonneg (b : Bool) : 0 ≤ ind b := by cases b <;> decide

theorem total_nonneg' (f : W n → Int) (h : ∀ x, 0 ≤ f x) : 0 ≤ total n f := by
  have := total_mono n (fun _ => 0) f h
  rw [total_zero] at this; exact this

/-- General plateau: q^(y)^2 is 0 or 2^n r, where r c = 2^n and some y attains 2^n r. -/
theorem plateau_general (hc : Cube β) :
    ∃ r c : Int, 0 ≤ r ∧ 0 ≤ c ∧ r * c = many n ∧
      (∀ y, transform (fun a => sign (β a)) y * transform (fun a => sign (β a)) y = 0 ∨
            transform (fun a => sign (β a)) y * transform (fun a => sign (β a)) y = many n * r) ∧
      (∃ y, transform (fun a => sign (β a)) y * transform (fun a => sign (β a)) y = many n * r) := by
  let S : W n → Int := fun y => total n (fun d => ind (rad β d) * sign (phi β y d))
  let r := total n (fun d => ind (rad β d))
  let c := total n (fun y => if S y = r then (1 : Int) else 0)
  have hS (y : W n) : S y = r * (if S y = r then 1 else 0) := by
    rcases signed_radical β y with h | h
    · change S y = 0 at h
      by_cases e : S y = r
      · rw [if_pos e, Int.mul_one]; exact e
      · rw [if_neg e, Int.mul_zero]; exact h
    · change S y = r at h; rw [if_pos h, Int.mul_one]; exact h
  have hsum : total n S = r * c := by
    rw [← total_scale]; apply congrArg (total n); funext y; exact hS y
  have par := Balanced242Section0320.parseval (fun a => sign (β a))
  simp only [sign_sq, total_const, Int.mul_one, spec_sq β hc, total_scale] at par
  change many n * total n S = many n * many n at par
  rw [hsum] at par
  have hrc : r * c = many n := Int.eq_of_mul_eq_mul_left (by have := many_pos n; omega) par
  have r0 : 0 ≤ r := total_nonneg' _ (fun d => ind_nonneg _)
  have c0 : 0 ≤ c := total_nonneg' _ (fun y => by split <;> decide)
  refine ⟨r, c, r0, c0, hrc, ?_, ?_⟩
  · intro y
    rw [spec_sq β hc]
    rcases signed_radical β y with h | h
    · left; rw [h, Int.mul_zero]
    · right; rw [h]
  · cases hb : (worlds n).any (fun y => decide (S y = r))
    · exfalso
      rw [List.any_eq_false] at hb
      have z : c = 0 := by
        have : (fun y => if S y = r then (1 : Int) else 0) = fun _ => 0 := by
          funext y; have := hb y (all_worlds n y); simp only [decide_eq_true_eq] at this
          rw [if_neg this]
        change total n _ = 0; rw [this, total_zero]
      rw [z, Int.mul_zero] at hrc
      have := many_pos n; omega
    · rw [List.any_eq_true] at hb
      obtain ⟨y, _, hy⟩ := hb
      simp only [decide_eq_true_eq] at hy
      exact ⟨y, by rw [spec_sq β hc]; change many n * S y = _; rw [hy]⟩

end Quadratic

/-! ## From an integer spectrum to cubic-free phase bits -/

theorem cube_of_spec {n : Nat} (D H : W n → Int) (hspec : ∀ a, transform D a = 2 * H a)
    (hodd : ∀ a, H a % 2 = 1) : Cube (fun a => bt (H a)) := by
  intro u v w a
  have e := diff_transform_dvd [u, v, w] D a
  rw [show transform D = fun b => 2 * H b from funext hspec, diff_scale] at e
  simp only [List.length_cons, List.length_nil] at e
  have e4 : (4:Int) ∣ differences [u, v, w] H a := by
    obtain ⟨k, hk⟩ := e; exact ⟨k, by simp at hk; omega⟩
  simp only [differences] at e4
  exact cube8 _ _ _ _ _ _ _ _ (hodd _) (hodd _) (hodd _) (hodd _) (hodd _) (hodd _) (hodd _)
    (hodd _) e4

/-! ## Seven variables -/

theorem sq_cases (z m : Int) (h : z * z = m * m) : z = m ∨ z = -m := by
  have : (z - m) * (z + m) = 0 := by
    rw [Int.sub_mul, Int.mul_add, Int.mul_add, Int.mul_comm m z]; omega
  rcases Int.mul_eq_zero.1 this with h | h
  · left; omega
  · right; omega

theorem divisors128_mem : ∀ r : Nat, r < 129 → 128 % r = 0 →
    r ∈ [0, 1, 2, 4, 8, 16, 32, 64, 128] := by decide

theorem divisors128 (r : Nat) (h1 : r < 129) (h0 : r ≠ 0) (h2 : 128 % r = 0) :
    r = 1 ∨ r = 2 ∨ r = 4 ∨ r = 8 ∨ r = 16 ∨ r = 32 ∨ r = 64 ∨ r = 128 := by
  have h := divisors128_mem r h1 h2
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at h; omega

theorem square_levels (r c : Int) (r0 : 0 ≤ r) (c0 : 0 ≤ c) (hrc : r * c = 128) (z : Int)
    (hz : z * z = 128 * r) :
    ∃ m : Int, (m = 16 ∨ m = 32 ∨ m = 64 ∨ m = 128) ∧ 128 * r = m * m := by
  obtain ⟨R, rfl⟩ : ∃ R : Nat, r = R := ⟨r.toNat, by omega⟩
  obtain ⟨C, rfl⟩ : ∃ C : Nat, c = C := ⟨c.toNat, by omega⟩
  have hRC : R * C = 128 := by exact_mod_cast hrc
  have R0 : R ≠ 0 := by intro h; rw [h] at hRC; simp at hRC
  have C0 : C ≠ 0 := by intro h; rw [h] at hRC; simp at hRC
  have Rle : R ≤ 128 := by
    have := Nat.le_mul_of_pos_right R (Nat.pos_of_ne_zero C0); omega
  have Rdvd : 128 % R = 0 := by rw [← hRC]; exact Nat.mul_mod_right R C
  have M := z.natAbs
  have hM : z.natAbs * z.natAbs = 128 * R := by
    have := congrArg Int.natAbs hz
    rw [Int.natAbs_mul] at this; rw [this]; simp [Int.natAbs_mul]
  have Mle : z.natAbs < 129 := by
    false_or_by_contra
    have := Nat.mul_le_mul (Nat.le_of_not_lt ‹_›) (Nat.le_of_not_lt ‹_›)
    omega
  generalize z.natAbs = M at hM Mle
  rcases divisors128 R (by omega) R0 Rdvd with h | h | h | h | h | h | h | h <;> subst h
  · exact absurd hM (by revert M; decide)
  · exact ⟨16, by decide, by decide⟩
  · exact absurd hM (by revert M; decide)
  · exact ⟨32, by decide, by decide⟩
  · exact absurd hM (by revert M; decide)
  · exact ⟨64, by decide, by decide⟩
  · exact absurd hM (by revert M; decide)
  · exact ⟨128, by decide, by decide⟩

theorem phase_bt (h : Int) (ho : h % 2 = 1) :
    Balanced242Section0320.phase h = sign (bt h) := by
  unfold Balanced242Section0320.phase bt sign
  by_cases e : h / 2 % 2 = 1
  · simp only [e, decide_true, if_true]; rw [if_neg (by omega)]
  · simp only [e, decide_false, Bool.false_eq_true, if_false]; rw [if_pos (by omega)]

/-- The plateau property for any 7-variable section with odd half-spectrum. -/
theorem plateau7 (D H : W 7 → Int) (hspec : ∀ a, transform D a = 2 * H a)
    (hodd : ∀ a, H a % 2 = 1) :
    ∃ m : Int, (m = 16 ∨ m = 32 ∨ m = 64 ∨ m = 128) ∧ ∀ y,
      transform (fun a => Balanced242Section0320.phase (H a)) y = 0 ∨
      transform (fun a => Balanced242Section0320.phase (H a)) y = m ∨
      transform (fun a => Balanced242Section0320.phase (H a)) y = -m := by
  have hq : (fun a => Balanced242Section0320.phase (H a)) = fun a => sign (bt (H a)) := by
    funext a; exact phase_bt _ (hodd a)
  rw [hq]
  obtain ⟨r, c, r0, c0, hrc, hall, ⟨y0, hy0⟩⟩ :=
    plateau_general (fun a => bt (H a)) (cube_of_spec D H hspec hodd)
  have h128 : many 7 = 128 := by decide
  rw [h128] at hrc hy0
  obtain ⟨m, hm, hmm⟩ := square_levels r c r0 c0 hrc _ hy0
  refine ⟨m, hm, fun y => ?_⟩
  rcases hall y with h | h
  · left
    rcases sq_cases _ 0 (by rw [h, Int.mul_zero]) with h' | h' <;> omega
  · right
    rw [h128, hmm] at h
    rcases sq_cases _ m h with h' | h'
    · left; exact h'
    · right; exact h'

/-- A (0,b,0) section (all |H| in {5,7}, exactly b of magnitude 5) forces b = 80.
    In particular there is no (0,32,0) or (0,48,0) section. -/
theorem section_0_b_0 (D H : W 7 → Int) (b : Int)
    (hD : ∀ y, -2 ≤ D y ∧ D y ≤ 2)
    (hspec : ∀ a, transform D a = 2 * H a)
    (hH : ∀ a, H a = 5 ∨ H a = -5 ∨ H a = 7 ∨ H a = -7)
    (h5 : total 7 (fun a => if H a = 5 ∨ H a = -5 then (1 : Int) else 0) = b) : b = 80 := by
  have hodd (a : W 7) : H a % 2 = 1 := by rcases hH a with h | h | h | h <;> rw [h] <;> decide
  obtain ⟨m, hm, hplat⟩ := plateau7 D H hspec hodd
  let q : W 7 → Int := fun a => Balanced242Section0320.phase (H a)
  let e : W 7 → Int := fun a => if H a = 5 ∨ H a = -5 then 1 else 0
  have hm128 : many 7 = 128 := by decide
  have he : total 7 e = b := h5
  have hb : b ≤ 128 := by
    have := total_mono 7 e (fun _ => 1) (fun a => by simp only [e]; split <;> decide)
    rw [total_const, hm128] at this; omega
  have F1 (a : W 7) : q a * q a = 1 := by
    rcases hH a with h | h | h | h <;> simp [q, Balanced242Section0320.phase, h]
  have F2 (a : W 7) : 2 * H a = -14 * q a + 24 * (q a * e a) := by
    rcases hH a with h | h | h | h <;> simp [q, e, Balanced242Section0320.phase, h]
  have F3 (a : W 7) : q a * H a = -7 + 12 * e a := by
    rcases hH a with h | h | h | h <;> simp [q, e, Balanced242Section0320.phase, h]
  have S1 : 128 * total 7 (fun y => D y * D y) = 25088 - 96 * b := by
    have p := Balanced242Section0320.parseval D
    simp only [hspec, hm128] at p
    have r (a : W 7) : 2 * H a * (2 * H a) = 196 - 96 * e a := by
      rcases hH a with h | h | h | h <;> simp [e, h]
    simp only [r, total_sub, total_const, total_scale, hm128] at p
    change 128 * 196 - 96 * total 7 e = 128 * _ at p
    omega
  have S2 : total 7 (fun y => D y * transform q y) = -1792 + 24 * b := by
    rw [← Balanced242Section0320.duality]
    have r (a : W 7) : q a * transform D a = -14 + 24 * e a := by
      rw [hspec, Int.mul_left_comm, F3]; omega
    simp only [r, total_add, total_const, total_scale, hm128]
    omega
  have S3 : total 7 (fun y => transform q y * transform q y) = 16384 := by
    rw [Balanced242Section0320.parseval]; simp only [F1, total_const, hm128]; decide
  have P (y : W 7) : 64 * D y = -7 * transform q y + 12 * total 7 (fun a => q a * e a * chr a y) := by
    have inv := inversion D y
    simp only [hspec, hm128, F2, Int.add_mul, total_add, Int.mul_assoc, total_scale] at inv
    have hq : total 7 (fun a => q a * chr a y) = transform q y := by
      unfold transform; apply congrArg (total 7); funext a
      rw [Balanced242Section0320.chr_comm]
    rw [hq] at inv
    have : total 7 (fun a => q a * (e a * chr a y)) = total 7 (fun a => q a * e a * chr a y) := by
      apply congrArg (total 7); funext a; rw [Int.mul_assoc]
    rw [this] at inv
    omega
  rcases hm with hm | hm | hm | hm
  · subst hm
    have pt (y : W 7) : 128 * (D y * D y) = 8 * (D y * transform q y) + transform q y * transform q y := by
      have hp := P y
      have hd : D y = -2 ∨ D y = -1 ∨ D y = 0 ∨ D y = 1 ∨ D y = 2 := by have := hD y; omega
      generalize total 7 (fun a => q a * e a * chr a y) = Y at hp
      rcases hplat y with h | h | h <;> change transform q y = _ at h <;>
        rw [h] at hp ⊢ <;> rcases hd with d | d | d | d | d <;> rw [d] at hp ⊢ <;> omega
    have sum := congrArg (total 7) (funext pt)
    simp only [total_add, total_scale] at sum
    rw [S2, S3] at sum
    omega
  all_goals
    subst hm
    have pt (y : W 7) : 1024 * (D y * D y) ≤ 4 * (transform q y * transform q y) := by
      have hp := P y
      have hd : D y = -2 ∨ D y = -1 ∨ D y = 0 ∨ D y = 1 ∨ D y = 2 := by have := hD y; omega
      generalize total 7 (fun a => q a * e a * chr a y) = Y at hp
      rcases hplat y with h | h | h <;> change transform q y = _ at h <;>
        rw [h] at hp ⊢ <;> rcases hd with d | d | d | d | d <;> rw [d] at hp ⊢ <;> omega
    have sum := total_mono 7 _ _ pt
    simp only [total_scale] at sum
    rw [S3] at sum
    omega

/-- The phase bound used by `half`: with plateau height m = 2^(7 - s/2),
    |T7| * m <= 16384, i.e. |T7| <= 128 * 2^(s/2), where T7 = sum of phase(H) * H. -/
theorem t7_bound (D H : W 7 → Int)
    (hD : ∀ y, -2 ≤ D y ∧ D y ≤ 2)
    (hspec : ∀ a, transform D a = 2 * H a)
    (hodd : ∀ a, H a % 2 = 1) :
    ∃ m : Int, (m = 16 ∨ m = 32 ∨ m = 64 ∨ m = 128) ∧
      (∀ y, transform (fun a => Balanced242Section0320.phase (H a)) y = 0 ∨
        transform (fun a => Balanced242Section0320.phase (H a)) y = m ∨
        transform (fun a => Balanced242Section0320.phase (H a)) y = -m) ∧
      -16384 ≤ m * total 7 (fun a => Balanced242Section0320.phase (H a) * H a) ∧
      m * total 7 (fun a => Balanced242Section0320.phase (H a) * H a) ≤ 16384 := by
  obtain ⟨m, hm, hplat⟩ := plateau7 D H hspec hodd
  refine ⟨m, hm, hplat, ?_⟩
  let q : W 7 → Int := fun a => Balanced242Section0320.phase (H a)
  have hm128 : many 7 = 128 := by decide
  have F1 (a : W 7) : q a * q a = 1 := by
    show Balanced242Section0320.phase (H a) * Balanced242Section0320.phase (H a) = 1
    unfold Balanced242Section0320.phase
    by_cases h : H a % 4 = 1
    · rw [if_pos h]; decide
    · rw [if_neg h]; decide
  have S3 : total 7 (fun y => transform q y * transform q y) = 16384 := by
    rw [Balanced242Section0320.parseval]; simp only [F1, total_const, hm128]; decide
  have dual : total 7 (fun y => D y * transform q y) = 2 * total 7 (fun a => q a * H a) := by
    rw [← Balanced242Section0320.duality, ← total_scale]
    apply congrArg (total 7); funext a; rw [hspec, Int.mul_left_comm]
  have up (y : W 7) : m * (D y * transform q y) ≤ 2 * (transform q y * transform q y) ∧
      -m * (D y * transform q y) ≤ 2 * (transform q y * transform q y) := by
    have hd : D y = -2 ∨ D y = -1 ∨ D y = 0 ∨ D y = 1 ∨ D y = 2 := by have := hD y; omega
    rcases hm with hm | hm | hm | hm <;> subst hm <;>
      rcases hplat y with h | h | h <;> change transform q y = _ at h <;> rw [h] <;>
      rcases hd with d | d | d | d | d <;> rw [d] <;> decide
  have s1 := total_mono 7 _ _ (fun y => (up y).1)
  have s2 := total_mono 7 _ _ (fun y => (up y).2)
  simp only [total_scale] at s1 s2
  rw [S3, dual] at s1 s2
  generalize total 7 (fun a => q a * H a) = T at s1 s2
  have h1 : m * (2 * T) = 2 * (m * T) := Int.mul_left_comm m 2 T
  have h2 : -m * (2 * T) = -(2 * (m * T)) := by rw [Int.neg_mul, h1]
  rw [h1] at s1; rw [h2] at s2
  change -16384 ≤ m * T ∧ m * T ≤ 16384
  exact ⟨by omega, by omega⟩

/-- No (0,32,0) section: the plateau hypothesis is now discharged. -/
theorem no_section_0_32_0 (D H : W 7 → Int)
    (hD : ∀ y, -2 ≤ D y ∧ D y ≤ 2)
    (hspec : ∀ a, transform D a = 2 * H a)
    (hH : ∀ a, H a = 5 ∨ H a = -5 ∨ H a = 7 ∨ H a = -7)
    (h5 : total 7 (fun a => if H a = 5 ∨ H a = -5 then (1 : Int) else 0) = 32) : False := by
  have hodd (a : W 7) : H a % 2 = 1 := by rcases hH a with h | h | h | h <;> rw [h] <;> decide
  obtain ⟨m, hm, hplat⟩ := plateau7 D H hspec hodd
  exact Balanced242Section0320.no_section_0_32_0 D H hD hspec hH h5 m hm hplat

end Balanced242Plateau

#print axioms Balanced242Plateau.plateau7
#print axioms Balanced242Plateau.no_section_0_32_0
#print axioms Balanced242Plateau.section_0_b_0
#print axioms Balanced242Plateau.t7_bound
