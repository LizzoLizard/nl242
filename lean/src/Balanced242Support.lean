import Balanced242Blocks

namespace Balanced242Support
open FrozenShells FreezeMovies CandyKnots CollisionLaw MaskRecovery SilentRoom Balanced242Parents Balanced242Blocks

private theorem append_sum (xs ys : List Int) : (xs ++ ys).sum = xs.sum + ys.sum := by
  induction xs <;> simp [*,Int.add_assoc]

private theorem sum_worlds (n : Nat) (f : W n → Int) :
    ((worlds n).map f).sum = total n f := by
  induction n with
  | zero => simp [worlds,total]
  | succ n ih => simp [worlds,total,List.map_map,append_sum,ih,Function.comp_def]

theorem inversion (v : W n → Int) (x : W n) :
    total n (fun a => transform v a * chr a x) = many n * v x := by
  have expand (a : W n) : transform v a * chr a x =
      total n (fun y => v y * (chr a x * chr a y)) := by
    rw [Int.mul_comm]; simp only [transform,← total_scale]
    apply congrArg (total n); funext y; ac_rfl
  simp only [expand]; rw [swap]
  simp only [total_scale,orthogonal]
  have factor (y : W n) : v y * (many n * hits x y) = many n * (hits x y * v y) := by ac_rfl
  simp only [factor,total_scale,select]

private def linearSum (ps : List (W n)) (H : W n → Int) (x : W n) :=
  (ps.map (fun a => H a * chr a x)).sum

/-- A function of e binary linear tests is constant on fibers of size
divisible by 2^(n-e) when e ≤ n. The carrier character allows the two
branches of each test to be combined using integer arithmetic. -/
private theorem fiber_dvd (ps : List (W n)) (H : W n → Int) (c : W n) (G : Int → Int) :
    many n ∣ many ps.length * total n (fun x => chr c x * G (linearSum ps H x)) := by
  induction ps generalizing c G with
  | nil =>
    have mass := identity_spectrum n c
    change total n (chr c) = _ at mass
    simp only [linearSum,List.map_nil,List.sum_nil,List.length_nil,show many 0 = 1 from rfl,Int.one_mul]
    simp only [Int.mul_comm _ (G 0),total_scale,mass]
    by_cases z : c = zero n
    · exact ⟨G 0,by simp [z,Int.mul_comm]⟩
    · exact ⟨0,by simp [z]⟩
  | cons p ps ih =>
    let plus (z : Int) := G (H p + z) + G (-H p + z)
    let minus (z : Int) := G (H p + z) - G (-H p + z)
    have point (x : W n) :
        2 * (chr c x * G (linearSum (p::ps) H x)) =
        chr c x * plus (linearSum ps H x) + chr (add n c p) x * minus (linearSum ps H x) := by
      simp only [linearSum,List.map_cons,List.sum_cons,chr,dot_add,signMul,plus,minus]
      cases hc : dot n c x <;> cases hp : dot n p x <;> simp [sign,hc,hp] <;> omega
    have step := Int.dvd_add (ih c plus) (ih (add n c p) minus)
    rw [←Int.mul_add,←total_add,←funext point,total_scale] at step
    simpa only [List.length_cons,many,Int.pow_succ,Int.mul_assoc] using step

def exceptions (H : W 8 → Int) := (worlds 8).filter (fun a => H a % 7 != 0)

private theorem reduce_list (m : Int) (ps : List (W 8)) (H : W 8 → Int) (x : W 8) :
    linearSum (ps.filter (fun a => H a % m != 0)) H x % m = linearSum ps H x % m := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    by_cases z : H p % m = 0
    · simp [List.filter_cons,z,linearSum] at ih ⊢
      rw [Int.add_emod,Int.mul_emod,z]; simp [ih]
    · simp only [List.filter_cons, bne_iff_ne.mpr z,if_true,linearSum,List.map_cons,List.sum_cons] at *
      rw [Int.add_emod,ih,←Int.add_emod]

def agreements (f g : Half) := countPair f g false + countPair f g true

/-- Removing multiples of seven in the high block preserves the agreement
test after inversion: the three possible inverse values are 0, 512, -512. -/
theorem sparse_high_agreements (f g : Half) :
    (256:Int) ∣ many (exceptions (hi f g)).length * agreements f g := by
  let H := hi f g
  let E := exceptions H
  let G (z : Int) : Int := if z % 7 = 0 then 1 else 0
  have inv (x : W 8) : linearSum (worlds 8) H x = 256 * (sign (f x) - sign (g x)) := by
    simp only [linearSum,sum_worlds,H,hi,spec,Int.sub_mul,total_sub,inversion]
    change 256 * _ - 256 * _ = 256 * (_ - _); omega
  have point (x : W 8) : chr (zero 8) x * G (linearSum E H x) =
      sameBit false (f x) (g x) + sameBit true (f x) (g x) := by
    simp only [G,E,exceptions,reduce_list,inv,chr,dot_zero,show sign false=1 from rfl,Int.one_mul]
    cases f x <;> cases g x <;> decide
  have h := fiber_dvd E H (zero 8) G
  simp only [point,total_add] at h
  exact h

private theorem count_list (xs : List α) (p : α → Bool) :
    ((xs.filter p).length : Int) = (xs.map (fun a => if p a then (1:Int) else 0)).sum := by
  induction xs with
  | nil => rfl
  | cons a xs ih => cases e : p a <;> simp [e,List.filter_cons,ih,Int.add_comm]

/-- In adapted coordinates, fewer than 64 agreements leave at most five
exceptional high masks. Their binary tests force the agreement count to
be divisible by eight, which excludes the entire interval from 60 to 63. -/
theorem agreement_floor (f g : Half)
    (axis : supportXor (halves f g) = (true,zero 8))
    (bal : total 9 (fun x => sign (halves f g x)) = 0)
    (cap : ∀ a, (lo f g a).natAbs ≤ 28 ∧ (hi f g a).natAbs ≤ 28) :
    64 ≤ agreements f g := by
  let E := exceptions (hi f g)
  let mark (a : W 8) : Int := if hi f g a % 7 != 0 then 1 else 0
  have sizeE : (E.length : Int) = total 8 mark := by
    unfold E exceptions; rw [count_list,sum_worlds]
  have pt (a : W 8) : hi f g a * hi f g a + 384 * mark a ≤ 784 := by
    have cap' := (cap a).2
    have res := (adapted_blocks f g axis bal a).2
    have vals : hi f g a = -28 ∨ hi f g a = -20 ∨ hi f g a = -12 ∨ hi f g a = -4 ∨
        hi f g a = 4 ∨ hi f g a = 12 ∨ hi f g a = 20 ∨ hi f g a = 28 := by omega
    rcases vals with e|e|e|e|e|e|e|e <;> simp [mark,e]
  have budget := total_mono 8 _ _ pt
  simp only [total_add,total_const,total_scale,diffEnergy,←sizeE] at budget
  change _ ≤ 256*784 at budget
  obtain ⟨eqv,minPairs,_⟩ := equal_pair_range f g axis bal cap
  by_cases small : agreements f g ≤ 62
  · have m : E.length ≤ 5 := by unfold agreements at small; omega
    obtain ⟨k,hk⟩ := sparse_high_agreements f g
    change many E.length * agreements f g = 256*k at hk
    have bottom : 60 ≤ agreements f g := by unfold agreements; omega
    have casesE : E.length = 0 ∨ E.length = 1 ∨ E.length = 2 ∨ E.length = 3 ∨ E.length = 4 ∨ E.length = 5 := by omega
    rcases casesE with e|e|e|e|e|e <;> rw [e] at hk <;> simp [many,Int.pow_succ] at hk <;> omega
  · unfold agreements at small ⊢; omega

private def bitValue (b : Bool) : Int := if b then 1 else 0

/-- Parity of a signed sum of linear tests is again a linear test. -/
private theorem parity_tests (v : W m → W n) (z : W m → Int) (a : W n) :
    total m (fun x => z x * bitValue (dot n a (v x))) % 2 =
    bitValue (dot n a (xorTotal m (fun x => if z x % 2 = 0 then zero n else v x))) := by
  induction m with
  | zero =>
    simp only [total,xorTotal]
    by_cases h : z () % 2 = 0 <;> cases e : dot n a (v ()) <;>
      simp [h,e,bitValue,dot_zero_right] <;> omega
  | succ m ih =>
    rw [total,Int.add_emod,xorTotal,dot_right]
    rw [ih (fun x => v (false,x)) (fun x => z (false,x)), ih (fun x => v (true,x)) (fun x => z (true,x))]
    generalize dot n a _ = b; generalize dot n a _ = c
    cases b <;> cases c <;> decide

def pairSign (f g : Half) (x : W 8) := sign (f x) + sign (g x)

theorem lo_transform (f g : Half) : lo f g = transform (pairSign f g) := by
  funext a; simp only [lo,spec,transform,pairSign,Int.add_mul,total_add]

/-- Changing signs while preserving every agreement site shifts the low
residue by a linear function. Its mask is the XOR of all changed agreement
sites. Both tables are balanced, so the constant term vanishes. -/
theorem same_support_residue (f g F G : Half)
    (same : ∀ x, f x = g x ↔ F x = G x)
    (bal : total 8 (pairSign f g) = 0) (bal' : total 8 (pairSign F G) = 0) :
    let delta := xorTotal 8 (fun x => if f x = g x ∧ f x ≠ F x then x else zero 8)
    ∀ a, lo F G a % 16 = (lo f g a + 8 * (if dot 8 a delta then 1 else 0)) % 16 := by
  let z (x : W 8) := if f x = g x ∧ f x ≠ F x then sign (F x) else 0
  have step (x : W 8) : pairSign F G x - pairSign f g x = 4*z x := by
    have s := same x
    cases h : f x <;> cases j : g x <;> cases k : F x <;> cases l : G x <;>
      simp_all [pairSign,z,sign]
  have deltaBit (x : W 8) : (if z x % 2 = 0 then zero 8 else x) =
      (if f x = g x ∧ f x ≠ F x then x else zero 8) := by
    by_cases h : f x = g x ∧ f x ≠ F x
    · simp only [z,if_pos h]; cases F x <;> rfl
    · simp [z,h]
  have zeroSum := congrArg (total 8) (funext step)
  simp only [total_sub,total_scale,bal,bal'] at zeroSum
  intro delta a
  dsimp only [delta]
  have linear := parity_tests (fun x : W 8 => x) z a
  simp only [deltaBit] at linear
  have diff : lo F G a - lo f g a = 4 * transform z a := by
    rw [lo_transform,lo_transform]
    simp only [transform,←total_sub,←Int.sub_mul,step,Int.mul_assoc,total_scale]
  have split (x : W 8) : z x * chr a x = z x - 2*(z x * bitValue (dot 8 a x)) := by
    cases h : dot 8 a x <;> simp [chr,sign,h,bitValue] <;> omega
  simp only [transform,split,total_sub,total_scale] at diff
  change (total 8 (fun x => z x * bitValue (dot 8 a x))) % 2 = _ at linear
  generalize dot 8 a (xorTotal 8 (fun x => if f x = g x ∧ f x ≠ F x then x else zero 8)) = b at linear ⊢
  have hz : total 8 z = 0 := by omega
  rw [hz] at diff
  let K := total 8 (fun x => z x * bitValue (dot 8 a x))
  change K % 2 = bitValue b at linear
  change lo F G a - lo f g a = 4*(0-2*K) at diff
  have target : lo F G a = lo f g a + 8*bitValue b + 16*(-(K/2) - bitValue b) := by omega
  change lo F G a % 16 = (lo f g a + 8*bitValue b) % 16
  rw [target,Int.add_mul_emod_self_left]

/-- Low energy on one fixed residue pattern. The subtraction of 256 accounts
for the balanced DC mask, which has actual magnitude zero. -/
theorem low_support_budget (f g : Half) (dc : lo f g (zero 8) = 0)
    (res : ∀ a, lo f g a % 8 = 0) (cap : ∀ a, (lo f g a).natAbs ≤ 24) :
    let Z := total 8 (fun a => if lo f g a % 16 = 0 then 1 else 0)
    1024 * agreements f g + 320*Z + 256 ≤ 147456 := by
  let mark (a : W 8) : Int := if lo f g a % 16 = 0 then 1 else 0
  have pt (a : W 8) : lo f g a * lo f g a + 320*mark a + 256*hits (zero 8) a ≤ 576 := by
    by_cases z : zero 8 = a
    · subst a; simp [dc,mark,hits]
    · have h := cap a; have r := res a
      have vals : lo f g a = -24 ∨ lo f g a = -16 ∨ lo f g a = -8 ∨ lo f g a = 0 ∨
          lo f g a = 8 ∨ lo f g a = 16 ∨ lo f g a = 24 := by omega
      rcases vals with e|e|e|e|e|e|e <;> simp [hits,z,mark,e]
  have h := total_mono 8 _ _ pt
  have sq (b c : Bool) : (sign b + sign c)*(sign b + sign c) =
      4*(sameBit false b c + sameBit true b c) := by cases b <;> cases c <;> decide
  simp only [total_add,total_scale,diagonal,total_const] at h
  rw [lo_transform,parsevalInt] at h
  simp only [pairSign,sq,total_scale,total_add] at h
  change 256*(4*(_+_)) + 320*total 8 mark + 256*1 ≤ 256*576 at h
  change 1024*(total 8 (fun w => sameBit false (f w) (g w)) + total 8 (fun w => sameBit true (f w) (g w))) + 320*total 8 mark + 256 ≤ 147456
  omega


def synth (F : W n → Int) (x : W n) := total n (fun a => F a * chr a x)
def sector (u : W n) (b : Bool) (F : W n → Int) (a : W n) :=
  if dot n a u = b then F a else 0

private theorem sector_inverse (u : W n) (b : Bool) (F : W n → Int) (x : W n) :
    2 * synth (sector u b F) x = synth F x + sign b * synth F (add n x u) := by
  simp only [synth,←total_scale,←total_add]
  apply congrArg (total n); funext a
  simp only [sector,chr,dot_right,signMul]
  cases h : dot n a u <;> cases b <;> cases j : dot n a x <;> simp [sign] <;> omega

/-- Inversion on one frequency coset specified by two binary tests. -/
theorem two_direction_inversion (F : W 8 → Int) (u v x : W 8) (p q : Bool) :
    4 * synth (sector u p (sector v q (transform F))) x =
    256 * ((F x + sign q * F (add 8 x v)) +
      sign p * (F (add 8 x u) + sign q * F (add 8 (add 8 x u) v))) := by
  let H := sector v q (transform F)
  calc
    _ = 2 * (2 * synth (sector u p H) x) := by dsimp only [H]; omega
    _ = 2 * (synth H x + sign p * synth H (add 8 x u)) := by rw [sector_inverse]
    _ = 2 * synth H x + sign p * (2 * synth H (add 8 x u)) := by
      rw [Int.mul_add,Int.mul_left_comm 2 (sign p)]
    _ = _ := by
      unfold H
      rw [sector_inverse v q (transform F) x,sector_inverse v q (transform F) (add 8 x u)]
      simp only [synth,inversion,show many 8 = 256 from rfl]
      cases p <;> cases q <;> simp [sign] <;> omega

private def score (k : Fin 4) (b : W 3) : Int :=
  match k.val with
  | 0 => 0
  | 1 => sign b.1
  | 2 => sign b.1 + sign b.2.1
  | _ => sign b.1 + sign b.2.1 + sign b.2.2.1

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
private theorem score_zero : ∀ (k : Fin 4) (x y z : W 3),
    score k x % 3 = 0 → score k y % 3 = 0 → score k z % 3 = 0 →
    score k (add 3 (add 3 x y) z) % 3 = 0 := by
  have finite : ∀ (k : Fin 4) (a b c d e f g h i : Bool),
      score k (a,b,c,()) % 3 = 0 → score k (d,e,f,()) % 3 = 0 →
      score k (g,h,i,()) % 3 = 0 →
      score k (add 3 (add 3 (a,b,c,()) (d,e,f,())) (g,h,i,())) % 3 = 0 := by decide
  intro k ⟨a,b,c,()⟩ ⟨d,e,f,()⟩ ⟨g,h,i,()⟩
  exact finite k a b c d e f g h i

def signedTest (p : W n × Bool) (x : W n) := xor p.2 (dot n p.1 x)

private theorem signedTest_three (p : W n × Bool) (x y z : W n) :
    signedTest p (add n (add n x y) z) =
    xor (xor (signedTest p x) (signedTest p y)) (signedTest p z) := by
  simp only [signedTest,dot_right]
  cases p.2 <;> cases dot n p.1 x <;> cases dot n p.1 y <;> cases dot n p.1 z <;> rfl

def threeScore (k : Fin 4) (p q r : W n × Bool) (x : W n) :=
  score k (signedTest p x,signedTest q x,signedTest r x,())

/-- The mod-three zero set of a sum of at most three signed characters is
closed under ternary XOR. k selects how many of the three terms to use. -/
theorem three_character_zeros (k : Fin 4) (p q r : W n × Bool) (x y z : W n)
    (hx : threeScore k p q r x % 3 = 0) (hy : threeScore k p q r y % 3 = 0)
    (hz : threeScore k p q r z % 3 = 0) :
    threeScore k p q r (add n (add n x y) z) % 3 = 0 := by
  simp only [threeScore,signedTest_three]
  exact score_zero k _ _ _ hx hy hz


private def signedSum (ps : List (W n × Bool)) (x : W n) :=
  (ps.map (fun p => sign (signedTest p x))).sum

private theorem short_score (ps : List (W n × Bool)) (short : ps.length ≤ 3) :
    ∃ (k : Fin 4) (p q r : W n × Bool), ∀ x, signedSum ps x = threeScore k p q r x := by
  let d : W n × Bool := (zero n,false)
  cases ps with
  | nil => exact ⟨0,d,d,d,fun _ => rfl⟩
  | cons p tail =>
    cases tail with
    | nil => exact ⟨1,p,d,d,fun _ => by simp [signedSum,threeScore,score]⟩
    | cons q tail =>
      cases tail with
      | nil => exact ⟨2,p,q,d,fun _ => by simp [signedSum,threeScore,score]⟩
      | cons r tail =>
        cases tail with
        | nil => exact ⟨3,p,q,r,fun _ => by simp [signedSum,threeScore,score,Int.add_assoc]⟩
        | cons s tail => simp at short

private def encodeTerm (H : W n → Int) (a : W n) : W n × Bool := (a,decide (H a % 3 = 2))

private theorem encode_sum (ps : List (W n)) (H : W n → Int) (x : W n)
    (nonzero : ∀ a ∈ ps, H a % 3 ≠ 0) :
    linearSum ps H x % 3 = signedSum (ps.map (encodeTerm H)) x % 3 := by
  induction ps with
  | nil => rfl
  | cons a ps ih =>
    have ha := nonzero a (by simp)
    have step : (H a * chr a x) % 3 = sign (signedTest (encodeTerm H a) x) % 3 := by
      have v : H a % 3 = 1 ∨ H a % 3 = 2 := by omega
      rw [Int.mul_emod]
      rcases v with h|h <;> cases j : dot n a x <;> simp [encodeTerm,h,signedTest,chr,j,sign]
    have tail := ih (fun b hb => nonzero b (by simp [hb]))
    simp only [linearSum,signedSum,List.map_cons,List.sum_cons] at tail ⊢
    rw [Int.add_emod,step,tail,←Int.add_emod]

/-- Three zeros and a nonzero at their ternary sum force at least four
frequency coefficients outside 3ℤ. Applies to a single selected sector. -/
theorem four_mod_three_terms (H : W 8 → Int) (x y z : W 8)
    (hx : synth H x % 3 = 0) (hy : synth H y % 3 = 0) (hz : synth H z % 3 = 0)
    (hw : synth H (add 8 (add 8 x y) z) % 3 ≠ 0) :
    4 ≤ ((worlds 8).filter (fun a => H a % 3 != 0)).length := by
  let E := (worlds 8).filter (fun a => H a % 3 != 0)
  apply Classical.byContradiction
  intro fail
  have short : (E.map (encodeTerm H)).length ≤ 3 := by
    rw [List.length_map]; unfold E; omega
  obtain ⟨k,p,q,r,h⟩ := short_score (E.map (encodeTerm H)) short
  have eqn (a : W 8) : synth H a % 3 = threeScore k p q r a % 3 := by
    have nonzero : ∀ b ∈ E, H b % 3 ≠ 0 := by
      intro b hb; exact bne_iff_ne.mp (List.mem_filter.mp hb).2
    have e := encode_sum E H a nonzero
    rw [h a] at e
    unfold E at e
    rw [reduce_list,linearSum,sum_worlds] at e
    exact e
  exact hw ((eqn _).trans (three_character_zeros k p q r x y z
    ((eqn _).symm.trans hx) ((eqn _).symm.trans hy) ((eqn _).symm.trans hz)))


/-- The total unsigned mass of four input positions. For F = pairSign f g,
this is twice the number of agreements among the four positions. -/
def cellMass (F : W 8 → Int) (u v x : W 8) :=
  (F x).natAbs + (F (add 8 x v)).natAbs + (F (add 8 x u)).natAbs +
    (F (add 8 (add 8 x u) v)).natAbs

private theorem singleton_value (a b c d : Int) (p q : Bool)
    (va : a = 0 ∨ a = 2 ∨ a = -2) (vb : b = 0 ∨ b = 2 ∨ b = -2)
    (vc : c = 0 ∨ c = 2 ∨ c = -2) (vd : d = 0 ∨ d = 2 ∨ d = -2)
    (h : a.natAbs+b.natAbs+c.natAbs+d.natAbs = 2) :
    let s := a + sign q * b + sign p * (c + sign q * d)
    s = 2 ∨ s = -2 := by
  rcases va with rfl|rfl|rfl <;> rcases vb with rfl|rfl|rfl <;>
    rcases vc with rfl|rfl|rfl <;> rcases vd with rfl|rfl|rfl <;>
    first | (exfalso; exact (by decide : ¬_) h) | (cases p <;> cases q <;> decide)

/-- Three empty translates whose ternary sum contains one occupied site
force four exceptional coefficients in each frequency sector, for every
assignment of signs to that support. -/
theorem occupancy_forces_four (F : W 8 → Int) (u v x y z : W 8)
    (values : ∀ a, F a = 0 ∨ F a = 2 ∨ F a = -2)
    (hx : cellMass F u v x = 0) (hy : cellMass F u v y = 0) (hz : cellMass F u v z = 0)
    (one : cellMass F u v (add 8 (add 8 x y) z) = 2) (p q : Bool) :
    let H := sector u p (sector v q (transform F))
    4 ≤ ((worlds 8).filter (fun a => H a % 3 != 0)).length := by
  let H := sector u p (sector v q (transform F))
  have empty (a : W 8) (e : cellMass F u v a = 0) : synth H a % 3 = 0 := by
    have inv := two_direction_inversion F u v a p q
    change 4 * synth H a = _ at inv
    unfold cellMass at e
    have e0 : F a = 0 := by omega
    have e1 : F (add 8 a v) = 0 := by omega
    have e2 : F (add 8 a u) = 0 := by omega
    have e3 : F (add 8 (add 8 a u) v) = 0 := by omega
    simp only [e0,e1,e2,e3,Int.mul_zero,Int.add_zero] at inv
    omega
  let w := add 8 (add 8 x y) z
  have last : synth H w % 3 ≠ 0 := by
    have inv := two_direction_inversion F u v w p q
    change 4 * synth H w = _ at inv
    change cellMass F u v w = 2 at one
    unfold cellMass at one
    have v0 := values w
    have v1 := values (add 8 w v)
    have v2 := values (add 8 w u)
    have v3 := values (add 8 (add 8 w u) v)
    have result := singleton_value _ _ _ _ p q v0 v1 v2 v3 one
    dsimp only at result
    rcases result with h|h <;> rw [h] at inv <;> omega
  exact four_mod_three_terms H x y z (empty x hx) (empty y hy) (empty z hz) last

/-- A 64-mask zero residue class and three 64-mask odd residue classes.
The balanced DC mask costs 256, and each low peak of magnitude 8 outside
the zero class costs 512 compared with magnitude 24. -/
theorem twelve_small_peaks (t small zeroCount : Int)
    (dc : 1 ≤ zeroCount) (h : 12 ≤ small)
    (energy : 1024*t = 64*256 + 192*576 - 256*zeroCount - 512*small) : t ≤ 117 := by omega

#print axioms occupancy_forces_four
#print axioms four_mod_three_terms
#print axioms two_direction_inversion
#print axioms three_character_zeros
#print axioms twelve_small_peaks
#print axioms sparse_high_agreements
#print axioms agreement_floor
#print axioms same_support_residue
#print axioms low_support_budget
end Balanced242Support
