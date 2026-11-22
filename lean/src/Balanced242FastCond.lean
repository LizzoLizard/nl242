/-
  Balanced242FastCond.lean — Kernel-fast pure-primitive-Nat verifier for 14-row
  anchor-pair certificates (`checkCondCertFast2` / `checkLayerFast2`), proved
  sound by direct implication into `Balanced242Farkas.checkLayerWithMask`.
  Zero Mathlib, zero `sorry`, zero `native_decide`.
-/
import Balanced242Farkas

namespace Balanced242FastCond

open Balanced242Farkas (Triple CondWeights unpackCondWeights condRhs scoreLo scoreHi
  tripleLe sixOK genSubtypes inAllowedMask checkCondRankFast checkCondCertFast
  checkLayerWithMask)

/-! ## Part 1: Pure primitive-`Nat` / `match`-only definitions (zero `WellFounded.fix`) -/

def absDiff (u v : Nat) : Nat :=
  match Nat.ble u v with
  | true => Nat.sub v u
  | false => Nat.sub u v

def tripleLeFast (a1 b1 c1 a2 b2 c2 : Nat) : Bool :=
  match Nat.beq a1 a2 with
  | true =>
    match Nat.beq b1 b2 with
    | true => Nat.ble c1 c2
    | false => Nat.ble b1 b2
  | false => Nat.ble a1 a2

def sixOKNat (a b c r : Nat) : Bool :=
  let m := Nat.add b c
  let mass := Nat.add (Nat.add (Nat.mul 6 a) (Nat.mul 3 b)) (Nat.mul 5 c)
  match Nat.beq (Nat.mod mass 4) 0 with
  | false => false
  | true =>
    match Nat.ble (Nat.add a m) 64 with
    | false => false
    | true =>
      match Nat.beq (Nat.mod m 2) 0 with
      | false => false
      | true =>
        let d := absDiff (Nat.add (Nat.add (Nat.mul 8 a) (Nat.mul 12 b)) (Nat.mul 4 c)) 448
        match Nat.beq r 6 with
        | true =>
          match Nat.ble 8 m with
          | false => false
          | true =>
            match Nat.beq (Nat.mod d 4) 0 with
            | false => false
            | true =>
              let tau := Nat.div d 4
              match Nat.ble tau 256 with
              | false => false
              | true =>
                let q := Nat.div tau 64
                let j := Nat.mod tau 64
                Nat.ble (Nat.add (Nat.add (Nat.mul (Nat.sub 64 j) (Nat.mul q q))
                  (Nat.mul j (Nat.mul (Nat.add q 1) (Nat.add q 1)))) (Nat.div mass 2)) 196
        | false =>
          match Nat.ble 4 m with
          | false => false
          | true =>
            match Nat.beq (Nat.mod d 8) 0 with
            | false => false
            | true =>
              let tau := Nat.div d 8
              match Nat.ble tau 64 with
              | false => false
              | true =>
                let q := Nat.div tau 16
                let j := Nat.mod tau 16
                Nat.ble (Nat.add (Nat.add (Nat.mul (Nat.sub 16 j) (Nat.mul q q))
                  (Nat.mul j (Nat.mul (Nat.add q 1) (Nat.add q 1)))) (Nat.div mass 2)) 196

def genSubLoopY (a b c r x z : Nat) : Nat → List Triple → List Triple
  | 0, acc => acc
  | fuel + 1, acc =>
    let y := Nat.add (Nat.mod (Nat.add (Nat.mul 2 x) z) 4) (Nat.mul 4 fuel)
    let acc' :=
      match Nat.ble y b with
      | false => acc
      | true =>
        let q1 := Nat.sub a x; let q2 := Nat.sub b y; let q3 := Nat.sub c z
        match tripleLeFast x y z q1 q2 q3 with
        | false => acc
        | true =>
          match sixOKNat x y z r with
          | false => acc
          | true =>
            match sixOKNat q1 q2 q3 r with
            | false => acc
            | true => (x, y, z) :: acc
    genSubLoopY a b c r x z fuel acc'

def genSubLoopZ (a b c r x : Nat) : Nat → List Triple → List Triple
  | 0, acc => acc
  | z + 1, acc =>
    genSubLoopZ a b c r x z (genSubLoopY a b c r x z (Nat.add (Nat.div b 4) 1) acc)

def genSubLoopX (a b c r : Nat) : Nat → List Triple → List Triple
  | 0, acc => acc
  | x + 1, acc =>
    genSubLoopX a b c r x (genSubLoopZ a b c r x (Nat.add c 1) acc)

def genSubFast (n : Triple) (r : Nat) : List Triple :=
  genSubLoopX n.1 n.2.1 n.2.2 r (Nat.add (Nat.div n.1 2) 1) []

def intLe (a b : Int) : Bool :=
  match a, b with
  | Int.ofNat m, Int.ofNat n => Nat.ble m n
  | Int.ofNat _, Int.negSucc _ => false
  | Int.negSucc _, Int.ofNat _ => true
  | Int.negSucc m, Int.negSucc n => Nat.ble n m

def listMinInt : List Int → Int → Int
  | [], m => m
  | x :: rest, m =>
    match intLe x m with
    | true => listMinInt rest x
    | false => listMinInt rest m

def inAllowedFast (mask : Nat) (x y z : Nat) : Bool :=
  match Nat.ble x 63 with
  | false => false
  | true =>
    match Nat.ble y 63 with
    | false => false
    | true =>
      match Nat.ble z 63 with
      | false => false
      | true =>
        let idx := Nat.add (Nat.mul (Nat.add (Nat.mul x 64) z) 64) y
        Nat.beq (Nat.land (Nat.shiftRight mask idx) 1) 1

def checkHiLoop (hi : Triple) (mask : Nat) (p : Triple) (sL : Int) : List (Triple × Int) → Bool
  | [] => true
  | (v, negSH) :: rest =>
    match intLe sL negSH with
    | true => checkHiLoop hi mask p sL rest
    | false =>
      match inAllowedFast mask (Nat.add p.1 v.1) (Nat.add p.2.1 v.2.1) (Nat.add p.2.2 v.2.2) with
      | false => checkHiLoop hi mask p sL rest
      | true =>
        match inAllowedFast mask (Nat.add p.1 (Nat.sub hi.1 v.1)) (Nat.add p.2.1 (Nat.sub hi.2.1 v.2.1))
            (Nat.add p.2.2 (Nat.sub hi.2.2 v.2.2)) with
        | false => checkHiLoop hi mask p sL rest
        | true => false

def checkLoLoop (lo hi : Triple) (mask : Nat) (W : CondWeights) (r : Nat) (minNegH : Int)
    (hiNeg : List (Triple × Int)) : List Triple → Bool
  | [] => true
  | p :: rest =>
    let sL := scoreLo lo W r p
    match intLe sL minNegH with
    | true => checkLoLoop lo hi mask W r minNegH hiNeg rest
    | false =>
      match checkHiLoop hi mask p sL hiNeg with
      | true => checkLoLoop lo hi mask W r minNegH hiNeg rest
      | false => false

def checkCondRankFast2 (lo hi : Triple) (mask : Nat) (W : CondWeights) (r : Nat) : Bool :=
  let subL := genSubFast lo r
  let subH := genSubFast hi r
  let hiNeg := subH.map (fun v => (v, -scoreHi hi W v))
  match hiNeg with
  | [] => true
  | (_, n0) :: rest =>
    let minNegH := listMinInt (rest.map Prod.snd) n0
    checkLoLoop lo hi mask W r minNegH hiNeg subL

def checkCondCertFast2 (lo hi : Triple) (mask : Nat) (ws : List (Nat × Int)) : Bool :=
  let W := unpackCondWeights ws
  match intLe 1 (condRhs lo hi W) with
  | false => false
  | true =>
    match checkCondRankFast2 lo hi mask W 4 with
    | false => false
    | true => checkCondRankFast2 lo hi mask W 6

def checkLayerFast2 (a b c : Nat) (mask : Nat) (layer : List (Triple × List (Nat × Int))) : Bool :=
  layer.all fun (lo, ws) =>
    checkCondCertFast2 lo (Nat.sub a lo.1, Nat.sub b lo.2.1, Nat.sub c lo.2.2) mask ws

/-! ## Part 2: Soundness proofs into `Balanced242Farkas` -/

private theorem intLe_iff (a b : Int) : intLe a b = true ↔ a ≤ b := by
  cases a with
  | ofNat m =>
    cases b with
    | ofNat n => simp [intLe, Nat.ble_eq]
    | negSucc n => simp [intLe, Int.negSucc_eq]; omega
  | negSucc m =>
    cases b with
    | ofNat n => simp [intLe, Int.negSucc_eq]; omega
    | negSucc n => simp [intLe, Nat.ble_eq, Int.negSucc_eq]; omega

private theorem listMinInt_le_base : ∀ (L : List Int) (m : Int), listMinInt L m ≤ m
  | [], m => Int.le_refl m
  | x :: rest, m => by
    unfold listMinInt
    cases h : intLe x m
    · dsimp only; exact listMinInt_le_base rest m
    · dsimp only
      have hle : x ≤ m := (intLe_iff x m).mp h
      have h1 := listMinInt_le_base rest x
      omega

private theorem listMinInt_le_mem : ∀ (L : List Int) (m x : Int), x ∈ L → listMinInt L m ≤ x
  | [], _, _, h => nomatch h
  | a :: rest, m, x, h => by
    unfold listMinInt
    rcases List.mem_cons.mp h with rfl | htail
    · cases hc : intLe x m
      · dsimp only
        have hgt : ¬ (x ≤ m) := fun hle => by rw [(intLe_iff x m).mpr hle] at hc; exact Bool.noConfusion hc
        have h1 := listMinInt_le_base rest m
        omega
      · dsimp only; exact listMinInt_le_base rest x
    · cases hc : intLe a m
      · dsimp only; exact listMinInt_le_mem rest m x htail
      · dsimp only; exact listMinInt_le_mem rest a x htail

private theorem tripleLeFast_eq (p q : Triple) :
    tripleLeFast p.1 p.2.1 p.2.2 q.1 q.2.1 q.2.2 = tripleLe p q := by
  unfold tripleLeFast tripleLe
  cases h1 : Nat.beq p.1 q.1
  · have hne : p.1 ≠ q.1 := by
      intro heq; rw [heq, Nat.beq_refl] at h1; exact Bool.noConfusion h1
    cases hlt : Nat.ble p.1 q.1
    · have hgt : q.1 < p.1 := by
        have : ¬ (p.1 ≤ q.1) := by intro h; rw [Nat.ble_eq.mpr h] at hlt; exact Bool.noConfusion hlt
        omega
      simp [show ¬(p.1 < q.1) by omega, hne]
    · have hle : p.1 ≤ q.1 := Nat.ble_eq.mp hlt
      simp [show p.1 < q.1 by omega]
  · have he1 : p.1 = q.1 := Nat.eq_of_beq_eq_true h1
    cases h2 : Nat.beq p.2.1 q.2.1
    · have hne2 : p.2.1 ≠ q.2.1 := by
        intro heq; rw [heq, Nat.beq_refl] at h2; exact Bool.noConfusion h2
      cases hlt2 : Nat.ble p.2.1 q.2.1
      · have : ¬ (p.2.1 ≤ q.2.1) := by intro h; rw [Nat.ble_eq.mpr h] at hlt2; exact Bool.noConfusion hlt2
        simp [he1, show ¬(p.2.1 < q.2.1) by omega, hne2]
      · have hle2 : p.2.1 ≤ q.2.1 := Nat.ble_eq.mp hlt2
        simp [he1, show p.2.1 < q.2.1 by omega]
    · have he2 : p.2.1 = q.2.1 := Nat.eq_of_beq_eq_true h2
      cases h3 : Nat.ble p.2.2 q.2.2
      · have : ¬ (p.2.2 ≤ q.2.2) := by intro h; rw [Nat.ble_eq.mpr h] at h3; exact Bool.noConfusion h3
        simp [he1, he2, this]
      · have hle3 : p.2.2 ≤ q.2.2 := Nat.ble_eq.mp h3
        simp [he1, he2, hle3]

private theorem absDiff_eq (u v : Nat) : (absDiff u v : Int) = (((u : Int) - (v : Int)).natAbs : Int) := by
  unfold absDiff
  cases h : Nat.ble u v
  · dsimp only
    have hgt : ¬ (u ≤ v) := by intro hle; rw [Nat.ble_eq.mpr hle] at h; exact Bool.noConfusion h
    change ((u - v : Nat) : Int) = (((u : Int) - (v : Int)).natAbs : Int)
    omega
  · dsimp only
    have hle : u ≤ v := Nat.ble_eq.mp h
    change ((v - u : Nat) : Int) = (((u : Int) - (v : Int)).natAbs : Int)
    omega

private theorem absDiff_mod_div (u v k : Nat) (hk : 0 < k)
    (hmod : ((u : Int) - (v : Int)) % (k : Int) = 0) :
    absDiff u v % k = 0 ∧ ((((u : Int) - (v : Int)) / (k : Int)).natAbs : Nat) = absDiff u v / k := by
  have hd_nat : absDiff u v = ((u : Int) - (v : Int)).natAbs := by
    have := absDiff_eq u v; omega
  have hmul : (u : Int) - (v : Int) = (k : Int) * (((u : Int) - (v : Int)) / (k : Int)) := by
    have := Int.ediv_add_emod ((u : Int) - (v : Int)) (k : Int); omega
  have habs : absDiff u v = k * (((u : Int) - (v : Int)) / (k : Int)).natAbs := by
    rw [hd_nat]
    have hna : ((u : Int) - (v : Int)).natAbs = ((k : Int) * (((u : Int) - (v : Int)) / (k : Int))).natAbs :=
      congrArg Int.natAbs hmul
    rw [hna, Int.natAbs_mul]; rfl
  refine ⟨by rw [habs, Nat.mul_mod_right], by rw [habs, Nat.mul_div_cancel_left _ hk]⟩

private theorem sixOKNat_of_sixOK (a b c r : Nat) (h : sixOK a b c r = true) :
    sixOKNat a b c r = true := by
  unfold sixOK at h
  dsimp only at h
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨hmass4, hsum64⟩, hm2⟩, hmge⟩, hph_mod⟩, htau_le⟩, hjen⟩ := h
  unfold sixOKNat
  dsimp only
  have c1 : Nat.beq (Nat.mod (Nat.add (Nat.add (Nat.mul 6 a) (Nat.mul 3 b)) (Nat.mul 5 c)) 4) 0 = true :=
    Nat.beq_eq.mpr hmass4
  have c2 : Nat.ble (Nat.add a (Nat.add b c)) 64 = true := Nat.ble_eq.mpr (by change a + (b + c) ≤ 64; omega)
  have c3 : Nat.beq (Nat.mod (Nat.add b c) 2) 0 = true := Nat.beq_eq.mpr hm2
  rw [c1, c2, c3]
  dsimp only
  have hph_eq : (-448 + 8 * (a : Int) + 12 * (b : Int) + 4 * (c : Int)) =
      ((8 * a + 12 * b + 4 * c : Nat) : Int) - (448 : Nat) := by omega
  cases hr : Nat.beq r 6
  · have hneq6 : r ≠ 6 := by intro heq; rw [heq] at hr; exact Bool.noConfusion hr
    simp only [hneq6, if_false] at hmge hph_mod htau_le hjen
    rw [hph_eq] at hph_mod htau_le hjen
    have hmd := absDiff_mod_div (8 * a + 12 * b + 4 * c) 448 8 (by omega) hph_mod
    have hmd2 : ((((8 * a + 12 * b + 4 * c : Nat) : Int) - (448 : Nat)) / 8).natAbs =
        absDiff (8 * a + 12 * b + 4 * c) 448 / 8 := hmd.2
    have cm : Nat.ble 4 (Nat.add b c) = true := Nat.ble_eq.mpr hmge
    have cd : Nat.beq (Nat.mod (absDiff (Nat.add (Nat.add (Nat.mul 8 a) (Nat.mul 12 b)) (Nat.mul 4 c)) 448) 8) 0 = true :=
      Nat.beq_eq.mpr hmd.1
    have htau_nat : absDiff (8 * a + 12 * b + 4 * c) 448 / 8 ≤ 64 := by
      have : ((((8 * a + 12 * b + 4 * c : Nat) : Int) - (448 : Nat)) / 8).natAbs ≤ 64 := by omega
      rw [hmd2] at this; exact this
    have ctau : Nat.ble (Nat.div (absDiff (Nat.add (Nat.add (Nat.mul 8 a) (Nat.mul 12 b)) (Nat.mul 4 c)) 448) 8) 64 = true :=
      Nat.ble_eq.mpr htau_nat
    dsimp only
    rw [cm, cd, ctau]
    dsimp only
    apply Nat.ble_eq.mpr
    rw [hmd2] at hjen
    let tau := absDiff (8 * a + 12 * b + 4 * c) 448 / 8
    change (16 - (tau : Int) % 16) * (((tau : Int) / 16) * ((tau : Int) / 16)) +
      (tau : Int) % 16 * (((tau : Int) / 16 + 1) * ((tau : Int) / 16 + 1)) ≤
      196 - ((6 * a + 3 * b + 5 * c : Nat) : Int) / 2 at hjen
    have hq_eq : ((tau : Int) / 16) = ((tau / 16 : Nat) : Int) := by omega
    have hj_eq : ((tau : Int) % 16) = ((tau % 16 : Nat) : Int) := by omega
    rw [hq_eq, hj_eq] at hjen
    have hsz : 16 - ((tau % 16 : Nat) : Int) = ((16 - tau % 16 : Nat) : Int) := by omega
    rw [hsz] at hjen
    have h1 : (((16 - tau % 16 : Nat) : Int) * (((tau / 16 : Nat) : Int) * ((tau / 16 : Nat) : Int))) =
        (((16 - tau % 16) * (tau / 16 * (tau / 16)) : Nat) : Int) := by simp [Int.ofNat_mul]
    have h2 : (((tau % 16 : Nat) : Int) * ((((tau / 16 : Nat) : Int) + 1) * (((tau / 16 : Nat) : Int) + 1))) =
        (((tau % 16) * ((tau / 16 + 1) * (tau / 16 + 1)) : Nat) : Int) := by
      have : ((tau / 16 : Nat) : Int) + 1 = ((tau / 16 + 1 : Nat) : Int) := by omega
      rw [this]; simp [Int.ofNat_mul]
    rw [h1, h2] at hjen
    have hhalf : ((6 * a + 3 * b + 5 * c : Nat) : Int) / 2 = (((6 * a + 3 * b + 5 * c) / 2 : Nat) : Int) := by omega
    rw [hhalf] at hjen
    change (16 - tau % 16) * (tau / 16 * (tau / 16)) +
      tau % 16 * ((tau / 16 + 1) * (tau / 16 + 1)) + (6 * a + 3 * b + 5 * c) / 2 ≤ 196
    omega
  · have heq6 : r = 6 := Nat.eq_of_beq_eq_true hr
    simp only [heq6, if_true] at hmge hph_mod htau_le hjen
    rw [hph_eq] at hph_mod htau_le hjen
    have hmd := absDiff_mod_div (8 * a + 12 * b + 4 * c) 448 4 (by omega) hph_mod
    have hmd2 : ((((8 * a + 12 * b + 4 * c : Nat) : Int) - (448 : Nat)) / 4).natAbs =
        absDiff (8 * a + 12 * b + 4 * c) 448 / 4 := hmd.2
    have cm : Nat.ble 8 (Nat.add b c) = true := Nat.ble_eq.mpr hmge
    have cd : Nat.beq (Nat.mod (absDiff (Nat.add (Nat.add (Nat.mul 8 a) (Nat.mul 12 b)) (Nat.mul 4 c)) 448) 4) 0 = true :=
      Nat.beq_eq.mpr hmd.1
    have htau_nat : absDiff (8 * a + 12 * b + 4 * c) 448 / 4 ≤ 256 := by
      have : ((((8 * a + 12 * b + 4 * c : Nat) : Int) - (448 : Nat)) / 4).natAbs ≤ 256 := by omega
      rw [hmd2] at this; exact this
    have ctau : Nat.ble (Nat.div (absDiff (Nat.add (Nat.add (Nat.mul 8 a) (Nat.mul 12 b)) (Nat.mul 4 c)) 448) 4) 256 = true :=
      Nat.ble_eq.mpr htau_nat
    dsimp only
    rw [cm, cd, ctau]
    dsimp only
    apply Nat.ble_eq.mpr
    rw [hmd2] at hjen
    let tau := absDiff (8 * a + 12 * b + 4 * c) 448 / 4
    change (64 - (tau : Int) % 64) * (((tau : Int) / 64) * ((tau : Int) / 64)) +
      (tau : Int) % 64 * (((tau : Int) / 64 + 1) * ((tau : Int) / 64 + 1)) ≤
      196 - ((6 * a + 3 * b + 5 * c : Nat) : Int) / 2 at hjen
    have hq_eq : ((tau : Int) / 64) = ((tau / 64 : Nat) : Int) := by omega
    have hj_eq : ((tau : Int) % 64) = ((tau % 64 : Nat) : Int) := by omega
    rw [hq_eq, hj_eq] at hjen
    have hsz : 64 - ((tau % 64 : Nat) : Int) = ((64 - tau % 64 : Nat) : Int) := by omega
    rw [hsz] at hjen
    have h1 : (((64 - tau % 64 : Nat) : Int) * (((tau / 64 : Nat) : Int) * ((tau / 64 : Nat) : Int))) =
        (((64 - tau % 64) * (tau / 64 * (tau / 64)) : Nat) : Int) := by simp [Int.ofNat_mul]
    have h2 : (((tau % 64 : Nat) : Int) * ((((tau / 64 : Nat) : Int) + 1) * (((tau / 64 : Nat) : Int) + 1))) =
        (((tau % 64) * ((tau / 64 + 1) * (tau / 64 + 1)) : Nat) : Int) := by
      have : ((tau / 64 : Nat) : Int) + 1 = ((tau / 64 + 1 : Nat) : Int) := by omega
      rw [this]; simp [Int.ofNat_mul]
    rw [h1, h2] at hjen
    have hhalf : ((6 * a + 3 * b + 5 * c : Nat) : Int) / 2 = (((6 * a + 3 * b + 5 * c) / 2 : Nat) : Int) := by omega
    rw [hhalf] at hjen
    change (64 - tau % 64) * (tau / 64 * (tau / 64)) +
      tau % 64 * ((tau / 64 + 1) * (tau / 64 + 1)) + (6 * a + 3 * b + 5 * c) / 2 ≤ 196
    omega

private theorem mem_genSubLoopY_acc (a b c r x z : Nat) :
    ∀ (k : Nat) (acc : List Triple) (p : Triple), p ∈ acc → p ∈ genSubLoopY a b c r x z k acc
  | 0, _, _, h => h
  | k + 1, acc, p, h => by
    apply mem_genSubLoopY_acc a b c r x z k
    dsimp only
    cases Nat.ble _ b
    · exact h
    · cases tripleLeFast _ _ _ _ _ _
      · exact h
      · cases sixOKNat _ _ _ r
        · exact h
        · cases sixOKNat _ _ _ r
          · exact h
          · exact List.mem_cons_of_mem _ h

private theorem mem_genSubLoopZ_acc (a b c r x : Nat) :
    ∀ (k : Nat) (acc : List Triple) (p : Triple), p ∈ acc → p ∈ genSubLoopZ a b c r x k acc
  | 0, _, _, h => h
  | k + 1, acc, p, h =>
    mem_genSubLoopZ_acc a b c r x k _ p (mem_genSubLoopY_acc a b c r x k _ acc p h)

private theorem mem_genSubLoopX_acc (a b c r : Nat) :
    ∀ (k : Nat) (acc : List Triple) (p : Triple), p ∈ acc → p ∈ genSubLoopX a b c r k acc
  | 0, _, _, h => h
  | k + 1, acc, p, h =>
    mem_genSubLoopX_acc a b c r k _ p (mem_genSubLoopZ_acc a b c r k _ acc p h)

private theorem mem_genSubLoopY (a b c r x z y : Nat)
    (hy : y ≤ b) (hmod : y % 4 = (2 * x + z) % 4)
    (hle : tripleLeFast x y z (a - x) (b - y) (c - z) = true)
    (hs1 : sixOKNat x y z r = true) (hs2 : sixOKNat (a - x) (b - y) (c - z) r = true) :
    ∀ (k : Nat) (acc : List Triple), y / 4 < k → (x, y, z) ∈ genSubLoopY a b c r x z k acc
  | 0, _, hk => nomatch hk
  | k + 1, acc, hk => by
    unfold genSubLoopY
    if heq : y / 4 = k then
      have hy_eq : Nat.add (Nat.mod (Nat.add (Nat.mul 2 x) z) 4) (Nat.mul 4 k) = y := by
        change (2 * x + z) % 4 + 4 * k = y; omega
      apply mem_genSubLoopY_acc a b c r x z k
      dsimp only
      rw [hy_eq, Nat.ble_eq.mpr hy]
      change (x, y, z) ∈
        match tripleLeFast x y z (a - x) (b - y) (c - z) with
        | false => acc
        | true =>
          match sixOKNat x y z r with
          | false => acc
          | true =>
            match sixOKNat (a - x) (b - y) (c - z) r with
            | false => acc
            | true => (x, y, z) :: acc
      rw [hle, hs1, hs2]
      exact List.mem_cons_self _ _
    else
      exact mem_genSubLoopY a b c r x z y hy hmod hle hs1 hs2 k _ (by omega)

private theorem mem_genSubLoopZ (a b c r x z y : Nat)
    (hy : y ≤ b) (hmod : y % 4 = (2 * x + z) % 4)
    (hle : tripleLeFast x y z (a - x) (b - y) (c - z) = true)
    (hs1 : sixOKNat x y z r = true) (hs2 : sixOKNat (a - x) (b - y) (c - z) r = true) :
    ∀ (k : Nat) (acc : List Triple), z < k → (x, y, z) ∈ genSubLoopZ a b c r x k acc
  | 0, _, hk => nomatch hk
  | k + 1, acc, hk => by
    unfold genSubLoopZ
    if heq : z = k then
      subst heq
      apply mem_genSubLoopZ_acc a b c r x z
      exact mem_genSubLoopY a b c r x z y hy hmod hle hs1 hs2 _ acc (by change y / 4 < b / 4 + 1; omega)
    else
      exact mem_genSubLoopZ a b c r x z y hy hmod hle hs1 hs2 k _ (by omega)

private theorem mem_genSubLoopX (a b c r x z y : Nat)
    (hy : y ≤ b) (hz : z ≤ c) (hmod : y % 4 = (2 * x + z) % 4)
    (hle : tripleLeFast x y z (a - x) (b - y) (c - z) = true)
    (hs1 : sixOKNat x y z r = true) (hs2 : sixOKNat (a - x) (b - y) (c - z) r = true) :
    ∀ (k : Nat) (acc : List Triple), x < k → (x, y, z) ∈ genSubLoopX a b c r k acc
  | 0, _, hk => nomatch hk
  | k + 1, acc, hk => by
    unfold genSubLoopX
    if heq : x = k then
      subst heq
      apply mem_genSubLoopX_acc a b c r x
      exact mem_genSubLoopZ a b c r x z y hy hmod hle hs1 hs2 _ acc (by change z < c + 1; omega)
    else
      exact mem_genSubLoopX a b c r x z y hy hz hmod hle hs1 hs2 k _ (by omega)

theorem mem_genSubFast_of_mem_genSubtypes (n : Triple) (r : Nat) (p : Triple)
    (hp : p ∈ genSubtypes n r) : p ∈ genSubFast n r := by
  rcases n with ⟨a, b, c⟩
  unfold genSubtypes at hp
  rw [List.mem_flatMap] at hp; rcases hp with ⟨x, hx, hp⟩
  rw [List.mem_flatMap] at hp; rcases hp with ⟨z, hz, hp⟩
  rw [List.mem_filterMap] at hp; rcases hp with ⟨y, hy, hp⟩
  rw [List.mem_range] at hx hy hz
  dsimp only at hp
  cases hcond : (tripleLe (x, y, z) (a - x, b - y, c - z) && sixOK x y z r && sixOK (a - x) (b - y) (c - z) r)
  · rw [hcond] at hp; simp at hp
  · rw [hcond] at hp
    simp only [if_true, Option.some.injEq] at hp
    subst hp
    simp only [Bool.and_eq_true] at hcond
    obtain ⟨⟨hle, hs1⟩, hs2⟩ := hcond
    have hx_half : x ≤ a / 2 := by
      unfold tripleLe at hle; dsimp only at hle
      simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hle
      omega
    have hmass4 : (6 * x + 3 * y + 5 * z) % 4 = 0 := by
      unfold sixOK at hs1; dsimp only at hs1
      simp only [Bool.and_eq_true, beq_iff_eq] at hs1
      exact hs1.1.1.1.1.1.1
    have hmod : y % 4 = (2 * x + z) % 4 := by omega
    have hleF : tripleLeFast x y z (a - x) (b - y) (c - z) = true := by
      rw [tripleLeFast_eq (x, y, z) (a - x, b - y, c - z)]; exact hle
    exact mem_genSubLoopX a b c r x z y (by omega) (by omega) hmod hleF
      (sixOKNat_of_sixOK x y z r hs1) (sixOKNat_of_sixOK (a - x) (b - y) (c - z) r hs2)
      (Nat.add (Nat.div a 2) 1) [] (by change x < a / 2 + 1; omega)

private theorem inAllowedFast_eq (mask : Nat) (p : Triple) :
    inAllowedFast mask p.1 p.2.1 p.2.2 = inAllowedMask mask p := by
  unfold inAllowedFast inAllowedMask Balanced242Farkas.halfBitIdx Balanced242Pair.testBit
  cases h1 : Nat.ble p.1 63
  · have : ¬ (p.1 < 64) := by intro h; rw [Nat.ble_eq.mpr (by omega)] at h1; exact Bool.noConfusion h1
    simp [this]
  · have hp1 : p.1 < 64 := by have := Nat.ble_eq.mp h1; omega
    cases h2 : Nat.ble p.2.1 63
    · have : ¬ (p.2.1 < 64) := by intro h; rw [Nat.ble_eq.mpr (by omega)] at h2; exact Bool.noConfusion h2
      simp [hp1, this]
    · have hp2 : p.2.1 < 64 := by have := Nat.ble_eq.mp h2; omega
      cases h3 : Nat.ble p.2.2 63
      · have : ¬ (p.2.2 < 64) := by intro h; rw [Nat.ble_eq.mpr (by omega)] at h3; exact Bool.noConfusion h3
        simp [hp1, hp2, this]
      · have hp3 : p.2.2 < 64 := by have := Nat.ble_eq.mp h3; omega
        simp only [hp1, hp2, hp3, decide_true, Bool.true_and]
        change Nat.beq ((mask >>> ((p.1 * 64 + p.2.2) * 64 + p.2.1)) &&& 1) 1 =
          ((mask >>> ((p.1 * 64 + p.2.2) * 64 + p.2.1)) % 2 == 1)
        rw [Nat.and_one_is_mod]
        cases h : Nat.beq ((mask >>> ((p.1 * 64 + p.2.2) * 64 + p.2.1)) % 2) 1
        · symm; apply beq_false_of_ne; intro heq; rw [heq] at h; exact Bool.noConfusion h
        · symm; exact beq_iff_eq.mpr (Nat.eq_of_beq_eq_true h)

private theorem checkHiLoop_sound (hi : Triple) (mask : Nat) (p : Triple) (sL : Int) :
    ∀ (L : List (Triple × Int)), checkHiLoop hi mask p sL L = true →
      ∀ (v : Triple) (negSH : Int), (v, negSH) ∈ L →
        sL ≤ negSH ∨
        (!(inAllowedMask mask (p.1 + v.1, p.2.1 + v.2.1, p.2.2 + v.2.2) &&
          inAllowedMask mask (p.1 + (hi.1 - v.1), p.2.1 + (hi.2.1 - v.2.1), p.2.2 + (hi.2.2 - v.2.2)))) = true
  | [], _, _, _, hmem => nomatch hmem
  | (u, nu) :: rest, hok, v, negSH, hmem => by
    unfold checkHiLoop at hok
    rcases List.mem_cons.mp hmem with heq | htail
    · injection heq with hv hnu; subst hv; subst hnu
      cases hle : intLe sL negSH
      · rw [hle] at hok
        right
        cases ha1 : inAllowedFast mask (Nat.add p.1 v.1) (Nat.add p.2.1 v.2.1) (Nat.add p.2.2 v.2.2)
        · have heq1 : inAllowedMask mask (p.1 + v.1, p.2.1 + v.2.1, p.2.2 + v.2.2) = false := by
            rw [← inAllowedFast_eq mask (p.1 + v.1, p.2.1 + v.2.1, p.2.2 + v.2.2)]; exact ha1
          rw [heq1]; rfl
        · rw [ha1] at hok
          cases ha2 : inAllowedFast mask (Nat.add p.1 (Nat.sub hi.1 v.1))
              (Nat.add p.2.1 (Nat.sub hi.2.1 v.2.1)) (Nat.add p.2.2 (Nat.sub hi.2.2 v.2.2))
          · have heq2 : inAllowedMask mask (p.1 + (hi.1 - v.1), p.2.1 + (hi.2.1 - v.2.1), p.2.2 + (hi.2.2 - v.2.2)) = false := by
              rw [← inAllowedFast_eq mask (p.1 + (hi.1 - v.1), p.2.1 + (hi.2.1 - v.2.1), p.2.2 + (hi.2.2 - v.2.2))]; exact ha2
            rw [heq2, Bool.and_false]; rfl
          · rw [ha2] at hok; exact Bool.noConfusion hok
      · left; exact (intLe_iff sL negSH).mp hle
    · cases hle : intLe sL nu
      · rw [hle] at hok
        cases ha1 : inAllowedFast mask (Nat.add p.1 u.1) (Nat.add p.2.1 u.2.1) (Nat.add p.2.2 u.2.2)
        · rw [ha1] at hok; exact checkHiLoop_sound hi mask p sL rest hok v negSH htail
        · rw [ha1] at hok
          cases ha2 : inAllowedFast mask (Nat.add p.1 (Nat.sub hi.1 u.1))
              (Nat.add p.2.1 (Nat.sub hi.2.1 u.2.1)) (Nat.add p.2.2 (Nat.sub hi.2.2 u.2.2))
          · rw [ha2] at hok; exact checkHiLoop_sound hi mask p sL rest hok v negSH htail
          · rw [ha2] at hok; exact Bool.noConfusion hok
      · rw [hle] at hok; exact checkHiLoop_sound hi mask p sL rest hok v negSH htail

private theorem checkLoLoop_sound (lo hi : Triple) (mask : Nat) (W : CondWeights) (r : Nat)
    (minNegH : Int) (hiNeg : List (Triple × Int))
    (hmin : ∀ x, x ∈ hiNeg → minNegH ≤ x.2) :
    ∀ (L : List Triple), checkLoLoop lo hi mask W r minNegH hiNeg L = true →
      ∀ (p : Triple), p ∈ L → ∀ (v : Triple) (negSH : Int), (v, negSH) ∈ hiNeg →
        scoreLo lo W r p ≤ negSH ∨
        (!(inAllowedMask mask (p.1 + v.1, p.2.1 + v.2.1, p.2.2 + v.2.2) &&
          inAllowedMask mask (p.1 + (hi.1 - v.1), p.2.1 + (hi.2.1 - v.2.1), p.2.2 + (hi.2.2 - v.2.2)))) = true
  | [], _, _, hmem, _, _, _ => nomatch hmem
  | q :: rest, hok, p, hmem, v, negSH, hv => by
    unfold checkLoLoop at hok
    dsimp only at hok
    rcases List.mem_cons.mp hmem with rfl | htail
    · cases hle : intLe (scoreLo lo W r p) minNegH
      · rw [hle] at hok
        cases hhi : checkHiLoop hi mask p (scoreLo lo W r p) hiNeg
        · rw [hhi] at hok; exact Bool.noConfusion hok
        · exact checkHiLoop_sound hi mask p (scoreLo lo W r p) hiNeg hhi v negSH hv
      · left
        have h1 : scoreLo lo W r p ≤ minNegH := (intLe_iff _ _).mp hle
        have h2 : minNegH ≤ negSH := hmin (v, negSH) hv
        omega
    · cases hle : intLe (scoreLo lo W r q) minNegH
      · rw [hle] at hok
        cases hhi : checkHiLoop hi mask q (scoreLo lo W r q) hiNeg
        · rw [hhi] at hok; exact Bool.noConfusion hok
        · rw [hhi] at hok; exact checkLoLoop_sound lo hi mask W r minNegH hiNeg hmin rest hok p htail v negSH hv
      · rw [hle] at hok; exact checkLoLoop_sound lo hi mask W r minNegH hiNeg hmin rest hok p htail v negSH hv

theorem checkCondRankFast_of_fast2 (lo hi : Triple) (mask : Nat) (W : CondWeights) (r : Nat)
    (hok : checkCondRankFast2 lo hi mask W r = true) :
    checkCondRankFast lo hi mask W r = true := by
  have hpair : ∀ (p v : Triple), p ∈ genSubtypes lo r → v ∈ genSubtypes hi r →
      scoreLo lo W r p + scoreHi hi W v ≤ 0 ∨
      (!(inAllowedMask mask (p.1 + v.1, p.2.1 + v.2.1, p.2.2 + v.2.2) &&
        inAllowedMask mask (p.1 + (hi.1 - v.1), p.2.1 + (hi.2.1 - v.2.1), p.2.2 + (hi.2.2 - v.2.2)))) = true := by
    intro p v hp hv
    have hpF := mem_genSubFast_of_mem_genSubtypes lo r p hp
    have hvF := mem_genSubFast_of_mem_genSubtypes hi r v hv
    unfold checkCondRankFast2 at hok
    dsimp only at hok
    cases hhn : (genSubFast hi r).map (fun v => (v, -scoreHi hi W v)) with
    | nil =>
      have hm : (v, -scoreHi hi W v) ∈ (genSubFast hi r).map (fun v => (v, -scoreHi hi W v)) :=
        List.mem_map.mpr ⟨v, hvF, rfl⟩
      rw [hhn] at hm; exact nomatch hm
    | cons hd rest =>
      rw [hhn] at hok
      dsimp only at hok
      have hmin : ∀ x, x ∈ hd :: rest → listMinInt (rest.map Prod.snd) hd.2 ≤ x.2 := by
        intro x hx
        rcases List.mem_cons.mp hx with rfl | htl
        · exact listMinInt_le_base (rest.map Prod.snd) x.2
        · exact listMinInt_le_mem (rest.map Prod.snd) hd.2 x.2 (List.mem_map.mpr ⟨x, htl, rfl⟩)
      have hvm : (v, -scoreHi hi W v) ∈ hd :: rest := by
        rw [← hhn]; exact List.mem_map.mpr ⟨v, hvF, rfl⟩
      rcases checkLoLoop_sound lo hi mask W r _ (hd :: rest) hmin (genSubFast lo r) hok p hpF v (-scoreHi hi W v) hvm with hle | hforb
      · left; omega
      · right; exact hforb
  unfold checkCondRankFast
  dsimp only
  cases hhs : (genSubtypes hi r).map (fun v => (v, scoreHi hi W v)) with
  | nil => rfl
  | cons hd rest =>
    dsimp only
    rw [List.all_eq_true]
    intro p hp
    split
    · rfl
    · rw [List.all_eq_true]
      intro vs hvs
      have hmem_map : vs ∈ (genSubtypes hi r).map (fun v => (v, scoreHi hi W v)) := by rw [hhs]; exact hvs
      rw [List.mem_map] at hmem_map
      rcases hmem_map with ⟨v, hv, rfl⟩
      if hle : scoreLo lo W r p + scoreHi hi W v ≤ 0 then
        simp [hle]
      else
        simp only [decide_eq_false hle, Bool.false_eq_true, if_false]
        rcases hpair p v hp hv with hle' | hforb
        · exfalso; omega
        · exact hforb

theorem checkCondCertFast_of_fast2 (lo hi : Triple) (mask : Nat) (ws : List (Nat × Int))
    (hok : checkCondCertFast2 lo hi mask ws = true) :
    checkCondCertFast lo hi mask ws = true := by
  unfold checkCondCertFast2 at hok
  dsimp only at hok
  unfold checkCondCertFast
  dsimp only
  cases h1 : intLe 1 (condRhs lo hi (unpackCondWeights ws))
  · rw [h1] at hok; exact Bool.noConfusion hok
  · rw [h1] at hok
    have hpos : 0 < condRhs lo hi (unpackCondWeights ws) := by
      have := (intLe_iff 1 _).mp h1; omega
    cases h4 : checkCondRankFast2 lo hi mask (unpackCondWeights ws) 4
    · rw [h4] at hok; exact Bool.noConfusion hok
    · rw [h4] at hok
      simp only [decide_eq_true hpos, checkCondRankFast_of_fast2 lo hi mask _ 4 h4,
        checkCondRankFast_of_fast2 lo hi mask _ 6 hok, Bool.and_true]

theorem checkLayerWithMask_of_fast2 (a b c : Nat) (mask : Nat)
    (layer : List (Triple × List (Nat × Int)))
    (hok : checkLayerFast2 a b c mask layer = true) :
    checkLayerWithMask a b c mask layer = true := by
  unfold checkLayerFast2 at hok
  unfold checkLayerWithMask
  rw [List.all_eq_true] at hok ⊢
  intro e he
  exact checkCondCertFast_of_fast2 e.1 (a - e.1.1, b - e.1.2.1, c - e.1.2.2) mask e.2 (hok e he)

theorem checkLayerFast2_append (a b c : Nat) (mask : Nat)
    (L1 L2 : List (Triple × List (Nat × Int))) :
    checkLayerFast2 a b c mask (L1 ++ L2) =
      (checkLayerFast2 a b c mask L1 && checkLayerFast2 a b c mask L2) := by
  unfold checkLayerFast2
  exact List.all_append

end Balanced242FastCond

#print axioms Balanced242FastCond.checkLayerWithMask_of_fast2
#print axioms Balanced242FastCond.checkLayerFast2_append
