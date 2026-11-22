/- Kernel-checked anchor-pair chunk 4 for (94,12,25,25,8), 1 anchor per theorem for low peak RAM. -/
import Balanced242T94Data
import Balanced242FastCond

namespace Balanced242T94L12_c4
open Balanced242Farkas (Triple)
open Balanced242FastCond Balanced242T94Data

private def checkHead (a b c : Nat) (mask : Nat) : List (Triple × List (Nat × Int)) → Bool
  | [] => true
  | (lo, ws) :: _ => checkCondCertFast2 lo (Nat.sub a lo.1, Nat.sub b lo.2.1, Nat.sub c lo.2.2) mask ws

private theorem step_drop (a b c : Nat) (mask : Nat) (L : List (Triple × List (Nat × Int))) (k : Nat)
    (hh : checkHead a b c mask (L.drop k) = true)
    (ht : checkLayerFast2 a b c mask (L.drop (k + 1)) = true) :
    checkLayerFast2 a b c mask (L.drop k) = true := by
  cases h : L.drop k with
  | nil => rfl
  | cons hd tl =>
    have htl : L.drop (k + 1) = tl := by
      have : L.drop (k + 1) = (L.drop k).tail := by simp [List.tail_drop]
      rw [this, h]; rfl
    rw [h] at hh; rw [htl] at ht
    unfold checkHead at hh
    unfold checkLayerFast2 at ht ⊢
    simp only [List.all_cons, hh, ht, Bool.and_true]

private theorem h0 : checkHead 12 25 25 mask_94_12_25_25 (layer0_94_12_25_25_c4.drop 0) = true := by decide +kernel
private theorem h1 : checkHead 12 25 25 mask_94_12_25_25 (layer0_94_12_25_25_c4.drop 1) = true := by decide +kernel
private theorem h2 : checkHead 12 25 25 mask_94_12_25_25 (layer0_94_12_25_25_c4.drop 2) = true := by decide +kernel
private theorem h3 : checkHead 12 25 25 mask_94_12_25_25 (layer0_94_12_25_25_c4.drop 3) = true := by decide +kernel
private theorem h4 : checkHead 12 25 25 mask_94_12_25_25 (layer0_94_12_25_25_c4.drop 4) = true := by decide +kernel
private theorem h5 : checkHead 12 25 25 mask_94_12_25_25 (layer0_94_12_25_25_c4.drop 5) = true := by decide +kernel
private theorem h6 : checkHead 12 25 25 mask_94_12_25_25 (layer0_94_12_25_25_c4.drop 6) = true := by decide +kernel
private theorem h7 : checkHead 12 25 25 mask_94_12_25_25 (layer0_94_12_25_25_c4.drop 7) = true := by decide +kernel
private theorem h8 : checkHead 12 25 25 mask_94_12_25_25 (layer0_94_12_25_25_c4.drop 8) = true := by decide +kernel
private theorem h9 : checkHead 12 25 25 mask_94_12_25_25 (layer0_94_12_25_25_c4.drop 9) = true := by decide +kernel
private theorem h10 : checkHead 12 25 25 mask_94_12_25_25 (layer0_94_12_25_25_c4.drop 10) = true := by decide +kernel
private theorem h11 : checkHead 12 25 25 mask_94_12_25_25 (layer0_94_12_25_25_c4.drop 11) = true := by decide +kernel
private theorem h12 : checkHead 12 25 25 mask_94_12_25_25 (layer0_94_12_25_25_c4.drop 12) = true := by decide +kernel
private theorem h13 : checkHead 12 25 25 mask_94_12_25_25 (layer0_94_12_25_25_c4.drop 13) = true := by decide +kernel
private theorem h14 : checkHead 12 25 25 mask_94_12_25_25 (layer0_94_12_25_25_c4.drop 14) = true := by decide +kernel

theorem chunk_ok : checkLayerFast2 12 25 25 mask_94_12_25_25 layer0_94_12_25_25_c4 = true :=
  (step_drop _ _ _ _ _ 0 h0 (step_drop _ _ _ _ _ 1 h1 (step_drop _ _ _ _ _ 2 h2 (step_drop _ _ _ _ _ 3 h3 (step_drop _ _ _ _ _ 4 h4 (step_drop _ _ _ _ _ 5 h5 (step_drop _ _ _ _ _ 6 h6 (step_drop _ _ _ _ _ 7 h7 (step_drop _ _ _ _ _ 8 h8 (step_drop _ _ _ _ _ 9 h9 (step_drop _ _ _ _ _ 10 h10 (step_drop _ _ _ _ _ 11 h11 (step_drop _ _ _ _ _ 12 h12 (step_drop _ _ _ _ _ 13 h13 (step_drop _ _ _ _ _ 14 h14 rfl)))))))))))))))

end Balanced242T94L12_c4
