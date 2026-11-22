import Balanced242Pair

namespace Balanced242Pair

set_option maxRecDepth 200000

theorem row_90_0 : rowCheck 90 0 = true := by decide +kernel
theorem row_90_1 : rowCheck 90 1 = true := by decide +kernel
theorem row_90_2 : rowCheck 90 2 = true := by decide +kernel
theorem row_90_3 : rowCheck 90 3 = true := by decide +kernel
theorem row_90_4 : rowCheck 90 4 = true := by decide +kernel
theorem row_90_5 : rowCheck 90 5 = true := by decide +kernel
theorem row_90_6 : rowCheck 90 6 = true := by decide +kernel
theorem row_90_7 : rowCheck 90 7 = true := by decide +kernel
theorem row_90_8 : rowCheck 90 8 = true := by decide +kernel
theorem row_90_9 : rowCheck 90 9 = true := by decide +kernel
theorem row_90_10 : rowCheck 90 10 = true := by decide +kernel
theorem row_90_11 : rowCheck 90 11 = true := by decide +kernel
theorem row_90_12 : rowCheck 90 12 = true := by decide +kernel
theorem row_90_13 : rowCheck 90 13 = true := by decide +kernel
theorem row_90_14 : rowCheck 90 14 = true := by decide +kernel
theorem row_90_15 : rowCheck 90 15 = true := by decide +kernel
theorem row_90_16 : rowCheck 90 16 = true := by decide +kernel
theorem row_90_17 : rowCheck 90 17 = true := by decide +kernel
theorem row_90_18 : rowCheck 90 18 = true := by decide +kernel
theorem row_90_19 : rowCheck 90 19 = true := by decide +kernel
theorem row_90_20 : rowCheck 90 20 = true := by decide +kernel
theorem row_90_21 : rowCheck 90 21 = true := by decide +kernel
theorem row_90_22 : rowCheck 90 22 = true := by decide +kernel
theorem row_90_23 : rowCheck 90 23 = true := by decide +kernel
theorem row_90_24 : rowCheck 90 24 = true := by decide +kernel
theorem row_90_25 : rowCheck 90 25 = true := by decide +kernel
theorem row_90_26 : rowCheck 90 26 = true := by decide +kernel
theorem row_90_27 : rowCheck 90 27 = true := by decide +kernel
theorem row_90_28 : rowCheck 90 28 = true := by decide +kernel
theorem row_90_29 : rowCheck 90 29 = true := by decide +kernel
theorem row_90_30 : rowCheck 90 30 = true := by decide +kernel
theorem row_90_31 : rowCheck 90 31 = true := by decide +kernel
theorem row_90_32 : rowCheck 90 32 = true := by decide +kernel
theorem row_90_33 : rowCheck 90 33 = true := by decide +kernel
theorem row_90_34 : rowCheck 90 34 = true := by decide +kernel
theorem row_90_35 : rowCheck 90 35 = true := by decide +kernel
theorem row_90_36 : rowCheck 90 36 = true := by decide +kernel
theorem row_90_37 : rowCheck 90 37 = true := by decide +kernel
theorem row_90_38 : rowCheck 90 38 = true := by decide +kernel
theorem row_90_39 : rowCheck 90 39 = true := by decide +kernel
theorem row_90_40 : rowCheck 90 40 = true := by decide +kernel

theorem rows_90 : ∀ a < 41, rowCheck 90 a = true := by
  intro a ha
  match a, ha with
  | 0, _ => exact row_90_0
  | 1, _ => exact row_90_1
  | 2, _ => exact row_90_2
  | 3, _ => exact row_90_3
  | 4, _ => exact row_90_4
  | 5, _ => exact row_90_5
  | 6, _ => exact row_90_6
  | 7, _ => exact row_90_7
  | 8, _ => exact row_90_8
  | 9, _ => exact row_90_9
  | 10, _ => exact row_90_10
  | 11, _ => exact row_90_11
  | 12, _ => exact row_90_12
  | 13, _ => exact row_90_13
  | 14, _ => exact row_90_14
  | 15, _ => exact row_90_15
  | 16, _ => exact row_90_16
  | 17, _ => exact row_90_17
  | 18, _ => exact row_90_18
  | 19, _ => exact row_90_19
  | 20, _ => exact row_90_20
  | 21, _ => exact row_90_21
  | 22, _ => exact row_90_22
  | 23, _ => exact row_90_23
  | 24, _ => exact row_90_24
  | 25, _ => exact row_90_25
  | 26, _ => exact row_90_26
  | 27, _ => exact row_90_27
  | 28, _ => exact row_90_28
  | 29, _ => exact row_90_29
  | 30, _ => exact row_90_30
  | 31, _ => exact row_90_31
  | 32, _ => exact row_90_32
  | 33, _ => exact row_90_33
  | 34, _ => exact row_90_34
  | 35, _ => exact row_90_35
  | 36, _ => exact row_90_36
  | 37, _ => exact row_90_37
  | 38, _ => exact row_90_38
  | 39, _ => exact row_90_39
  | 40, _ => exact row_90_40
  | n + 41, h => exact absurd h (by omega)

/-- No global high profile and phase rank at agreement count 90 admits an assignment of
    admissible hyperplane splits satisfying the moment identities. -/
theorem no_assignment_90 (a b c r : Nat) (hT : 6 * a + 3 * b + 5 * c = 8 * 90 - 480)
    (hr : r ∈ ranks 90 (a + c)) (x y z : Nat → Nat) (drop : Nat → Bool)
    (hadm : ∀ w < 255, admissible a b c r (x w) (y w) (z w) (drop w) = true)
    (hmom : vsum 255 (fun w => row a b c (x w) (y w) (z w) (drop w)) = rhs a b c r) : False :=
  no_assignment 90 a b c r rows_90 hT hr x y z drop hadm hmom

end Balanced242Pair

#print axioms Balanced242Pair.no_assignment_90
