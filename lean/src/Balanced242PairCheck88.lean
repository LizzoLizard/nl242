import Balanced242Pair

namespace Balanced242Pair

set_option maxRecDepth 200000

theorem row_88_0 : rowCheck 88 0 = true := by decide +kernel
theorem row_88_1 : rowCheck 88 1 = true := by decide +kernel
theorem row_88_2 : rowCheck 88 2 = true := by decide +kernel
theorem row_88_3 : rowCheck 88 3 = true := by decide +kernel
theorem row_88_4 : rowCheck 88 4 = true := by decide +kernel
theorem row_88_5 : rowCheck 88 5 = true := by decide +kernel
theorem row_88_6 : rowCheck 88 6 = true := by decide +kernel
theorem row_88_7 : rowCheck 88 7 = true := by decide +kernel
theorem row_88_8 : rowCheck 88 8 = true := by decide +kernel
theorem row_88_9 : rowCheck 88 9 = true := by decide +kernel
theorem row_88_10 : rowCheck 88 10 = true := by decide +kernel
theorem row_88_11 : rowCheck 88 11 = true := by decide +kernel
theorem row_88_12 : rowCheck 88 12 = true := by decide +kernel
theorem row_88_13 : rowCheck 88 13 = true := by decide +kernel
theorem row_88_14 : rowCheck 88 14 = true := by decide +kernel
theorem row_88_15 : rowCheck 88 15 = true := by decide +kernel
theorem row_88_16 : rowCheck 88 16 = true := by decide +kernel
theorem row_88_17 : rowCheck 88 17 = true := by decide +kernel
theorem row_88_18 : rowCheck 88 18 = true := by decide +kernel
theorem row_88_19 : rowCheck 88 19 = true := by decide +kernel
theorem row_88_20 : rowCheck 88 20 = true := by decide +kernel
theorem row_88_21 : rowCheck 88 21 = true := by decide +kernel
theorem row_88_22 : rowCheck 88 22 = true := by decide +kernel
theorem row_88_23 : rowCheck 88 23 = true := by decide +kernel
theorem row_88_24 : rowCheck 88 24 = true := by decide +kernel
theorem row_88_25 : rowCheck 88 25 = true := by decide +kernel
theorem row_88_26 : rowCheck 88 26 = true := by decide +kernel
theorem row_88_27 : rowCheck 88 27 = true := by decide +kernel
theorem row_88_28 : rowCheck 88 28 = true := by decide +kernel
theorem row_88_29 : rowCheck 88 29 = true := by decide +kernel
theorem row_88_30 : rowCheck 88 30 = true := by decide +kernel
theorem row_88_31 : rowCheck 88 31 = true := by decide +kernel
theorem row_88_32 : rowCheck 88 32 = true := by decide +kernel
theorem row_88_33 : rowCheck 88 33 = true := by decide +kernel
theorem row_88_34 : rowCheck 88 34 = true := by decide +kernel
theorem row_88_35 : rowCheck 88 35 = true := by decide +kernel
theorem row_88_36 : rowCheck 88 36 = true := by decide +kernel
theorem row_88_37 : rowCheck 88 37 = true := by decide +kernel

theorem rows_88 : ∀ a < 38, rowCheck 88 a = true := by
  intro a ha
  match a, ha with
  | 0, _ => exact row_88_0
  | 1, _ => exact row_88_1
  | 2, _ => exact row_88_2
  | 3, _ => exact row_88_3
  | 4, _ => exact row_88_4
  | 5, _ => exact row_88_5
  | 6, _ => exact row_88_6
  | 7, _ => exact row_88_7
  | 8, _ => exact row_88_8
  | 9, _ => exact row_88_9
  | 10, _ => exact row_88_10
  | 11, _ => exact row_88_11
  | 12, _ => exact row_88_12
  | 13, _ => exact row_88_13
  | 14, _ => exact row_88_14
  | 15, _ => exact row_88_15
  | 16, _ => exact row_88_16
  | 17, _ => exact row_88_17
  | 18, _ => exact row_88_18
  | 19, _ => exact row_88_19
  | 20, _ => exact row_88_20
  | 21, _ => exact row_88_21
  | 22, _ => exact row_88_22
  | 23, _ => exact row_88_23
  | 24, _ => exact row_88_24
  | 25, _ => exact row_88_25
  | 26, _ => exact row_88_26
  | 27, _ => exact row_88_27
  | 28, _ => exact row_88_28
  | 29, _ => exact row_88_29
  | 30, _ => exact row_88_30
  | 31, _ => exact row_88_31
  | 32, _ => exact row_88_32
  | 33, _ => exact row_88_33
  | 34, _ => exact row_88_34
  | 35, _ => exact row_88_35
  | 36, _ => exact row_88_36
  | 37, _ => exact row_88_37
  | n + 38, h => exact absurd h (by omega)

/-- No global high profile and phase rank at agreement count 88 admits an assignment of
    admissible hyperplane splits satisfying the moment identities. -/
theorem no_assignment_88 (a b c r : Nat) (hT : 6 * a + 3 * b + 5 * c = 8 * 88 - 480)
    (hr : r ∈ ranks 88 (a + c)) (x y z : Nat → Nat) (drop : Nat → Bool)
    (hadm : ∀ w < 255, admissible a b c r (x w) (y w) (z w) (drop w) = true)
    (hmom : vsum 255 (fun w => row a b c (x w) (y w) (z w) (drop w)) = rhs a b c r) : False :=
  no_assignment 88 a b c r rows_88 hT hr x y z drop hadm hmom

end Balanced242Pair

#print axioms Balanced242Pair.no_assignment_88
