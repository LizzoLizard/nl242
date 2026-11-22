import Balanced242Pair

namespace Balanced242Pair

set_option maxRecDepth 200000

theorem row_92_0 : rowCheck 92 0 = true := by decide +kernel
theorem row_92_1 : rowCheck 92 1 = true := by decide +kernel
theorem row_92_2 : rowCheck 92 2 = true := by decide +kernel
theorem row_92_3 : rowCheck 92 3 = true := by decide +kernel
theorem row_92_4 : rowCheck 92 4 = true := by decide +kernel
theorem row_92_5 : rowCheck 92 5 = true := by decide +kernel
theorem row_92_6 : rowCheck 92 6 = true := by decide +kernel
theorem row_92_7 : rowCheck 92 7 = true := by decide +kernel
theorem row_92_8 : rowCheck 92 8 = true := by decide +kernel
theorem row_92_9 : rowCheck 92 9 = true := by decide +kernel
theorem row_92_10 : rowCheck 92 10 = true := by decide +kernel
theorem row_92_11 : rowCheck 92 11 = true := by decide +kernel
theorem row_92_12 : rowCheck 92 12 = true := by decide +kernel
theorem row_92_13 : rowCheck 92 13 = true := by decide +kernel
theorem row_92_14 : rowCheck 92 14 = true := by decide +kernel
theorem row_92_15 : rowCheck 92 15 = true := by decide +kernel
theorem row_92_16 : rowCheck 92 16 = true := by decide +kernel
theorem row_92_17 : rowCheck 92 17 = true := by decide +kernel
theorem row_92_18 : rowCheck 92 18 = true := by decide +kernel
theorem row_92_19 : rowCheck 92 19 = true := by decide +kernel
theorem row_92_20 : rowCheck 92 20 = true := by decide +kernel
theorem row_92_21 : rowCheck 92 21 = true := by decide +kernel
theorem row_92_22 : rowCheck 92 22 = true := by decide +kernel
theorem row_92_23 : rowCheck 92 23 = true := by decide +kernel
theorem row_92_24 : rowCheck 92 24 = true := by decide +kernel
theorem row_92_25 : rowCheck 92 25 = true := by decide +kernel
theorem row_92_26 : rowCheck 92 26 = true := by decide +kernel
theorem row_92_27 : rowCheck 92 27 = true := by decide +kernel
theorem row_92_28 : rowCheck 92 28 = true := by decide +kernel
theorem row_92_29 : rowCheck 92 29 = true := by decide +kernel
theorem row_92_30 : rowCheck 92 30 = true := by decide +kernel
theorem row_92_31 : rowCheck 92 31 = true := by decide +kernel
theorem row_92_32 : rowCheck 92 32 = true := by decide +kernel
theorem row_92_33 : rowCheck 92 33 = true := by decide +kernel
theorem row_92_34 : rowCheck 92 34 = true := by decide +kernel
theorem row_92_35 : rowCheck 92 35 = true := by decide +kernel
theorem row_92_36 : rowCheck 92 36 = true := by decide +kernel
theorem row_92_37 : rowCheck 92 37 = true := by decide +kernel
theorem row_92_38 : rowCheck 92 38 = true := by decide +kernel
theorem row_92_39 : rowCheck 92 39 = true := by decide +kernel
theorem row_92_40 : rowCheck 92 40 = true := by decide +kernel
theorem row_92_41 : rowCheck 92 41 = true := by decide +kernel
theorem row_92_42 : rowCheck 92 42 = true := by decide +kernel

theorem rows_92 : ∀ a < 43, rowCheck 92 a = true := by
  intro a ha
  match a, ha with
  | 0, _ => exact row_92_0
  | 1, _ => exact row_92_1
  | 2, _ => exact row_92_2
  | 3, _ => exact row_92_3
  | 4, _ => exact row_92_4
  | 5, _ => exact row_92_5
  | 6, _ => exact row_92_6
  | 7, _ => exact row_92_7
  | 8, _ => exact row_92_8
  | 9, _ => exact row_92_9
  | 10, _ => exact row_92_10
  | 11, _ => exact row_92_11
  | 12, _ => exact row_92_12
  | 13, _ => exact row_92_13
  | 14, _ => exact row_92_14
  | 15, _ => exact row_92_15
  | 16, _ => exact row_92_16
  | 17, _ => exact row_92_17
  | 18, _ => exact row_92_18
  | 19, _ => exact row_92_19
  | 20, _ => exact row_92_20
  | 21, _ => exact row_92_21
  | 22, _ => exact row_92_22
  | 23, _ => exact row_92_23
  | 24, _ => exact row_92_24
  | 25, _ => exact row_92_25
  | 26, _ => exact row_92_26
  | 27, _ => exact row_92_27
  | 28, _ => exact row_92_28
  | 29, _ => exact row_92_29
  | 30, _ => exact row_92_30
  | 31, _ => exact row_92_31
  | 32, _ => exact row_92_32
  | 33, _ => exact row_92_33
  | 34, _ => exact row_92_34
  | 35, _ => exact row_92_35
  | 36, _ => exact row_92_36
  | 37, _ => exact row_92_37
  | 38, _ => exact row_92_38
  | 39, _ => exact row_92_39
  | 40, _ => exact row_92_40
  | 41, _ => exact row_92_41
  | 42, _ => exact row_92_42
  | n + 43, h => exact absurd h (by omega)

/-- No global high profile and phase rank at agreement count 92 admits an assignment of
    admissible hyperplane splits satisfying the moment identities. -/
theorem no_assignment_92 (a b c r : Nat) (hT : 6 * a + 3 * b + 5 * c = 8 * 92 - 480)
    (hr : r ∈ ranks 92 (a + c)) (x y z : Nat → Nat) (drop : Nat → Bool)
    (hadm : ∀ w < 255, admissible a b c r (x w) (y w) (z w) (drop w) = true)
    (hmom : vsum 255 (fun w => row a b c (x w) (y w) (z w) (drop w)) = rhs a b c r) : False :=
  no_assignment 92 a b c r rows_92 hT hr x y z drop hadm hmom

end Balanced242Pair

#print axioms Balanced242Pair.no_assignment_92
