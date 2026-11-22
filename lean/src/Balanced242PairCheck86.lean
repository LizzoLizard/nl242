import Balanced242Pair

namespace Balanced242Pair

set_option maxRecDepth 200000

theorem row_86_0 : rowCheck 86 0 = true := by decide +kernel
theorem row_86_1 : rowCheck 86 1 = true := by decide +kernel
theorem row_86_2 : rowCheck 86 2 = true := by decide +kernel
theorem row_86_3 : rowCheck 86 3 = true := by decide +kernel
theorem row_86_4 : rowCheck 86 4 = true := by decide +kernel
theorem row_86_5 : rowCheck 86 5 = true := by decide +kernel
theorem row_86_6 : rowCheck 86 6 = true := by decide +kernel
theorem row_86_7 : rowCheck 86 7 = true := by decide +kernel
theorem row_86_8 : rowCheck 86 8 = true := by decide +kernel
theorem row_86_9 : rowCheck 86 9 = true := by decide +kernel
theorem row_86_10 : rowCheck 86 10 = true := by decide +kernel
theorem row_86_11 : rowCheck 86 11 = true := by decide +kernel
theorem row_86_12 : rowCheck 86 12 = true := by decide +kernel
theorem row_86_13 : rowCheck 86 13 = true := by decide +kernel
theorem row_86_14 : rowCheck 86 14 = true := by decide +kernel
theorem row_86_15 : rowCheck 86 15 = true := by decide +kernel
theorem row_86_16 : rowCheck 86 16 = true := by decide +kernel
theorem row_86_17 : rowCheck 86 17 = true := by decide +kernel
theorem row_86_18 : rowCheck 86 18 = true := by decide +kernel
theorem row_86_19 : rowCheck 86 19 = true := by decide +kernel
theorem row_86_20 : rowCheck 86 20 = true := by decide +kernel
theorem row_86_21 : rowCheck 86 21 = true := by decide +kernel
theorem row_86_22 : rowCheck 86 22 = true := by decide +kernel
theorem row_86_23 : rowCheck 86 23 = true := by decide +kernel
theorem row_86_24 : rowCheck 86 24 = true := by decide +kernel
theorem row_86_25 : rowCheck 86 25 = true := by decide +kernel
theorem row_86_26 : rowCheck 86 26 = true := by decide +kernel
theorem row_86_27 : rowCheck 86 27 = true := by decide +kernel
theorem row_86_28 : rowCheck 86 28 = true := by decide +kernel
theorem row_86_29 : rowCheck 86 29 = true := by decide +kernel
theorem row_86_30 : rowCheck 86 30 = true := by decide +kernel
theorem row_86_31 : rowCheck 86 31 = true := by decide +kernel
theorem row_86_32 : rowCheck 86 32 = true := by decide +kernel
theorem row_86_33 : rowCheck 86 33 = true := by decide +kernel
theorem row_86_34 : rowCheck 86 34 = true := by decide +kernel

theorem rows_86 : ∀ a < 35, rowCheck 86 a = true := by
  intro a ha
  match a, ha with
  | 0, _ => exact row_86_0
  | 1, _ => exact row_86_1
  | 2, _ => exact row_86_2
  | 3, _ => exact row_86_3
  | 4, _ => exact row_86_4
  | 5, _ => exact row_86_5
  | 6, _ => exact row_86_6
  | 7, _ => exact row_86_7
  | 8, _ => exact row_86_8
  | 9, _ => exact row_86_9
  | 10, _ => exact row_86_10
  | 11, _ => exact row_86_11
  | 12, _ => exact row_86_12
  | 13, _ => exact row_86_13
  | 14, _ => exact row_86_14
  | 15, _ => exact row_86_15
  | 16, _ => exact row_86_16
  | 17, _ => exact row_86_17
  | 18, _ => exact row_86_18
  | 19, _ => exact row_86_19
  | 20, _ => exact row_86_20
  | 21, _ => exact row_86_21
  | 22, _ => exact row_86_22
  | 23, _ => exact row_86_23
  | 24, _ => exact row_86_24
  | 25, _ => exact row_86_25
  | 26, _ => exact row_86_26
  | 27, _ => exact row_86_27
  | 28, _ => exact row_86_28
  | 29, _ => exact row_86_29
  | 30, _ => exact row_86_30
  | 31, _ => exact row_86_31
  | 32, _ => exact row_86_32
  | 33, _ => exact row_86_33
  | 34, _ => exact row_86_34
  | n + 35, h => exact absurd h (by omega)

/-- No global high profile and phase rank at agreement count 86 admits an assignment of
    admissible hyperplane splits satisfying the moment identities. -/
theorem no_assignment_86 (a b c r : Nat) (hT : 6 * a + 3 * b + 5 * c = 8 * 86 - 480)
    (hr : r ∈ ranks 86 (a + c)) (x y z : Nat → Nat) (drop : Nat → Bool)
    (hadm : ∀ w < 255, admissible a b c r (x w) (y w) (z w) (drop w) = true)
    (hmom : vsum 255 (fun w => row a b c (x w) (y w) (z w) (drop w)) = rhs a b c r) : False :=
  no_assignment 86 a b c r rows_86 hT hr x y z drop hadm hmom

end Balanced242Pair

#print axioms Balanced242Pair.no_assignment_86
