import MIL.Common
import Mathlib.Data.Real.Basic

namespace C02S04

section
variable (a b c d : ℝ)

#check (min_le_left a b : min a b ≤ a)
#check (min_le_right a b : min a b ≤ b)
#check (le_min : c ≤ a → c ≤ b → c ≤ min a b)

example : min a b = min b a := by
  apply le_antisymm
  · show min a b ≤ min b a
    apply le_min
    · apply min_le_right
    apply min_le_left
  · show min b a ≤ min a b
    apply le_min
    · apply min_le_right
    apply min_le_left

example : min a b = min b a := by
  have h : ∀ x y : ℝ, min x y ≤ min y x := by
    intro x y
    apply le_min
    apply min_le_right
    apply min_le_left
  apply le_antisymm
  apply h
  apply h

example : min a b = min b a := by
  apply le_antisymm
  repeat
    apply le_min
    apply min_le_right
    apply min_le_left

example : max a b = max b a := by
  apply le_antisymm
  repeat
    apply max_le
    apply le_max_right
    apply le_max_left

theorem min_aux₀ : min a (min b c) ≤ a := by
    apply min_le_left

theorem min_aux₁ : min a (min b c) ≤ b := by
  apply min_le_of_right_le
  apply min_le_left

theorem min_aux₂ : min a (min b c) ≤ c := by
  apply min_le_of_right_le
  apply min_le_right

theorem min_assoc₁ : min (min a b) c = min a (min b c) := by
  apply le_antisymm
  · show min (min a b) c ≤ min a (min b c)
    rw [min_comm]
    apply le_min
    · apply min_aux₁
    · apply le_min
      · apply min_aux₂
      · apply min_aux₀
  · show min a (min b c) ≤ min (min a b) c
    apply le_min
    · apply le_min
      · apply min_aux₀
      · apply min_aux₁
    · apply min_aux₂

theorem aux : min a b + c ≤ min (a + c) (b + c) := by
  apply le_min
  · show min a b + c ≤ a + c
    apply add_le_add
    apply min_le_left
    apply le_refl

  · show min a b + c ≤ b + c
    apply add_le_add
    apply min_le_right
    apply le_refl


example : min a b + c = min (a + c) (b + c) := by
  apply le_antisymm
  · apply aux

  show min (a + c) (b + c) ≤ min a b + c
  rw [←sub_add_cancel (min (a + c) (b + c)) c]
  apply add_le_add_right

  apply le_min
  · nth_rewrite 2 [←sub_add_cancel a c]
    nth_rewrite 3 [←add_comm c]
    rw [add_sub c]
    apply sub_le_sub_right
    rw [add_comm]
    apply min_le_left
  · nth_rewrite 2 [←sub_add_cancel b c]
    nth_rewrite 3 [←add_comm c]
    rw [add_sub c]
    apply sub_le_sub_right
    rw [add_comm b]
    apply min_le_right

#check (abs_add : ∀ a b : ℝ, |a + b| ≤ |a| + |b|)

example : |a| - |b| ≤ |a - b| := by
  nth_rewrite 1 [←sub_add_cancel a b]
  rw [←sub_add_cancel |a - b| |b|, ←add_comm |b|, add_sub]
  apply sub_le_sub_right
  rw [add_comm |b|]
  apply abs_add


end

section
variable (w x y z : ℕ)

example (h₀ : x ∣ y) (h₁ : y ∣ z) : x ∣ z :=
  dvd_trans h₀ h₁

example : x ∣ y * x * z := by
  apply dvd_mul_of_dvd_left
  apply dvd_mul_left

example : x ∣ x ^ 2 := by
  apply dvd_mul_left

example (h : x ∣ w) : x ∣ y * (x * z) + x ^ 2 + w ^ 2 := by
  rw [←mul_assoc, mul_comm y, mul_assoc, pow_two, pow_two, ←mul_add, add_comm]
  apply dvd_add
  · apply dvd_trans h
    apply dvd_mul_left
  · apply dvd_mul_of_dvd_left
    apply dvd_refl

end

section
variable (m n : ℕ)

#check (Nat.gcd_zero_right n : Nat.gcd n 0 = n)
#check (Nat.gcd_zero_left n : Nat.gcd 0 n = n)
#check (Nat.lcm_zero_right n : Nat.lcm n 0 = 0)
#check (Nat.lcm_zero_left n : Nat.lcm 0 n = 0)

example : Nat.gcd m n = Nat.gcd n m := by
  apply Nat.dvd_antisymm
  repeat
    apply Nat.dvd_gcd
    apply gcd_dvd_right
    apply gcd_dvd_left
end
