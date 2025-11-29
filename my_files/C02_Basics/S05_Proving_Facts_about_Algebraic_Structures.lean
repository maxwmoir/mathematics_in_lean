import MIL.Common
import Mathlib.Topology.MetricSpace.Basic

section
variable {α : Type*} [PartialOrder α]
variable (x y z : α)

#check x ≤ y
#check (le_refl x : x ≤ x)
#check (le_trans : x ≤ y → y ≤ z → x ≤ z)
#check (le_antisymm : x ≤ y → y ≤ x → x = y)


#check x < y
#check (lt_irrefl x : ¬ (x < x))
#check (lt_trans : x < y → y < z → x < z)
#check (lt_of_le_of_lt : x ≤ y → y < z → x < z)
#check (lt_of_lt_of_le : x < y → y ≤ z → x < z)

example : x < y ↔ x ≤ y ∧ x ≠ y :=
  lt_iff_le_and_ne

end

section
variable {α : Type*} [Lattice α]
variable (x y z : α)

#check x ⊓ y
#check (inf_le_left : x ⊓ y ≤ x)
#check (inf_le_right : x ⊓ y ≤ y)
#check (le_inf : z ≤ x → z ≤ y → z ≤ x ⊓ y)

#check x ⊔ y
#check (le_sup_left : x ≤ x ⊔ y)
#check (le_sup_right : y ≤ x ⊔ y)
#check (sup_le : x ≤ z → y ≤ z → x ⊔ y ≤ z)

theorem my_inf_comm : x ⊓ y = y ⊓ x := by
  apply le_antisymm
  repeat
    apply le_inf
    apply inf_le_right
    apply inf_le_left

theorem my_inf_assoc : x ⊓ y ⊓ z = x ⊓ (y ⊓ z) := by
  apply le_antisymm
  · apply le_inf
    · rw [my_inf_comm ]
      trans (x ⊓ y)
      apply inf_le_right
      apply inf_le_left

    · apply le_inf
      · rw [my_inf_comm]
        trans (x ⊓ y)
        apply inf_le_right
        apply inf_le_right

      · rw [my_inf_comm]
        apply inf_le_left

  · show x ⊓ (y ⊓ z) ≤ x ⊓ y ⊓ z
    apply le_inf
    apply le_inf
    · apply inf_le_left
    · trans (y ⊓ z)
      apply inf_le_right
      apply inf_le_left
    · trans (y ⊓ z)
      apply inf_le_right
      apply inf_le_right


example : x ⊔ y = y ⊔ x := by
  apply le_antisymm
  repeat
    apply sup_le
    apply le_sup_right
    apply le_sup_left

example : x ⊔ y ⊔ z = x ⊔ (y ⊔ z) := by
  apply le_antisymm

  · show x ⊔ y ⊔ z ≤ x ⊔ (y ⊔ z)
    apply sup_le
    apply sup_le
    · apply le_sup_left
    · trans (y ⊔ z)
      apply le_sup_left
      apply le_sup_right
    · trans (y ⊔ z)
      apply le_sup_right
      apply le_sup_right

  · show x ⊔ (y ⊔ z) ≤ x ⊔ y ⊔ z
    apply sup_le
    rw [sup_comm]
    trans (x ⊔ y)
    apply le_sup_left
    apply le_sup_right

    apply sup_le
    rw [sup_comm]
    trans (x ⊔ y)
    apply le_sup_right
    apply le_sup_right

    rw [sup_comm]
    apply le_sup_left

theorem absorb1 : x ⊓ (x ⊔ y) = x := by
  apply le_antisymm
  · apply inf_le_left

  · apply le_inf
    apply le_refl
    apply le_sup_left

theorem absorb2 : x ⊔ x ⊓ y = x := by
  apply le_antisymm

  · show x ⊔ x ⊓ y ≤ x
    apply sup_le
    apply le_refl
    apply inf_le_left

  · show x ≤ x ⊔ x ⊓ y
    apply le_sup_left

end

section
variable {α : Type*} [DistribLattice α]
variable (x y z : α)

#check (inf_sup_left x y z : x ⊓ (y ⊔ z) = x ⊓ y ⊔ x ⊓ z)
#check (inf_sup_right x y z : (x ⊔ y) ⊓ z = x ⊓ z ⊔ y ⊓ z)
#check (sup_inf_left x y z : x ⊔ y ⊓ z = (x ⊔ y) ⊓ (x ⊔ z))
#check (sup_inf_right x y z : x ⊓ y ⊔ z = (x ⊔ z) ⊓ (y ⊔ z))
end

section
variable {α : Type*} [Lattice α]
variable (a b c : α)

example (h : ∀ x y z : α, x ⊓ (y ⊔ z) = x ⊓ y ⊔ x ⊓ z) : a ⊔ b ⊓ c = (a ⊔ b) ⊓ (a ⊔ c) := by
  rw [h, inf_comm (a ⊔ b), inf_sup_self, inf_comm (a ⊔ b), h, ←sup_assoc]
  nth_rewrite 2 [inf_comm]
  rw [sup_inf_self, inf_comm c]


example (h : ∀ x y z : α, x ⊔ y ⊓ z = (x ⊔ y) ⊓ (x ⊔ z)) : a ⊓ (b ⊔ c) = a ⊓ b ⊔ a ⊓ c := by


  rw [h, ←sup_comm a, sup_inf_self]
  nth_rewrite 2 [sup_comm]
  rw [h, ←inf_assoc, sup_comm c, inf_sup_self, sup_comm c]
end

section
variable {R : Type*} [Ring R] [PartialOrder R] [IsStrictOrderedRing R]
variable (a b c : R)

#check (add_le_add_left : a ≤ b → ∀ c, c + a ≤ c + b)
#check (mul_pos : 0 < a → 0 < b → 0 < a * b)

#check (mul_nonneg : 0 ≤ a → 0 ≤ b → 0 ≤ a * b)

example (h : a ≤ b) : 0 ≤ b - a := by
  sorry

example (h: 0 ≤ b - a) : a ≤ b := by
  sorry

example (h : a ≤ b) (h' : 0 ≤ c) : a * c ≤ b * c := by
  sorry

end

section
variable {X : Type*} [MetricSpace X]
variable (x y z : X)

#check (dist_self x : dist x x = 0)
#check (dist_comm x y : dist x y = dist y x)
#check (dist_triangle x y z : dist x z ≤ dist x y + dist y z)

example (x y : X) : 0 ≤ dist x y := by
  sorry

end
