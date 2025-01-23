import Mathlib.Data.Set.Basic

variable {α : Type*}
variable (a b : Set α)
open Set

example : (a ∪ b)ᶜ = aᶜ ∩ bᶜ  := by
  rw [inter_eq_compl_compl_union_compl]
  rw [compl_compl]
  rw [compl_compl]

