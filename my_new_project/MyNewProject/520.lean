import Mathlib.Data.Set.Basic

variable {α : Type*}
variable (a b : Set α)
open Set

example : (a ∪ b)ᶜ = aᶜ ∩ bᶜ  := by
  rw [inter_eq_compl_compl_union_compl]
  rw [compl_compl]
  rw [compl_compl]


example : 1 + 1 = 2 := by
  trivial

variable {n : Nat}

example : 259 + 18 = 277 := by
  trivial
