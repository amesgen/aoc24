import Batteries

abbrev ℕ := Nat
abbrev ℤ := Int

abbrev RBMap α [Ord α] β := Batteries.RBMap α β compare
abbrev RBSet α [Ord α] := Batteries.RBSet α compare

instance {α β} [Ord α] [Ord β] : Ord (α × β) where
  compare := compareLex (compareOn (·.1)) (compareOn (·.2))

instance {α β γ} [HAdd α β γ] : HAdd (α × α) (β × β) (γ × γ) where
  hAdd := fun (a₀, b₀) (a₁, b₁) ↦ (a₀ + a₁, b₀ + b₁)

instance {α β γ} [HSub α β γ] : HSub (α × α) (β × β) (γ × γ) where
  hSub := fun (a₀, b₀) (a₁, b₁) ↦ (a₀ - a₁, b₀ - b₁)

namespace List

variable {α β}

def sortOn [Ord β] (f : α → β) (as : List α) : List α :=
  let cmp := compareLex (compareOn (·.2.2)) (compareOn (·.1))
  as.map (fun a ↦ (a, f a)) |>.enum
    |> (Batteries.RBSet.ofList · cmp) |>.toList.map (·.2.1)

def sort [Ord α] (as : List α) : List α := as.sortOn id

end List
