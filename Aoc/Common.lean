import Batteries
import Mathlib.Data.Nat.Log
import Mathlib.Data.Int.GCD
import Mathlib.Logic.Function.Iterate

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

namespace Batteries.RBMap

variable {α β}

def ofListWith (l : List (α × β))
    (combine : β → β → β) (cmp : α → α → Ordering) : RBMap α β cmp :=
  l.map (fun (a, b) ↦ RBMap.single a b)
    |>.foldl (RBMap.mergeWith fun _ ↦ combine) RBMap.empty

def group (l : List (α × β)) (cmp : α → α → Ordering)
    (cmp' : β → β → Ordering) : RBMap α (RBSet β cmp') cmp :=
  l.map (fun (a, b) ↦ (a, RBSet.single b)) |> (ofListWith · RBSet.union cmp)

end RBMap
