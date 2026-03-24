/-!
  A small Lean 4 model of "exotic material" quantities without mathlib.
  It defines what "large amount" means and proves basic theorems about
  preserving largeness when combining material.
-/

structure ExoticMaterial where
  amount : Nat
deriving Repr

def largeThreshold : Nat := 1000000

def IsLarge (m : ExoticMaterial) : Prop :=
  largeThreshold ≤ m.amount

def combine (a b : ExoticMaterial) : ExoticMaterial :=
  { amount := a.amount + b.amount }

theorem combine_amount (a b : ExoticMaterial) :
    (combine a b).amount = a.amount + b.amount := rfl

theorem large_of_ge (m : ExoticMaterial) (h : largeThreshold ≤ m.amount) :
    IsLarge m := h

theorem right_le_add (a b : Nat) : b ≤ a + b := by
  simpa [Nat.add_comm] using Nat.le_add_left b a

theorem combine_large_right (a b : ExoticMaterial) (hb : IsLarge b) :
    IsLarge (combine a b) := by
  unfold IsLarge at hb ⊢
  exact Nat.le_trans hb (right_le_add a.amount b.amount)

theorem combine_large_left (a b : ExoticMaterial) (ha : IsLarge a) :
    IsLarge (combine a b) := by
  unfold IsLarge at ha ⊢
  have h : a.amount ≤ a.amount + b.amount := by
    simpa [Nat.add_comm] using right_le_add b.amount a.amount
  simpa [combine] using Nat.le_trans ha h

theorem combine_two_large (a b : ExoticMaterial)
    (_ha : IsLarge a) (hb : IsLarge b) :
    IsLarge (combine a b) := by
  -- One large input is already enough, so we can use either side.
  exact combine_large_right a b hb
