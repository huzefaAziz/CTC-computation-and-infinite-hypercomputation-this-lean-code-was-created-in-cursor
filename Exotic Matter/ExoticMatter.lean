/-!
# Exotic matter, in Lean 4

A diagonal ("Hawking–Ellis type I") stress–energy tensor, seen in a local orthonormal
frame, is fixed by an energy density `ρ` and three principal pressures `p₁ p₂ p₃`.
Ordinary matter obeys the classical *energy conditions*; exotic matter breaks at least one.

    DEC ──► WEC ──► NEC ◄── SEC        (an arrow means "implies")

Scalars are `Int` (multiples of some fixed unit), so this file needs only core Lean 4.
Every proof is plain ordered arithmetic, so it ports to `ℝ` with Mathlib by swapping
`omega` for `linarith`.
-/

/-- Stress–energy of a diagonal fluid: energy density `ρ` and principal pressures `pᵢ`. -/
structure Fluid where
  ρ  : Int
  p₁ : Int
  p₂ : Int
  p₃ : Int
  deriving Repr, DecidableEq

namespace Fluid

/-- Null energy condition: `ρ + pᵢ ≥ 0`. -/
def NEC (T : Fluid) : Prop := 0 ≤ T.ρ + T.p₁ ∧ 0 ≤ T.ρ + T.p₂ ∧ 0 ≤ T.ρ + T.p₃

/-- Weak energy condition: every observer measures `ρ ≥ 0`. -/
def WEC (T : Fluid) : Prop := 0 ≤ T.ρ ∧ T.NEC

/-- Strong energy condition: gravity attracts, `ρ + Σpᵢ ≥ 0`. -/
def SEC (T : Fluid) : Prop := 0 ≤ T.ρ + T.p₁ + T.p₂ + T.p₃ ∧ T.NEC

/-- Dominant energy condition: `ρ ≥ |pᵢ|`, so energy never flows faster than light. -/
def DEC (T : Fluid) : Prop :=
  (-T.ρ ≤ T.p₁ ∧ T.p₁ ≤ T.ρ) ∧ (-T.ρ ≤ T.p₂ ∧ T.p₂ ≤ T.ρ) ∧ (-T.ρ ≤ T.p₃ ∧ T.p₃ ≤ T.ρ)

/-- Ordinary matter obeys every energy condition. -/
def Ordinary (T : Fluid) : Prop := T.NEC ∧ T.WEC ∧ T.SEC ∧ T.DEC

/-- **Exotic matter** breaks at least one energy condition. -/
def Exotic (T : Fluid) : Prop := ¬ T.Ordinary

/-- The really exotic stuff (traversable wormholes, warp drives): breaks the null condition. -/
def NullExotic (T : Fluid) : Prop := ¬ T.NEC

instance (T : Fluid) : Decidable T.NEC := inferInstanceAs (Decidable (_ ∧ _ ∧ _))
instance (T : Fluid) : Decidable T.WEC := inferInstanceAs (Decidable (_ ∧ _))
instance (T : Fluid) : Decidable T.SEC := inferInstanceAs (Decidable (_ ∧ _))
instance (T : Fluid) : Decidable T.DEC := inferInstanceAs (Decidable ((_ ∧ _) ∧ (_ ∧ _) ∧ (_ ∧ _)))
instance (T : Fluid) : Decidable T.Ordinary := inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))
instance (T : Fluid) : Decidable T.Exotic := inferInstanceAs (Decidable (¬ _))
instance (T : Fluid) : Decidable T.NullExotic := inferInstanceAs (Decidable (¬ _))

/-! ## The hierarchy of conditions -/

theorem WEC.nec {T : Fluid} (h : T.WEC) : T.NEC := h.2
theorem SEC.nec {T : Fluid} (h : T.SEC) : T.NEC := h.2

theorem DEC.wec {T : Fluid} (h : T.DEC) : T.WEC := by
  unfold DEC WEC NEC at *; omega

/-- Ordinary matter is exactly matter obeying the strong and dominant conditions. -/
theorem ordinary_iff (T : Fluid) : T.Ordinary ↔ T.SEC ∧ T.DEC := by
  unfold Ordinary SEC DEC WEC NEC; omega

/-- Breaking the null condition breaks the weak one too. -/
theorem NullExotic.not_wec {T : Fluid} (h : T.NullExotic) : ¬ T.WEC := fun hw => h hw.nec

theorem NullExotic.exotic {T : Fluid} (h : T.NullExotic) : T.Exotic := fun ho => h ho.1

/-- Negative energy density is exotic. -/
theorem exotic_of_neg_energy {T : Fluid} (h : T.ρ < 0) : T.Exotic := by
  unfold Exotic Ordinary NEC WEC SEC DEC; omega

/-! ## A zoo of fluids -/

/-- Pressureless dust. -/
def dust : Fluid := ⟨1, 0, 0, 0⟩
/-- Radiation, `p = ρ/3`. -/
def radiation : Fluid := ⟨3, 1, 1, 1⟩
/-- A cosmological constant `Λ`: `p = -ρ`. Positive `Λ` is dark energy. -/
def cosmoConst (Λ : Int) : Fluid := ⟨Λ, -Λ, -Λ, -Λ⟩
/-- Anti-de Sitter vacuum: negative cosmological constant. -/
def adsVacuum : Fluid := cosmoConst (-1)
/-- Phantom energy, `p = wρ` with `w = -3/2 < -1`. -/
def phantom : Fluid := ⟨2, -3, -3, -3⟩
/-- Casimir vacuum between parallel plates: `ε · diag(-1, 1, 1, -3)` with `ε = π²ħc / (720 a⁴)`. -/
def casimir (ε : Int) : Fluid := ⟨-ε, ε, ε, -3 * ε⟩
/-- Morris–Thorne wormhole throat (`b' = 1/2`): radial tension `4` beats density `2`. -/
def wormholeThroat : Fluid := ⟨2, -4, 1, 1⟩

/-- Dark energy is only *mildly* exotic: it never breaks NEC… -/
theorem cosmoConst_nec (Λ : Int) : (cosmoConst Λ).NEC := by
  simp only [cosmoConst, NEC]; omega

/-- …it just stops gravity from attracting. -/
theorem cosmoConst_not_sec {Λ : Int} (h : 0 < Λ) : ¬ (cosmoConst Λ).SEC := by
  simp only [cosmoConst, SEC, NEC]; omega

/-- The Casimir vacuum breaks the null condition for *every* plate separation. -/
theorem casimir_nullExotic {ε : Int} (h : 0 < ε) : (casimir ε).NullExotic := by
  simp only [casimir, NullExotic, NEC]; omega

/-- Morris–Thorne flare-out: radial tension `τ` exceeding the density `ρ` breaks NEC. -/
theorem throat_nullExotic {ρ τ pt : Int} (h : ρ < τ) : (Fluid.mk ρ (-τ) pt pt).NullExotic := by
  simp only [NullExotic, NEC]; omega

example : dust.Ordinary := by decide
example : radiation.Ordinary := by decide
example : (cosmoConst 1).NEC ∧ (cosmoConst 1).WEC ∧ (cosmoConst 1).DEC := by decide
example : adsVacuum.NEC ∧ ¬ adsVacuum.WEC := by decide
example : phantom.NullExotic := by decide
example : wormholeThroat.NullExotic := by decide

/-- First (strongest) energy condition a fluid violates. -/
def classify (T : Fluid) : String :=
  if ¬ T.NEC then "exotic: breaks NEC (wormhole / warp-drive grade)"
  else if ¬ T.WEC then "exotic: negative energy density"
  else if ¬ T.SEC then "exotic: gravitationally repulsive"
  else if ¬ T.DEC then "exotic: superluminal energy flow"
  else "ordinary"

end Fluid

/-! ## Exotic matter as a type -/

open Fluid

/-- Exotic matter: a fluid bundled with a proof that it breaks an energy condition. -/
abbrev ExoticMatter := {T : Fluid // T.Exotic}

/-- Here is one: a Casimir vacuum, certified exotic. -/
def casimirVacuum : ExoticMatter := ⟨casimir 1, by decide⟩

/-- And a phantom fluid. -/
def phantomFluid : ExoticMatter := ⟨phantom, by decide⟩

/-- Exotic matter in the sci-fi sense: Newton's `m·a = F` with `m < 0` accelerates *against* the force. -/
theorem negative_mass_recoils {m a F : Int} (hm : m < 0) (h : m * a = F) (hF : 0 < F) : a < 0 := by
  by_cases ha : a < 0
  · exact ha
  · have h1 : 0 ≤ (-m) * a := Int.mul_nonneg (by omega) (by omega)
    rw [Int.neg_mul] at h1
    omega

#eval do
  for (name, T) in [("dust", dust), ("radiation", radiation), ("dark energy", cosmoConst 1),
      ("AdS vacuum", adsVacuum), ("phantom energy", phantom), ("Casimir vacuum", casimir 1),
      ("wormhole throat", wormholeThroat)] do
    IO.println s!"{name}: {T.classify}"
