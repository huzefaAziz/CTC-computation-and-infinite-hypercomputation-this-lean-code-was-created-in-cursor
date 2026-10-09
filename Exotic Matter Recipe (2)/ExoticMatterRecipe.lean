import Mathlib

/-!
# 🧪 Recipe for Exotic Matter (Casimir-vacuum edition)

**Exotic matter** (in general relativity) is matter that violates the *null energy
condition* (NEC): along some light ray, `ρ + p < 0`.  Traversable wormholes and warp
drives need it, and Nature serves a tiny portion in the **Casimir effect**: between two
ideal parallel plates a distance `a` apart, the vacuum has energy density

    ρ = − π² ħ c / (720 a⁴)  < 0.

Below: pantry → ingredients → method → serve.  Lean *proves* the dish is exotic.

Run it at https://live.lean-lang.org (the "Mathlib" project) — nothing to install.
-/

noncomputable section

namespace ExoticMatter

/-! ## 1. The pantry: stress–energy and the energy conditions -/

/-- Static diagonal stress–energy tensor in an orthonormal frame:
energy density `rho` and principal pressures `px py pz` (SI units, per m³). -/
structure StressEnergy where
  rho : ℝ
  px  : ℝ
  py  : ℝ
  pz  : ℝ

/-- Null energy condition: `ρ + pᵢ ≥ 0` in every principal direction. -/
def NEC (T : StressEnergy) : Prop :=
  0 ≤ T.rho + T.px ∧ 0 ≤ T.rho + T.py ∧ 0 ≤ T.rho + T.pz

/-- Weak energy condition: non-negative energy density, plus the NEC. -/
def WEC (T : StressEnergy) : Prop := 0 ≤ T.rho ∧ NEC T

/-- Strong energy condition: the NEC, plus `ρ + px + py + pz ≥ 0`. -/
def SEC (T : StressEnergy) : Prop := NEC T ∧ 0 ≤ T.rho + T.px + T.py + T.pz

/-- Dominant energy condition: energy density dominates every pressure, `ρ ≥ |pᵢ|`. -/
def DEC (T : StressEnergy) : Prop := |T.px| ≤ T.rho ∧ |T.py| ≤ T.rho ∧ |T.pz| ≤ T.rho

/-- **Exotic matter**: stress–energy that violates the null energy condition. -/
def Exotic (T : StressEnergy) : Prop := ¬ NEC T

/-- A perfect fluid: energy density `rho`, isotropic pressure `p`. -/
def fluid (rho p : ℝ) : StressEnergy := ⟨rho, p, p, p⟩

/-- Sanity check: ordinary matter (dust `p = 0`, radiation `p = ρ/3`, stiff matter
`p = ρ`, …) is **not** exotic. -/
theorem ordinary_not_exotic {rho p : ℝ} (h₀ : 0 ≤ p) (h₁ : p ≤ rho) :
    ¬ Exotic (fluid rho p) := by
  intro h
  have hsum : 0 ≤ rho + p := by linarith
  exact h ⟨hsum, hsum, hsum⟩

/-- Plain empty vacuum: nothing in, nothing out. -/
def plainVacuum : StressEnergy := fluid 0 0

theorem plainVacuum_not_exotic : ¬ Exotic plainVacuum :=
  ordinary_not_exotic (rho := 0) (p := 0) le_rfl le_rfl

/-! ## 2. The ingredients -/

/-- Everything you need from the cupboard. -/
structure Ingredients where
  hbar : ℝ   -- reduced Planck constant, J·s
  c    : ℝ   -- speed of light, m/s
  gap  : ℝ   -- distance between the plates, m
  hbar_pos : 0 < hbar
  c_pos    : 0 < c
  gap_pos  : 0 < gap

/-- A well-stocked lab: real SI constants, plates one micrometre apart. -/
def pantry : Ingredients where
  hbar := 1054571817 / 10 ^ 43   -- 1.054571817 × 10⁻³⁴ J·s
  c    := 299792458              -- m/s
  gap  := 1 / 10 ^ 6             -- 1 µm
  hbar_pos := by norm_num
  c_pos    := by norm_num
  gap_pos  := by norm_num

/-! ## 3. The dish: the Casimir vacuum -/

/-- Casimir energy density between ideal parallel plates: `ρ = −π² ħ c / (720 a⁴)`. -/
def casimirRho (I : Ingredients) : ℝ :=
  -(Real.pi ^ 2 * I.hbar * I.c / (720 * I.gap ^ 4))

/-- Casimir stress–energy `T = ρ · diag(1, −1, −1, 3)` (traceless; `z` ⟂ plates). -/
def casimirTensor (I : Ingredients) : StressEnergy where
  rho := casimirRho I
  px  := -casimirRho I
  py  := -casimirRho I
  pz  := 3 * casimirRho I

/-- The Casimir vacuum has negative energy density. -/
theorem casimirRho_neg (I : Ingredients) : casimirRho I < 0 := by
  have h1 := I.hbar_pos
  have h2 := I.c_pos
  have h3 := I.gap_pos
  have h : 0 < Real.pi ^ 2 * I.hbar * I.c / (720 * I.gap ^ 4) := by positivity
  unfold casimirRho
  linarith

/-- The Casimir vacuum violates the NEC (along `z`): it is exotic matter. -/
theorem casimir_exotic (I : Ingredients) : Exotic (casimirTensor I) := by
  intro h
  obtain ⟨_, _, hz⟩ := h
  have hz' : 0 ≤ casimirRho I + 3 * casimirRho I := hz
  have hneg := casimirRho_neg I
  linarith

/-- It is just as bad for the other energy conditions. -/
theorem casimir_not_wec (I : Ingredients) : ¬ WEC (casimirTensor I) :=
  fun h => casimir_exotic I h.2

theorem casimir_not_sec (I : Ingredients) : ¬ SEC (casimirTensor I) :=
  fun h => casimir_exotic I h.1

theorem casimir_not_dec (I : Ingredients) : ¬ DEC (casimirTensor I) := by
  intro h
  obtain ⟨h1, _, _⟩ := h
  have hneg : (casimirTensor I).rho < 0 := casimirRho_neg I
  have habs := abs_nonneg (casimirTensor I).px
  linarith

/-! ## 4. The method -/

/-- State of the laboratory. -/
structure Kitchen where
  evacuated : Bool
  cold      : Bool
  plates    : Bool
  deriving Repr

/-- The three steps.  Order matters! -/
inductive Step
  | pumpDown       -- evacuate the chamber
  | coolToGround   -- cryo-cool towards T → 0 (only works once evacuated)
  | insertPlates   -- two parallel ideal conductors (only if evacuated *and* cold)

def Step.run : Step → Kitchen → Kitchen
  | .pumpDown,     k => { k with evacuated := true }
  | .coolToGround, k => { k with cold := k.evacuated }
  | .insertPlates, k => { k with plates := k.evacuated && k.cold }

/-- Follow the steps, starting from an empty lab. -/
def bake (steps : List Step) : Kitchen :=
  steps.foldl (fun k s => s.run k) ⟨false, false, false⟩

/-- The lab is ready when every condition holds. -/
def Kitchen.ready (k : Kitchen) : Bool := k.evacuated && k.cold && k.plates

/-- 📜 The recipe. -/
def recipe : List Step := [.pumpDown, .coolToGround, .insertPlates]

/-- The oven: a ready lab yields the Casimir vacuum, anything else yields plain vacuum. -/
def serve (steps : List Step) (I : Ingredients) : StressEnergy :=
  if (bake steps).ready then casimirTensor I else plainVacuum

theorem recipe_ready : (bake recipe).ready = true := by decide

theorem serve_recipe (I : Ingredients) : serve recipe I = casimirTensor I := by
  simp [serve, recipe_ready]

/-- 🍽️ Bon appétit: following the recipe yields exotic matter, with any ingredients. -/
theorem recipe_yields_exotic_matter (I : Ingredients) : Exotic (serve recipe I) := by
  rw [serve_recipe]
  exact casimir_exotic I

/-- No shortcuts: insert the plates before pumping down and you just get plain vacuum. -/
theorem wrong_order_gives_vacuum (I : Ingredients) :
    serve [.insertPlates, .pumpDown, .coolToGround] I = plainVacuum := by
  have h : (bake [Step.insertPlates, Step.pumpDown, Step.coolToGround]).ready = false := by
    decide
  simp [serve, h]

/-! ## 5. Serving suggestion: hold a wormhole open -/

/-- For a Morris–Thorne throat of radius `r₀` with shape function `b` (units `G = c = 1`),
the Einstein equations give, at the throat, `ρ = b'(r₀)/(8π r₀²)` and `p_r = −1/(8π r₀²)`.
The *flare-out* condition `b'(r₀) < 1` then forces `ρ + p_r < 0`: NEC violation, i.e. exotic
matter.  (Point the Casimir plates' normal along the radial direction.) -/
theorem throat_needs_exotic_matter {r₀ b' : ℝ} (hr : 0 < r₀) (hflare : b' < 1) :
    b' / (8 * Real.pi * r₀ ^ 2) + (-1) / (8 * Real.pi * r₀ ^ 2) < 0 := by
  have hD : 0 < 8 * Real.pi * r₀ ^ 2 := by positivity
  have h : b' / (8 * Real.pi * r₀ ^ 2) + (-1) / (8 * Real.pi * r₀ ^ 2)
      = (b' - 1) / (8 * Real.pi * r₀ ^ 2) := by ring
  rw [h]
  exact div_neg_of_neg_of_pos (by linarith) hD

/-! ## 6. Reality check

With a 1 µm gap the Casimir vacuum is only about −433 µJ/m³.  Holding open a 1 m wormhole
throat (`b' = 0`) would need `ρ + p_r = −c⁴ / (8π G r₀²) ≈ −4.8 × 10⁴² J/m³`, roughly
45 orders of magnitude more.  Great recipe for a physics lab; not yet for a starship. 🚀 -/

/-- Casimir yield in µJ/m³ (plain `Float`, so `#eval` can run it); `gap` in metres. -/
def casimirYield (gap : Float) : Float :=
  1.0e6 * (-(3.141592653589793 * 3.141592653589793 * 1.054571817e-34 * 299792458.0)
    / (720.0 * gap * gap * gap * gap))

#eval casimirYield 1.0e-6   -- plates 1 µm apart: about -433.375257 (µJ/m³)
#eval bake recipe           -- { evacuated := true, cold := true, plates := true }
#print axioms recipe_yields_exotic_matter   -- [propext, Classical.choice, Quot.sound]

end ExoticMatter

end
