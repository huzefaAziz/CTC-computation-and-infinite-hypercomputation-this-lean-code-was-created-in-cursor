import Mathlib

/-!
# From exotic matter to a closed timelike curve (toy formalisation)

Units `G = c = 1`, signature `(−,+,+,+)`.  The recipe is the Morris–Thorne–Yurtsever
(1988) wormhole time machine:

1. Holding a wormhole throat open needs "flare-out" matter, which violates the
   null energy condition (NEC).                          → `flare_out_violates_NEC`
2. Drag one mouth around at speed `v`.  Twin-paradox time dilation makes the two
   mouths' clocks drift apart by `Δ = τ (1 − √(1 − v²))`, as large as you like.
                                                         → `exists_offset_gt`
3. Leave mouth A, travel outside to mouth B (distance `L`, so the trip takes
   `T > L`), enter B and come out of A `Δ` earlier.  This closes into a timelike
   loop exactly when `L < Δ`.                            → `hasCTC_iff`

`exotic_wormhole_time_machine` bundles 1–3.

**What this is not:** a derivation from Einstein's equations.  The throat formulas are
the standard Einstein-tensor components of the Morris–Thorne metric
`ds² = −e^{2Φ(r)} dt² + dr²/(1 − b(r)/r) + r² dΩ²`, entered as definitions, and the
wormhole is modelled by identifying two worldlines of 1+1 Minkowski space.

Run it inside a Lake project that depends on Mathlib:  `lake env lean ExoticCTC.lean`
-/

noncomputable section

namespace ExoticCTC

/-! ## 1. Exotic matter: flare-out forces a null-energy-condition violation -/

/-- Energy density of a Morris–Thorne wormhole at radius `r` (the `tt` Einstein equation):
`ρ = b′ / (8π r²)`.  Here `db` stands for `b′(r)`, the derivative of the shape function. -/
def energyDensity (r db : ℝ) : ℝ := db / (8 * Real.pi * r ^ 2)

/-- Radial pressure (the `rr` Einstein equation):
`p_r = (−b/r + 2 (r − b) Φ′) / (8π r²)`.  Here `b = b(r)` and `dPhi = Φ′(r)`. -/
def radialPressure (r b dPhi : ℝ) : ℝ :=
  (-(b / r) + 2 * (r - b) * dPhi) / (8 * Real.pi * r ^ 2)

/-- Null energy condition along the radial null direction: `T_{μν} kᵘ kᵛ = ρ + p_r ≥ 0`. -/
def RadialNEC (ρ p : ℝ) : Prop := 0 ≤ ρ + p

/-- At the throat `r = b = r₀` the two equations combine to
`ρ + p_r = −(1 − b′) / (8π r₀²)`; the redshift function `Φ` drops out. -/
theorem NEC_sum_at_throat {r₀ db dPhi : ℝ} (hr : 0 < r₀) :
    energyDensity r₀ db + radialPressure r₀ r₀ dPhi = -((1 - db) / (8 * Real.pi * r₀ ^ 2)) := by
  unfold energyDensity radialPressure
  rw [← add_div, div_self hr.ne', sub_self]
  ring

/-- **Exotic matter.**  If the throat `r₀ > 0` flares out (`b′(r₀) < 1`), the matter there
violates the null energy condition, whatever the redshift function does. -/
theorem flare_out_violates_NEC {r₀ db dPhi : ℝ} (hr : 0 < r₀) (hflare : db < 1) :
    ¬ RadialNEC (energyDensity r₀ db) (radialPressure r₀ r₀ dPhi) := by
  intro hNEC
  unfold RadialNEC at hNEC
  rw [NEC_sum_at_throat hr] at hNEC
  have hden : 0 < 8 * Real.pi * r₀ ^ 2 :=
    mul_pos (mul_pos (by norm_num) Real.pi_pos) (pow_pos hr 2)
  have hpos : 0 < (1 - db) / (8 * Real.pi * r₀ ^ 2) := div_pos (sub_pos.mpr hflare) hden
  linarith

/-! ## 2. Twin-paradox clock offset between the mouths -/

/-- Offset between the mouths' clocks after one mouth has flown at speed `v` (c = 1) for
coordinate time `τ` and come back: `Δ = τ (1 − √(1 − v²))`.  (Idealised: acceleration phases
and gravitational redshift are ignored.) -/
def clockOffset (v τ : ℝ) : ℝ := τ * (1 - Real.sqrt (1 - v ^ 2))

theorem sqrt_one_sub_sq_lt_one {v : ℝ} (hv0 : 0 < v) (hv1 : v < 1) :
    Real.sqrt (1 - v ^ 2) < 1 := by
  have h0 : 0 ≤ 1 - v ^ 2 := by nlinarith [mul_pos hv0 (sub_pos.mpr hv1)]
  have h1 : 1 - v ^ 2 < 1 := by nlinarith [mul_pos hv0 hv0]
  calc Real.sqrt (1 - v ^ 2) < Real.sqrt 1 := Real.sqrt_lt_sqrt h0 h1
    _ = 1 := Real.sqrt_one

/-- However large the target `L`, flying a mouth at any speed `0 < v < 1` for long enough
pushes the clock offset past it. -/
theorem exists_offset_gt {v : ℝ} (hv0 : 0 < v) (hv1 : v < 1) (L : ℝ) :
    ∃ τ : ℝ, 0 < τ ∧ L < clockOffset v τ := by
  have hc : 0 < 1 - Real.sqrt (1 - v ^ 2) := sub_pos.mpr (sqrt_one_sub_sq_lt_one hv0 hv1)
  refine ⟨(|L| + 1) / (1 - Real.sqrt (1 - v ^ 2)), div_pos (by positivity) hc, ?_⟩
  have h : (|L| + 1) / (1 - Real.sqrt (1 - v ^ 2)) * (1 - Real.sqrt (1 - v ^ 2)) = |L| + 1 := by
    rw [div_mul_eq_mul_div, mul_div_assoc, div_self hc.ne', mul_one]
  unfold clockOffset
  rw [h]
  linarith [le_abs_self L]

/-! ## 3. The loop: an outside leg plus a wormhole jump -/

/-- Events of 1+1 Minkowski space, `(t, x)` with `c = 1`. -/
abbrev Event := ℝ × ℝ

/-- `q` lies in the chronological future of `p`: a straight future-directed timelike
segment joins them, i.e. `|Δx| < Δt`. -/
def Chrono (p q : Event) : Prop := |q.2 - p.2| < q.1 - p.1

/-- Mouth A sits at `x = 0`, mouth B at `x = L`.  Because of the clock offset `Δ`, whoever
enters B at outside time `t` leaves A at outside time `t − Δ`. -/
def throughB2A (Δ : ℝ) (p : Event) : Event := (p.1 - Δ, 0)

/-- A closed timelike loop exists: start at mouth A at time `t₀`, fly outside to mouth B
(`q.2 = L`) along a timelike segment, jump through the wormhole, and land exactly where
and when you started. -/
def HasCTC (L Δ : ℝ) : Prop :=
  ∃ (t₀ : ℝ) (q : Event), q.2 = L ∧ Chrono (t₀, 0) q ∧ throughB2A Δ q = (t₀, 0)

/-- The loop exists iff the clock offset exceeds the outside light-crossing time `L`. -/
theorem hasCTC_iff {L Δ : ℝ} (hL : 0 < L) : HasCTC L Δ ↔ L < Δ := by
  constructor
  · rintro ⟨t₀, q, hq, hchrono, hjump⟩
    have h1 : q.1 - Δ = t₀ := congrArg Prod.fst hjump
    have h2 : |q.2 - 0| < q.1 - t₀ := hchrono
    rw [hq, sub_zero, abs_of_pos hL] at h2
    linarith
  · intro h
    refine ⟨0, (Δ, L), rfl, ?_, ?_⟩
    · show |L - 0| < Δ - 0
      simpa [abs_of_pos hL] using h
    · simp [throughB2A]

/-! ## 4. Putting it together -/

/-- **Time machine from exotic matter** (Morris–Thorne–Yurtsever, idealised).
Flare-out matter holds the throat open (and violates the NEC); dragging a mouth at speed
`v < 1` for long enough then produces a closed timelike loop. -/
theorem exotic_wormhole_time_machine
    {r₀ db dPhi L v : ℝ} (hr : 0 < r₀) (hflare : db < 1)
    (hL : 0 < L) (hv0 : 0 < v) (hv1 : v < 1) :
    (¬ RadialNEC (energyDensity r₀ db) (radialPressure r₀ r₀ dPhi)) ∧
      ∃ τ : ℝ, 0 < τ ∧ HasCTC L (clockOffset v τ) := by
  refine ⟨flare_out_violates_NEC hr hflare, ?_⟩
  obtain ⟨τ, hτ, h⟩ := exists_offset_gt hv0 hv1 L
  exact ⟨τ, hτ, (hasCTC_iff hL).2 h⟩

end ExoticCTC

end

/-!
## Going further (not done here)

* Real geometry instead of a toy: a metric field `g` on a chart of `Fin 4 → ℝ`, with
  ```
  def IsCTC {n : ℕ} (g : (Fin n → ℝ) → (Fin n → ℝ) → (Fin n → ℝ) → ℝ)
      (γ : ℝ → Fin n → ℝ) (P : ℝ) : Prop :=
    0 < P ∧ Function.Periodic γ P ∧ Differentiable ℝ γ ∧
      ∀ s, g (γ s) (deriv γ s) (deriv γ s) < 0
  ```
  (a wormhole needs several charts, so a closed curve is then closed only up to the
  gluing map).
* Derive `energyDensity` / `radialPressure` from the Einstein tensor of the
  Morris–Thorne metric instead of postulating them.
* The real "exotic matter ⇒ CTC" direction is the family of Tipler/Hawking-type theorems:
  a time machine forming in a finite region forces energy-condition violations.
* PhysLean already has the twin paradox; it could replace `clockOffset`.
-/
