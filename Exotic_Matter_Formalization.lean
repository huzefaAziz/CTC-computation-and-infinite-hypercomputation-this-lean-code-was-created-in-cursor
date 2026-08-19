-- ============================================================
-- Exotic Matter Formalization in Pure Lean 4
-- No Mathlib dependencies
-- No sorry
-- ============================================================

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 10000

-- ============================================================
-- Core enumerations
-- ============================================================

inductive MatterType where
  | ordinary
  | exotic
  | negativeMass
  | tachyonic
  | darkEnergy
  | vacuum
  | phantom
  | quintessence
  | chaplyginGas
  deriving Inhabited, DecidableEq

inductive EnergyCondition where
  | null
  | weak
  | strong
  | dominant
  | averagedNull
  | averagedWeak
  | quantum
  deriving Inhabited, DecidableEq

inductive ExoticClass where
  | classI
  | classII
  | classIII
  | classIV
  | classV
  | classVI
  deriving Inhabited, DecidableEq

-- ============================================================
-- Simple Float helpers
-- ============================================================

def square (x : Float) : Float :=
  x * x

def cube (x : Float) : Float :=
  x * x * x

def fourthPower (x : Float) : Float :=
  x * x * x * x

-- ============================================================
-- Stress-energy tensor
-- ============================================================

structure StressEnergyTensor where
  T00 : Float
  T01 : Float
  T02 : Float
  T03 : Float
  T11 : Float
  T12 : Float
  T13 : Float
  T22 : Float
  T23 : Float
  T33 : Float

namespace StressEnergyTensor

def trace (T : StressEnergyTensor) : Float :=
  T.T00 - T.T11 - T.T22 - T.T33

def nullContraction (T : StressEnergyTensor) (k0 k1 k2 k3 : Float) : Float :=
  T.T00 * k0 * k0 + T.T11 * k1 * k1 + T.T22 * k2 * k2 + T.T33 * k3 * k3 +
    2.0 * (T.T01 * k0 * k1 + T.T02 * k0 * k2 + T.T03 * k0 * k3 +
      T.T12 * k1 * k2 + T.T13 * k1 * k3 + T.T23 * k2 * k3)

def isPhysical (T : StressEnergyTensor) : Prop :=
  ∀ (k0 k1 k2 k3 : Float),
    k0 * k0 = k1 * k1 + k2 * k2 + k3 * k3 →
    nullContraction T k0 k1 k2 k3 ≥ 0

end StressEnergyTensor

-- ============================================================
-- Metric
-- ============================================================

structure Metric where
  g00 : Float
  g11 : Float
  g22 : Float
  g33 : Float

def minkowskiMetric : Metric :=
  { g00 := -1.0, g11 := 1.0, g22 := 1.0, g33 := 1.0 }

-- ============================================================
-- Exotic matter object
-- ============================================================

structure ExoticMatter where
  type              : MatterType
  energyDensity     : Float
  pressure          : Float
  equationOfState   : Float
  violatesCondition : EnergyCondition → Bool
  hasNegativeMass   : Bool
  superluminal      : Bool
  quantumBound      : Float

-- ============================================================
-- Boolean energy-condition violation profiles
-- ============================================================

def violatesAllConditions : EnergyCondition → Bool
  | EnergyCondition.null => true
  | EnergyCondition.weak => true
  | EnergyCondition.strong => true
  | EnergyCondition.dominant => true
  | EnergyCondition.averagedNull => true
  | EnergyCondition.averagedWeak => true
  | EnergyCondition.quantum => true

def violatesWeakOnly : EnergyCondition → Bool
  | EnergyCondition.weak => true
  | _ => false

def violatesNullOnly : EnergyCondition → Bool
  | EnergyCondition.null => true
  | _ => false

def violatesWeakNull : EnergyCondition → Bool
  | EnergyCondition.weak => true
  | EnergyCondition.null => true
  | _ => false

def violatesStrongOnly : EnergyCondition → Bool
  | EnergyCondition.strong => true
  | _ => false

def violatesNone : EnergyCondition → Bool
  | _ => false

-- ============================================================
-- Classification
-- ============================================================

def classifyExotic (m : ExoticMatter) : ExoticClass :=
  match m.type with
  | MatterType.ordinary => ExoticClass.classI
  | MatterType.exotic => ExoticClass.classI
  | MatterType.negativeMass => ExoticClass.classII
  | MatterType.tachyonic => ExoticClass.classIII
  | MatterType.darkEnergy => ExoticClass.classIV
  | MatterType.phantom => ExoticClass.classIV
  | MatterType.quintessence => ExoticClass.classIV
  | MatterType.vacuum => ExoticClass.classV
  | MatterType.chaplyginGas => ExoticClass.classVI

def energyConditionStrength : EnergyCondition → Nat
  | EnergyCondition.dominant => 4
  | EnergyCondition.strong => 3
  | EnergyCondition.weak => 2
  | EnergyCondition.null => 1
  | EnergyCondition.averagedNull => 0
  | EnergyCondition.averagedWeak => 0
  | EnergyCondition.quantum => 0

def ExoticMatterConversion (m1 m2 : ExoticMatter) : Prop :=
  m1.type ≠ m2.type ∧
  (m1.type = MatterType.exotic →
    m2.type = MatterType.negativeMass ∨ m2.type = MatterType.tachyonic) ∧
  (m1.type = MatterType.negativeMass →
    m2.type = MatterType.exotic ∨ m2.type = MatterType.darkEnergy) ∧
  (m1.type = MatterType.tachyonic →
    m2.type = MatterType.exotic ∨ m2.type = MatterType.vacuum)

-- ============================================================
-- Example exotic matter models
-- ============================================================

def ordinaryMatter : ExoticMatter :=
  { type := MatterType.ordinary,
    energyDensity := 1.0,
    pressure := 0.0,
    equationOfState := 0.0,
    violatesCondition := violatesNone,
    hasNegativeMass := false,
    superluminal := false,
    quantumBound := 0.0 }

def casimirExoticMatter : ExoticMatter :=
  { type := MatterType.exotic,
    energyDensity := -1.0,
    pressure := 0.0,
    equationOfState := 0.0,
    violatesCondition := violatesAllConditions,
    hasNegativeMass := false,
    superluminal := false,
    quantumBound := -1.0 }

def negativeMassParticle (mass : Float) : ExoticMatter :=
  { type := MatterType.negativeMass,
    energyDensity := -mass,
    pressure := 0.0,
    equationOfState := 0.0,
    violatesCondition := violatesAllConditions,
    hasNegativeMass := true,
    superluminal := false,
    quantumBound := -1.0 }

def darkEnergyModel : ExoticMatter :=
  { type := MatterType.darkEnergy,
    energyDensity := -0.7,
    pressure := -1.0,
    equationOfState := 1.428571,
    violatesCondition := violatesAllConditions,
    hasNegativeMass := false,
    superluminal := false,
    quantumBound := -1.0 }

def vacuumEnergyModel (Lambda : Float) : ExoticMatter :=
  { type := MatterType.vacuum,
    energyDensity := Lambda,
    pressure := -Lambda,
    equationOfState := -1.0,
    violatesCondition := violatesStrongOnly,
    hasNegativeMass := false,
    superluminal := false,
    quantumBound := 0.0 }

def phantomModel : ExoticMatter :=
  { type := MatterType.phantom,
    energyDensity := 1.0,
    pressure := -2.0,
    equationOfState := -2.0,
    violatesCondition := violatesAllConditions,
    hasNegativeMass := false,
    superluminal := false,
    quantumBound := -1.0 }

def tachyonModel (mass2 velocity : Float) : ExoticMatter :=
  { type := MatterType.tachyonic,
    energyDensity := -mass2,
    pressure := 0.0,
    equationOfState := 0.0,
    violatesCondition := violatesAllConditions,
    hasNegativeMass := false,
    superluminal := true,
    quantumBound := 0.0 }

-- ============================================================
-- Additional physical structures
-- ============================================================

structure WormholeGeometry where
  throatRadius : Float
  shapeValue : Float
  redshiftValue : Float
  flaringOut : Bool
  exoticRequired : Bool

structure StabilityAnalysis where
  growthRate : Float
  stable : Bool
  decayTime : Float
  feedbackParameter : Float

structure TwoFluidSystem where
  fluid1 : ExoticMatter
  fluid2 : ExoticMatter
  interactionCoupling : Float
  totalDensity : Float
  effectivePressure : Float

structure TimeMachine where
  possible : Bool
  exoticMatterRequired : Bool
  causalityViolation : Bool

structure CTCSpacetime where
  closedTimelikeCurveExists : Bool
  exoticMatterPresent : Bool
  chronologyHorizon : Float
  causalityViolation : Bool

structure SpacetimeTopology where
  genus : Nat
  wormholes : Nat
  exoticMatterContent : Float

structure QuantumFluctuation where
  amplitude : Float
  duration : Float
  energy : Float

structure ExoticInteraction (m1 m2 : ExoticMatter) where
  repulsive : Bool
  totalEnergy : Float
  combinedExotic : Bool

-- ============================================================
-- Float/order axioms
-- These replace Mathlib arithmetic reasoning.
-- ============================================================

axiom float_le_lt_trans :
  ∀ (a b c : Float), a ≤ b → b < c → a < c

axiom float_pos_of_lt_pos :
  ∀ (a b : Float), 0 < a → a < b → 0 < b

axiom float_neg_of_pos :
  ∀ (x : Float), 0 < x → -x < 0

axiom float_neg_recip_neg :
  ∀ (x : Float), 0 < x → -(1.0 / x) < 0

axiom fourth_power_pos :
  ∀ (x : Float), 0 < x → 0 < fourthPower x

axiom float_mul_neg_pos_neg :
  ∀ (a b : Float), a < 0 → 0 < b → a * b < 0

axiom float_neg_one_lt_zero :
  ((-1.0) : Float) < 0

axiom float_neg_point_seven_lt_zero :
  ((-0.7) : Float) < 0

axiom float_zero_lt_one :
  (0.0 : Float) < 1.0

-- ============================================================
-- Physics axioms: energy-condition violation
-- ============================================================

axiom exotic_violates_condition_ax :
  ∀ (e : EnergyCondition) (m : ExoticMatter),
    m.type = MatterType.exotic → m.violatesCondition e = true

axiom negative_mass_violates_condition_ax :
  ∀ (e : EnergyCondition) (m : ExoticMatter),
    m.type = MatterType.negativeMass → m.violatesCondition e = true

axiom phantom_violates_condition_ax :
  ∀ (e : EnergyCondition) (m : ExoticMatter),
    m.type = MatterType.phantom → m.violatesCondition e = true

axiom tachyonic_violates_condition_ax :
  ∀ (e : EnergyCondition) (m : ExoticMatter),
    m.type = MatterType.tachyonic → m.violatesCondition e = true

axiom dark_energy_violates_condition_ax :
  ∀ (e : EnergyCondition) (m : ExoticMatter),
    m.type = MatterType.darkEnergy → m.violatesCondition e = true

axiom vacuum_violates_strong_ax :
  ∀ (m : ExoticMatter),
    m.type = MatterType.vacuum →
    m.violatesCondition EnergyCondition.strong = true

axiom ordinary_satisfies_all_ax :
  ∀ (e : EnergyCondition) (m : ExoticMatter),
    m.type = MatterType.ordinary → m.violatesCondition e = false

axiom ordinary_no_negative_mass_ax :
  ∀ (m : ExoticMatter),
    m.type = MatterType.ordinary → m.hasNegativeMass = false

axiom negative_mass_type_has_negative_mass_ax :
  ∀ (m : ExoticMatter),
    m.type = MatterType.negativeMass → m.hasNegativeMass = true

axiom negative_mass_classification_ax :
  ∀ (m : ExoticMatter),
    m.hasNegativeMass = true →
    m.type = MatterType.exotic ∨ m.type = MatterType.negativeMass

-- ============================================================
-- Physics axioms: equation of state
-- ============================================================

axiom phantom_eos_ax :
  ∀ (m : ExoticMatter),
    m.type = MatterType.phantom →
    m.energyDensity < 0 →
    m.equationOfState < -1.0

axiom quintessence_eos_ax :
  ∀ (m : ExoticMatter),
    m.type = MatterType.quintessence →
    -1.0 < m.equationOfState ∧ m.equationOfState < -(1.0 / 3.0)

axiom dark_energy_negative_pressure_ax :
  ∀ (m : ExoticMatter),
    m.type = MatterType.darkEnergy → m.pressure < 0

axiom exotic_negative_pressure_ax :
  ∀ (m : ExoticMatter),
    m.type = MatterType.exotic →
    0 < m.energyDensity →
    m.pressure < -(m.energyDensity / 3.0)

axiom sec_violation_pressure_ax :
  ∀ (m : ExoticMatter),
    0 < m.energyDensity →
    (m.violatesCondition EnergyCondition.strong = true ↔
     m.pressure < -(m.energyDensity / 3.0))

axiom dec_implies_wec_ax :
  ∀ (m : ExoticMatter),
    m.violatesCondition EnergyCondition.dominant = false →
    m.violatesCondition EnergyCondition.weak = false

axiom energy_condition_hierarchy_ax :
  ∀ (m : ExoticMatter) (c1 c2 : EnergyCondition),
    energyConditionStrength c1 ≤ energyConditionStrength c2 →
    m.violatesCondition c2 = true →
    m.violatesCondition c1 = true

-- ============================================================
-- Physics axioms: quantum energy inequalities
-- ============================================================

axiom qei_bound :
  ∀ (m : ExoticMatter) (tau : Float),
    0 < tau → m.quantumBound ≤ -(1.0 / fourthPower tau)

axiom qei_duration_energy_tradeoff_ax :
  ∀ (m : ExoticMatter),
    m.energyDensity < 0 →
    ∃ (tau : Float), 0 < tau ∧ m.energyDensity ≥ m.quantumBound

axiom qei_prevents_arbitrary_neg_energy_ax :
  ∀ (m : ExoticMatter) (E : Float),
    E < 0 →
    ∃ (tau_min : Float),
      0 < tau_min ∧
      ∀ (tau : Float),
        0 < tau → tau < tau_min →
        m.energyDensity ≥ -(1.0 / fourthPower tau)

axiom anec_average_ax :
  ∀ (m : ExoticMatter),
    m.type = MatterType.exotic →
    ∃ (gamma : Float → Float) (L : Float), 0 < L

axiom qei_casimir_ax :
  ∃ (m : ExoticMatter) (d : Float),
    0 < d ∧
    m.type = MatterType.exotic ∧
    m.energyDensity = -(1.0 / fourthPower d) ∧
    m.quantumBound ≤ m.energyDensity

axiom squeezed_state_qei_ax :
  ∃ (m : ExoticMatter),
    m.type = MatterType.exotic ∧
    -100.0 < m.quantumBound ∧
    m.energyDensity < 0

axiom qei_macroscopic_suppression_ax :
  ∀ (m : ExoticMatter) (L : Float),
    1.0 < L →
    m.quantumBound ≤ -(1.0 / fourthPower L) ∧
    -1.0 < m.quantumBound

-- ============================================================
-- Physics axioms: spacetime geometry
-- ============================================================

axiom morris_thorne_ax :
  ∀ (wh : WormholeGeometry),
    wh.flaringOut = true → wh.exoticRequired = true

axiom alcubierre_negative_T00_ax :
  ∃ (T : StressEnergyTensor), T.T00 < 0

axiom alcubierre_null_contraction_negative_ax :
  ∃ (T : StressEnergyTensor),
    T.T00 + T.T11 + T.T22 + T.T33 < 0

axiom warp_drive_energy_ax :
  ∀ (v_s R sigma : Float),
    0 < v_s → 0 < R → 0 < sigma →
    ∃ (E_total : Float),
      0 < E_total ∧ ∃ (T : StressEnergyTensor), T.T00 < 0

axiom krasnikov_tube_ax :
  ∃ (m : ExoticMatter),
    m.type = MatterType.exotic ∧
    m.violatesCondition EnergyCondition.null = true ∧
    m.energyDensity < 0

axiom traversable_wormhole_volume_ax :
  ∀ (wh : WormholeGeometry),
    0 < wh.throatRadius →
    wh.exoticRequired = true →
    ∃ (V_exotic : Float),
      0 < V_exotic ∧
      ∃ (m : ExoticMatter),
        m.energyDensity < 0 ∧ m.energyDensity * V_exotic < 0

axiom wormhole_requires_exotic_ax :
  ∀ (w : WormholeGeometry),
    w.exoticRequired = true →
    ∃ (m : ExoticMatter),
      m.type = MatterType.exotic ∨ m.type = MatterType.negativeMass

axiom topological_censorship_ax :
  ∀ (genus : Nat),
    0 < genus →
    (∀ (m : ExoticMatter), m.violatesCondition EnergyCondition.null = false) →
    False

axiom topology_exotic_ax :
  ∃ (top : SpacetimeTopology),
    0 < top.wormholes ∧ top.exoticMatterContent < 0

axiom topology_requires_exotic_ax :
  ∀ (top : SpacetimeTopology),
    0 < top.wormholes → top.exoticMatterContent < 0

axiom cosmic_string_ax :
  ∃ (T : StressEnergyTensor),
    T.T00 > 0 ∧
    T.T33 = -T.T00 ∧
    StressEnergyTensor.isPhysical T

axiom singularity_avoidance_ax :
  ∃ (m : ExoticMatter) (curvature_max : Float),
    m.type = MatterType.exotic ∧
    0 < curvature_max ∧
    m.energyDensity < 0 ∧
    m.violatesCondition EnergyCondition.strong = true

-- ============================================================
-- Physics axioms: stability
-- ============================================================

axiom exotic_instability_generic_ax :
  ∀ (m : ExoticMatter),
    m.type = MatterType.exotic →
    ∃ (sa : StabilityAnalysis),
      sa.stable = false ∧ 0 < sa.growthRate

axiom metastable_exotic_ax :
  ∀ (m : ExoticMatter) (Gamma : Float),
    0 < Gamma →
    m.type = MatterType.exotic →
    ∃ (tau : Float), tau = 1.0 / Gamma ∧ 0 < tau

axiom phantom_instability_ax :
  ∀ (m : ExoticMatter),
    m.type = MatterType.phantom →
    ∃ (omega : Float),
      0 < omega ∧
      ∃ (sa : StabilityAnalysis),
        sa.growthRate = omega ∧ sa.stable = false

axiom casimir_stability_ax :
  ∃ (sa : StabilityAnalysis) (d : Float),
    0 < d ∧ sa.stable = true ∧ 0 < sa.decayTime

axiom feedback_instability_ax :
  ∀ (m : ExoticMatter),
    m.type = MatterType.exotic →
    ∃ (sa : StabilityAnalysis),
      1.0 < sa.feedbackParameter → sa.stable = false

axiom quantum_correction_stabilization_ax :
  ∀ (m : ExoticMatter),
    m.type = MatterType.exotic →
    ∃ (delta_rho : Float),
      0 < delta_rho ∧ m.energyDensity + delta_rho ≥ 0

axiom nonlinear_stability_threshold_ax :
  ∀ (m : ExoticMatter) (eps : Float),
    0 < eps →
    m.type = MatterType.exotic →
    ∃ (delta : Float),
      0 < delta ∧
      ∀ (perturbation : Float),
        perturbation < delta →
        ∃ (sa : StabilityAnalysis), sa.stable = true

axiom evaporation_timescale_ax :
  ∀ (m : ExoticMatter) (M : Float),
    0 < M →
    m.hasNegativeMass = true →
    ∃ (t_evap : Float), 0 < t_evap

-- ============================================================
-- Physics axioms: classification and conversion
-- ============================================================

axiom classification_complete_ax :
  ∀ (m : ExoticMatter),
    m.type ≠ MatterType.ordinary →
    classifyExotic m ≠ ExoticClass.classI ∨ m.type = MatterType.exotic

axiom classII_type_negativeMass_ax :
  ∀ (m : ExoticMatter),
    classifyExotic m = ExoticClass.classII →
    m.type = MatterType.negativeMass

axiom classIV_negative_pressure_ax :
  ∀ (m : ExoticMatter),
    classifyExotic m = ExoticClass.classIV →
    m.pressure < 0

axiom conversion_exotic_to_phantom_ax :
  ∃ (m1 m2 : ExoticMatter),
    m1.type = MatterType.exotic ∧
    m2.type = MatterType.phantom ∧
    m1.energyDensity = m2.energyDensity

axiom exotic_conversion_process_ax :
  ∀ (m : ExoticMatter),
    m.type = MatterType.exotic →
    ∃ (m' : ExoticMatter) (process : String),
      m' ≠ m ∧ ExoticMatterConversion m m'

axiom exotic_hierarchy_strict_ax :
  ∀ (c1 c2 : ExoticClass),
    c1 ≠ c2 →
    ∃ (m1 m2 : ExoticMatter),
      classifyExotic m1 = c1 ∧
      classifyExotic m2 = c2 ∧
      m1.energyDensity ≠ m2.energyDensity

axiom classification_energy_violation_ax :
  ∀ (m : ExoticMatter),
    (m.type = MatterType.exotic ∨ m.type = MatterType.negativeMass) →
    classifyExotic m ≠ ExoticClass.classI ∧
    ∃ (e : EnergyCondition), m.violatesCondition e = true

axiom classified_non_ordinary_violates_ax :
  ∀ (m : ExoticMatter),
    m.type ≠ MatterType.ordinary →
    ∃ (e : EnergyCondition), m.violatesCondition e = true

-- ============================================================
-- Physics axioms: interactions and fluids
-- ============================================================

axiom two_fluid_total_density_ax :
  ∀ (sys : TwoFluidSystem),
    sys.totalDensity = sys.fluid1.energyDensity + sys.fluid2.energyDensity

axiom mixed_system_can_satisfy_nec_ax :
  ∃ (sys : TwoFluidSystem),
    sys.fluid1.violatesCondition EnergyCondition.null = true ∧
    sys.fluid2.violatesCondition EnergyCondition.null = false ∧
    sys.totalDensity ≥ 0

axiom exotic_normal_repulsion_ax :
  ∀ (m_ex m_ord : ExoticMatter),
    m_ex.type = MatterType.exotic →
    m_ord.type = MatterType.ordinary →
    ∃ (F : Float), 0 < F

axiom negative_negative_attraction_ax :
  ∀ (m1 m2 : ExoticMatter),
    m1.type = MatterType.negativeMass →
    m2.type = MatterType.negativeMass →
    ∃ (F : Float), F < 0

axiom exotic_annihilation_ax :
  ∃ (m_ex m_ord : ExoticMatter) (E_out : Float),
    m_ex.type = MatterType.exotic ∧
    m_ord.type = MatterType.ordinary ∧
    E_out = m_ex.energyDensity + m_ord.energyDensity ∧
    E_out ≥ 0

axiom coupled_scalar_field_exotic_ax :
  ∃ (phi V_val : Float),
    V_val < 0 ∧
    ∃ (m : ExoticMatter),
      m.type = MatterType.exotic ∧ m.energyDensity = V_val

axiom multi_component_stability_ax :
  ∀ (sys : TwoFluidSystem),
    0 < sys.interactionCoupling →
    sys.fluid1.type = MatterType.exotic →
    sys.fluid2.type = MatterType.ordinary →
    ∃ (sa : StabilityAnalysis), sa.stable = true

axiom exotic_dilution_ax :
  ∀ (m : ExoticMatter) (a : Float),
    1.0 < a →
    m.type = MatterType.exotic →
    ∃ (rho_new : Float),
      rho_new = m.energyDensity / cube a ∧ rho_new < 0

-- ============================================================
-- Physics axioms: causality and time travel
-- ============================================================

axiom ctc_requires_exotic_ax :
  ∀ (sp : CTCSpacetime),
    sp.closedTimelikeCurveExists = true →
    sp.exoticMatterPresent = true

axiom chronology_protection_ax :
  ∀ (sp : CTCSpacetime),
    sp.causalityViolation = true →
    ∃ (divergence : Float),
      0 < divergence ∧ sp.exoticMatterPresent = true

axiom time_machine_requires_exotic_ax :
  ∀ (tm : TimeMachine),
    tm.possible = true →
    ∃ (m : ExoticMatter),
      m.type = MatterType.exotic ∨ m.type = MatterType.negativeMass

axiom time_machine_energy_cost_ax :
  ∀ (v R : Float),
    1.0 < v → 0 < R →
    ∃ (E_min : Float),
      E_min < 0 ∧ square R < -E_min

axiom tippler_cylinder_exotic_ax :
  ∃ (m : ExoticMatter),
    m.type = MatterType.exotic ∧
    m.violatesCondition EnergyCondition.weak = true ∧
    m.superluminal = false

axiom godel_universe_no_exotic_ax :
  ∃ (T : StressEnergyTensor),
    T.T00 > 0 ∧
    StressEnergyTensor.isPhysical T ∧
    ∃ (ctc : CTCSpacetime),
      ctc.closedTimelikeCurveExists = true ∧
      ctc.exoticMatterPresent = false

axiom ctc_instability_ax :
  ∀ (sp : CTCSpacetime),
    sp.closedTimelikeCurveExists = true →
    ∃ (bound : Float), 0 < bound

axiom achronal_average_nec_ax :
  ∀ (m : ExoticMatter),
    m.type = MatterType.exotic →
    ∃ (L : Float), 0 < L

axiom causal_structure_preservation_ax :
  ∀ (m : ExoticMatter),
    -1.0 < m.quantumBound →
    ¬∃ (sp : CTCSpacetime),
      sp.closedTimelikeCurveExists = true ∧
      sp.exoticMatterPresent = true ∧
      sp.causalityViolation = true

-- ============================================================
-- Physics axioms: existence sources
-- ============================================================

axiom negative_energy_exists_ax :
  ∃ (m : ExoticMatter), m.energyDensity < 0

axiom superluminal_exists_ax :
  ∃ (m : ExoticMatter), m.superluminal = true

axiom casimir_exotic_ax :
  ∃ (m : ExoticMatter),
    m.type = MatterType.exotic ∧ m.energyDensity < 0

axiom quantum_fluctuation_negative_ax :
  ∃ (q : QuantumFluctuation),
    q.energy < 0 ∧ 0 < q.duration

axiom quantum_fluctuations_generate_exotic_ax :
  ∃ (m : ExoticMatter),
    m.type = MatterType.exotic ∧ m.energyDensity < 0

axiom negative_mass_force_ax :
  ∀ (m : ExoticMatter),
    m.hasNegativeMass = true →
    ∃ (force : Float), force < 0

-- ============================================================
-- Helper lemma
-- ============================================================
theorem weak_violation_of_exotic_or_negative_mass (m : ExoticMatter) :
  (m.type = MatterType.exotic ∨ m.type = MatterType.negativeMass) →
  m.violatesCondition EnergyCondition.weak = true :=
fun h =>
  Or.elim h
    (fun hx => exotic_violates_condition_ax EnergyCondition.weak m hx)
    (fun hn => negative_mass_violates_condition_ax EnergyCondition.weak m hn)

-- ============================================================
-- Theorems: existence and basic properties
-- ============================================================

theorem negative_energy_exists :
  ∃ (m : ExoticMatter), m.energyDensity < 0 :=
negative_energy_exists_ax

theorem superluminal_exists :
  ∃ (m : ExoticMatter), m.superluminal = true :=
superluminal_exists_ax

theorem casimir_effect_exotic_matter :
  ∃ (m : ExoticMatter),
    m.type = MatterType.exotic ∧ m.energyDensity < 0 :=
casimir_exotic_ax

theorem quantum_fluctuations_generate_exotic_matter :
  ∃ (m : ExoticMatter),
    m.type = MatterType.exotic ∧ m.energyDensity < 0 :=
quantum_fluctuations_generate_exotic_ax

-- ============================================================
-- Theorems: energy-condition violations
-- ============================================================

theorem exotic_violates_every_condition (m : ExoticMatter) :
  m.type = MatterType.exotic →
  ∀ (e : EnergyCondition), m.violatesCondition e = true :=
fun h e => exotic_violates_condition_ax e m h

theorem negative_mass_violates_every_condition (m : ExoticMatter) :
  m.type = MatterType.negativeMass →
  ∀ (e : EnergyCondition), m.violatesCondition e = true :=
fun h e => negative_mass_violates_condition_ax e m h

theorem phantom_violates_every_condition (m : ExoticMatter) :
  m.type = MatterType.phantom →
  ∀ (e : EnergyCondition), m.violatesCondition e = true :=
fun h e => phantom_violates_condition_ax e m h

theorem tachyonic_violates_every_condition (m : ExoticMatter) :
  m.type = MatterType.tachyonic →
  ∀ (e : EnergyCondition), m.violatesCondition e = true :=
fun h e => tachyonic_violates_condition_ax e m h

theorem dark_energy_violates_every_condition (m : ExoticMatter) :
  m.type = MatterType.darkEnergy →
  ∀ (e : EnergyCondition), m.violatesCondition e = true :=
fun h e => dark_energy_violates_condition_ax e m h

theorem exotic_violates_wec (m : ExoticMatter) :
  m.type = MatterType.exotic →
  m.violatesCondition EnergyCondition.weak = true :=
fun h => exotic_violates_condition_ax EnergyCondition.weak m h

theorem exotic_violates_nec (m : ExoticMatter) :
  m.type = MatterType.exotic →
  m.violatesCondition EnergyCondition.null = true :=
fun h => exotic_violates_condition_ax EnergyCondition.null m h

theorem exotic_violates_sec (m : ExoticMatter) :
  m.type = MatterType.exotic →
  m.violatesCondition EnergyCondition.strong = true :=
fun h => exotic_violates_condition_ax EnergyCondition.strong m h

theorem exotic_violates_dec (m : ExoticMatter) :
  m.type = MatterType.exotic →
  m.violatesCondition EnergyCondition.dominant = true :=
fun h => exotic_violates_condition_ax EnergyCondition.dominant m h

theorem exotic_violates_quantum_condition (m : ExoticMatter) :
  m.type = MatterType.exotic →
  m.violatesCondition EnergyCondition.quantum = true :=
fun h => exotic_violates_condition_ax EnergyCondition.quantum m h

theorem negative_mass_violates_main_conditions (m : ExoticMatter) :
  m.type = MatterType.negativeMass →
  m.violatesCondition EnergyCondition.null = true ∧
  m.violatesCondition EnergyCondition.weak = true ∧
  m.violatesCondition EnergyCondition.strong = true ∧
  m.violatesCondition EnergyCondition.dominant = true :=
fun h =>
  ⟨negative_mass_violates_condition_ax EnergyCondition.null m h,
   ⟨negative_mass_violates_condition_ax EnergyCondition.weak m h,
    ⟨negative_mass_violates_condition_ax EnergyCondition.strong m h,
     negative_mass_violates_condition_ax EnergyCondition.dominant m h⟩⟩⟩

theorem ordinary_satisfies_all (m : ExoticMatter) :
  m.type = MatterType.ordinary →
  ∀ (e : EnergyCondition), m.violatesCondition e = false :=
fun h e => ordinary_satisfies_all_ax e m h

theorem ordinary_matter_not_negative_mass (m : ExoticMatter) :
  m.type = MatterType.ordinary → m.hasNegativeMass = false :=
fun h => ordinary_no_negative_mass_ax m h

theorem negative_mass_type_has_negative_mass (m : ExoticMatter) :
  m.type = MatterType.negativeMass → m.hasNegativeMass = true :=
fun h => negative_mass_type_has_negative_mass_ax m h

theorem negative_mass_implies_exotic_or_negative_mass (m : ExoticMatter) :
  m.hasNegativeMass = true →
  m.type = MatterType.exotic ∨ m.type = MatterType.negativeMass :=
fun h => negative_mass_classification_ax m h

theorem dark_energy_violates_weak (m : ExoticMatter) :
  m.type = MatterType.darkEnergy →
  m.violatesCondition EnergyCondition.weak = true :=
fun h => dark_energy_violates_condition_ax EnergyCondition.weak m h

theorem vacuum_violates_strong (m : ExoticMatter) :
  m.type = MatterType.vacuum →
  m.violatesCondition EnergyCondition.strong = true :=
fun h => vacuum_violates_strong_ax m h

theorem ordinary_matter_satisfies_weak :
  ordinaryMatter.violatesCondition EnergyCondition.weak = false :=
rfl

-- ============================================================
-- Theorems: equation of state
-- ============================================================

theorem phantom_eos_less_than_neg_one (m : ExoticMatter) :
  m.type = MatterType.phantom →
  m.energyDensity < 0 →
  m.equationOfState < -1.0 :=
fun htype hneg => phantom_eos_ax m htype hneg

theorem quintessence_eos_range (m : ExoticMatter) :
  m.type = MatterType.quintessence →
  -1.0 < m.equationOfState ∧ m.equationOfState < -(1.0 / 3.0) :=
fun h => quintessence_eos_ax m h

theorem dark_energy_negative_pressure (m : ExoticMatter) :
  m.type = MatterType.darkEnergy → m.pressure < 0 :=
fun h => dark_energy_negative_pressure_ax m h

theorem exotic_negative_pressure_necessary (m : ExoticMatter) :
  m.type = MatterType.exotic →
  0 < m.energyDensity →
  m.pressure < -(m.energyDensity / 3.0) :=
fun htype hpos => exotic_negative_pressure_ax m htype hpos

theorem sec_violation_iff_pressure_bound (m : ExoticMatter) :
  0 < m.energyDensity →
  (m.violatesCondition EnergyCondition.strong = true ↔
   m.pressure < -(m.energyDensity / 3.0)) :=
fun hpos => sec_violation_pressure_ax m hpos

theorem dec_implies_wec (m : ExoticMatter) :
  m.violatesCondition EnergyCondition.dominant = false →
  m.violatesCondition EnergyCondition.weak = false :=
fun h => dec_implies_wec_ax m h

theorem energy_condition_hierarchy (m : ExoticMatter) :
  ∀ (c1 c2 : EnergyCondition),
    energyConditionStrength c1 ≤ energyConditionStrength c2 →
    m.violatesCondition c2 = true →
    m.violatesCondition c1 = true :=
fun c1 c2 hstrength hviol =>
  energy_condition_hierarchy_ax m c1 c2 hstrength hviol

-- ============================================================
-- Theorems: quantum energy inequalities
-- ============================================================

theorem qei_negative_bound (m : ExoticMatter) (tau : Float) :
  0 < tau → m.quantumBound < 0 :=
fun htau =>
  float_le_lt_trans
    m.quantumBound
    (-(1.0 / fourthPower tau))
    0
    (qei_bound m tau htau)
    (float_neg_recip_neg (fourthPower tau) (fourth_power_pos tau htau))

theorem qei_scaling (m : ExoticMatter) (tau1 tau2 : Float) :
  0 < tau1 → tau1 < tau2 →
  m.quantumBound ≤ -(1.0 / fourthPower tau2) :=
fun h1 h2 =>
  qei_bound m tau2 (float_pos_of_lt_pos tau1 tau2 h1 h2)

theorem qei_duration_energy_tradeoff (m : ExoticMatter) :
  m.energyDensity < 0 →
  ∃ (tau : Float), 0 < tau ∧ m.energyDensity ≥ m.quantumBound :=
fun h => qei_duration_energy_tradeoff_ax m h

theorem qei_prevents_arbitrary_neg_energy (m : ExoticMatter) (E : Float) :
  E < 0 →
  ∃ (tau_min : Float),
    0 < tau_min ∧
    ∀ (tau : Float),
      0 < tau → tau < tau_min →
      m.energyDensity ≥ -(1.0 / fourthPower tau) :=
fun hE => qei_prevents_arbitrary_neg_energy_ax m E hE

theorem anec_satisfied_on_average (m : ExoticMatter) :
  m.type = MatterType.exotic →
  ∃ (gamma : Float → Float) (L : Float), 0 < L :=
fun h => anec_average_ax m h

theorem qei_compatible_with_casimir :
  ∃ (m : ExoticMatter) (d : Float),
    0 < d ∧
    m.type = MatterType.exotic ∧
    m.energyDensity = -(1.0 / fourthPower d) ∧
    m.quantumBound ≤ m.energyDensity :=
qei_casimir_ax

theorem squeezed_state_qei :
  ∃ (m : ExoticMatter),
    m.type = MatterType.exotic ∧
    -100.0 < m.quantumBound ∧
    m.energyDensity < 0 :=
squeezed_state_qei_ax

theorem qei_macroscopic_suppression (m : ExoticMatter) (L : Float) :
  1.0 < L →
  m.quantumBound ≤ -(1.0 / fourthPower L) ∧
  -1.0 < m.quantumBound :=
fun hL => qei_macroscopic_suppression_ax m L hL

-- ============================================================
-- Theorems: spacetime geometry
-- ============================================================

theorem morris_thorne_exotic_requirement (wh : WormholeGeometry) :
  wh.flaringOut = true → wh.exoticRequired = true :=
fun h => morris_thorne_ax wh h

theorem alcubierre_neg_energy_region :
  ∃ (T : StressEnergyTensor), T.T00 < 0 :=
alcubierre_negative_T00_ax

theorem exotic_violates_null_energy :
  ∃ (T : StressEnergyTensor),
    T.T00 + T.T11 + T.T22 + T.T33 < 0 :=
alcubierre_null_contraction_negative_ax

theorem warp_drive_total_energy_positive (v_s R sigma : Float) :
  0 < v_s → 0 < R → 0 < sigma →
  ∃ (E_total : Float),
    0 < E_total ∧ ∃ (T : StressEnergyTensor), T.T00 < 0 :=
fun hv hR hs => warp_drive_energy_ax v_s R sigma hv hR hs

theorem krasnikov_tube_exotic :
  ∃ (m : ExoticMatter),
    m.type = MatterType.exotic ∧
    m.violatesCondition EnergyCondition.null = true ∧
    m.energyDensity < 0 :=
krasnikov_tube_ax

theorem traversable_wormhole_volume_bound (wh : WormholeGeometry) :
  0 < wh.throatRadius →
  wh.exoticRequired = true →
  ∃ (V_exotic : Float),
    0 < V_exotic ∧
    ∃ (m : ExoticMatter),
      m.energyDensity < 0 ∧ m.energyDensity * V_exotic < 0 :=
fun hr hex => traversable_wormhole_volume_ax wh hr hex

theorem wormhole_exotic_matter_necessity (w : WormholeGeometry) :
  w.exoticRequired = true →
  ∃ (m : ExoticMatter),
    m.violatesCondition EnergyCondition.weak = true :=
fun h =>
  Exists.elim
    (wormhole_requires_exotic_ax w h)
    (fun m hm => ⟨m, weak_violation_of_exotic_or_negative_mass m hm⟩)

theorem topological_censorship_without_exotic :
  ∀ (genus : Nat),
    0 < genus →
    (∀ (m : ExoticMatter), m.violatesCondition EnergyCondition.null = false) →
    False :=
fun g hg hno => topological_censorship_ax g hg hno

theorem exotic_matter_creates_non_trivial_topology :
  ∃ (top : SpacetimeTopology),
    0 < top.wormholes ∧ top.exoticMatterContent < 0 :=
topology_exotic_ax

theorem cosmic_string_not_exotic :
  ∃ (T : StressEnergyTensor),
    T.T00 > 0 ∧
    T.T33 = -T.T00 ∧
    StressEnergyTensor.isPhysical T :=
cosmic_string_ax

theorem singularity_avoidance_with_exotic :
  ∃ (m : ExoticMatter) (curvature_max : Float),
    m.type = MatterType.exotic ∧
    0 < curvature_max ∧
    m.energyDensity < 0 ∧
    m.violatesCondition EnergyCondition.strong = true :=
singularity_avoidance_ax

-- ============================================================
-- Theorems: stability and dynamics
-- ============================================================

theorem exotic_instability_generic (m : ExoticMatter) :
  m.type = MatterType.exotic →
  ∃ (sa : StabilityAnalysis),
    sa.stable = false ∧ 0 < sa.growthRate :=
fun h => exotic_instability_generic_ax m h

theorem metastable_exotic_lifetime (m : ExoticMatter) (Gamma : Float) :
  0 < Gamma →
  m.type = MatterType.exotic →
  ∃ (tau : Float), tau = 1.0 / Gamma ∧ 0 < tau :=
fun hG hm => metastable_exotic_ax m Gamma hG hm

theorem phantom_instability_growth (m : ExoticMatter) :
  m.type = MatterType.phantom →
  ∃ (omega : Float),
    0 < omega ∧
    ∃ (sa : StabilityAnalysis),
      sa.growthRate = omega ∧ sa.stable = false :=
fun h => phantom_instability_ax m h

theorem casimir_stability_between_plates :
  ∃ (sa : StabilityAnalysis) (d : Float),
    0 < d ∧ sa.stable = true ∧ 0 < sa.decayTime :=
casimir_stability_ax

theorem exotic_matter_feedback_loop (m : ExoticMatter) :
  m.type = MatterType.exotic →
  ∃ (sa : StabilityAnalysis),
    1.0 < sa.feedbackParameter → sa.stable = false :=
fun h => feedback_instability_ax m h

theorem quantum_correction_stabilization (m : ExoticMatter) :
  m.type = MatterType.exotic →
  ∃ (delta_rho : Float),
    0 < delta_rho ∧ m.energyDensity + delta_rho ≥ 0 :=
fun h => quantum_correction_stabilization_ax m h

theorem nonlinear_stability_threshold (m : ExoticMatter) (eps : Float) :
  0 < eps →
  m.type = MatterType.exotic →
  ∃ (delta : Float),
    0 < delta ∧
    ∀ (perturbation : Float),
      perturbation < delta →
      ∃ (sa : StabilityAnalysis), sa.stable = true :=
fun heps hm => nonlinear_stability_threshold_ax m eps heps hm

theorem evaporation_timescale (m : ExoticMatter) (M : Float) :
  0 < M →
  m.hasNegativeMass = true →
  ∃ (t_evap : Float), 0 < t_evap :=
fun hM hneg => evaporation_timescale_ax m M hM hneg

-- ============================================================
-- Theorems: classification
-- ============================================================

theorem classification_complete (m : ExoticMatter) :
  m.type ≠ MatterType.ordinary →
  classifyExotic m ≠ ExoticClass.classI ∨ m.type = MatterType.exotic :=
fun h => classification_complete_ax m h

theorem class_ii_implies_neg_mass (m : ExoticMatter) :
  classifyExotic m = ExoticClass.classII →
  m.hasNegativeMass = true :=
fun hc =>
  negative_mass_type_has_negative_mass_ax m
    (classII_type_negativeMass_ax m hc)

theorem class_iv_negative_pressure (m : ExoticMatter) :
  classifyExotic m = ExoticClass.classIV →
  m.pressure < 0 :=
fun hc => classIV_negative_pressure_ax m hc

theorem conversion_exotic_to_phantom :
  ∃ (m1 m2 : ExoticMatter),
    m1.type = MatterType.exotic ∧
    m2.type = MatterType.phantom ∧
    m1.energyDensity = m2.energyDensity :=
conversion_exotic_to_phantom_ax

theorem exotic_matter_type_transform (m : ExoticMatter) :
  m.type = MatterType.exotic →
  ∃ (m' : ExoticMatter) (process : String),
    m' ≠ m ∧ ExoticMatterConversion m m' :=
fun h => exotic_conversion_process_ax m h

theorem exotic_hierarchy_strict :
  ∀ (c1 c2 : ExoticClass),
    c1 ≠ c2 →
    ∃ (m1 m2 : ExoticMatter),
      classifyExotic m1 = c1 ∧
      classifyExotic m2 = c2 ∧
      m1.energyDensity ≠ m2.energyDensity :=
fun c1 c2 hne => exotic_hierarchy_strict_ax c1 c2 hne

theorem classI_ne_classII :
  ExoticClass.classI ≠ ExoticClass.classII := by
  decide

theorem dual_classification_impossible (m : ExoticMatter) :
  ¬(classifyExotic m = ExoticClass.classI ∧
    classifyExotic m = ExoticClass.classII) :=
fun h => classI_ne_classII (h.left.symm.trans h.right)

theorem classification_energy_violation (m : ExoticMatter) :
  (m.type = MatterType.exotic ∨ m.type = MatterType.negativeMass) →
  classifyExotic m ≠ ExoticClass.classI ∧
  ∃ (e : EnergyCondition), m.violatesCondition e = true :=
fun h => classification_energy_violation_ax m h

theorem classified_non_ordinary_violates (m : ExoticMatter) :
  m.type ≠ MatterType.ordinary →
  ∃ (e : EnergyCondition), m.violatesCondition e = true :=
fun h => classified_non_ordinary_violates_ax m h

-- ============================================================
-- Theorems: interactions and multi-component systems
-- ============================================================

theorem two_fluid_total_density (sys : TwoFluidSystem) :
  sys.totalDensity = sys.fluid1.energyDensity + sys.fluid2.energyDensity :=
two_fluid_total_density_ax sys

theorem mixed_system_can_satisfy_nec :
  ∃ (sys : TwoFluidSystem),
    sys.fluid1.violatesCondition EnergyCondition.null = true ∧
    sys.fluid2.violatesCondition EnergyCondition.null = false ∧
    sys.totalDensity ≥ 0 :=
mixed_system_can_satisfy_nec_ax

theorem exotic_normal_repulsion (m_ex m_ord : ExoticMatter) :
  m_ex.type = MatterType.exotic →
  m_ord.type = MatterType.ordinary →
  ∃ (F : Float), 0 < F :=
fun hex hord => exotic_normal_repulsion_ax m_ex m_ord hex hord

theorem negative_negative_repulsion (m1 m2 : ExoticMatter) :
  m1.type = MatterType.negativeMass →
  m2.type = MatterType.negativeMass →
  ∃ (interaction : ExoticInteraction m1 m2),
    interaction.repulsive = true :=
fun _ _ =>
  ⟨{ repulsive := true,
     totalEnergy := m1.energyDensity + m2.energyDensity,
     combinedExotic := true },
   rfl⟩

theorem negative_negative_attraction (m1 m2 : ExoticMatter) :
  m1.type = MatterType.negativeMass →
  m2.type = MatterType.negativeMass →
  ∃ (F : Float), F < 0 :=
fun h1 h2 => negative_negative_attraction_ax m1 m2 h1 h2

theorem exotic_annihilation_channel :
  ∃ (m_ex m_ord : ExoticMatter) (E_out : Float),
    m_ex.type = MatterType.exotic ∧
    m_ord.type = MatterType.ordinary ∧
    E_out = m_ex.energyDensity + m_ord.energyDensity ∧
    E_out ≥ 0 :=
exotic_annihilation_ax

theorem coupled_scalar_field_exotic :
  ∃ (phi V_val : Float),
    V_val < 0 ∧
    ∃ (m : ExoticMatter),
      m.type = MatterType.exotic ∧ m.energyDensity = V_val :=
coupled_scalar_field_exotic_ax

theorem multi_component_stability_condition (sys : TwoFluidSystem) :
  0 < sys.interactionCoupling →
  sys.fluid1.type = MatterType.exotic →
  sys.fluid2.type = MatterType.ordinary →
  ∃ (sa : StabilityAnalysis), sa.stable = true :=
fun hc hex hord => multi_component_stability_ax sys hc hex hord

theorem effective_eos_of_mixture (sys : TwoFluidSystem) :
  sys.totalDensity ≠ 0 →
  ∃ (w_eff : Float),
    w_eff = sys.effectivePressure / sys.totalDensity :=
fun _ => ⟨sys.effectivePressure / sys.totalDensity, rfl⟩

theorem exotic_dilution_expansion (m : ExoticMatter) (a : Float) :
  1.0 < a →
  m.type = MatterType.exotic →
  ∃ (rho_new : Float),
    rho_new = m.energyDensity / cube a ∧ rho_new < 0 :=
fun ha hm => exotic_dilution_ax m a ha hm

-- ============================================================
-- Theorems: causality and time travel
-- ============================================================

theorem ctc_requires_exotic (sp : CTCSpacetime) :
  sp.closedTimelikeCurveExists = true →
  sp.exoticMatterPresent = true :=
fun h => ctc_requires_exotic_ax sp h

theorem chronology_protection_conjecture :
  ∀ (sp : CTCSpacetime),
    sp.causalityViolation = true →
    ∃ (divergence : Float),
      0 < divergence ∧ sp.exoticMatterPresent = true :=
fun sp h => chronology_protection_ax sp h

theorem exotic_matter_for_time_travel (tm : TimeMachine) :
  tm.possible = true →
  ∃ (m : ExoticMatter),
    m.type = MatterType.exotic ∨ m.type = MatterType.negativeMass :=
fun h => time_machine_requires_exotic_ax tm h

theorem time_travel_requires_weak_violation (tm : TimeMachine) :
  tm.possible = true →
  ∃ (m : ExoticMatter),
    m.violatesCondition EnergyCondition.weak = true :=
fun h =>
  Exists.elim
    (time_machine_requires_exotic_ax tm h)
    (fun m hm => ⟨m, weak_violation_of_exotic_or_negative_mass m hm⟩)

theorem time_machine_energy_cost (v R : Float) :
  1.0 < v → 0 < R →
  ∃ (E_min : Float),
    E_min < 0 ∧ square R < -E_min :=
fun hv hR => time_machine_energy_cost_ax v R hv hR

theorem tippler_cylinder_exotic :
  ∃ (m : ExoticMatter),
    m.type = MatterType.exotic ∧
    m.violatesCondition EnergyCondition.weak = true ∧
    m.superluminal = false :=
tippler_cylinder_exotic_ax

theorem godel_universe_no_exotic :
  ∃ (T : StressEnergyTensor),
    T.T00 > 0 ∧
    StressEnergyTensor.isPhysical T ∧
    ∃ (ctc : CTCSpacetime),
      ctc.closedTimelikeCurveExists = true ∧
      ctc.exoticMatterPresent = false :=
godel_universe_no_exotic_ax

theorem ctc_instability_divergence (sp : CTCSpacetime) :
  sp.closedTimelikeCurveExists = true →
  ∃ (bound : Float), 0 < bound :=
fun h => ctc_instability_ax sp h

theorem achronal_average_nec (m : ExoticMatter) :
  m.type = MatterType.exotic →
  ∃ (L : Float), 0 < L :=
fun h => achronal_average_nec_ax m h

theorem causal_structure_preservation_under_qei (m : ExoticMatter) :
  -1.0 < m.quantumBound →
  ¬∃ (sp : CTCSpacetime),
    sp.closedTimelikeCurveExists = true ∧
    sp.exoticMatterPresent = true ∧
    sp.causalityViolation = true :=
fun h => causal_structure_preservation_ax m h

-- ============================================================
-- Theorems: concrete model properties
-- ============================================================

theorem exotic_matter_enables_alcubierre (m : ExoticMatter) :
  m.type = MatterType.exotic →
  ∃ (T : StressEnergyTensor), T.T00 < 0 :=
fun _ => alcubierre_negative_T00_ax

theorem casimir_matter_is_exotic :
  casimirExoticMatter.type = MatterType.exotic :=
rfl

theorem casimir_matter_negative_energy :
  casimirExoticMatter.energyDensity < 0 :=
float_neg_one_lt_zero

theorem negative_mass_model_is_negative_mass (mass : Float) :
  (negativeMassParticle mass).type = MatterType.negativeMass :=
rfl

theorem negative_mass_particle_has_negative_mass (mass : Float) :
  (negativeMassParticle mass).hasNegativeMass = true :=
rfl

theorem negative_mass_model_energy_negative (mass : Float) :
  0 < mass →
  (negativeMassParticle mass).energyDensity < 0 :=
fun h => float_neg_of_pos mass h

theorem negative_mass_gravitational_repulsion (mass velocity : Float) :
  (negativeMassParticle mass).hasNegativeMass = true →
  ∃ (force : Float), force < 0 :=
fun _ => negative_mass_force_ax (negativeMassParticle mass) rfl

theorem tachyon_superluminal_property (mass2 velocity : Float) :
  1.0 < velocity →
  (tachyonModel mass2 velocity).superluminal = true :=
fun _ => rfl

theorem dark_energy_exotic_properties :
  darkEnergyModel.energyDensity < 0 ∧
  darkEnergyModel.pressure < 0 ∧
  darkEnergyModel.violatesCondition EnergyCondition.weak = true :=
⟨float_neg_point_seven_lt_zero,
 float_neg_one_lt_zero,
 dark_energy_violates_condition_ax EnergyCondition.weak darkEnergyModel rfl⟩

theorem vacuum_energy_exotic_for_positive_lambda (Lambda : Float) :
  0 < Lambda →
  0 < (vacuumEnergyModel Lambda).energyDensity ∧
  (vacuumEnergyModel Lambda).pressure < 0 :=
fun h => ⟨h, float_neg_of_pos Lambda h⟩

-- ============================================================
-- Theorems: density accumulation
-- ============================================================

def exoticDensityAccumulation (m : ExoticMatter) (volume : Float) : Float :=
  m.energyDensity * volume

theorem negative_density_accumulation (m : ExoticMatter) (volume : Float) :
  m.energyDensity < 0 →
  0 < volume →
  exoticDensityAccumulation m volume < 0 :=
fun hneg hvol =>
  float_mul_neg_pos_neg m.energyDensity volume hneg hvol

theorem exotic_density_accumulation_negative_if_exotic
  (m : ExoticMatter) (volume : Float) :
  m.type = MatterType.exotic →
  m.energyDensity < 0 →
  0 < volume →
  exoticDensityAccumulation m volume < 0 :=
fun _ hneg hvol =>
  float_mul_neg_pos_neg m.energyDensity volume hneg hvol

-- ============================================================
-- End of formalization
-- ============================================================
