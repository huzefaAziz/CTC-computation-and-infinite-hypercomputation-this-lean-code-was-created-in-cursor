import Mathlib

/-!
# Closed Timelike Curves in Relativistic Computation

Lean 4 formalization scaffold for:

  Hajnal Andreka, Istvan Nemeti, Gergely Szekely,
  "Closed Timelike Curves in Relativistic Computation",
  arXiv:1105.0047v1 (30 April 2011).

This file formalizes the paper's logical structure and its central wormhole
signal-timing argument.  The paper is a research article in general relativity,
not a list of mathematical lemmas; therefore geometric and physical facts that
are not derived here are represented explicitly as model hypotheses/fields.

In particular, this file is NOT a derivation of wormholes or CTCs from Einstein's
field equations.  It also does not prove that the required spacetime, infinite
computer, or physical resources exist.  Those are assumptions discussed by the
paper, not consequences of the elementary timing argument below.

The model uses an integer-indexed worldline for an abstract spacetime and real
numbers for the wormhole timing calculation.  The integer-indexed worldline is
a formal abstraction of an indefinitely extendible timelike curve.
-/

namespace RelativisticComputation

/-! ## 1. CTCs and Malament–Hogarth spacetimes -/

/--
An abstract spacetime model.

`ctc_causality` records the causal property used in the paper's statement that
a spacetime containing a CTC is a Malament–Hogarth spacetime: every point on
the closed timelike curve lies in the causal past of its chosen anchor event.
This is an explicit spacetime assumption, not a theorem about arbitrary
relations `timelike` and `causallyPrecedes`.
-/
structure AbstractSpacetime where
  Event : Type
  timelike : Event → Event → Prop
  causallyPrecedes : Event → Event → Prop
  ctc_causality :
    ∀ (γ : ℤ → Event),
      (∀ t : ℤ, timelike (γ t) (γ (t + 1))) →
      (∃ period : ℤ, 0 < period ∧ ∀ t : ℤ, γ (t + period) = γ t) →
      ∀ t : ℤ, causallyPrecedes (γ t) (γ 0)

/-- A timelike curve that closes after a positive parameter period. -/
def IsClosedTimelikeCurve (S : AbstractSpacetime)
    (γ : ℤ → S.Event) : Prop :=
  (∀ t : ℤ, S.timelike (γ t) (γ (t + 1))) ∧
  (∃ period : ℤ, 0 < period ∧ ∀ t : ℤ, γ (t + period) = γ t)

/--
The discrete abstraction of a Malament–Hogarth spacetime: an event has an
indefinitely extendible timelike curve in its causal past.
-/
def IsMalamentHogarthSpacetime (S : AbstractSpacetime) : Prop :=
  ∃ observer : S.Event, ∃ γ : ℤ → S.Event,
    (∀ t : ℤ, S.timelike (γ t) (γ (t + 1))) ∧
    (∀ t : ℤ, S.causallyPrecedes (γ t) observer)

/-- Paper's cited implication: every spacetime containing a CTC is MH. -/
theorem every_ctc_spacetime_is_mh
    (S : AbstractSpacetime)
    (hCTC : ∃ γ : ℤ → S.Event, IsClosedTimelikeCurve S γ) :
    IsMalamentHogarthSpacetime S := by
  obtain ⟨γ, hγ⟩ := hCTC
  rcases hγ with ⟨hTimelike, hPeriod⟩
  refine ⟨γ 0, γ, hTimelike, ?_⟩
  intro t
  exact S.ctc_causality γ hTimelike hPeriod t

/-! ### The infinite-search example (ZF consistency) -/

/--
Abstract model of the paper's search through proofs for a contradiction.
`hasContradiction` means that a contradiction is derivable in the chosen
formal system. `emitsSignal` means that the search detects it and sends the
signal. `signalCorrect` is the completeness/correctness condition for this
idealized search procedure.
-/
structure ContradictionSearch where
  hasContradiction : Prop
  emitsSignal : Prop
  signalCorrect : emitsSignal ↔ hasContradiction

/-- In this model, consistency means that no contradiction is derivable. -/
def IsConsistent (C : ContradictionSearch) : Prop :=
  ¬ C.hasContradiction

/-- The programmer receives no contradiction signal. -/
def ReceivesNoSignal (C : ContradictionSearch) : Prop :=
  ¬ C.emitsSignal

/-- The central no-signal/consistency equivalence used by the paper. -/
theorem no_signal_iff_consistent (C : ContradictionSearch) :
    ReceivesNoSignal C ↔ IsConsistent C := by
  constructor
  · intro hNoSignal hContradiction
    exact hNoSignal (C.signalCorrect.mpr hContradiction)
  · intro hConsistent hSignal
    exact hConsistent (C.signalCorrect.mp hSignal)

/--
The experiment decides consistency by observation; it does not derive a
consistency proof inside the same axiom system.  This reflects the paper's
footnote concerning Gödel's second incompleteness theorem.
-/
theorem no_signal_tells_programmer_consistent
    (C : ContradictionSearch)
    (hNoSignal : ReceivesNoSignal C) : IsConsistent C :=
  (no_signal_iff_consistent C).mp hNoSignal

/-! ## 2–3. Computer heaps, space, and the black-hole constraint -/

/--
A linear heap model: `n` copies of a fixed-size computer have total mass
proportional to `n`, and are separated at a fixed distance so that the heap
radius is also proportional to `n`.

`schwarzschildFactor * mass ≤ radius` is the abstract safety inequality.  The
paper uses proportionality to explain how repeated computers may avoid their
combined Schwarzschild radius overtaking the heap radius.
-/
structure LinearComputerHeap where
  schwarzschildFactor : ℝ
  massPerComputer : ℝ
  spacingPerComputer : ℝ
  spacing_safe : schwarzschildFactor * massPerComputer ≤ spacingPerComputer

def LinearComputerHeap.totalMass (H : LinearComputerHeap) (n : ℕ) : ℝ :=
  (n : ℝ) * H.massPerComputer

def LinearComputerHeap.heapRadius (H : LinearComputerHeap) (n : ℕ) : ℝ :=
  (n : ℝ) * H.spacingPerComputer

def LinearComputerHeap.IsSafe (H : LinearComputerHeap) : Prop :=
  ∀ n : ℕ,
    H.schwarzschildFactor * H.totalMass n ≤ H.heapRadius n

/-- Fixed mass and fixed spacing give a safe linear heap under `spacing_safe`. -/
theorem linear_heap_is_safe (H : LinearComputerHeap) : H.IsSafe := by
  intro n
  have hn : 0 ≤ (n : ℝ) := by positivity
  have h := mul_le_mul_of_nonneg_left H.spacing_safe hn
  simpa [LinearComputerHeap.totalMass, LinearComputerHeap.heapRadius,
    mul_assoc, mul_comm, mul_left_comm] using h

/--
Example 2 abstraction: non-parallel identifications produce unbounded
separation while the computer's speed remains fixed and below light speed.
The geometric construction itself is not encoded in this record.
-/
structure ExampleTwoLayout where
  separation : ℕ → ℝ
  computerSpeed : ℝ
  lightSpeed : ℝ
  speed_nonnegative : 0 ≤ computerSpeed
  speed_bounded : computerSpeed ≤ lightSpeed
  separation_unbounded : ∀ bound : ℝ, ∃ n : ℕ, bound < separation n

/--
Example 3 abstraction: a finite-width strip cannot accommodate a computation
whose required spatial extent is unbounded.
-/
structure ExampleThreeLayout where
  stripWidth : ℝ
  requiredSpace : ℕ → ℝ
  requiredSpace_unbounded : ∀ bound : ℝ, ∃ n : ℕ, bound < requiredSpace n

theorem example_three_cannot_fit_unbounded_computation
    (E : ExampleThreeLayout) :
    ¬ (∀ n : ℕ, E.requiredSpace n ≤ E.stripWidth) := by
  intro hFits
  obtain ⟨n, hn⟩ := E.requiredSpace_unbounded E.stripWidth
  exact (not_le_of_gt hn) (hFits n)

/--
A capacity is unbounded when it can exceed every finite requested step count.
-/
def HasUnboundedStepCapacity (capacity : ℕ) : Prop :=
  ∀ bound : ℕ, ∃ n : ℕ, bound < n ∧ n ≤ capacity

/-- A finite step capacity cannot support arbitrarily many computation steps. -/
theorem finite_capacity_is_not_unbounded (capacity : ℕ) :
    ¬ HasUnboundedStepCapacity capacity := by
  intro h
  obtain ⟨n, hAbove, hWithinCapacity⟩ := h capacity
  omega

/--
Example 1 abstraction: a fixed-size computer is assigned a finite step
capacity.  The paper does not give a numerical capacity; it argues that fixing
computer size bounds its computational power.
-/
structure ExampleOneLayout where
  fixedComputerSize : ℝ
  fixedComputerSizePositive : 0 < fixedComputerSize
  finiteStepCapacity : ℕ

theorem example_one_is_not_hypercomputational
    (E : ExampleOneLayout) :
    ¬ HasUnboundedStepCapacity E.finiteStepCapacity :=
  finite_capacity_is_not_unbounded E.finiteStepCapacity

/-! ## 4. The wormhole signal mechanism -/

/--
The two timing quantities in Examples 4 and 5:

* `mouthTimeDelay`: the temporal offset between the wormhole mouths;
* `returnTravelTime`: the time needed for the signal to travel back from mouth
  B to mouth A (including the reflection leg represented by the model).

The key hypothesis is exactly the paper's inequality:
`returnTravelTime < mouthTimeDelay`.
-/
structure WormholeSetup where
  mouthTimeDelay : ℝ
  returnTravelTime : ℝ
  delay_exceeds_return : returnTravelTime < mouthTimeDelay

/-- Net amount by which one complete signal cycle moves the signal to the past. -/
def WormholeSetup.rewindAmount (W : WormholeSetup) : ℝ :=
  W.mouthTimeDelay - W.returnTravelTime

/-- One full wormhole/reflection cycle applied to a signal's time coordinate. -/
def WormholeSetup.rewindOnce (W : WormholeSetup) (t : ℝ) : ℝ :=
  t - W.rewindAmount

/-- The time coordinate after `n` repeated wormhole/reflection cycles. -/
def WormholeSetup.rewindAfter (W : WormholeSetup) (initialTime : ℝ) : ℕ → ℝ
  | 0 => initialTime
  | n + 1 => W.rewindAfter initialTime n - W.rewindAmount

theorem WormholeSetup.rewindAmount_pos (W : WormholeSetup) :
    0 < W.rewindAmount := by
  dsimp [WormholeSetup.rewindAmount]
  linarith [W.delay_exceeds_return]

/-- Closed form for the repeated signal time. -/
theorem WormholeSetup.rewindAfter_formula
    (W : WormholeSetup) (initialTime : ℝ) (n : ℕ) :
    W.rewindAfter initialTime n =
      initialTime - (n : ℝ) * W.rewindAmount := by
  induction n with
  | zero => simp [WormholeSetup.rewindAfter]
  | succ n ih =>
      simp [WormholeSetup.rewindAfter, ih]
      ring

/-- Every positive number of cycles sends the signal strictly earlier. -/
theorem WormholeSetup.rewindAfter_strictly_earlier
    (W : WormholeSetup) (initialTime : ℝ) {n : ℕ} (hn : 0 < n) :
    W.rewindAfter initialTime n < initialTime := by
  rw [W.rewindAfter_formula]
  have hnReal : 0 < (n : ℝ) := by exact_mod_cast hn
  have hprod : 0 < (n : ℝ) * W.rewindAmount :=
    mul_pos hnReal W.rewindAmount_pos
  linarith

/--
The key timing theorem: repeated cycles can place the signal before any chosen
lower time bound.  This is the mathematical core of Example 4.
-/
theorem WormholeSetup.rewindBefore_any_time
    (W : WormholeSetup) (emissionTime lowerBound : ℝ) :
    ∃ n : ℕ, W.rewindAfter emissionTime n < lowerBound := by
  have hgap : 0 < W.rewindAmount := W.rewindAmount_pos
  obtain ⟨n, hn⟩ :=
    exists_nat_gt ((emissionTime - lowerBound) / W.rewindAmount)
  have hmul : emissionTime - lowerBound < (n : ℝ) * W.rewindAmount :=
    (div_lt_iff₀ hgap).mp hn
  refine ⟨n, ?_⟩
  rw [W.rewindAfter_formula]
  linarith

/-- Example 4: an earlier mouth and a later mouth in the cut-and-paste model. -/
structure ExampleFourCutAndPaste where
  earlierMouthTime : ℝ
  laterMouthTime : ℝ
  mouthOrder : earlierMouthTime < laterMouthTime

/--
Example 5: the twin-paradox construction is represented by a mouth time offset
large enough to exceed the signal travel time.  Relativity's time-dilation
calculation is an input assumption (`h`), not derived by this definition.
-/
def twinParadoxWormhole
    (timeDilation signalTravelTime : ℝ)
    (h : signalTravelTime < timeDilation) : WormholeSetup :=
  { mouthTimeDelay := timeDilation
    returnTravelTime := signalTravelTime
    delay_exceeds_return := h }

/-! ### The complete idealized hypercomputer -/

/--
The paper's proposed architecture: the computer remains outside the CTC region;
only the contradiction/result signal is routed through the wormhole.
-/
structure WormholeHypercomputer where
  wormhole : WormholeSetup
  search : ContradictionSearch
  computer_stays_outside_ctc : Prop
  only_result_signal_uses_ctc : Prop

/-- If a contradiction signal is emitted, enough wormhole cycles put it before
any specified initialization time. -/
theorem contradiction_signal_can_reach_before_initialization
    (H : WormholeHypercomputer) (emissionTime initializationTime : ℝ)
    (_hSignal : H.search.emitsSignal) :
    ∃ n : ℕ,
      H.wormhole.rewindAfter emissionTime n < initializationTime :=
  H.wormhole.rewindBefore_any_time emissionTime initializationTime

/--
The idealized experiment's decision rule.  The left side is the observable
outcome; the right side is consistency in the search model.
-/
theorem wormhole_experiment_decides_consistency
    (H : WormholeHypercomputer) :
    (¬ H.search.emitsSignal) ↔ ¬ H.search.hasContradiction :=
  no_signal_iff_consistent H.search

/-! ## 5–6. Physical interpretation and the blueshift discussion -/

/--
Route-level statement corresponding to the paper's design choice.  It records
that the computer itself does not enter the CTC region; only the result signal
does.  It is not a proof that a traversable wormhole exists.
-/
def UsesSignalOnlyArchitecture (H : WormholeHypercomputer) : Prop :=
  H.computer_stays_outside_ctc ∧ H.only_result_signal_uses_ctc

/--
The paper's blueshift point is specific: its wormhole setup avoids the
Kerr–Newman black-hole hypercomputation route associated with the familiar
blueshift difficulty.  This marker deliberately does not claim a general
physical theorem that every frequency shift in every wormhole is bounded.
-/
structure BlueshiftScope where
  usesKerrNewmanInterior : Prop
  avoidsKerrNewmanInterior : ¬ usesKerrNewmanInterior

theorem wormhole_route_avoids_kerr_newman_interior
    (B : BlueshiftScope) : ¬ B.usesKerrNewmanInterior :=
  B.avoidsKerrNewmanInterior

/--
Physical caveat from Section 6: the paper treats macroscopic wormholes and
methods for creating them as speculative.  The formal model does not assume
that they have been observed or that a construction method is known.
-/
structure WormholePhysicalStatus where
  wormholesExistInUniverse : Prop
  knownCreationMethod : Prop

/-! ## 7. Repeatability and the infinite-space allocation -/

/-- The total fraction of the universe reserved by the paper's allocation. -/
noncomputable def repeatabilityBudget : ℝ := 1 / 1_000_000

/-- Remaining budget after `n` computers, halved at each successive step. -/
noncomputable def remainingBudget (n : ℕ) : ℝ :=
  repeatabilityBudget / (2 : ℝ) ^ n

/-- Cumulative fraction used after `n` allocation steps. -/
noncomputable def usedBudget (n : ℕ) : ℝ :=
  repeatabilityBudget - remainingBudget n

theorem remaining_budget_nonnegative (n : ℕ) :
    0 ≤ remainingBudget n := by
  dsimp [remainingBudget, repeatabilityBudget]
  positivity

theorem used_budget_never_exceeds_total (n : ℕ) :
    usedBudget n ≤ repeatabilityBudget := by
  dsimp [usedBudget]
  have h := remaining_budget_nonnegative n
  linarith

theorem used_budget_is_strictly_below_total (n : ℕ) :
    usedBudget n < repeatabilityBudget := by
  dsimp [usedBudget]
  have h : 0 < remainingBudget n := by
    dsimp [remainingBudget, repeatabilityBudget]
    positivity
  linarith

/-- The first allocation is 1/2,000,000 of the universe, as in Section 7. -/
theorem first_allocation_matches_paper :
    usedBudget 1 = 1 / 2_000_000 := by
  norm_num [usedBudget, remainingBudget, repeatabilityBudget]

/-! ## 8. Faster-than-light motion and CTCs -/

/--
Logical form of the paper's result: if time travel using FTL observers is
possible, then time travel is possible without relying on those observers.
This is represented as an explicit theorem-hypothesis supplied by the
relativistic model under study.
-/
structure FasterThanLightResult where
  timeTravelWithFTLObservers : Prop
  timeTravelWithoutFTLObservers : Prop
  ftl_does_not_add_time_travel :
    timeTravelWithFTLObservers → timeTravelWithoutFTLObservers

theorem ftl_observers_do_not_add_time_travel
    (R : FasterThanLightResult)
    (h : R.timeTravelWithFTLObservers) :
    R.timeTravelWithoutFTLObservers :=
  R.ftl_does_not_add_time_travel h

/--
The paper's dimension-dependent discussion is recorded as labels, not proved
from a coordinate model here: (1+1), (1+3), and the conjectural (3+3) case.
-/
inductive SpacetimeDimensionCase
  | onePlusOne
  | onePlusThree
  | threePlusThree
  deriving DecidableEq, Repr

/-! ## 9. Main conclusion in the formal model -/

/--
If the wormhole delay exceeds the return travel time, the result signal can be
moved before an arbitrary lower time bound.  If no contradiction signal is
emitted, the search model declares the axiom system consistent.
-/
theorem paper_core_conclusion
    (H : WormholeHypercomputer)
    (emissionTime initializationTime : ℝ) :
    (∃ n : ℕ,
      H.wormhole.rewindAfter emissionTime n < initializationTime) ∧
    ((¬ H.search.emitsSignal) ↔ ¬ H.search.hasContradiction) := by
  constructor
  · exact H.wormhole.rewindBefore_any_time emissionTime initializationTime
  · exact no_signal_iff_consistent H.search

end RelativisticComputation
