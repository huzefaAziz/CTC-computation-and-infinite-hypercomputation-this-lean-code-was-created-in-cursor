import Mathlib

/-!
# Formalisation of Todd A. Brun, "Computers with closed timelike curves can solve hard problems"

Source: arXiv:gr-qc/0209061v1 (18 September 2002), sections 1--5.

This file formalises the paper's mathematical/computational model.  It does NOT prove
that closed timelike curves exist, that a physical CTC computer can be built, or that
the proposed complexity-theoretic speedups are physically achievable.

Important fidelity note:
* The first factoring program tests `p > 1` before accepting a returned factor.
* The recursive helper as printed tests `(p = 0) OR (N mod p = 0)` while its register
  is initialised to `-1`.  The literal arithmetic makes `-1` divide every integer,
  and `p = 0` is accepted unconditionally.  Those lines therefore do not express the
  surrounding prose's intended "a correct answer came back" test.

The literal tests are retained below and their edge cases are proved.  The intended
self-consistent computation is then represented separately with `Option Nat`: `none`
means no message arrived, while `some p` is accepted only when `p` is a valid factor.
This makes the modelling choice explicit rather than silently repairing the source.
-/

set_option autoImplicit false

namespace BrunCTC

/-! ## 1. The CTC register and `timeSet` -/

abbrev Tick := Nat

/-- The paper's register is an integer-valued register. -/
abbrev PaperRegister := Int

/-- `timeSet(t, x)`: replace the register value at the earlier tick `t` by `x`. -/
def timeSet (history : Tick → PaperRegister) (t : Tick) (x : PaperRegister) :
    Tick → PaperRegister :=
  fun t' => if t' = t then x else history t'

@[simp] theorem timeSet_at (history : Tick → PaperRegister) (t : Tick)
    (x : PaperRegister) :
    timeSet history t x t = x := by
  simp [timeSet]

/-- The literal initial value used in the paper's programs. -/
def initialTimeRegister : PaperRegister := -1

/-- The first program's factor test: `p > 1` and `N mod p = 0`.
    Divisibility is used as the exact mathematical form of the modulo test. -/
def firstProgramGate (N : Nat) (p : PaperRegister) : Prop :=
  1 < p ∧ p ∣ (N : Int)

theorem firstProgram_rejects_initial_sentinel (N : Nat) :
    ¬ firstProgramGate N initialTimeRegister := by
  simp [firstProgramGate, initialTimeRegister]

/-- The recursive helper's gate, translated literally from
    `(p = 0) OR (N mod p = 0)`. -/
def recursiveHelperGate (N : Nat) (p : PaperRegister) : Prop :=
  p = 0 ∨ p ∣ (N : Int)

/-- The literal `p = 0` arm accepts zero without checking the interval. -/
theorem recursiveHelper_accepts_zero (N : Nat) :
    recursiveHelperGate N 0 := by
  exact Or.inl rfl

/-- In integer arithmetic, `-1` divides every integer.  Thus the literal recursive
    helper gate also accepts the paper's initial register value. -/
theorem recursiveHelper_accepts_initial_sentinel (N : Nat) :
    recursiveHelperGate N initialTimeRegister := by
  right
  change ∃ q : Int, (N : Int) = (-1 : Int) * q
  exact ⟨-(N : Int), by ring⟩

/-- The main recursive program on page 5 tests only `N mod p = 0`.
    This is again divisibility, and so it accepts `p = -1`. -/
def recursiveMainGate (N : Nat) (p : PaperRegister) : Prop :=
  p ∣ (N : Int)

theorem recursiveMain_accepts_initial_sentinel (N : Nat) :
    recursiveMainGate N initialTimeRegister := by
  change ∃ q : Int, (N : Int) = (-1 : Int) * q
  exact ⟨-(N : Int), by ring⟩

/-! ## 2. Ordinary factoring and the recursive interval search -/

/-- A proper factor candidate in an inclusive search interval. -/
def FactorInRange (N lo hi p : Nat) : Prop :=
  lo ≤ p ∧ p ≤ hi ∧ 1 < p ∧ p ∣ N

/-- The bottom-level exhaustive search from the paper.
    `Nat.find` selects the least witness, matching the increasing trial loop.
    This is a noncomputable specification of the finite search. -/
noncomputable def bruteForce (N lo hi : Nat) :
    Option {p : Nat // FactorInRange N lo hi p} := by
  classical
  by_cases h : ∃ p, FactorInRange N lo hi p
  · exact some ⟨Nat.find h, Nat.find_spec h⟩
  · exact none

/-- The finite bottom-level search succeeds exactly when the interval contains
    a factor.  Soundness is carried by the subtype returned by `bruteForce`. -/
theorem bruteForce_complete (N lo hi : Nat) :
    (bruteForce N lo hi).isSome ↔ ∃ p, FactorInRange N lo hi p := by
  classical
  by_cases h : ∃ p, FactorInRange N lo hi p
  · simp [bruteForce, h]
  · simp [bruteForce, h]

/-- Section 1's non-recursive trial-division program: search from `2` through
    `sqrt N`; return `N` if no proper divisor is found. -/
noncomputable def directFactorProgram (N : Nat) : Nat :=
  match bruteForce N 2 (Nat.sqrt N) with
  | some q => q.val
  | none => N

/-- The direct program always returns a divisor greater than one for `N ≥ 2`.
    When the input is composite, the finite search is over its possible
    nontrivial factors; when no such factor is found, the program returns `N`. -/
theorem directFactorProgram_is_factor (N : Nat) (hN : 2 ≤ N) :
    1 < directFactorProgram N ∧ directFactorProgram N ∣ N := by
  unfold directFactorProgram
  cases hSearch : bruteForce N 2 (Nat.sqrt N) with
  | none =>
      simpa [hSearch] using
        (show 1 < N ∧ N ∣ N from ⟨by omega, dvd_rfl⟩)
  | some q =>
      simpa [hSearch] using
        (show 1 < q.val ∧ q.val ∣ N from
          ⟨q.property.2.2.1, q.property.2.2.2⟩)

/-- Recursive interval factoring from section 2.

    The paper writes the midpoint as `(nStart + nEnd) / 2`.  The expression
    `lo + (hi - lo) / 2` is equal to it when `lo ≤ hi` and makes the interval
    measure explicit.  The return type carries a proof that any returned value
    is in the requested interval and divides `N`.
-/
noncomputable def recursiveFactor (N lo hi nTractable : Nat)
    (hTractable : 0 < nTractable) :
    Option {p : Nat // FactorInRange N lo hi p} := by
  classical
  by_cases hSmall : hi - lo < nTractable
  · exact bruteForce N lo hi
  ·
    let mid := lo + (hi - lo) / 2
    have hGap : 0 < hi - lo := by omega
    have hLoLeHi : lo ≤ hi := by omega
    have hLoLeMid : lo ≤ mid := by
      dsimp [mid]
      omega
    have hMidLtHi : mid < hi := by
      dsimp [mid]
      omega
    exact
      match recursiveFactor N lo mid nTractable hTractable with
      | some q =>
          some ⟨q.val, by
            rcases q.property with ⟨hLo, hMid, hGreater, hDivides⟩
            exact ⟨hLo, le_trans hMid (Nat.le_of_lt hMidLtHi), hGreater, hDivides⟩
          ⟩
      | none =>
          match recursiveFactor N (mid + 1) hi nTractable hTractable with
          | some q =>
              some ⟨q.val, by
                rcases q.property with ⟨hMid, hHi, hGreater, hDivides⟩
                have hLoMidSucc : lo ≤ mid + 1 := by omega
                exact ⟨le_trans hLoMidSucc hMid, hHi, hGreater, hDivides⟩
              ⟩
          | none => none
termination_by hi - lo
decreasing_by
  all_goals
    simp_wf
    omega

/-- The paper's outer program searches `[2, sqrt N]` and returns `N` if no
    nontrivial divisor is found (the prime-number case in the paper). -/
noncomputable def recursiveFactorAnswer (N nTractable : Nat)
    (hTractable : 0 < nTractable) : Nat :=
  match recursiveFactor N 2 (Nat.sqrt N) nTractable hTractable with
  | some q => q.val
  | none => N

/-- Regardless of whether the interval search finds a proper divisor, the outer
    program returns a divisor greater than one: either the found divisor or `N`. -/
theorem recursiveFactorAnswer_is_factor (N nTractable : Nat)
    (hTractable : 0 < nTractable) (hN : 2 ≤ N) :
    1 < recursiveFactorAnswer N nTractable hTractable ∧
      recursiveFactorAnswer N nTractable hTractable ∣ N := by
  unfold recursiveFactorAnswer
  cases hSearch : recursiveFactor N 2 (Nat.sqrt N) nTractable hTractable with
  | none =>
      simpa [hSearch] using
        (show 1 < N ∧ N ∣ N from ⟨by omega, dvd_rfl⟩)
  | some q =>
      simpa [hSearch] using
        (show 1 < q.val ∧ q.val ∣ N from
          ⟨q.property.2.2.1, q.property.2.2.2⟩)

/-! ## 3. Self-consistency and the CTC factoring argument -/

/-- A valid answer to the factoring task.  As in the paper, `N` itself is the
    returned answer when no proper divisor exists. -/
def ValidFactorAnswer (N p : Nat) : Prop :=
  1 < p ∧ p ∣ N

/-- Intended prose-level behaviour of the CTC factoring program:
    accept a valid factor received from the future; otherwise run the ordinary
    search and send that answer back with `timeSet`. -/
noncomputable def ctcFactorStep (N : Nat) (futureRegister : Option Nat)
    (computedAnswer : Nat) : Option Nat := by
  classical
  exact match futureRegister with
  | none => some computedAnswer
  | some p =>
      if ValidFactorAnswer N p then some p else some computedAnswer

/-- A self-consistent register is a fixed point of the program's update rule. -/
def SelfConsistent {α : Type} (update : α → α) (state : α) : Prop :=
  update state = state

/-- The fixed-point argument used by the paper: when the ordinary search would
    return a valid answer, a self-consistent CTC register cannot be empty or
    contain an invalid candidate.  It must already contain a valid answer, so
    the search branch is skipped. -/
theorem selfConsistent_ctc_has_factor (N computedAnswer : Nat)
    (hComputed : ValidFactorAnswer N computedAnswer)
    (futureRegister : Option Nat)
    (hSelf : SelfConsistent (fun future => ctcFactorStep N future computedAnswer) futureRegister) :
    ∃ p, futureRegister = some p ∧ ValidFactorAnswer N p := by
  cases futureRegister with
  | none =>
      simp [SelfConsistent, ctcFactorStep] at hSelf
  | some p =>
      by_cases hFactor : ValidFactorAnswer N p
      · exact ⟨p, rfl, hFactor⟩
      · have hEq : p = computedAnswer := by
          have hEq' : computedAnswer = p := by
            apply Option.some.inj
            simpa [SelfConsistent, ctcFactorStep, hFactor] using hSelf
          exact hEq'.symm
        subst p
        exact ⟨computedAnswer, rfl, hComputed⟩

/-- The preceding fixed-point theorem applies to the recursive factoring result. -/
theorem recursive_ctc_factor_is_valid (N nTractable : Nat)
    (hTractable : 0 < nTractable) (hN : 2 ≤ N)
    (futureRegister : Option Nat)
    (hSelf : SelfConsistent
      (fun future => ctcFactorStep N future (recursiveFactorAnswer N nTractable hTractable))
      futureRegister) :
    ∃ p, futureRegister = some p ∧ ValidFactorAnswer N p := by
  apply selfConsistent_ctc_has_factor
  · exact recursiveFactorAnswer_is_factor N nTractable hTractable hN
  · exact hSelf

/-! ## 4. SAT: exhaustive assignment search and recursive splitting -/

/-- A Boolean formula is represented by its evaluator on bit strings.
    For the paper, the evaluator is the conjunction of the CNF clauses `φ`. -/
abbrev BooleanFormula := List Bool → Prop

/-- SAT for an `n`-bit assignment. -/
def SAT (n : Nat) (φ : BooleanFormula) : Prop :=
  ∃ bits, bits.length = n ∧ φ bits

/-- Split an `(n+1)`-bit SAT instance according to its first bit.
    This is the recursive search over the two halves of the assignment space. -/
theorem SAT_split_first_bit (n : Nat) (φ : BooleanFormula) :
    SAT (n + 1) φ ↔
      SAT n (fun xs => φ (false :: xs)) ∨
      SAT n (fun xs => φ (true :: xs)) := by
  constructor
  · rintro ⟨bits, hLength, hSatisfies⟩
    cases bits with
    | nil => simp at hLength
    | cons bit rest =>
        cases bit
        · left
          exact ⟨rest, by simpa using hLength, hSatisfies⟩
        · right
          exact ⟨rest, by simpa using hLength, hSatisfies⟩
  · rintro (⟨rest, hLength, hSatisfies⟩ | ⟨rest, hLength, hSatisfies⟩)
    · exact ⟨false :: rest, by simp [hLength], hSatisfies⟩
    · exact ⟨true :: rest, by simp [hLength], hSatisfies⟩

/-! ## 5. Quantified SAT (QSAT / QBF) -/

inductive Quantifier where
  | existsQ
  | forallQ
  deriving DecidableEq, Repr

/-- Alternating quantifier prefix, starting with `exists`:
    `∃ x₁ ∀ x₂ ∃ x₃ ∀ x₄ ...`. -/
def alternatingQuantifiers : Quantifier → Nat → List Quantifier
  | _, 0 => []
  | .existsQ, Nat.succ n => .existsQ :: alternatingQuantifiers .forallQ n
  | .forallQ, Nat.succ n => .forallQ :: alternatingQuantifiers .existsQ n

/-- Evaluate a quantified prefix.  Existential quantifiers become disjunctions;
    universal quantifiers become conjunctions.  Variables are appended in order. -/
def evalPrefix (φ : BooleanFormula) : List Quantifier → List Bool → Prop
  | [], assignment => φ assignment
  | .existsQ :: rest, assignment =>
      evalPrefix φ rest (assignment ++ [false]) ∨
      evalPrefix φ rest (assignment ++ [true])
  | .forallQ :: rest, assignment =>
      evalPrefix φ rest (assignment ++ [false]) ∧
      evalPrefix φ rest (assignment ++ [true])

/-- Moving an already fixed prefix into the formula leaves the remaining
    quantified evaluation unchanged. -/
theorem evalPrefix_append (φ : BooleanFormula) (qs : List Quantifier)
    (fixedPrefix suffix : List Bool) :
    evalPrefix φ qs (fixedPrefix ++ suffix) =
      evalPrefix (fun xs => φ (fixedPrefix ++ xs)) qs suffix := by
  induction qs generalizing suffix with
  | nil =>
      simp [evalPrefix]
  | cons q qs ih =>
      cases q <;> simp [evalPrefix, List.append_assoc, ih]

theorem evalPrefix_at_prefix (φ : BooleanFormula) (qs : List Quantifier)
    (fixedPrefix : List Bool) :
    evalPrefix φ qs fixedPrefix =
      evalPrefix (fun xs => φ (fixedPrefix ++ xs)) qs [] := by
  simpa using evalPrefix_append φ qs fixedPrefix []

/-- The alternating quantified satisfiability problem for `n` variables. -/
def QSAT (n : Nat) (φ : BooleanFormula) : Prop :=
  evalPrefix φ (alternatingQuantifiers .existsQ n) []

/-- Brun's equation (3): after fixing the first two variables, the remaining
    QSAT instances have two fewer variables:

      QSAT(φ) = (QSAT(φ00) ∧ QSAT(φ01)) ∨ (QSAT(φ10) ∧ QSAT(φ11)).
-/
theorem QSAT_two_variable_recurrence (n : Nat) (φ : BooleanFormula) :
    QSAT (n + 2) φ ↔
      (QSAT n (fun xs => φ (false :: false :: xs)) ∧
       QSAT n (fun xs => φ (false :: true :: xs))) ∨
      (QSAT n (fun xs => φ (true :: false :: xs)) ∧
       QSAT n (fun xs => φ (true :: true :: xs))) := by
  simp only [QSAT, alternatingQuantifiers, evalPrefix]
  simp only [List.nil_append, List.cons_append]
  rw [evalPrefix_at_prefix φ (alternatingQuantifiers .existsQ n)
        [false, false]]
  rw [evalPrefix_at_prefix φ (alternatingQuantifiers .existsQ n)
        [false, true]]
  rw [evalPrefix_at_prefix φ (alternatingQuantifiers .existsQ n)
        [true, false]]
  rw [evalPrefix_at_prefix φ (alternatingQuantifiers .existsQ n)
        [true, true]]
  all_goals rfl

/-- The paper assumes an even number of variables for its alternating QSAT
    example.  This wrapper expresses that convention directly. -/
def QSATEven (pairs : Nat) (φ : BooleanFormula) : Prop :=
  QSAT (2 * pairs) φ

/-! ## 6. Complexity-theoretic scope of the paper's argument

The paper argues that the same CTC/fixed-point construction can be applied to
SAT (hence to NP via reductions) and to alternating quantified SAT (QSAT/QBF,
a PSPACE-complete problem).  The definitions and recurrence above formalise the
Boolean search structure.  They do not, by themselves, formalise polynomial-time
reductions for every language in NP/PSPACE, a machine-cost model, or a theorem
that NP or PSPACE collapses in ordinary computation.  Those claims are conditional
on the paper's CTC computation assumptions.
-/

/-! ## 7. Quantum considerations

The paper discusses (without proving) Hawking's chronology-protection conjecture,
Deutsch's many-worlds treatment of CTC consistency, and the possibility that
other quantum effects could obstruct the algorithm.  These are recorded as
alternative hypotheses, not asserted as Lean theorems.
-/

/-- The chronology-protection hypothesis: CTCs do not occur. -/
def ChronologyProtectionHypothesis (CTCsExist : Prop) : Prop :=
  ¬ CTCsExist

/-- A Deutsch-style consistency condition is a fixed point of the evolution map. -/
def DeutschConsistency {State : Type} (evolution : State → State)
    (state : State) : Prop :=
  evolution state = state

/-! ## 8. Conclusion encoded as a conditional statement

Under a deterministic update rule, and assuming a self-consistent register value,
the fixed-point theorem above says that the program's register contains a valid
factor answer.  This is a theorem about the abstract model, not about the existence
or stability of physical CTCs.
-/

end BrunCTC
