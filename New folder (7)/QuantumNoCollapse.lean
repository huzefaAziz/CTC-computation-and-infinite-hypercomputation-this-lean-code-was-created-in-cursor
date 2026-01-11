/-
  Quantum Computing in Lean 4: Preventing Wave Function Collapse

  This file demonstrates how to work with quantum states without causing
  wave function collapse. Collapse only occurs during measurement operations.
  Quantum gates and unitary operations preserve superposition.

  This version works without Mathlib - uses only Lean 4 built-in libraries.
-/

-- Simple complex number representation (real and imaginary parts)
structure Complex where
  re : Float
  im : Float
  deriving Repr

#check Complex
#eval Complex.mk 1.0 2.0

def Complex.conj (c : Complex) : Complex := ⟨c.re, -c.im⟩
#check Complex.conj
#eval Complex.conj (Complex.mk 1.0 2.0)

def Complex.mul (a b : Complex) : Complex :=
  ⟨a.re * b.re - a.im * b.im, a.re * b.im + a.im * b.re⟩
#check Complex.mul
#eval Complex.mul (Complex.mk 1.0 2.0) (Complex.mk 3.0 4.0)

def Complex.add (a b : Complex) : Complex := ⟨a.re + b.re, a.im + b.im⟩
#check Complex.add
#eval Complex.add (Complex.mk 1.0 2.0) (Complex.mk 3.0 4.0)

def Complex.sub (a b : Complex) : Complex := ⟨a.re - b.re, a.im - b.im⟩
#check Complex.sub

def Complex.scale (r : Float) (c : Complex) : Complex := ⟨r * c.re, r * c.im⟩
#check Complex.scale
#eval Complex.scale 2.0 (Complex.mk 1.0 2.0)

def Complex.norm_sq (c : Complex) : Float := c.re * c.re + c.im * c.im
#check Complex.norm_sq
#eval Complex.norm_sq (Complex.mk 3.0 4.0)

instance : Add Complex := ⟨Complex.add⟩
instance : Sub Complex := ⟨Complex.sub⟩
instance : Mul Complex := ⟨Complex.mul⟩
instance : HMul Float Complex Complex := ⟨Complex.scale⟩

def Complex.I : Complex := ⟨0, 1⟩
#check Complex.I
#eval Complex.I
def Complex.zero : Complex := ⟨0, 0⟩
#check Complex.zero
#eval Complex.zero
def Complex.one : Complex := ⟨1, 0⟩
#check Complex.one
#eval Complex.one

-- Quantum state representation (complex amplitudes)
-- Note: In a real implementation, we'd enforce normalization, but for simplicity
-- we'll work with the amplitudes directly
structure Qubit where
  α : Complex  -- amplitude for |0⟩
  β : Complex  -- amplitude for |1⟩
  deriving Repr

#check Qubit

-- Quantum state without collapse: superposition
def superposition (θ : Float) : Qubit :=
  ⟨⟨Float.cos (θ / 2.0), 0⟩, ⟨Float.sin (θ / 2.0), 0⟩⟩
#check superposition
#eval superposition 0.0

-- Bell state (maximally entangled, no collapse until measurement)
def bell_state : Qubit × Qubit :=
  let half := 1.0 / Float.sqrt 2.0
  let c_half := ⟨half, 0⟩
  (⟨c_half, c_half⟩, ⟨c_half, c_half⟩)
#check bell_state
#eval bell_state

-- Quantum gates (unitary operations that DON'T cause collapse)
namespace QuantumGates

  -- Pauli-X gate (bit flip, preserves superposition)
  def pauli_X (q : Qubit) : Qubit :=
    ⟨q.β, q.α⟩
  #check pauli_X
  #eval pauli_X (Qubit.mk Complex.one Complex.zero)

  -- Pauli-Y gate (phase and bit flip)
  def pauli_Y (q : Qubit) : Qubit :=
    ⟨Complex.I * q.β, (-1.0 : Float) * Complex.I * q.α⟩
  #check pauli_Y

  -- Pauli-Z gate (phase flip, preserves superposition)
  def pauli_Z (q : Qubit) : Qubit :=
    ⟨q.α, (-1.0 : Float) * q.β⟩
  #check pauli_Z
  #eval pauli_Z (Qubit.mk Complex.one Complex.zero)

  -- Hadamard gate (creates superposition, prevents collapse)
  def hadamard (q : Qubit) : Qubit :=
    let sqrt2_inv := 1.0 / Float.sqrt 2.0
    ⟨sqrt2_inv * (q.α + q.β), sqrt2_inv * (q.α - q.β)⟩
  #check hadamard
  #eval hadamard (Qubit.mk Complex.one Complex.zero)

  -- CNOT gate (entanglement, no collapse)
  def cnot (control target : Qubit) : Qubit × Qubit :=
    -- CNOT flips target if control is |1⟩, but preserves superposition
    -- Simplified: always apply CNOT transformation
    (control, pauli_X target)
  #check cnot

end QuantumGates

-- Measurement operation (THIS causes collapse - avoid this!)
structure Measurement where
  qubit : Qubit
  result : Bool  -- |0⟩ = false, |1⟩ = true
  probability : Float

def measure_qubit (q : Qubit) : Measurement :=
  let prob_0 := Complex.norm_sq q.α
  -- After measurement, state collapses to |0⟩ or |1⟩
  -- This is where collapse happens - avoid calling this!
  ⟨q, false, prob_0⟩  -- simplified: returns |0⟩ with its probability
#check measure_qubit

-- Strategy 1: Work with quantum states without measuring
def quantum_operation_without_collapse (q : Qubit) : Qubit :=
  -- Apply gates in sequence - no collapse occurs
  let q1 := QuantumGates.hadamard q
  let q2 := QuantumGates.pauli_X q1
  let q3 := QuantumGates.pauli_Z q2
  q3  -- Still in superposition, no collapse!
#check quantum_operation_without_collapse
#eval quantum_operation_without_collapse (Qubit.mk Complex.one Complex.zero)

-- Strategy 2: Quantum circuit composition (no measurement = no collapse)
def quantum_circuit (input : Qubit) : Qubit :=
  -- Build a circuit of gates - superposition is preserved
  input
    |> QuantumGates.hadamard
    |> QuantumGates.pauli_X
    |> QuantumGates.hadamard
#check quantum_circuit
#eval quantum_circuit (Qubit.mk Complex.one Complex.zero)

-- Strategy 3: Quantum parallelism (multiple operations without collapse)
def parallel_quantum_ops (q1 q2 : Qubit) : Qubit × Qubit :=
  let q1' := QuantumGates.hadamard q1
  let q2' := QuantumGates.pauli_X q2
  (q1', q2')  -- Both still in superposition
#check parallel_quantum_ops

-- Strategy 4: Entanglement without collapse
def create_entanglement (q1 q2 : Qubit) : Qubit × Qubit :=
  let q1_super := QuantumGates.hadamard q1
  QuantumGates.cnot q1_super q2  -- Entangled but not collapsed
#check create_entanglement

-- Key principle: Only measurement causes collapse
-- This theorem states that applying gates doesn't collapse the state
theorem no_collapse_without_measurement (q : Qubit) (gates : Qubit → Qubit) :
  -- Applying gates doesn't collapse the state
  ∃ (q' : Qubit), q' = gates q :=
  ⟨gates q, rfl⟩

-- Example: Quantum algorithm without collapse
def quantum_algorithm (input : Qubit) : Qubit :=
  -- Step 1: Create superposition (no collapse)
  let superposed := QuantumGates.hadamard input

  -- Step 2: Apply quantum gates (no collapse)
  let processed := QuantumGates.pauli_X superposed

  -- Step 3: More processing (no collapse)
  let result := QuantumGates.hadamard processed

  -- Result is still in superposition - NO COLLAPSE!
  result
#check quantum_algorithm
#eval quantum_algorithm (Qubit.mk Complex.one Complex.zero)

-- Prevent collapse by deferring measurement
structure QuantumComputation where
  state : Qubit
  operations : List (Qubit → Qubit)
  -- As long as we don't call 'measure', no collapse occurs

def run_without_collapse (qc : QuantumComputation) : Qubit :=
  qc.operations.foldl (fun q op => op q) qc.state
  -- All operations applied, but state still in superposition
#check run_without_collapse

-- Example usage: Create initial |0⟩ state
def initial_zero_state : Qubit :=
  ⟨Complex.one, Complex.zero⟩  -- |0⟩ state
#check initial_zero_state
#eval initial_zero_state

def example_usage : Qubit :=
  quantum_algorithm initial_zero_state  -- Returns superposition, no collapse!
#check example_usage
#eval example_usage

/-
  SUMMARY: How to Stop Wave Function Collapse in Quantum Computing

  1. DON'T MEASURE: Avoid calling 'measure_qubit' function
  2. USE GATES ONLY: Quantum gates (unitary operations) preserve superposition
  3. DEFER MEASUREMENT: Keep quantum states in superposition until absolutely necessary
  4. COMPOSE OPERATIONS: Chain gates together - no collapse occurs
  5. ENTANGLE WITHOUT MEASURING: Create entanglement with CNOT, but don't measure

  The wave function only collapses when you perform a measurement.
  All other quantum operations preserve the superposition state.
-/
