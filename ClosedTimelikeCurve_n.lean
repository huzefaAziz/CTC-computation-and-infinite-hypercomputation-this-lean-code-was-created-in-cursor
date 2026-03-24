/-!
# Closed timelike curves (minimal layer, no Mathlib)

Built only from small “molecular” pieces: a type of events, a binary
“timelike step” relation, finite indexed paths, and the predicates
*timelike path* and *closed*. A **closed timelike curve** is a timelike
path that returns to its starting event with at least one nontrivial step.

This is a **discrete** model (no `Real`, no manifolds): it matches the
idea of a causal loop in a spacetime discretization or a causal-set style
picture, and compiles with the standard Lean prelude alone.
-/

variable {M : Type}

/-- One timelike step from `a` to `b` according to `γ`. -/
abbrev TimelikeStep (γ : M → M → Prop) (a b : M) : Prop :=
  γ a b

/-- `p` is a timelike path of `n` steps (so `n + 1` vertices). -/
def PathTimelike {n : Nat} (γ : M → M → Prop) (p : Fin (n + 1) → M) : Prop :=
  ∀ i : Fin n, γ (p i.castSucc) (p i.succ)

/-- The path closes: last vertex equals the first. -/
def PathClosed {n : Nat} (p : Fin (n + 1) → M) : Prop :=
  p 0 = p (Fin.last n)

/-- A nontrivial closed timelike curve: timelike, closed, and at least one step. -/
def IsClosedTimelikeCurve {n : Nat} (γ : M → M → Prop) (p : Fin (n + 1) → M) : Prop :=
  PathTimelike γ p ∧ PathClosed p ∧ n > 0

/-!
### Tiny example: three events in a causal triangle
-/

inductive Atom : Type
  | a | b | c

/-- Timelike edges `a → b → c → a` (a discrete CTC). -/
def causalStep : Atom → Atom → Prop
  | .a, .b => True
  | .b, .c => True
  | .c, .a => True
  | _, _   => False

def causalLoop : Fin 4 → Atom
  | ⟨0, _⟩ => .a
  | ⟨1, _⟩ => .b
  | ⟨2, _⟩ => .c
  | ⟨3, _⟩ => .a

private theorem path_timelike_triangle : PathTimelike causalStep causalLoop := by
  intro i
  match i with
  | ⟨0, _⟩ => trivial
  | ⟨1, _⟩ => trivial
  | ⟨2, _⟩ => trivial

private theorem path_closed_triangle : PathClosed causalLoop := rfl

theorem exists_closed_timelike_curve :
    IsClosedTimelikeCurve causalStep causalLoop :=
  ⟨path_timelike_triangle, path_closed_triangle, Nat.succ_pos _⟩
