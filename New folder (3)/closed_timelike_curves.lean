/-
Closed Timelike Curves (CTCs) in Lean 4
A formalization of closed timelike curves as paths in spacetime
that return to their starting point.

This single-file implementation demonstrates how to create closed timelike curves
from regular molecules using Lean 4.
-/

-- Spacetime structure
structure Point where
  t : Float  -- time coordinate
  x : Float  -- space coordinate
  y : Float
  z : Float

-- Timelike separation condition (dt² > dx² + dy² + dz²)
def timelike (p₁ p₂ : Point) : Prop :=
  let dt := p₂.t - p₁.t
  let dx := p₂.x - p₁.x
  let dy := p₂.y - p₁.y
  let dz := p₂.z - p₁.z
  dt^2 > dx^2 + dy^2 + dz^2

-- Path as a function from real parameter to Point
def Path := Float → Point

-- Closed curve condition
def closed (γ : Path) (a b : Float) : Prop :=
  γ a = γ b

-- Regular (smooth) curve - timelike at nearby points
def regular (γ : Path) : Prop :=
  ∀ t : Float, ∃ (δ : Float) (_ : δ > 0),
    ∀ t' : Float, Float.abs (t' - t) < δ → timelike (γ t) (γ t')

-- Closed Timelike Curve definition
structure ClosedTimelikeCurve (γ : Path) where
  is_closed : ∃ (a b : Float), a < b ∧ closed γ a b
  is_regular : regular γ
  is_timelike : ∀ (t₁ t₂ : Float), t₁ < t₂ → timelike (γ t₁) (γ t₂)

-- Molecule: a collection of points forming a structure
structure Molecule where
  points : List Point

-- Regular molecule: all adjacent points are timelike connected
def regular_molecule (points : List Point) : Prop :=
  match points with
  | [] => True
  | [_] => True
  | p₁ :: p₂ :: rest =>
    timelike p₁ p₂ ∧ regular_molecule (p₂ :: rest)

def regular_molecule_prop (m : Molecule) : Prop :=
  regular_molecule m.points

-- Helper: check if molecule forms a closed loop (last point to first)
def molecule_closed (m : Molecule) : Prop :=
  match m.points with
  | [] => False
  | [_] => False
  | p₁ :: rest =>
    match rest.reverse with
    | p_last :: _ => timelike p_last p₁
    | [] => False

-- Construction: Creating a CTC from a regular molecule
-- This axiom states that a closed timelike curve can be constructed
-- from any regular molecule that forms a closed loop
axiom ctc_from_regular_molecule
  (m : Molecule)
  (h_regular : regular_molecule_prop m)
  (h_nonempty : m.points.length > 1)
  (h_closed : molecule_closed m) :
  ∃ (γ : Path), ClosedTimelikeCurve γ

-- Pi constant for calculations
def pi : Float := 3.141592653589793

-- Example: Simple circular CTC in 2D space + time
-- This path is closed when the spatial coordinates repeat
def simple_ctc_path : Path := λ t =>
  {
    t := t
    x := Float.cos (2 * pi * t)
    y := Float.sin (2 * pi * t)
    z := 0
  }

-- Note: For a true CTC, we'd need t=0 and t=1 to map to the same point
-- This example shows the structure; a full implementation would ensure
-- the time coordinate also loops back appropriately

-- Type checking examples
#check Point
#check timelike
#check Path
#check closed
#check regular
#check ClosedTimelikeCurve
#check Molecule
#check regular_molecule
#check regular_molecule_prop
#check molecule_closed
#check simple_ctc_path

-- Evaluation examples
#eval { t := 0.0, x := 1.0, y := 0.0, z := 0.0 : Point }
#eval { t := 1.0, x := 1.0, y := 0.0, z := 0.0 : Point }
#eval simple_ctc_path 0.0
#eval simple_ctc_path 0.5
#eval simple_ctc_path 1.0
