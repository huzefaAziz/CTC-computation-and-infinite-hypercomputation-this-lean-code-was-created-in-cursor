/-- Closed Timelike Curve (CTC) using regular molecule-like structures --/

structure Point where
  x : Float
  y : Float
  z : Float
  t : Float  -- time coordinate
  deriving Repr, Inhabited

structure Molecule where
  position : Point
  velocity : Point  -- velocity vector (vx, vy, vz, vt = 1 for timelike)
  mass : Float
  deriving Repr, Inhabited

structure WorldLine where
  events : List Point
  deriving Repr, Inhabited

/-- Pi constant for Float calculations --/
def pi : Float := 3.14159265358979323846

/-- Check if a curve is timelike (spacetime interval < 0) --/
def isTimelike (p1 p2 : Point) : Bool :=
  let Δt := p2.t - p1.t
  let Δx := p2.x - p1.x
  let Δy := p2.y - p1.y
  let Δz := p2.z - p1.z
  let interval := Δt^2 - (Δx^2 + Δy^2 + Δz^2)
  interval > 0

/-- Check if a worldline forms a closed timelike curve --/
def isClosedTimelikeCurve (wl : WorldLine) : Bool :=
  match wl.events with
  | [] => false
  | [_] => false
  | points =>
    let first := points.head!
    let last := points.getLast!
    let isClosed := first.x == last.x && first.y == last.y &&
                    first.z == last.z && first.t == last.t
    if isClosed then
      let pairs := List.zip points (points.drop 1)
      pairs.all fun (p1, p2) => isTimelike p1 p2
    else
      false

/-- Create a regular molecule at a point --/
def createMolecule (pos : Point) (mass : Float) : Molecule :=
  {
    position := pos
    velocity := { x := 0.0, y := 0.0, z := 0.0, t := 1.0 }
    mass := mass
  }

/-- Generate a closed timelike curve using regular molecules --/
def createCTC (center : Point) (radius : Float) (steps : Nat) : WorldLine :=
  let steps_f : Float := steps.toFloat
  let angle_step := 2 * pi / steps_f
  let makePoint (i : Nat) : Point :=
    let i_f : Float := i.toFloat
    let angle := angle_step * i_f
    let t_offset := radius * Float.sin angle
    {
      x := center.x + radius * Float.cos angle
      y := center.y + radius * Float.sin angle
      z := center.z
      t := center.t + t_offset
    }
  let events := (List.range steps).map makePoint
  -- Close the curve by adding the starting point at the end
  match events with
  | [] => { events := [center] }
  | h :: _ => { events := events ++ [h] }

/-- Example usage: Create molecules along a CTC --/
def moleculesOnCTC (center : Point) (radius : Float) (steps : Nat) : List Molecule :=
  let ctc := createCTC center radius steps
  ctc.events.map fun point => createMolecule point 1.0

/-- Example: Simple closed timelike curve --/
def exampleCTC : WorldLine :=
  let center : Point := { x := 0.0, y := 0.0, z := 0.0, t := 0.0 }
  createCTC center 1.0 8

/-- Example: Molecules on the CTC --/
def exampleMolecules : List Molecule :=
  moleculesOnCTC { x := 0.0, y := 0.0, z := 0.0, t := 0.0 } 1.0 8

-- Type checks
#check Point
#check Molecule
#check WorldLine
#check isTimelike
#check isClosedTimelikeCurve
#check createMolecule
#check createCTC
#check moleculesOnCTC

-- Evaluation examples
#eval exampleCTC
#eval exampleMolecules

-- Additional checks and evaluations
#eval createMolecule { x := 1.0, y := 2.0, z := 3.0, t := 4.0 } 5.0
#eval isTimelike { x := 0.0, y := 0.0, z := 0.0, t := 0.0 } { x := 0.1, y := 0.1, z := 0.1, t := 1.0 }
#check exampleCTC
#check exampleMolecules
