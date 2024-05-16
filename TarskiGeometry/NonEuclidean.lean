import TarskiGeometry.Axioms
import Mathlib.Analysis.InnerProductSpace.PiL2

-- #check EuclideanSpace ℝ (Fin 2)

def hyperbolicPlane : Set (ℝ × ℝ) := {x : ℝ × ℝ | x.1^2 + x.2^2 < 1}
