import Mathlib.Algebra.CubicDiscriminant
import Mathlib.FieldTheory.Adjoin

def hello := "world"

def xcubed_eq_2 : Cubic ℚ where
  a := 3
  b := 0
  c := 0
  d := 2


noncomputable def roots := Cubic.roots xcubed_eq_2

def my_field := IntermediateField.adjoin ℚ roots

noncomputable def xcubed_eq_2_poly := Cubic.toPoly xcubed_eq_2 


def q_field : Field ℚ := sorry

