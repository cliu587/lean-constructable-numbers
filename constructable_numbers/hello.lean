import Mathlib.FieldTheory.IntermediateField
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.CubicDiscriminant
import Mathlib.Analysis.Complex.Polynomial
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.RootsOfUnity.Basic
import Mathlib.Data.Nat.Parity

noncomputable section

-- open scoped Classical Polynomial
open Polynomial

variable {F : Type} {E : Type}

inductive is_constructable_ℝ : ℝ → Prop
| base (a : ℚ) : is_constructable_ℝ (algebraMap ℚ  ℝ a)
| add (a b : ℝ) : is_constructable_ℝ a → is_constructable_ℝ b → is_constructable_ℝ (a+b)
| neg (a : ℝ) : is_constructable_ℝ a → is_constructable_ℝ (-a)
| mul (a b : ℝ) : is_constructable_ℝ a → is_constructable_ℝ b → is_constructable_ℝ (a*b)
| inv (a : ℝ) : is_constructable_ℝ a → is_constructable_ℝ a⁻¹
| rad (a : ℝ) (hn : n ≠ 0) : is_constructable_ℝ (a^2) → is_constructable_ℝ a

inductive is_constructable_ℂ : ℂ → Prop
| base (a : ℚ) : is_constructable_ℂ (algebraMap ℚ  ℂ a)
| add (a b : ℂ) : is_constructable_ℂ a → is_constructable_ℂ b → is_constructable_ℂ (a+b)
| neg (a : ℂ) : is_constructable_ℂ a → is_constructable_ℂ (-a)
| mul (a b : ℂ) : is_constructable_ℂ a → is_constructable_ℂ b → is_constructable_ℂ (a*b)
| inv (a : ℂ) : is_constructable_ℂ a → is_constructable_ℂ a⁻¹
| rad (a : ℂ) (hn : n ≠ 0) : is_constructable_ℂ (a^2) → is_constructable_ℂ a


def constructable : IntermediateField ℚ ℝ where
  carrier := is_constructable_ℝ
  mul_mem' := sorry
  add_mem' := sorry
  algebraMap_mem' := sorry
  neg_mem' := sorry
  inv_mem' := sorry

-- Unclear if needed...
theorem is_integral (a : constructable) : IsIntegral ℚ a := sorry

-- Proving statements about constructable numbers by induction
lemma induction (P : constructable → Prop)
(base : ∀ a : ℚ, P a)
(add : ∀ a b : constructable, P a → P b → P (a + b))
(neg : ∀ a : constructable, P a → P (-a))
(mul : ∀ a b : constructable, P a → P b → P (a * b))
(inv : ∀ a : constructable, P a → P a⁻¹)
(rad : ∀ a : constructable, P (a^2) → P a)
(a : constructable) : P a := sorry

def cbrt_two: ℝ := Real.rpow 2 (1/3)

def cbrt_two_is_integral : IsIntegral ℚ cbrt_two := sorry
-- Statement to be proved inductively.
-- Adjoin parentheses
-- \ ] )
-- \ ( [
def rank_pow_two_over_ℚ (a : constructable) : Prop := ∃(n: ℕ), FiniteDimensional.finrank ℚ ℚ⟮a.val⟯ = 2^n

-- If a number is constructable it sits in a field extension of rank 2^n
lemma constructable_implies_rank_pow_two_over_ℚ (a: constructable) : rank_pow_two_over_ℚ a := sorry

lemma cbrt_two_not_constructable: ¬is_constructable_ℝ cbrt_two := by
  intro h
  have c: constructable := ⟨_, h⟩

  -- (2^{1/3})^3 = 2, use later to justify 
  have cbrt_two_cubed_eq_2 : cbrt_two^(3: ℕ) = 2 := by 
    have two_nonneg: 0 ≤ (2: ℝ) := by norm_num
    rw[cbrt_two]
    norm_num
    rw [←Real.rpow_mul two_nonneg]
    norm_num

  have p: ℚ[X] := X^3 - 2
  -- X^3 is degree 3 and add -2
  have p_is_deg_three : p.natDegree = 3 := by sorry
  -- ?
  have irreducible_p : Irreducible p := by sorry
  -- Inspection?
  have monic_p : Monic p := by sorry
  -- Substitution
  have cbrt_two_evals_to_zero: Polynomial.eval₂ (algebraMap ℚ ℝ) (cbrt_two) (p) = 0 := by sorry

  have p_is_min_poly: p = minpoly ℚ cbrt_two := by apply minpoly.eq_of_irreducible_of_monic irreducible_p cbrt_two_evals_to_zero monic_p


  -- (2^{1/3})^3 = 2 -> [ℚ⟮2^{1/3}⟯: ℚ] = 3
  have ℚ_adj_cbrt_two_rank_eq_3 : FiniteDimensional.finrank ℚ ℚ⟮cbrt_two⟯ = 3 := by 
    rw[←p_is_deg_three]
    rw[p_is_min_poly]
    exact IntermediateField.adjoin.finrank cbrt_two_is_integral 


  have ℚ_adj_cbrt_two_rank_eq_two_pow : rank_pow_two_over_ℚ c := constructable_implies_rank_pow_two_over_ℚ c

  have ⟨n, pf_field_ext⟩ := ℚ_adj_cbrt_two_rank_eq_two_pow
  rw[pf_field_ext] at ℚ_adj_cbrt_two_rank_eq_3

  have even_two_n : Even (2^n) := by
    apply Nat.even_pow.mpr
    constructor
    · simp
    · 
      rw[Ne]
      intro nez
      rw[nez] at ℚ_adj_cbrt_two_rank_eq_3
      simp at ℚ_adj_cbrt_two_rank_eq_3

  have three_odd : Odd (3) := by simp
  have even_three : Even (3) := by 
    rw[← ℚ_adj_cbrt_two_rank_eq_3]
    exact even_two_n

  contradiction



-- Nonsense scratch below.
def cbrt_two_poly: ℚ[X] := X^3 - 2

def cbrt_two_poly_splits_in_ℂ: Splits (algebraMap ℚ ℂ) cbrt_two_poly := IsAlgClosed.splits_codomain (k:= ℂ) (K:= ℚ) (f:= algebraMap ℚ ℂ) cbrt_two_poly

-- TODO
def cbrt_two_poly_deg_nz: cbrt_two_poly.degree ≠ 0 := by
  rw[cbrt_two_poly]
  sorry



-- TODO: How to get cbrt(2): ℝ here?
def cbrt_two_roots := Polynomial.exists_root_of_splits (algebraMap ℚ ℂ) (cbrt_two_poly_splits_in_ℂ) (cbrt_two_poly_deg_nz)

-- TODO
def cbrt_two_poly_deg: cbrt_two_poly.natDegree = 3 := by
  rw[cbrt_two_poly]
  sorry

-- TODO (needed?)
def cbrt_two_poly_irred: Irreducible cbrt_two_poly := sorry

lemma cbrt_two_poly_degree_three (hx : Polynomial.aeval (a: ℂ) (cbrt_two_poly) = 0) : (minpoly ℚ a).natDegree = 3 := by
  sorry

theorem cbrt_two_not_constructable (hx : Polynomial.aeval (a: ℝ) (cbrt_two_poly) = 0):
  ¬(is_constructable_ℂ a) := by
  intro h
  have extension_property: deg_pow_two_extension ⟨a,h⟩ := by apply constructable' (cbrt_two_poly) ⟨a, h⟩ hx
  have ⟨n, nnez, deg_pf⟩ := extension_property
  have deg_pf' : (minpoly ℚ a).natDegree = 2^n := deg_pf

  -- Derive contradiction: a^3 = 2 so a = cbrt(2), but degree of min-poly of a is a power of 2.
  sorry
end

example (z : ℝ) (h : 0 ≤ z) : (z ^ (1/3 : ℝ)) ^ (3 : ℝ) = z :=
by
  rw [← Real.rpow_mul h]
  norm_num

example (h: ∀ (i: ℕ), i > 2 ∧ i > 3): ∀ i, i > 2 := by
  intro i
  exact (h i).left