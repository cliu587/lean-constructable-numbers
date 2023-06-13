import Mathlib.FieldTheory.IntermediateField
-- import Mathlib.Analysis.SpecialFunctions.Pow.Real
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
def cbrt_two_cubed_eq_2 : (cbrt_two)^3 = 2 := by 
  have two_nonneg: 0 ≤ (2: ℝ) := by norm_num
  rw[cbrt_two]; norm_num
  rw [←Real.rpow_mul two_nonneg]; norm_num

def p: ℚ[X] := X^3 - 2

def p_is_deg_three : p.natDegree = 3 := by apply natDegree_X_pow_sub_C (n:=3) (r := (2: ℚ))

def monic_p : Monic p := by
  apply leadingCoeff_X_pow_sub_C (by norm_num)

def p_nonzero: p ≠ 0 := by 
  apply Monic.ne_zero monic_p

def cbrt_two_evals_to_zero: eval₂ (algebraMap ℚ ℝ) (cbrt_two) (p) = 0 := by 
  have pow_cubed := eval₂_X_pow (n:=3) (R:= ℚ) (S:= ℝ) (algebraMap ℚ ℝ)
  have pow_cubed_cbrt_two := pow_cubed cbrt_two
  -- TODO: something problematic with power maps, but below should work after fixing type issues
  -- rw[cbrt_two_cubed_eq_2] at pow_cubed_cbrt_two
  -- TODO: This should be by substitution as well
  have x_cubed_cbrt_two_eq_two : eval₂ (algebraMap ℚ ℝ) cbrt_two (X ^ 3) = 2 := by sorry

  have two_c : eval₂ (algebraMap ℚ ℝ) cbrt_two (C 2) = 2 := by apply eval₂_C

  have x_cubed_minus_two_eq_zero: eval₂ (algebraMap ℚ ℝ) cbrt_two (X ^ 3 - C 2) = 0 := by 
    have tmp := eval₂_sub (algebraMap ℚ ℝ) (x:= cbrt_two) (R := ℚ) (S := ℝ) (p := X^3) (q := C 2)
    rw[x_cubed_cbrt_two_eq_two, two_c, sub_self 2] at tmp
    exact tmp

  apply x_cubed_minus_two_eq_zero

def irreducible_p : Irreducible p := by 
  sorry

def p_is_min_poly: p = minpoly ℚ cbrt_two := by apply minpoly.eq_of_irreducible_of_monic irreducible_p cbrt_two_evals_to_zero monic_p


def cbrt_two_is_integral : IsIntegral ℚ cbrt_two := by
  refine Iff.mp isAlgebraic_iff_isIntegral ?_
  apply isAlgebraic_of_mem_rootSet (p:= X^3 - 2) (x:= cbrt_two)
  · refine Iff.mpr mem_rootSet ?_
    constructor
    · apply p_nonzero
    · 
      rw[←p, p_is_min_poly]
      simp


-- Proposition to be proved inductively.
def rank_pow_two_over_ℚ (a : constructable) : Prop := ∃(n: ℕ), FiniteDimensional.finrank ℚ ℚ⟮a.val⟯ = 2^n

-- If a number is constructable it sits in a field extension of rank 2^n (to be proven)
lemma constructable_implies_rank_pow_two_over_ℚ (a: constructable) : rank_pow_two_over_ℚ a := sorry

lemma cbrt_two_not_constructable: ¬is_constructable_ℝ cbrt_two := by
  intro h
  let c : constructable := ⟨_, h⟩
  -- (2^{1/3})^3 = 2, use later to justify p is monic

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