import Mathlib.FieldTheory.IntermediateField
-- import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.CubicDiscriminant
import Mathlib.Analysis.Complex.Polynomial
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.RootsOfUnity.Basic
import Mathlib.Data.Nat.Parity
import Mathlib.Data.Real.Irrational

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

def cbrt_two_irrational: Irrational cbrt_two := by
  apply irrational_nrt_of_notint_nrt 3 2
  · 
    -- Issue with power rewriting, TODO
    sorry
  · rintro ⟨y, pf⟩
    -- cbrt_two has decimal, shouldn't be too impossible.
    sorry
  · norm_num


def p: ℚ[X] := X^3 - C 2

def p_is_deg_three : p.natDegree = 3 := by apply natDegree_X_pow_sub_C (n:=3) (r := 2)

def monic_p : Monic p := by
  apply leadingCoeff_X_pow_sub_C (by norm_num)

def p_nonzero: p ≠ 0 := by 
  apply Monic.ne_zero monic_p

-- Only TODO is the rewriting business.
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

-- TODO: No root means no linear factor...
lemma irreducible_of_not_root (f : ℚ[X]) (hfdeg : f.degree ≤ 3) (hf : ∀ x, f.eval x ≠ 0) :
  Irreducible f := sorry

-- Not sure how to prove yet...
def irreducible_p : Irreducible p := by 
  have p_leq_3 : p.degree ≤ 3 := by
    have p_deg_three : p.degree = 3 := by apply degree_X_pow_sub_C (by norm_num) (a := 2)
    exact le_of_eq p_deg_three

  -- Unclear how to prove this.
  have eval_nnz : ∀ x, p.eval x ≠ 0 := by
    intro x
    intro pxz 
    rw[p] at pxz
    apply Irrational.ne_rat cbrt_two_irrational x
    sorry

  apply irreducible_of_not_root p p_leq_3 eval_nnz

  -- Direct proof would be below.
  -- apply irreducible_iff.mpr
  -- constructor
  -- · 
  --   intro p_unit
  --   rw[p] at p_unit
  --   have x_cubed_deg_zero := natDegree_eq_zero_of_isUnit p_unit
  --   have x_cubed_deg_three := natDegree_X_pow_sub_C (n:=3) (r := (2: ℚ))
  --   rw[x_cubed_deg_three] at x_cubed_deg_zero
  --   contradiction
  -- · 
  --   intro p1 p2 h
  --   sorry

def p_is_min_poly: p = minpoly ℚ cbrt_two := by apply minpoly.eq_of_irreducible_of_monic irreducible_p cbrt_two_evals_to_zero monic_p


def cbrt_two_is_integral : IsIntegral ℚ cbrt_two := by
  refine Iff.mp isAlgebraic_iff_isIntegral ?_
  apply isAlgebraic_of_mem_rootSet (p:= X^3 - C 2) (x:= cbrt_two)
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