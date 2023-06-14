import Mathlib.FieldTheory.IntermediateField
import Mathlib.Algebra.CubicDiscriminant
import Mathlib.Analysis.Complex.Polynomial
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.RootsOfUnity.Basic
import Mathlib.Data.Nat.Parity
import Mathlib.Data.Real.Irrational

-- https://leanprover.zulipchat.com/#narrow/stream/287929-mathlib4/topic/!4.234085
local macro_rules | `($x ^ $y)   => `(HPow.hPow $x $y)

noncomputable section

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

def cbrt_two: ℝ := Real.rpow (2: ℝ) (3⁻¹: ℝ)
def cbrt_two_cubed_eq_2 : (cbrt_two)^(3: ℕ) = 2 := by 
  have two_nn: 0 ≤ (2: ℝ) := by norm_num
  have three_nz: (3: ℕ) ≠ (0) := by norm_num
  have cbrt_cubed_rw: ((2:ℝ) ^ ((3:ℝ)⁻¹)) ^ (3: ℕ) = 2 := by
    have tmp := Real.rpow_nat_inv_pow_nat two_nn three_nz
    dsimp at tmp
    exact tmp
  rw[cbrt_two];dsimp; rw[cbrt_cubed_rw]

def p: ℚ[X] := X^3 - C 2

def p_is_deg_three : p.natDegree = 3 := by apply natDegree_X_pow_sub_C (n:=3) (r := 2)

def monic_p : Monic p := by
  apply leadingCoeff_X_pow_sub_C (by norm_num)

def p_nonzero: p ≠ 0 := by 
  apply Monic.ne_zero monic_p

def cbrt_two_evals_to_zero: eval₂ (algebraMap ℚ ℝ) (cbrt_two) (p) = 0 := by 
  have pow_cubed := eval₂_X_pow (n:=3) (R:= ℚ) (S:= ℝ) (algebraMap ℚ ℝ)
  have x_cubed_cbrt_two_eq_two : eval₂ (algebraMap ℚ ℝ) cbrt_two (X ^ 3) = 2:= by
    have := pow_cubed cbrt_two
    rw[cbrt_two_cubed_eq_2] at this
    exact this
    
  have two_c : eval₂ (algebraMap ℚ ℝ) cbrt_two (C 2) = 2 := by apply eval₂_C

  have x_cubed_minus_two_eq_zero: eval₂ (algebraMap ℚ ℝ) cbrt_two (X ^ 3 - C 2) = 0 := by 
    have := eval₂_sub (algebraMap ℚ ℝ) (x:= cbrt_two) (R := ℚ) (S := ℝ) (p := X^3) (q := C 2)
    rw[x_cubed_cbrt_two_eq_two, two_c, sub_self 2] at this; exact this

  apply x_cubed_minus_two_eq_zero

-- TODO
def irreducible_p: Irreducible p := by sorry


-- Gauss' Lemma doesn't seem ported: cannot reduce to Z irreducibility.
def irreducible_p_eisenstein: Irreducible p := by
  -- have p_is_eisenstein : IsEisensteinAt p (2) (R := ℤ):= sorry
  sorry

-- Perhaps promising but not sure how to prove
-- Uses the fact that cbrt_two is irrational so eval x (X^3-2) ≠ 0
-- for any rational x
def irreducible_p_not_linear_factor: Irreducible p := by 

  have cbrt_two_irrational: Irrational cbrt_two := by
    apply irrational_nrt_of_notint_nrt 3 2
    · rw[cbrt_two_cubed_eq_2]; rfl
    · rintro ⟨y, pf⟩
      -- Prove false from cbrt_two = (y: ℤ)
      -- cbrt_two has decimal, shouldn't be too impossible.
      sorry
    · norm_num

  -- No root of a degree ≤ 3 polynomial means no linear factor. 
  -- Probably will use Polynomial.Monic.irreducible_iff_natDegree' ?
  have irreducible_of_not_root (f : ℚ[X]) (hfdeg : f.degree ≤ 3) (hf : ∀ x, ¬(f.eval x = 0)) : Irreducible f := sorry

  have p_leq_3 : p.degree ≤ 3 := by
    have p_deg_three : p.degree = 3 := degree_X_pow_sub_C (by norm_num) (a := 2)
    exact le_of_eq p_deg_three

  -- Unclear how to prove this.
  have eval_nnz : ∀ x, ¬(p.eval x = 0) := by
    intro x
    by_contra pxz

    rw[p] at pxz
    have is_root : IsRoot p x := pxz
    have pxz' : eval x ((X^3): ℚ[X]) = 2 := by 
      -- apply eval_add (p:=pxz) (q := C (2:ℚ)) (x := x)
      sorry
    let cbrt_two_roots := nthRoots 3 (2: ℚ)
    have zero_le_three: 0 < 3 := by norm_num
    have x_in_cbrt_two_roots : x ∈ cbrt_two_roots := by
      apply (mem_nthRoots (zero_le_three)).mpr
      rw[←pxz']
      simp
    
    have cbrt_two_ne_x := Irrational.ne_rat cbrt_two_irrational x (x := cbrt_two)

    sorry
  apply irreducible_of_not_root p p_leq_3 eval_nnz

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


-- Type of proposition constructable numbers satisfies that cbrt_two does not.
def rank_pow_two_over_ℚ (a : constructable) : Prop := ∃(n: ℕ), FiniteDimensional.finrank ℚ ℚ⟮a.val⟯ = 2^n

-- If a number is constructable it sits in a field extension of rank 2ⁿ (to be proven)
lemma constructable_implies_rank_pow_two_over_ℚ (a: constructable) : rank_pow_two_over_ℚ a := sorry

-- Main theorem
theorem cbrt_two_not_constructable: ¬is_constructable_ℝ cbrt_two := by
  by_contra h
  let c : constructable := ⟨_, h⟩
  -- [ℚ⟮cbrt_two⟯: ℚ] = 3
  have ℚ_adj_cbrt_two_rank_eq_3 : FiniteDimensional.finrank ℚ ℚ⟮cbrt_two⟯ = 3 := by 
    rw[←p_is_deg_three, p_is_min_poly]
    exact IntermediateField.adjoin.finrank cbrt_two_is_integral 

  have ℚ_adj_cbrt_two_rank_eq_two_pow : rank_pow_two_over_ℚ c := constructable_implies_rank_pow_two_over_ℚ c

  -- [ℚ(cbrt_two) : ℚ] = 2^n along with proof 
  have ⟨(n: ℕ), pf_rank_pow_2_ext⟩ := ℚ_adj_cbrt_two_rank_eq_two_pow
  rw[pf_rank_pow_2_ext] at ℚ_adj_cbrt_two_rank_eq_3

  have even_two_n : Even (2^n) := by
    apply Nat.even_pow.mpr; constructor
    · exact Nat.even_iff.mpr rfl
    · by_contra nez
      rw[nez] at ℚ_adj_cbrt_two_rank_eq_3
      contradiction

  have even_three : Even (3) := by 
    rw[← ℚ_adj_cbrt_two_rank_eq_3]
    exact even_two_n

  contradiction