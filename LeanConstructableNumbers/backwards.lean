import Mathlib.FieldTheory.IntermediateField
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.RingTheory.RootsOfUnity.Basic
import Mathlib.RingTheory.Polynomial.GaussLemma

-- https://leanprover.zulipchat.com/#narrow/stream/287929-mathlib4/topic/!4.234085
-- Otherwise coersion problems with a ^ b
local macro_rules | `($x ^ $y)   => `(HPow.hPow $x $y)

noncomputable section

open Polynomial FiniteDimensional

-- https://github.com/leanprover-community/mathlib4/pull/5069 !!
-- Hot off the presses two days ago.
lemma gauss_lemma {p: ℤ[X]} (hp: IsPrimitive p): Irreducible p ↔ Irreducible (map (algebraMap ℤ ℚ) p) := IsPrimitive.Int.irreducible_iff_irreducible_map_cast hp

-- This file defines ∛2, p(x) = x³-2, and prove p(x) is the minimal polynomial over ℚ of ∛2.
def cbrt_two: ℂ := Real.rpow (2: ℝ) (3⁻¹: ℝ)
def cbrt_two_cubed_eq_2 : (cbrt_two)^(3: ℕ) = 2 := by 
  have two_nn: 0 ≤ (2: ℝ) := by norm_num
  have three_nz: (3: ℕ) ≠ (0) := by norm_num
  have cbrt_cubed_rw: ((2:ℝ) ^ ((3:ℝ)⁻¹)) ^ (3: ℕ) = 2 := by
    have tmp := Real.rpow_nat_inv_pow_nat two_nn three_nz
    rw [Nat.cast_ofNat] at tmp; assumption

  rw[cbrt_two, Real.rpow_eq_pow]
  norm_cast

-- Prove x^3-2 is the minimal polynomial of ∛2 over ℚ and that [ℚ(∛2):ℚ] = 3
-- For that, we need p irreducible AND ∛2 is a root of p AND p monic 
def p: ℚ[X] := X^3 - C 2

def p_is_deg_three : p.natDegree = 3 := natDegree_X_pow_sub_C (n:=3) (r := 2)

def p_monic : Monic p := leadingCoeff_X_pow_sub_C (by norm_num)

def p_nonzero: p ≠ 0 := Monic.ne_zero p_monic

def cbrt_two_evals_to_zero: eval₂ (algebraMap ℚ ℂ) (cbrt_two) (p) = 0 := by 
  have pow_cubed := eval₂_X_pow (n:=3) (R:= ℚ) (S:= ℂ) (algebraMap ℚ ℂ)
  have x_cubed_cbrt_two_eq_two : eval₂ (algebraMap ℚ ℂ) cbrt_two (X ^ 3) = 2:= by
    have := pow_cubed cbrt_two
    rwa[cbrt_two_cubed_eq_2] at this
    
  have two_c : eval₂ (algebraMap ℚ ℂ) cbrt_two (C 2) = 2 := by rw [eval₂_C]; norm_num

  have x_cubed_minus_two_eq_zero: eval₂ (algebraMap ℚ ℂ) cbrt_two (X ^ 3 - C 2) = 0 := by 
    have := eval₂_sub (algebraMap ℚ ℂ) (x:= cbrt_two) (R := ℚ) (S := ℂ) (p := X^3) (q := C 2)
    rwa[x_cubed_cbrt_two_eq_two, two_c, sub_self 2] at this

  assumption

def p_irreducible: Irreducible p := by
  -- Show p_z irreducible then apply Gauss
  let p_z: ℤ[X] := X^3 - C 2 
  have p_z_eq_p : map (algebraMap ℤ ℚ) p_z = p := by 
    rw[p]; simp only [algebraMap_int_eq, map_ofNat, Polynomial.map_sub, Polynomial.map_pow, map_X, Polynomial.map_ofNat]
  rw[←p_z_eq_p]

  have p_z_natDeg_eq_3 : p_z.natDegree = 3 := natDegree_X_pow_sub_C

  have p_z_primitive : IsPrimitive p_z := by
    have three_nez: 3 ≠ 0 := by norm_num
    have : Monic p_z := monic_X_pow_sub_C (2: ℤ) (three_nez)
    apply this.isPrimitive

  let ideal_2: Ideal ℤ := Ideal.span ({(2: ℤ)})

  have ideal_2_prime: Ideal.IsPrime ideal_2 := by
    have two_irred: Irreducible (2: ℤ) := PrincipalIdealRing.irreducible_iff_prime.mpr (Int.prime_two)
    have two_maximal := by apply PrincipalIdealRing.isMaximal_of_irreducible (two_irred)
    exact Ideal.IsMaximal.isPrime two_maximal

  -- (X^3 - 2): ℤ[X] irreducible by Eisenstein
  have p_z_irred : Irreducible p_z := by
    have p_is_eisenstein : IsEisensteinAt p_z ideal_2 := by
      constructor
      · intro h;
        have zero_lt_3 : 0 < 3 := by norm_num
        have leading_coeff_one : leadingCoeff ((X^3 - C 2): ℤ[X]) = 1 := leadingCoeff_X_pow_sub_C (zero_lt_3)
        rw[leading_coeff_one] at h
        have : 2 ∣ 1 := Ideal.mem_span_singleton.mp h
        contradiction
      · intro pow pow_lt_deg;
        rw[p_z_natDeg_eq_3] at pow_lt_deg
        simp only [map_ofNat, coeff_sub]
        interval_cases pow
        · 
          have l1: coeff (X^3: ℤ[X]) 0 = 0 := by apply coeff_X_pow 3
          have l2: coeff 2 0 = (2: ℤ) := coeff_C_zero
          rw[l1,l2]; simp only [zero_sub, neg_mem_iff]; exact Ideal.mem_span_singleton_self 2
        · 
          have l1: coeff (X^3: ℤ[X]) 1 = 0 := by apply coeff_X_pow 3
          have l2: coeff 2 1 = (0: ℤ) := coeff_C_ne_zero (one_ne_zero)
          rw[l1,l2]; simp only [sub_self, Submodule.zero_mem]
        · 
          have l1: coeff (X^3: ℤ[X]) 2 = 0 := by apply coeff_X_pow 3
          have l2: coeff 2 2 = (0: ℤ) := coeff_C_ne_zero (two_ne_zero)
          rw[l1,l2]; simp only [sub_self, Submodule.zero_mem]
      · 
        rw[Ideal.span_singleton_pow]
        norm_num
        by_contra two_in_4_ideal
        have : coeff (X^3: ℤ[X]) 0 = 0 := by apply coeff_X_pow 3
        rw[this] at two_in_4_ideal
        have : coeff 2 0 = (2: ℤ) := coeff_C_zero
        rw[this] at two_in_4_ideal
        norm_num at two_in_4_ideal
        have : 4 ∣ 2 := Ideal.mem_span_singleton.mp two_in_4_ideal
        contradiction
    apply p_is_eisenstein.irreducible
    · exact ideal_2_prime
    · exact p_z_primitive
    · rw[p_z_natDeg_eq_3]; norm_num
    
  exact (gauss_lemma p_z_primitive).mp p_z_irred

lemma p_is_min_poly: p = minpoly ℚ cbrt_two := minpoly.eq_of_irreducible_of_monic p_irreducible cbrt_two_evals_to_zero p_monic

-- ∛2 is integral over ℚ
lemma cbrt_two_is_integral : IsIntegral ℚ cbrt_two := by
  refine Iff.mp isAlgebraic_iff_isIntegral ?_
  apply isAlgebraic_of_mem_rootSet (p:= X^3 - C 2) (x:= cbrt_two)
  · refine Iff.mpr mem_rootSet ?_
    constructor
    · exact p_nonzero
    · rw[←p, p_is_min_poly]; apply minpoly.aeval
