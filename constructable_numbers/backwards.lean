import Mathlib.FieldTheory.IntermediateField
import Mathlib.Algebra.CubicDiscriminant
import Mathlib.Analysis.Complex.Polynomial
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.RootsOfUnity.Basic
import Mathlib.Data.Nat.Parity
import Mathlib.Data.Real.Irrational

-- https://leanprover.zulipchat.com/#narrow/stream/287929-mathlib4/topic/!4.234085
-- Otherwise coersion problems with a ^ b
local macro_rules | `($x ^ $y)   => `(HPow.hPow $x $y)

noncomputable section

open Polynomial

variable {F : Type} {E : Type}

-- START: Create subfield of constructable numbers and prove they sit in an extension field of ℚ with rank a power of 2.
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

def rank_pow_two_over_ℚ (a : constructable) : Prop := ∃(n: ℕ), FiniteDimensional.finrank ℚ ℚ⟮a.val⟯ = 2^n

-- To prove by induction: (a: constructable) → [ℚ(a) : ℚ] = 2ⁿ
lemma constructable_implies_rank_pow_two_over_ℚ (a: constructable) : rank_pow_two_over_ℚ a := sorry

-- END section



-- START: Prove ∛2 not constructable.
def cbrt_two: ℝ := Real.rpow (2: ℝ) (3⁻¹: ℝ)
def cbrt_two_cubed_eq_2 : (cbrt_two)^(3: ℕ) = 2 := by 
  have two_nn: 0 ≤ (2: ℝ) := by norm_num
  have three_nz: (3: ℕ) ≠ (0) := by norm_num
  have cbrt_cubed_rw: ((2:ℝ) ^ ((3:ℝ)⁻¹)) ^ (3: ℕ) = 2 := by
    have tmp := Real.rpow_nat_inv_pow_nat two_nn three_nz
    dsimp at tmp
    exact tmp
  rw[cbrt_two];dsimp; rw[cbrt_cubed_rw]

-- Create p, and prove p is the min poly of ∛2 and that [ℚ(∛2):ℚ] = 3
-- for that, we need p irreducible AND ∛2 is a root of p AND p monic 
def p: ℚ[X] := X^3 - C 2

def p_is_deg_three : p.natDegree = 3 := natDegree_X_pow_sub_C (n:=3) (r := 2)

def p_monic : Monic p := leadingCoeff_X_pow_sub_C (by norm_num)

def p_nonzero: p ≠ 0 := Monic.ne_zero p_monic

def cbrt_two_evals_to_zero: eval₂ (algebraMap ℚ ℝ) (cbrt_two) (p) = 0 := by 
  have pow_cubed := eval₂_X_pow (n:=3) (R:= ℚ) (S:= ℝ) (algebraMap ℚ ℝ)
  have x_cubed_cbrt_two_eq_two : eval₂ (algebraMap ℚ ℝ) cbrt_two (X ^ 3) = 2:= by
    have := pow_cubed cbrt_two
    rwa[cbrt_two_cubed_eq_2] at this
    
  have two_c : eval₂ (algebraMap ℚ ℝ) cbrt_two (C 2) = 2 := by apply eval₂_C

  have x_cubed_minus_two_eq_zero: eval₂ (algebraMap ℚ ℝ) cbrt_two (X ^ 3 - C 2) = 0 := by 
    have := eval₂_sub (algebraMap ℚ ℝ) (x:= cbrt_two) (R := ℚ) (S := ℝ) (p := X^3) (q := C 2)
    rwa[x_cubed_cbrt_two_eq_two, two_c, sub_self 2] at this

  assumption

-- (Sorried Gauss's Lemma due to not being ported)
/-- **Gauss's Lemma** for `ℤ` states that a primitive integer polynomial is irreducible iff it is
  irreducible over `ℚ`. -/
-- theorem is_primitive.int.irreducible_iff_irreducible_map_cast
--   {p : ℤ[X]} (hp : p.is_primitive) :
--   irreducible p ↔ irreducible (p.map (int.cast_ring_hom ℚ)) :=
-- hp.irreducible_iff_irreducible_map_fraction_map
lemma gauss_lemma {p: ℤ[X]} (hp: IsPrimitive p): Irreducible p ↔ Irreducible (map (algebraMap ℤ ℚ) p) := sorry

def p_irreducible: Irreducible p := by
  -- Show p_z irreducible then apply Gauss
  let p_z: ℤ[X] := X^3 - C 2 
  have p_z_eq_p : map (algebraMap ℤ ℚ) p_z = p := by 
    rw[p]; simp
  rw[←p_z_eq_p]

  have p_z_natDeg_eq_3 : p_z.natDegree = 3 := by apply natDegree_X_pow_sub_C (n:=3) (r := 2)

  have p_z_primitive : IsPrimitive p_z := by
    have three_nez: 3 ≠ 0 := by norm_num
    have : Monic p_z := monic_X_pow_sub_C (2: ℤ) (three_nez)
    apply this.isPrimitive

  let ideal_2: Ideal ℤ := Ideal.span ({(2: ℤ)})

  have ideal_2_prime: Ideal.IsPrime ideal_2 := by
    have two_irred: Irreducible (2: ℤ ) := PrincipalIdealRing.irreducible_iff_prime.mpr (Int.prime_two)
    have two_maximal := by apply PrincipalIdealRing.isMaximal_of_irreducible (two_irred)
    exact Ideal.IsMaximal.isPrime two_maximal

  -- (X^3 - 2): ℤ[X] irreducible by Eisenstein
  have p_z_irred : Irreducible p_z := by
    have p_is_eisenstein : IsEisensteinAt p_z ideal_2 := by
      constructor
      · intro h; dsimp at h
        have zero_lt_3 : 0 < 3 := by norm_num
        have leading_coeff_one : leadingCoeff ((X^3 - C 2): ℤ[X]) = 1 := leadingCoeff_X_pow_sub_C (zero_lt_3)
        rw[leading_coeff_one] at h
        have : 2 ∣ 1 := Ideal.mem_span_singleton.mp h
        contradiction
      · intro pow pow_lt_deg; dsimp; dsimp at pow_lt_deg
        rw[p_z_natDeg_eq_3] at pow_lt_deg
        simp
        interval_cases pow
        · 
          have l1: coeff (X^3: ℤ[X]) 0 = 0 := by apply coeff_X_pow 3
          have l2: coeff 2 0 = (2: ℤ) := by apply coeff_C_zero (a:=2)
          rw[l1,l2]; simp; exact Ideal.mem_span_singleton_self 2
        · 
          have l1: coeff (X^3: ℤ[X]) 1 = 0 := by apply coeff_X_pow 3
          have l2: coeff 2 1 = (0: ℤ) := by apply coeff_C_ne_zero (a:=2) (one_ne_zero)
          rw[l1,l2]; simp
        · 
          have l1: coeff (X^3: ℤ[X]) 2 = 0 := by apply coeff_X_pow 3
          have l2: coeff 2 2 = (0: ℤ) := by apply coeff_C_ne_zero (a:=2) (two_ne_zero)
          rw[l1,l2]; simp
      · 
        rw[Ideal.span_singleton_pow]
        dsimp; norm_num
        by_contra two_in_4_ideal
        have : coeff (X^3: ℤ[X]) 0 = 0 := by apply coeff_X_pow 3
        rw[this] at two_in_4_ideal
        have : coeff 2 0 = (2: ℤ) := by apply coeff_C_zero (a:=2)
        rw[this] at two_in_4_ideal
        norm_num at two_in_4_ideal
        have : 4 ∣ 2 := Ideal.mem_span_singleton.mp two_in_4_ideal
        contradiction
    apply p_is_eisenstein.irreducible
    · exact ideal_2_prime
    · exact p_z_primitive
    · rw[p_z_natDeg_eq_3]; norm_num
    
  exact (gauss_lemma p_z_primitive).mp p_z_irred

lemma p_is_min_poly: p = minpoly ℚ cbrt_two := by apply minpoly.eq_of_irreducible_of_monic p_irreducible cbrt_two_evals_to_zero p_monic

-- Last step: [ℚ(∛2):ℚ] = 3
lemma cbrt_two_is_integral : IsIntegral ℚ cbrt_two := by
  refine Iff.mp isAlgebraic_iff_isIntegral ?_
  apply isAlgebraic_of_mem_rootSet (p:= X^3 - C 2) (x:= cbrt_two)
  · refine Iff.mpr mem_rootSet ?_
    constructor
    · apply p_nonzero
    · rw[←p, p_is_min_poly]; simp

-- Main theorem
theorem cbrt_two_not_constructable: ¬is_constructable_ℝ cbrt_two := by
  by_contra cbrt_two_constructable
  let c : constructable := ⟨_, cbrt_two_constructable⟩

  -- [ℚ⟮cbrt_two⟯: ℚ] = 3
  have ℚ_adj_cbrt_two_rank_eq_3 : FiniteDimensional.finrank ℚ ℚ⟮cbrt_two⟯ = 3 := by 
    rw[←p_is_deg_three, p_is_min_poly]
    exact IntermediateField.adjoin.finrank cbrt_two_is_integral 

  have ℚ_adj_cbrt_two_rank_eq_two_pow : rank_pow_two_over_ℚ c := constructable_implies_rank_pow_two_over_ℚ c

  -- [ℚ(cbrt_two) : ℚ] = 2ⁿ along with proof 
  have ⟨(n: ℕ), pf_rank_pow_2_ext⟩ := ℚ_adj_cbrt_two_rank_eq_two_pow
  rw[pf_rank_pow_2_ext] at ℚ_adj_cbrt_two_rank_eq_3

  -- We now have 2ⁿ = 3 for some natural ℕ - derive some contradiction.
  have : Even 3 := by
    have : Even (2^n) := by
      apply Nat.even_pow.mpr; constructor
      · exact Nat.even_iff.mpr rfl
      · by_contra nez
        rw[nez] at ℚ_adj_cbrt_two_rank_eq_3
        contradiction
    rwa[← ℚ_adj_cbrt_two_rank_eq_3]
  contradiction
