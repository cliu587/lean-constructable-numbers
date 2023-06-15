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

open Polynomial FiniteDimensional

variable {F : Type} {E : Type}

-- START: Create subfield of constructable numbers and prove they sit in an extension field of ℚ with rank a power of 2.
inductive is_alg_constructable : ℝ → Prop
| base (a : ℚ) : is_alg_constructable (algebraMap ℚ  ℝ a)
| add (a b : ℝ) : is_alg_constructable a → is_alg_constructable b → is_alg_constructable (a+b)
| neg (a : ℝ) : is_alg_constructable a → is_alg_constructable (-a)
| mul (a b : ℝ) : is_alg_constructable a → is_alg_constructable b → is_alg_constructable (a*b)
| inv (a : ℝ) : is_alg_constructable a → is_alg_constructable a⁻¹
| sqrt (a : ℝ) : is_alg_constructable (a^2) → is_alg_constructable a

instance alg_constructable : IntermediateField ℚ ℝ where
  carrier := is_alg_constructable
  mul_mem' := by
    intro a b ca cb
    apply is_alg_constructable.mul
    exact ca; exact cb;
  add_mem' := by
    intro a b ca cb
    apply is_alg_constructable.add
    exact ca; exact cb;
  algebraMap_mem' := is_alg_constructable.base 
  neg_mem' := by
    intro a ca
    apply is_alg_constructable.neg
    exact ca;
  inv_mem' := by
    intro a ca
    apply is_alg_constructable.inv
    exact ca;

-- #check @is_alg_constructable.rec (motive := fun _ => P : Prop)
-- Proving statements about constructable numbers by induction
lemma induction (P : alg_constructable → Prop)
(base : ∀ a : ℚ, P a)
(add : ∀ a b : alg_constructable, P a → P b → P (a + b))
(neg : ∀ a : alg_constructable, P a → P (-a))
(mul : ∀ a b : alg_constructable, P a → P b → P (a * b))
(inv : ∀ a : alg_constructable, P a → P a⁻¹)
(sqrt : ∀ a : alg_constructable, P (a^2) → P a)
(a : alg_constructable) : P a := by

  have recursor := is_alg_constructable.rec (motive := fun c ctr => P ⟨c, ctr⟩)

  have base_ind: ∀ (a : ℚ), P ⟨a, is_alg_constructable.base a⟩ := base

  have add_ind: ∀ (a b : ℝ) 
    (ca : is_alg_constructable a) 
    (cb : is_alg_constructable b), 
    P ⟨a, ca⟩ → P ⟨b, cb⟩ → P ⟨a+b, is_alg_constructable.add a b ca cb⟩ := 
      fun a b ca cb => add ⟨a, ca⟩ ⟨b, cb⟩
  
  have neg_ind : ∀ (a : ℝ) (ca : is_alg_constructable a), 
    P ⟨a, ca⟩ → P ⟨-a, is_alg_constructable.neg a ca⟩ := 
    fun a ca => neg ⟨a, ca⟩

  have mul_ind: ∀ (a b : ℝ) 
    (ca : is_alg_constructable a) 
    (cb : is_alg_constructable b), 
    P ⟨a, ca⟩ → P ⟨b, cb⟩ → P ⟨a * b, is_alg_constructable.mul a b ca cb⟩ := 
      fun a b ca cb pa pb => mul ⟨a, ca⟩ ⟨b, cb⟩ pa pb

  have inv_ind: ∀ (a : ℝ) 
    (ca : is_alg_constructable a),
    P ⟨a, ca⟩ → P ⟨a⁻¹, is_alg_constructable.inv a ca ⟩ := 
      fun a ca pa => inv ⟨a, ca⟩ pa

  have sqrt_ind: ∀ (a : ℝ) 
    (cas : is_alg_constructable (a ^ 2)),
    P ⟨a^2, cas⟩  → P ⟨a, is_alg_constructable.sqrt a cas⟩ := 
      fun a cas pas => sqrt ⟨a, is_alg_constructable.sqrt a cas⟩ pas

  apply recursor base_ind add_ind neg_ind mul_ind inv_ind sqrt_ind


def sits_in_normal_extension_of_deg_pow_two (a : alg_constructable): Prop := ∃ K : IntermediateField ℚ ℝ, Normal ℚ K ∧ ∃
(m : ℕ), FiniteDimensional.finrank ℚ K = 2^m ∧ ↑a ∈ K

-- TODO
lemma TO_PROVE_BY_INDUCTION_constructable_implies_sits_in_normal_extension_of_deg_pow_two (a: alg_constructable) : sits_in_normal_extension_of_deg_pow_two a := by sorry

-- END forward section

-- START: Prove ∛2 not constructable.
def cbrt_two: ℝ := Real.rpow (2: ℝ) (3⁻¹: ℝ)
def cbrt_two_cubed_eq_2 : (cbrt_two)^(3: ℕ) = 2 := by 
  have two_nn: 0 ≤ (2: ℝ) := by norm_num
  have three_nz: (3: ℕ) ≠ (0) := by norm_num
  have cbrt_cubed_rw: ((2:ℝ) ^ ((3:ℝ)⁻¹)) ^ (3: ℕ) = 2 := by
    have tmp := Real.rpow_nat_inv_pow_nat two_nn three_nz
    dsimp only [Nat.cast_ofNat] at tmp; assumption
  rw[cbrt_two];dsimp only [Real.rpow_eq_pow]; rw[cbrt_cubed_rw]

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
    rw[p]; simp only [algebraMap_int_eq, map_ofNat, Polynomial.map_sub, Polynomial.map_pow, map_X, Polynomial.map_ofNat]
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
          have l2: coeff 2 0 = (2: ℤ) := by apply coeff_C_zero (a:=2)
          rw[l1,l2]; simp only [zero_sub, neg_mem_iff]; exact Ideal.mem_span_singleton_self 2
        · 
          have l1: coeff (X^3: ℤ[X]) 1 = 0 := by apply coeff_X_pow 3
          have l2: coeff 2 1 = (0: ℤ) := by apply coeff_C_ne_zero (a:=2) (one_ne_zero)
          rw[l1,l2]; simp only [sub_self, Submodule.zero_mem]
        · 
          have l1: coeff (X^3: ℤ[X]) 2 = 0 := by apply coeff_X_pow 3
          have l2: coeff 2 2 = (0: ℤ) := by apply coeff_C_ne_zero (a:=2) (two_ne_zero)
          rw[l1,l2]; simp only [sub_self, Submodule.zero_mem]
      · 
        rw[Ideal.span_singleton_pow]
        norm_num
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

-- Last step: ∛2 is integral over ℚ
lemma cbrt_two_is_integral : IsIntegral ℚ cbrt_two := by
  refine Iff.mp isAlgebraic_iff_isIntegral ?_
  apply isAlgebraic_of_mem_rootSet (p:= X^3 - C 2) (x:= cbrt_two)
  · refine Iff.mpr mem_rootSet ?_
    constructor
    · apply p_nonzero
    · rw[←p, p_is_min_poly]; apply minpoly.aeval

-- Theorem: Cannot double the cube, meaning cannot construct ∛2
theorem cbrt_two_not_constructable: ¬is_alg_constructable cbrt_two := by
  -- Assume ∛2 is constructable, and derive a contradiction.
  by_contra cbrt_two_constructable
  let c : alg_constructable := ⟨_, cbrt_two_constructable⟩

  -- [ℚ⟮∛2⟯: ℚ] = 3
  have ℚ_adj_cbrt_two_rank_eq_3 : FiniteDimensional.finrank ℚ ℚ⟮cbrt_two⟯ = 3 := by 
    rw[←p_is_deg_three, p_is_min_poly]
    exact IntermediateField.adjoin.finrank cbrt_two_is_integral 

  -- ∛2 ∈ L for some extension field L such that [L : ℚ] = 2^m
  have ⟨L, _, m, rank_eq_two_pow_m, c_in_L⟩ := TO_PROVE_BY_INDUCTION_constructable_implies_sits_in_normal_extension_of_deg_pow_two c

  -- Apply tower law to conclude [ℚ(∛2): ℚ] | 2^m
  have : Module ℚ⟮cbrt_two⟯ L := by
    apply RingHom.toModule
    exact Subsemiring.inclusion (IntermediateField.adjoin_simple_le_iff.mpr c_in_L)

  have : FiniteDimensional ℚ ℚ⟮cbrt_two⟯ := by
    apply FiniteDimensional.finiteDimensional_of_finrank 
    rw[ℚ_adj_cbrt_two_rank_eq_3]; exact zero_lt_three

  have : finrank ℚ ℚ⟮cbrt_two⟯ * finrank ℚ⟮cbrt_two⟯ L = finrank ℚ L := by 
    apply FiniteDimensional.finrank_mul_finrank
  rw[←this, ℚ_adj_cbrt_two_rank_eq_3] at rank_eq_two_pow_m

  have : 3 ∣ 2 := by 
    have : 3 ∣ 2^m := dvd_of_mul_right_eq (finrank ℚ⟮cbrt_two⟯ L) rank_eq_two_pow_m
    apply Nat.Prime.dvd_of_dvd_pow Nat.prime_three this
  contradiction

-- SCRATCH

-- lemma IntermediateField.finrank_congr [Field F] [Field E] [Algebra F E] (K L : IntermediateField F E) (h : K = L) : FiniteDimensional.finrank F K = FiniteDimensional.finrank F L := by
--   subst h
--   rfl

-- instance compositum_normal {F E : Type _} [Field F] [Field E] [Algebra F E]
--     (K L : IntermediateField F E) [Normal F K] [Normal F L] :
--     Normal F (K ⊔ L : IntermediateField F E) :=
--   sorry

-- lemma degree_compositum_normal {F E : Type _} [Field F] [Field E] [Algebra F E]
--     (K L : IntermediateField F E) [Normal F K] [Normal F L] :
--     finrank F (K ⊔ L : IntermediateField F E) ∣ finrank F K * finrank F L  :=
--   sorry

--   -- have tmp := FiniteDimensional.finrank_mul_finrank' (F:=ℚ) (K:=ℚ⟮a⟯) (A:=L)

--   -- want: ℚ⟮a⟯ ≤ L, [L:ℚ] = [L:ℚ⟮a⟯] [ℚ⟮a⟯:ℚ], [L:ℚ = 2^m] implies [ℚ⟮a⟯:ℚ] = 2^n.
  

--   sorry




-- -- Did not bother proving this in generality.
-- def rank_pow_two_over_ℚ (a : alg_constructable) : Prop := ∃(n: ℕ), FiniteDimensional.finrank ℚ ℚ⟮a.val⟯ = 2^n

-- -- To prove by induction: (a: alg_constructable) → [ℚ(a) : ℚ] = 2ⁿ
-- lemma constructable_implies_rank_pow_two_over_ℚ (a: alg_constructable) : rank_pow_two_over_ℚ a := by 
--   apply induction rank_pow_two_over_ℚ
--   · intro a
--     use 0; simp
--     exact SubfieldClass.coe_rat_mem ⊥ a
--   · intro a b ha hb
--     -- TODO: Requires some proofs.
--     have : rank_pow_two_over_ℚ (a + b) := sorry
--     assumption

--   · intro a ⟨n, ha⟩
--     use n; simp; 
--     rw[←ha]
--     apply IntermediateField.finrank_congr
--     apply le_antisymm
--     . rw [IntermediateField.adjoin_simple_le_iff]
--       apply IntermediateField.neg_mem
--       apply IntermediateField.mem_adjoin_simple_self
--     . rw [IntermediateField.adjoin_simple_le_iff]
--       nth_rw 1 [←neg_neg a]
--       apply IntermediateField.neg_mem
--       apply IntermediateField.mem_adjoin_simple_self

--   · -- TODO: Requires some proofs.
--     intro a b ha hb
--     have : rank_pow_two_over_ℚ (a * b) := sorry
--     assumption

--   · intro a ⟨n, ha⟩
--     use n; simp; rw[←ha]
--     apply IntermediateField.finrank_congr
--     apply le_antisymm
--     · rw [IntermediateField.adjoin_simple_le_iff]
--       apply IntermediateField.inv_mem
--       apply IntermediateField.mem_adjoin_simple_self
--     · rw [IntermediateField.adjoin_simple_le_iff]
--       nth_rw 1 [←inv_inv a]
--       apply IntermediateField.inv_mem
--       apply IntermediateField.mem_adjoin_simple_self

--   · -- TODO: Requires some proofs.
--     intro a ⟨n, ha⟩
--     have : rank_pow_two_over_ℚ (a) := sorry
--     assumption

