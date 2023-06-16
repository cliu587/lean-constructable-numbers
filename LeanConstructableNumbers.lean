import LeanConstructableNumbers.forward
import LeanConstructableNumbers.backwards

open FiniteDimensional

-- Theorem: Cannot double the cube, meaning cannot construct ∛2
theorem cbrt_two_not_constructable: ¬is_alg_constructable ℚ ℝ cbrt_two := by
  -- Assume ∛2 is constructable, and derive a contradiction.
  by_contra cbrt_two_constructable
  let c : alg_constructable ℚ ℝ:= ⟨_, cbrt_two_constructable⟩

  -- [ℚ⟮∛2⟯: ℚ] = 3
  have ℚ_adj_cbrt_two_rank_eq_3 : finrank ℚ ℚ⟮cbrt_two⟯ = 3 := by 
    rw[←p_is_deg_three, p_is_min_poly]
    exact IntermediateField.adjoin.finrank cbrt_two_is_integral 

  -- ∛2 ∈ L for some extension field L such that [L : ℚ] = 2^m
  have ⟨L, _, m, rank_eq_two_pow_m, c_in_L⟩ := TO_PROVE_BY_INDUCTION_constructable_implies_sits_in_normal_extension_of_deg_pow_two c

  -- Apply tower law to conclude [ℚ(∛2): ℚ] | 2^m
  have : Module ℚ⟮cbrt_two⟯ L := by
    apply RingHom.toModule
    exact Subsemiring.inclusion (IntermediateField.adjoin_simple_le_iff.mpr c_in_L)

  have : FiniteDimensional ℚ ℚ⟮cbrt_two⟯ := by
    apply finiteDimensional_of_finrank 
    rw[ℚ_adj_cbrt_two_rank_eq_3]; exact zero_lt_three

  have : finrank ℚ ℚ⟮cbrt_two⟯ * finrank ℚ⟮cbrt_two⟯ L = finrank ℚ L := by 
    apply finrank_mul_finrank
  rw[←this, ℚ_adj_cbrt_two_rank_eq_3] at rank_eq_two_pow_m

  have : 3 ∣ 2 := by 
    have : 3 ∣ 2^m := dvd_of_mul_right_eq (finrank ℚ⟮cbrt_two⟯ L) rank_eq_two_pow_m
    apply Nat.Prime.dvd_of_dvd_pow Nat.prime_three this
  contradiction