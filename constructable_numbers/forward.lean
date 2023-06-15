import Mathlib.FieldTheory.IntermediateField
import Mathlib.FieldTheory.Tower
import Mathlib.FieldTheory.Adjoin
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.CubicDiscriminant
import Mathlib.Analysis.Complex.Polynomial
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.RootsOfUnity.Basic

set_option maxHeartbeats 0

-- variable (F : Type _) [Field F] (E : Type _) [Field E] [Algebra F E]

-- inductive is_alg_constructable : E → Prop  where
-- | base (a : F) : is_alg_constructable (algebraMap F E a)
-- | add (a b : E) : is_alg_constructable a → is_alg_constructable b → is_alg_constructable (a + b)
-- | neg (a : E) : is_alg_constructable a → is_alg_constructable (-a)
-- | mul (a b : E) : is_alg_constructable a → is_alg_constructable b → is_alg_constructable (a * b)
-- | inv (a : E) : is_alg_constructable a → is_alg_constructable a⁻¹
-- | rad (a : E) : is_alg_constructable (a*a) → is_alg_constructable a

-- def alg_constructable : IntermediateField F E where
--   carrier := is_alg_constructable F E
--   algebraMap_mem':= by
--     exact is_alg_constructable.base
--   zero_mem' := by
--     rw [←map_zero (algebraMap F E)]
--     exact is_alg_constructable.base 0
--   add_mem' := by
--     intro a b
--     exact is_alg_constructable.add a b
--   neg_mem' := by
--     exact is_alg_constructable.neg
--   one_mem' := by
--     rw [←map_one (algebraMap F E)]
--     exact is_alg_constructable.base 1
--   mul_mem' := by
--     intro a b
--     exact is_alg_constructable.mul a b
--   inv_mem' := by
--     exact is_alg_constructable.inv

-- lemma pow_of_two_base_lemma (a: ℝ) (b:ℚ) (h : a = algebraMap ℚ ℝ b) :
--   FiniteDimensional.finrank ℚ ℚ⟮a⟯  = 1 := by 
--   simp 
--   rw [h]
--   apply IntermediateField.algebraMap_mem 

-- variable (X : Type)

-- #check X
-- #check (Set.univ : Set X)
-- #check X = (Set.univ : Set X)

variable (a: ℝ) (b: ℝ)
noncomputable def qa := IntermediateField.adjoin (ℚ) ({a})
#check (inferInstance : Field ℚ)
#check (inferInstance : Module ℚ (IntermediateField.adjoin ℚ {a}))

#check (inferInstance : Module qa (IntermediateField.adjoin qa {b}))


lemma pw_of_two_add_lemma (a : ℝ) (b : ℝ) (ha: FiniteDimensional.finrank ℚ ℚ⟮a⟯ = m) 
(hb: FiniteDimensional.finrank ℚ ℚ⟮b⟯ = n) (hab : FiniteDimensional.finrank ℚ ℚ⟮a+b⟯ = l) (haab : FiniteDimensional.finrank ℚ⟮a⟯ ((ℚ⟮a⟯)⟮b⟯) = (k: ℕ)) :
 l ∣ (m*n) := by
  have Q_sub_Qa : ⊥ ≤ ℚ⟮a⟯ := by 
    exact bot_le  
  have Qa_sub_Qab : ℚ⟮a⟯ ≤ ℚ⟮a, b⟯ := by 
    apply IntermediateField.adjoin.mono
    change {a} ⊆ {a, b}
    simp
  have Qapb_sub_Qab : ℚ⟮a+b⟯ ≤ ℚ⟮a, b⟯ := by sorry
    -- use adjoin_le_iff
  have Qab_eq_Qab : ℚ⟮a, b⟯ = ℚ⟮a⟯⟮b⟯.restrictScalars _ := by sorry
    -- use adjoin_adjoin_left
    -- .restrictScalars to get statement of have to be less angry
  have rank_Qab : FiniteDimensional.finrank ℚ ℚ⟮a,b⟯ = m*n := by sorry
    -- use finrank_mul_finrank
  have q : ℕ := 2 --FiniteDimensional.finrank ℚ⟮a+b⟯ ℚ⟮a,b⟯
  have rank_Qapb : m*n = l*q := by sorry
  dsimp [Dvd.dvd]
  use q
  exact rank_Qapb


lemma pw_of_two_mul_lemma (a : ℝ) (b : ℝ) (ha: FiniteDimensional.finrank ℚ ℚ⟮a⟯ = m) 
(hb: FiniteDimensional.finrank ℚ ℚ⟮b⟯ = n) (hab : FiniteDimensional.finrank ℚ ℚ⟮a*b⟯ = l) :
 l ∣ (m*n) := by 
  have Q_sub_Qa : ⊥ ≤ ℚ⟮a⟯ := by 
      exact bot_le  
  have Qa_sub_Qab : ℚ⟮a⟯ ≤ ℚ⟮a, b⟯ := by sorry
    -- use adjoin.mono
  have Qapb_sub_Qab : ℚ⟮a*b⟯ ≤ ℚ⟮a, b⟯ := by sorry
    -- use adjoin.adjoin_contains_field_as_subfield??
  have Qab_eq_Qab : ℚ⟮a, b⟯ = ℚ⟮a⟯⟮b⟯.restrictScalars _ := by sorry
    -- use adjoin_adjoin_left
    -- .restrictScalars to get statement of have to be less angry
  have rank_Qab : FiniteDimensional.finrank ℚ ℚ⟮a,b⟯ = m*n := by sorry
    -- use finrank_mul_finrank
  have q : ℕ := 2 --FiniteDimensional.finrank ℚ⟮a+b⟯ ℚ⟮a,b⟯
  have rank_Qapb : m*n = l*q := by sorry
  dsimp [Dvd.dvd]
  use q
  exact rank_Qapb


lemma pw_of_two_neg_lemma (a : ℝ) (b : ℝ) (ha: FiniteDimensional.finrank ℚ ℚ⟮a⟯ = m) 
 (hnega : FiniteDimensional.finrank ℚ ℚ⟮-a⟯ = l) : m = l := by 
  have a_in_Qna : a ∈ ℚ⟮-a⟯ := by sorry
    -- Q(-a) is a field and a is -a's additive inverse
  have Q_in_Qna : ⊥ ≤ ℚ⟮-a⟯ := by 
    exact bot_le
  have Qa_sub_Qna : ℚ⟮a⟯ ≤ ℚ⟮-a⟯ := by sorry
    -- Q(a) is the smallest field containing a dn Q and Q(-a) is a field containing a and Q
  have na_in_Qa : -a ∈ ℚ⟮a⟯ := by sorry
    -- Q(a) is a field and -a is a's additive inverse
  have Q_in_Qa : ⊥ ≤ ℚ⟮a⟯ := by 
    exact bot_le
  have Qna_sub_Qa : ℚ⟮-a⟯ ≤ ℚ⟮a⟯ := by sorry
    -- Q(-a) is the smallest field containing -a and Q and Q(a) is a field containing a and Q
  have Qa_eq_Qna : ℚ⟮a⟯ = ℚ⟮-a⟯ := by 
    ext x 
    constructor
    . apply Qa_sub_Qna
    . apply Qna_sub_Qa
  rw [Qa_eq_Qna] at ha
  rw [ha] at hnega
  exact hnega
    

    
lemma pw_of_two_inv_lemma (a : ℝ) (b : ℝ) (ha: FiniteDimensional.finrank ℚ ℚ⟮a⟯ = m) 
 (hinva : FiniteDimensional.finrank ℚ ℚ⟮a⁻¹⟯ = l) : m = l := by 
  have a_in_Qia : a ∈ ℚ⟮a⁻¹⟯ := by sorry
  have Q_in_Qia : ⊥ ≤ ℚ⟮a⁻¹⟯ := by 
    exact bot_le
  have Qa_sub_Qia : ℚ⟮a⟯ ≤ ℚ⟮a⁻¹⟯ := by sorry
  have ia_in_Qa : -a ∈ ℚ⟮a⟯ := by sorry
  have Q_in_Qa : ⊥ ≤ ℚ⟮a⟯ := by 
    exact bot_le
  have Qa_sub_Qia : ℚ⟮a⟯ ≤ ℚ⟮a⁻¹⟯ := by sorry
  have Qa_eq_Qia : ℚ⟮a⟯ = ℚ⟮a⁻¹⟯ := by sorry
  rw [Qa_eq_Qia] at ha
  rw [ha] at hinva
  exact hinva


lemma pw_of_two_rad_lemma (a : ℝ) (b : ℝ) (hasq: FiniteDimensional.finrank ℚ ℚ⟮a*a⟯ = m) 
 (ha : FiniteDimensional.finrank ℚ ℚ⟮a⟯ = l) : l = m ∨ l = 2 * m  := by 
  have Qaa_sub_Qa : ℚ⟮a*a⟯ ≤ ℚ⟮a⟯ := by sorry
  have fr_Qa_Qasq : FiniteDimensional.finrank ℚ⟮a*a⟯ ℚ⟮a⟯ ≤ 2  := by sorry
  --I really don't know this one yet
  sorry

 
 
  





  



  

