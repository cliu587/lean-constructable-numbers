import Mathlib.FieldTheory.IntermediateField
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.FieldTheory.Normal
import Mathlib.FieldTheory.SplittingField.Construction
import Mathlib.FieldTheory.Minpoly.Basic
import Mathlib.LinearAlgebra.FiniteDimensional


open FiniteDimensional

set_option maxHeartbeats 0
set_option synthInstance.maxHeartbeats 1000000
open Polynomial
variable (F : Type _) [Field F] (E : Type _) [Field E] [Algebra F E] [IsAlgClosed E]

inductive is_alg_constructable : E → Prop  where
| base (a : F) : is_alg_constructable (algebraMap F E a)
| add (a b : E) : is_alg_constructable a → is_alg_constructable b → is_alg_constructable (a + b)
| neg (a : E) : is_alg_constructable a → is_alg_constructable (-a)
| mul (a b : E) : is_alg_constructable a → is_alg_constructable b → is_alg_constructable (a * b)
| inv (a : E) : is_alg_constructable a → is_alg_constructable a⁻¹
| rad (a : E) : is_alg_constructable (a ^ 2) → is_alg_constructable a

def alg_constructable : IntermediateField F E where
  carrier := is_alg_constructable F E
  algebraMap_mem':= by
    exact is_alg_constructable.base
  zero_mem' := by
    rw [←map_zero (algebraMap F E)]
    exact is_alg_constructable.base 0
  add_mem' := by
    intro a b
    exact is_alg_constructable.add a b
  neg_mem' := by
    exact is_alg_constructable.neg
  one_mem' := by
    rw [←map_one (algebraMap F E)]
    exact is_alg_constructable.base 1
  mul_mem' := by
    intro a b
    exact is_alg_constructable.mul a b
  inv_mem' := by
    exact is_alg_constructable.inv


variable {F E}

-- Proving statements about constructable numbers by induction
lemma induction (P : alg_constructable F E → Prop)
(base : ∀ a : F, P ⟨algebraMap F E a, is_alg_constructable.base a⟩)
(add : ∀ a b : alg_constructable F E, P a → P b → P (a + b))
(neg : ∀ a : alg_constructable F E, P a → P (-a))
(mul : ∀ a b : alg_constructable F E , P a → P b → P (a * b))
(inv : ∀ a : alg_constructable F E, P a → P a⁻¹)
(sqrt : ∀ a : alg_constructable F E, P (a^2) → P a)
(a : alg_constructable F E) : P a := by

  have recursor := is_alg_constructable.rec (motive := fun c ctr => P ⟨c, ctr⟩)

  have base_ind: ∀ (a : F), P ⟨algebraMap F E a, is_alg_constructable.base a⟩ := base

  have add_ind: ∀ (a b : E) 
    (ca : is_alg_constructable F E a) 
    (cb : is_alg_constructable F E b), 
    P ⟨a, ca⟩ → P ⟨b, cb⟩ → P ⟨a+b, is_alg_constructable.add a b ca cb⟩ := 
      fun a b ca cb => add ⟨a, ca⟩ ⟨b, cb⟩
  
  have neg_ind : ∀ (a : E) (ca : is_alg_constructable F E a), 
    P ⟨a, ca⟩ → P ⟨-a, is_alg_constructable.neg a ca⟩ := 
    fun a ca => neg ⟨a, ca⟩

  have mul_ind: ∀ (a b : E) 
    (ca : is_alg_constructable F E a) 
    (cb : is_alg_constructable F E b), 
    P ⟨a, ca⟩ → P ⟨b, cb⟩ → P ⟨a * b, is_alg_constructable.mul a b ca cb⟩ := 
      fun a b ca cb pa pb => mul ⟨a, ca⟩ ⟨b, cb⟩ pa pb

  have inv_ind: ∀ (a : E) 
    (ca : is_alg_constructable F E a),
    P ⟨a, ca⟩ → P ⟨a⁻¹, is_alg_constructable.inv a ca ⟩ := 
      fun a ca pa => inv ⟨a, ca⟩ pa

  have sqrt_ind: ∀ (a : E) 
    (cas : is_alg_constructable F E (a ^ 2)),
    P ⟨a^2, cas⟩  → P ⟨a, is_alg_constructable.rad a cas⟩ := 
      fun a cas pas => sqrt ⟨a, is_alg_constructable.rad a cas⟩ pas

  apply recursor base_ind add_ind neg_ind mul_ind inv_ind sqrt_ind

-- Main proposition, characterizing constructable numbers.
def P (a : alg_constructable F E): Prop := ∃ K : IntermediateField F E, Normal F K ∧ ∃
(m : ℕ), FiniteDimensional.finrank F K = 2^m ∧ ↑a ∈ K  

-- Should be hot off the presses in Mathlib.
instance compositum_normal {F E : Type _} [Field F] [Field E] [Algebra F E]
    (K L : IntermediateField F E) [Normal F K] [Normal F L] :
    Normal F (K ⊔ L : IntermediateField F E) := by
  let ϕ : Bool → IntermediateField F E := Bool.rec L K
  have : ∀ i, Normal F (↥(ϕ i : IntermediateField F E)) :=
    fun i => match i with
    | true => inferInstance
    | false => inferInstance
  have h := IntermediateField.normal_iSup F E ϕ
  rwa [iSup_bool_eq] at h

-- Sorry'ed lemma
lemma degree_compositum_normal
    (K L : IntermediateField F E) [Normal F K] [Normal F L] :
    finrank F (K ⊔ L : IntermediateField F E) ∣ finrank F K * finrank F L  :=
  sorry

lemma P_induction_base (a:F) : P (algebraMap F (alg_constructable F E) a) := by 
  use ⊥
  constructor
  . rw [←iSup_of_empty Empty.rec]
    exact @IntermediateField.normal_iSup F E _ _ _ Empty Empty.rec Empty.rec -- seems like we can assume F is normal 
  . use 0

    constructor
    . simp -- need to find theorem that says the rank of a field over itself is 1
    . apply IntermediateField.algebraMap_mem -- very obvious just typing is incompatible

variable (X : Type)

lemma P_induction_add (a : alg_constructable F E) (b : alg_constructable F E) (ha: P a) 
(hb: P b) : P (a + b) := by
  rcases ha with ⟨Ka, ha1, n, ha2, ha3⟩ 
  rcases hb with ⟨Kb, hb1, m, hb2, hb3⟩
  use Ka⊔Kb 
  constructor
  . apply compositum_normal
  . have h4: finrank F (Ka ⊔ Kb : IntermediateField F E) ∣ finrank F Ka * finrank F Kb := by
      apply degree_compositum_normal Ka Kb
    dsimp [Dvd.dvd] at h4
    rcases h4 with ⟨s, h5⟩ 
    rw [ha2] at h5
    rw [hb2] at h5
    rw [←pow_add] at h5
    have h6 : finrank F { x // x ∈ Ka ⊔ Kb } ∣  2^(n+m) := by 
      dsimp [Dvd.dvd]
      use s
      exact h5
    rw [Nat.dvd_prime_pow Nat.prime_two] at h6
    rcases h6 with ⟨l, ⟨h6', h6⟩⟩  
    use (l)
    constructor
    . exact h6
    . have aK : ↑a ∈ Ka ⊔ Kb := by 
        have : Ka ≤ Ka ⊔ Kb := by 
          apply le_sup_left
        apply this
        exact ha3
      have bK : ↑b ∈ Ka ⊔ Kb := by 
        have : Kb ≤ Ka ⊔ Kb := by 
          apply le_sup_right
        apply this
        exact hb3
      apply IntermediateField.add_mem
      . exact aK
      . exact bK
    


lemma P_induction_mul (a : alg_constructable F E) (b : alg_constructable F E) 
(ha: P a) (hb: P b) :  P (a*b) := by 
  rcases ha with ⟨Ka, ha1, n, ha2, ha3⟩ 
  rcases hb with ⟨Kb, hb1, m, hb2, hb3⟩
  use Ka⊔Kb 
  constructor
  . apply compositum_normal
  . have h4: finrank F (Ka ⊔ Kb : IntermediateField F E) ∣ finrank F Ka * finrank F Kb := by
      apply degree_compositum_normal Ka Kb
    dsimp [Dvd.dvd] at h4
    rcases h4 with ⟨s, h5⟩ 
    rw [ha2] at h5
    rw [hb2] at h5
    rw [←pow_add] at h5
    have h6 : finrank F { x // x ∈ Ka ⊔ Kb } ∣  2^(n+m) := by 
      dsimp [Dvd.dvd]
      use s
      exact h5
    rw [Nat.dvd_prime_pow Nat.prime_two] at h6
    rcases h6 with ⟨l, ⟨h6', h6⟩⟩  
    use (l)
    constructor
    . exact h6
    . have aK : ↑a ∈ Ka ⊔ Kb := by 
        have : Ka ≤ Ka ⊔ Kb := by 
          apply le_sup_left
        apply this
        exact ha3
      have bK : ↑b ∈ Ka ⊔ Kb := by 
        have : Kb ≤ Ka ⊔ Kb := by 
          apply le_sup_right
        apply this
        exact hb3
      apply IntermediateField.mul_mem
      . exact aK
      . exact bK

lemma P_induction_neg (a : alg_constructable F E) (ha: P a) : P (-a):= by 
  rcases ha with ⟨K, h, n, h3, h4⟩  
  use K
  constructor
  . apply h
  . constructor
    . constructor
      . apply h3
      . apply IntermediateField.neg_mem
        exact h4

lemma P_induction_inv (a : alg_constructable F E) (ha: P a) : P (a⁻¹) := by 
  rcases ha with ⟨K, h, n, h3, h4⟩  
  use K
  constructor
  . apply h
  . constructor
    . constructor
      . apply h3
      . apply IntermediateField.inv_mem
        exact h4

lemma P_induction_sqrt (a: alg_constructable F E) 
  (hasq: P (a^2)) : P a  := by 
  rcases hasq with ⟨K, h, n, h3, h4⟩ 
  have h' : ∃ p : F[X], p ≠ 0 ∧ Polynomial.IsSplittingField F K p := by
    have : FiniteDimensional F K := by 
      apply FiniteDimensional.finiteDimensional_of_finrank 
      rw [h3]
      norm_num
    have := Normal.exists_isSplittingField F K
    rcases this with ⟨p, hp⟩
    by_cases hp' : p = 0   
    . use C 1
      constructor
      . norm_num
      . rw [IntermediateField.isSplittingField_iff]
        constructor
        . apply Polynomial.splits_C 
        . rw [Polynomial.rootSet_C]
          rw [IntermediateField.isSplittingField_iff, hp'] at hp
          rw [Polynomial.rootSet_zero] at hp
          exact hp.2
    . use p
      constructor
      . exact hp'
      . exact hp
  rcases h' with ⟨p, hp0, hp⟩  
  let q := ( p * ((minpoly F ((a : E)^2)).comp (Polynomial.X * Polynomial.X : F[X] )) )
  let L := IntermediateField.adjoin F (Polynomial.rootSet q E )
  use L  
  constructor
  . have : Polynomial.Splits (algebraMap F E) q := by
      apply IsAlgClosed.splits_codomain
    have := IntermediateField.adjoin_rootSet_isSplittingField this
    apply Normal.of_isSplittingField q
  use (n + 1) 
  constructor
  . sorry
  . apply IntermediateField.subset_adjoin
    rw [Polynomial.mem_rootSet_of_ne, map_mul]
    rw [Polynomial.aeval_comp, map_mul]
    rw [Polynomial.aeval_X, sq]
    rw [minpoly.aeval]
    rw [mul_zero]
    apply mul_ne_zero
    . exact hp0
    . rw [Ne, Polynomial.comp_eq_zero_iff]
      push_neg
      constructor
      . apply minpoly.ne_zero
        rw [sq] at h4
        have := Normal.isIntegral h ⟨(a * a: E), h4⟩ 
        rw [sq]
        rw [IntermediateField.isIntegral_iff] at this
        exact this
      . intro h₄
        simp [Polynomial.X_ne_zero]

-- Proof of main proposition using induction.
lemma TO_PROVE_BY_INDUCTION_constructable_implies_sits_in_normal_extension_of_deg_pow_two (a: alg_constructable F E) : P a:= by 
  apply induction P
  . apply P_induction_base
  · apply P_induction_add
  · apply P_induction_neg
  · apply P_induction_mul
  · apply P_induction_inv
  · apply P_induction_sqrt
    
    
