import Mathlib.FieldTheory.IntermediateField
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.FieldTheory.Normal


set_option maxHeartbeats 0
set_option synthInstance.maxHeartbeats 1000000

variable (F : Type _) [Field F] (E : Type _) [Field E] [Algebra F E]

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

def P (a : alg_constructable F E): Prop := ∃ K : IntermediateField F E, Normal F K ∧ ∃
(m : ℕ), FiniteDimensional.finrank F K = 2^m ∧ ↑a ∈ K  


instance compositum_normal
    (K L : IntermediateField F E) [Normal F K] [Normal F L] :
    Normal F (K ⊔ L : IntermediateField F E) :=
  sorry

open FiniteDimensional

lemma degree_compositum_normal
    (K L : IntermediateField F E) [Normal F K] [Normal F L] :
    finrank F (K ⊔ L : IntermediateField F E) ∣ finrank F K * finrank F L  :=
  sorry

#check(Normal)
lemma pow_of_two_base_lemma (a:F)  : P (algebraMap F (alg_constructable F E) a ) := by 
  use ⊥
  constructor
  . rw [←iSup_of_empty Empty.rec]
    exact @IntermediateField.normal_iSup F E _ _ _ Empty Empty.rec Empty.rec -- seems like we can assume F is normal 
  . use 0
    constructor
    . simp -- need to find theorem that says the rank of a field over itself is 1
    . apply IntermediateField.algebraMap_mem -- very obvious just typing is incompatible

  

variable (X : Type)



  

lemma pw_of_two_add_lemma (l : ℕ) (a : alg_constructable F E) (b : alg_constructable F E) (ha: P a) 
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
    


lemma pw_of_two_mul_lemma (l:ℕ) (a : alg_constructable F E) (b : alg_constructable F E) 
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



lemma pw_of_two_neg_lemma (a : alg_constructable F E) (ha: P a) : P (-a):= by 
  rcases ha with ⟨K, h, n, h3, h4⟩  
  use K
  constructor
  . apply h
  . constructor
    . constructor
      . apply h3
      . apply IntermediateField.neg_mem
        exact h4

  
lemma pw_of_two_inv_lemma (a : alg_constructable F E) (ha: P a) : P (a⁻¹) := by 
  rcases ha with ⟨K, h, n, h3, h4⟩  
  use K
  constructor
  . apply h
  . constructor
    . constructor
      . apply h3
      . apply IntermediateField.inv_mem
        exact h4


lemma pw_of_two_rad_lemma (a: E) (L : IntermediateField F E) (ha : a^2 ∈ alg_constructable F E)
  (hasq: P ⟨a^2, ha⟩) : P (⟨a, is_alg_constructable.rad a ha⟩ : alg_constructable F E) := by 
  rcases hasq with ⟨K, h, n, h3, h4⟩ 
  use K⟮a⟯.restrictScalars F --needs to be K(a)?? either way I need more info about L and how to define it in the first place
  constructor
  . 
  use (n + 1)
  constructor
  . sorry
  . sorry



 
 
  





  



  

