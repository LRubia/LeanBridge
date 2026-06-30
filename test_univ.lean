import Mathlib
open NumberField

def IsContainedInCyclotomic (K : Type*) [Field K] [Algebra ℚ K] : Prop :=
  ∃ n : ℕ, 0 < n ∧ Nonempty (K →ₐ[ℚ] CyclotomicField n ℚ)

def ramifiedPrimes (K : Type*) [Field K] [NumberField K] : Set ℕ :=
  {q | q.Prime ∧ 1 < Ideal.ramificationIdxIn (Ideal.span {(q : ℤ)}) (𝓞 K)}

theorem test_pattern (H : ∀ (K : Type*) [Field K] [NumberField K] [IsAbelianGalois ℚ K],
    (∃ m : ℕ, Module.finrank ℚ K = 2 ^ m) → ramifiedPrimes K ⊆ {2} → IsContainedInCyclotomic K)
    (K : Type*) [Field K] [NumberField K] [IsAbelianGalois ℚ K]
    (hdeg : ∃ m : ℕ, Module.finrank ℚ K = 2 ^ m) (hsub : ramifiedPrimes K ⊆ {2}) :
    IsContainedInCyclotomic K := by
  exact H K hdeg hsub
