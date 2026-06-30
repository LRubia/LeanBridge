import Mathlib
import LeanBridge.Ramification

/-!
# The Kronecker–Weber Theorem

This file contains sorry'd Lean statements for the blueprint `kw-thm`, formalizing the
Kronecker–Weber theorem (every finite abelian extension of `ℚ` is contained in a cyclotomic
field) together with the supporting theory of higher ramification groups, Hilbert's different
formula, and the classical reduction steps.

The proofs are intentionally omitted (`sorry`); this file fixes faithful statements and the
canonical Mathlib types used to express them.
-/

noncomputable section

open NumberField Polynomial Ramification
open scoped NumberField

namespace KroneckerWeber

/-! ## Auxiliary predicates -/

/-- A field `K` over `ℚ` is contained in a cyclotomic field if it embeds (as a `ℚ`-algebra) into
`CyclotomicField n ℚ` for some positive `n`. This is the Lean rendering of "`K ⊆ ℚ(ζ_n)`". -/
def IsContainedInCyclotomic (K : Type*) [Field K] [Algebra ℚ K] : Prop :=
  ∃ n : ℕ, 0 < n ∧ Nonempty (K →ₐ[ℚ] CyclotomicField n ℚ)

/-- The set of rational primes that ramify in a number field `K`: those `q` for which the
ramification index over `(q)` (common to all primes above `q`) exceeds `1`. -/
def ramifiedPrimes (K : Type*) [Field K] [NumberField K] : Set ℕ :=
  {q | q.Prime ∧ 1 < Ideal.ramificationIdxIn (Ideal.span {(q : ℤ)}) (𝓞 K)}

/-! ## Reductions -/

/-- **Compositum of abelian extensions.** If `K` and `L` are abelian subextensions of `E/F`, then
their compositum `K ⊔ L` is abelian over `F`, and restriction gives an injective homomorphism
`Gal(KL/F) ↪ Gal(K/F) × Gal(L/F)`. -/
theorem compositum_abelian {F E : Type*} [Field F] [Field E] [Algebra F E]
    (K L : IntermediateField F E) [IsAbelianGalois F K] [IsAbelianGalois F L] :
    IsAbelianGalois F ↥(K ⊔ L) ∧
      ∃ f : (↥(K ⊔ L) ≃ₐ[F] ↥(K ⊔ L)) →* (K ≃ₐ[F] K) × (L ≃ₐ[F] L), Function.Injective f := by
  sorry

/-- **Reduction to prime power degree.** If Kronecker–Weber holds for every abelian extension of
prime power degree, then it holds for every finite abelian extension. -/
theorem reduction_prime_power
    (H : ∀ (K : Type*) [Field K] [NumberField K] [IsAbelianGalois ℚ K],
          (∃ p m : ℕ, p.Prime ∧ Module.finrank ℚ K = p ^ m) → IsContainedInCyclotomic K)
    (K : Type*) [Field K] [NumberField K] [IsAbelianGalois ℚ K] :
    IsContainedInCyclotomic K := by
  sorry

/-- **Tame inertia at `q ≠ p`.** For `K/ℚ` abelian of degree `p^m` and a prime `q ≠ p` ramified at
`Q`, the inertia is tame: `V_1(Q | q) = {1}`, the inertia group is cyclic, its order is a power of
`p`, and divides `q - 1`. -/
theorem tame_inertia_cyclic (K : Type*) [Field K] [NumberField K] [IsAbelianGalois ℚ K]
    {p : ℕ} (hp : p.Prime) {m : ℕ} (hdeg : Module.finrank ℚ K = p ^ m)
    {q : ℕ} (hq : q.Prime) (hqp : q ≠ p) (Q : Ideal (𝓞 K)) [Q.IsPrime]
    [Q.LiesOver (Ideal.span {(q : ℤ)})]
    (hram : 1 < Nat.card (ramificationGroup (K ≃ₐ[ℚ] K) Q 0)) :
    ramificationGroup (K ≃ₐ[ℚ] K) Q 1 = ⊥ ∧
      IsCyclic (ramificationGroup (K ≃ₐ[ℚ] K) Q 0) ∧
      (∃ k : ℕ, Nat.card (ramificationGroup (K ≃ₐ[ℚ] K) Q 0) = p ^ k) ∧
      Nat.card (ramificationGroup (K ≃ₐ[ℚ] K) Q 0) ∣ q - 1 := by
  sorry

/-- **Unique totally ramified cyclotomic subfield.** For a prime `q` and `e ∣ q - 1`, the field
`ℚ(ζ_q)` has a unique subfield `L` of degree `e`, and `q` is totally ramified in `L`. -/
theorem cyclotomic_unique_subfield {q : ℕ} (hq : q.Prime) {e : ℕ} (he : e ∣ q - 1) :
    ∃ L : IntermediateField ℚ (CyclotomicField q ℚ),
      Module.finrank ℚ L = e ∧
      Ideal.ramificationIdxIn (Ideal.span {(q : ℤ)}) (𝓞 L) = e ∧
      ∀ L' : IntermediateField ℚ (CyclotomicField q ℚ), Module.finrank ℚ L' = e → L' = L := by
  sorry

/-- **Stripping one ramified prime via the inertia field.** In the setting of `tame_inertia_cyclic`,
there is an abelian extension `K'/ℚ` of `p`-power degree with strictly fewer ramified primes than
`K`, such that `K` is contained in a cyclotomic field whenever `K'` is. -/
theorem inertia_field_strip_prime (K : Type*) [Field K] [NumberField K] [IsAbelianGalois ℚ K]
    {p : ℕ} (hp : p.Prime) {m : ℕ} (hdeg : Module.finrank ℚ K = p ^ m)
    {q : ℕ} (hq : q.Prime) (hqp : q ≠ p) (hqram : q ∈ ramifiedPrimes K) :
    ∃ (K' : Type*) (_ : Field K') (_ : NumberField K') (_ : IsAbelianGalois ℚ K'),
      (∃ m' : ℕ, Module.finrank ℚ K' = p ^ m') ∧
      (ramifiedPrimes K').ncard < (ramifiedPrimes K).ncard ∧
      (IsContainedInCyclotomic K' → IsContainedInCyclotomic K) := by
  sorry

/-- **Reduction to a single ramified prime.** If Kronecker–Weber holds for every abelian extension
of `p`-power degree ramified only at `p`, then it holds for every abelian extension of `p`-power
degree. -/
theorem reduction_single_prime.{u} {p : ℕ} (hp : p.Prime)
    (H : ∀ (K : Type u) [Field K] [NumberField K] [IsAbelianGalois ℚ K],
          (∃ m : ℕ, Module.finrank ℚ K = p ^ m) → ramifiedPrimes K ⊆ {p} →
            IsContainedInCyclotomic K)
    (K : Type u) [Field K] [NumberField K] [IsAbelianGalois ℚ K]
    {m : ℕ} (hdeg : Module.finrank ℚ K = p ^ m) :
    IsContainedInCyclotomic K := by
  -- Strong induction on (ramifiedPrimes K).ncard
  let P (n : ℕ) : Prop := ∀ (K' : Type u) [Field K'] [NumberField K'] [IsAbelianGalois ℚ K'],
    (∃ m' : ℕ, Module.finrank ℚ K' = p ^ m') → (ramifiedPrimes K').ncard = n → IsContainedInCyclotomic K'
  have hP : ∀ n, (∀ k < n, P k) → P n := by
    intro n ih K' _ _ _ hdeg' hncard
    rcases hdeg' with ⟨m', hdeg'_val⟩
    by_cases hsubset : ramifiedPrimes K' ⊆ {p}
    · exact H K' (⟨m', hdeg'_val⟩) hsubset
    · rcases Set.not_subset.mp hsubset with ⟨q, hq_mem, hq_not⟩
      simp at hq_not
      have hq_prime : q.Prime := hq_mem.1
      rcases inertia_field_strip_prime K' hp hdeg'_val hq_prime hq_not hq_mem with ⟨K'', _, _, _, hdeg'', hlt, himpl⟩
      have hlt' : (ramifiedPrimes K'').ncard < n := by
        rw [hncard] at hlt
        exact hlt
      have h_ih := ih (ramifiedPrimes K'').ncard hlt' K'' hdeg'' rfl
      exact himpl h_ih
  have h_all : P ((ramifiedPrimes K).ncard) :=
    Nat.strong_induction_on (ramifiedPrimes K).ncard hP
  exact h_all K (⟨m, hdeg⟩) rfl

/-- **Total ramification of the residual prime.** A nontrivial abelian extension `K/ℚ` of `p`-power
degree ramified only at `p` is totally ramified at `p`. -/
theorem totally_ramified_of_unique_prime {p : ℕ} (hp : p.Prime) (K : Type*) [Field K]
    [NumberField K] [IsAbelianGalois ℚ K] {m : ℕ} (hm : 1 ≤ m)
    (hdeg : Module.finrank ℚ K = p ^ m) (hram : ramifiedPrimes K ⊆ {p}) :
    Ideal.ramificationIdxIn (Ideal.span {(p : ℤ)}) (𝓞 K) = p ^ m := by
  sorry

/-! ## The case `p = 2` -/

/-- **Quadratic fields ramified only at `2`.** A quadratic field ramified only at `2`
(`ℚ(√2)`, `ℚ(i)`, or `ℚ(√-2)`) is contained in the `8`th cyclotomic field. -/
theorem quadratic_ramified_two (K : Type*) [Field K] [NumberField K] [IsAbelianGalois ℚ K]
    (hdeg : Module.finrank ℚ K = 2) (hram : ramifiedPrimes K ⊆ {2}) :
    Nonempty (K →ₐ[ℚ] CyclotomicField 8 ℚ) := by
  sorry

/-- **Maximal real cyclotomic subfield at `2`.** For `m > 1`, the maximal real subfield `L` of
`ℚ(ζ_{2^{m+2}})` has cyclic Galois group of order `2^m`, and `L` contains `ℚ(√2)` as its unique
quadratic (degree-`2`) subfield: there is an intermediate field `F` of degree `2` over `ℚ`
containing a square root of `2` (hence `F = ℚ(√2)`) which is the only degree-`2` subfield of `L`. -/
theorem real_subfield_cyclic_two {m : ℕ} (hm : 1 < m) :
    IsCyclic (↥(NumberField.maximalRealSubfield (CyclotomicField (2 ^ (m + 2)) ℚ)) ≃ₐ[ℚ]
        ↥(NumberField.maximalRealSubfield (CyclotomicField (2 ^ (m + 2)) ℚ))) ∧
      Module.finrank ℚ ↥(NumberField.maximalRealSubfield (CyclotomicField (2 ^ (m + 2)) ℚ)) =
        2 ^ m ∧
      ∃ F : IntermediateField ℚ
          ↥(NumberField.maximalRealSubfield (CyclotomicField (2 ^ (m + 2)) ℚ)),
        Module.finrank ℚ F = 2 ∧
        (∃ x : F, (x : ↥(NumberField.maximalRealSubfield (CyclotomicField (2 ^ (m + 2)) ℚ))) ^ 2
          = 2) ∧
        ∀ F' : IntermediateField ℚ
            ↥(NumberField.maximalRealSubfield (CyclotomicField (2 ^ (m + 2)) ℚ)),
          Module.finrank ℚ F' = 2 → F' = F := by
  sorry

/-- **Kronecker–Weber for `p = 2`.** An abelian extension `K/ℚ` of degree `2^m` ramified only at
`2` is contained in a cyclotomic field. -/
theorem case_two (K : Type*) [Field K] [NumberField K] [IsAbelianGalois ℚ K]
    {m : ℕ} (hdeg : Module.finrank ℚ K = 2 ^ m) (hram : ramifiedPrimes K ⊆ {2}) :
    IsContainedInCyclotomic K := by
  sorry

/-! ## The case of odd `p` -/

/-- **Different exponent for `m = 1`, odd `p`.** For odd `p` and `K/ℚ` cyclic of degree `p`
ramified only at `p`, with `P` over `p`, the prime `p` is totally ramified and
`diff(𝒪_K | ℤ) = P^{2(p-1)}`. -/
theorem odd_different_base {p : ℕ} (hp : p.Prime) (hodd : Odd p) (K : Type*) [Field K]
    [NumberField K] [IsAbelianGalois ℚ K] (hdeg : Module.finrank ℚ K = p)
    (hram : ramifiedPrimes K ⊆ {p}) (P : Ideal (𝓞 K)) [P.IsPrime]
    [P.LiesOver (Ideal.span {(p : ℤ)})] :
    differentIdeal ℤ (𝓞 K) = P ^ (2 * (p - 1)) := by
  sorry

/-- **Cyclicity of the Galois group, odd `p`.** For odd `p` and `K/ℚ` abelian of degree `p^2`
ramified only at `p`, the Galois group is cyclic. -/
theorem odd_galois_cyclic {p : ℕ} (hp : p.Prime) (hodd : Odd p) (K : Type*) [Field K]
    [NumberField K] [IsAbelianGalois ℚ K] (hdeg : Module.finrank ℚ K = p ^ 2)
    (hram : ramifiedPrimes K ⊆ {p}) :
    IsCyclic (K ≃ₐ[ℚ] K) := by
  sorry

/-- **Cyclicity for general `m`, odd `p`.** For odd `p` and `K/ℚ` abelian of degree `p^m` ramified
only at `p`, the Galois group is cyclic. -/
theorem odd_galois_cyclic_general {p : ℕ} (hp : p.Prime) (hodd : Odd p) (K : Type*) [Field K]
    [NumberField K] [IsAbelianGalois ℚ K] {m : ℕ} (hdeg : Module.finrank ℚ K = p ^ m)
    (hram : ramifiedPrimes K ⊆ {p}) :
    IsCyclic (K ≃ₐ[ℚ] K) := by
  sorry

/-- **Unique cyclotomic subfield of `p`-power degree, odd `p`.** For odd `p` and `m ≥ 1`, the field
`ℚ(ζ_{p^{m+1}})` has a unique subfield `L` of degree `p^m`, with cyclic Galois group of order
`p^m`. -/
theorem odd_unique_subfield {p : ℕ} (hp : p.Prime) (hodd : Odd p) {m : ℕ} (hm : 1 ≤ m) :
    ∃ L : IntermediateField ℚ (CyclotomicField (p ^ (m + 1)) ℚ),
      Module.finrank ℚ L = p ^ m ∧ IsCyclic (L ≃ₐ[ℚ] L) ∧
        ∀ L' : IntermediateField ℚ (CyclotomicField (p ^ (m + 1)) ℚ),
          Module.finrank ℚ L' = p ^ m → L' = L := by
  sorry

/-- **Kronecker–Weber for odd `p`.** An abelian extension `K/ℚ` of degree `p^m` (odd `p`) ramified
only at `p` is contained in a cyclotomic field. -/
theorem case_odd {p : ℕ} (hp : p.Prime) (hodd : Odd p) (K : Type*) [Field K] [NumberField K]
    [IsAbelianGalois ℚ K] {m : ℕ} (hdeg : Module.finrank ℚ K = p ^ m)
    (hram : ramifiedPrimes K ⊆ {p}) :
    IsContainedInCyclotomic K := by
  sorry

/-! ## The Kronecker–Weber theorem -/

/-- **Kronecker–Weber.** Every finite abelian extension `K/ℚ` is contained in a cyclotomic field:
there is a positive `n` and a `ℚ`-algebra embedding `K → ℚ(ζ_n)`. -/
theorem abelian_subset_cyclotomic.{u} (K : Type u) [Field K] [NumberField K]
    [IsAbelianGalois ℚ K] :
    IsContainedInCyclotomic K := by
  -- Assemble from the reductions and the two prime cases. The strip-prime
  -- induction lives inside `reduction_single_prime`. Universes are pinned to `u`
  -- so the inner field variables do not leave universe metavariables.
  apply reduction_prime_power.{u, u}
  intro K' _ _ _ hdeg
  obtain ⟨p, m, hp, hdeg'⟩ := hdeg
  refine reduction_single_prime.{u} hp ?_ K' hdeg'
  intro K'' _ _ _ hpm hram
  obtain ⟨m', hdeg''⟩ := hpm
  by_cases h2 : p = 2
  · subst h2
    exact case_two K'' hdeg'' hram
  · exact case_odd hp (hp.odd_of_ne_two h2) K'' hdeg'' hram

end KroneckerWeber
