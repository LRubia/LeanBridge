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
  classical
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : NeZero q := ⟨hq.ne_zero⟩
  haveI : NeZero ((q : ℕ) : ℚ) := ⟨Nat.cast_ne_zero.mpr (NeZero.ne q)⟩
  haveI : IsCyclotomicExtension {q} ℚ (CyclotomicField q ℚ) :=
    CyclotomicField.isCyclotomicExtension q ℚ
  haveI : IsGalois ℚ (CyclotomicField q ℚ) :=
    IsCyclotomicExtension.isGalois {q} ℚ (CyclotomicField q ℚ)
  haveI : FiniteDimensional ℚ (CyclotomicField q ℚ) := inferInstance
  have hq1 : 1 ≤ q - 1 := by have := hq.two_le; omega
  -- Galois group `Gal(ℚ(ζ_q)/ℚ) ≅ (ZMod q)ˣ`, cyclic of order `q - 1`.
  let ee : (CyclotomicField q ℚ ≃ₐ[ℚ] CyclotomicField q ℚ) ≃* (ZMod q)ˣ :=
    IsCyclotomicExtension.Rat.galEquivZMod q (CyclotomicField q ℚ)
  let φ : (CyclotomicField q ℚ ≃ₐ[ℚ] CyclotomicField q ℚ) →* (ZMod q)ˣ := ee
  have hφ : Function.Injective φ := ee.injective
  haveI hUcyc : IsCyclic (ZMod q)ˣ := inferInstance
  haveI hGcyc : IsCyclic (CyclotomicField q ℚ ≃ₐ[ℚ] CyclotomicField q ℚ) :=
    isCyclic_of_surjective ee.symm ee.symm.surjective
  -- The target subgroup has cardinality `d = (q-1)/e`, giving index (hence degree) `e`.
  set d := (q - 1) / e with hd_def
  have hde : d * e = q - 1 := Nat.div_mul_cancel he
  have hd_dvd : d ∣ q - 1 := ⟨e, hde.symm⟩
  have he0 : 0 < e := by
    rcases Nat.eq_zero_or_pos e with h | h
    · rw [h, Nat.mul_zero] at hde; omega
    · exact h
  have hd0 : 0 < d := by
    rcases Nat.eq_zero_or_pos d with h | h
    · rw [h, Nat.zero_mul] at hde; omega
    · exact h
  have hcardU : Nat.card (ZMod q)ˣ = q - 1 := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient, Nat.totient_prime hq]
  have hcardG : Nat.card (CyclotomicField q ℚ ≃ₐ[ℚ] CyclotomicField q ℚ) = q - 1 := by
    rw [Nat.card_congr ee.toEquiv, hcardU]
  set HU : Subgroup (ZMod q)ˣ := (powMonoidHom d).ker with hHU
  have hcardHU : Nat.card HU = d := by
    rw [hHU, IsCyclic.card_powMonoidHom_ker, hcardU, Nat.gcd_eq_right hd_dvd]
  have huniqU : ∀ S : Subgroup (ZMod q)ˣ, Nat.card S = d → S = HU := by
    intro S hS
    have hle : S ≤ HU := by
      intro x hx
      have hxo : (⟨x, hx⟩ : S) ^ d = 1 :=
        orderOf_dvd_iff_pow_eq_one.mp (hS ▸ orderOf_dvd_natCard _)
      have hx1 : x ^ d = 1 := by
        have h2 := congrArg (fun y : S => (y : (ZMod q)ˣ)) hxo
        simpa using h2
      simpa [hHU, MonoidHom.mem_ker, powMonoidHom] using hx1
    exact Subgroup.eq_of_le_of_card_ge hle (le_of_eq (hcardHU.trans hS.symm))
  set H : Subgroup (CyclotomicField q ℚ ≃ₐ[ℚ] CyclotomicField q ℚ) := HU.comap φ with hHdef
  have hcardH : Nat.card H = d := by
    rw [hHdef, Subgroup.comap_equiv_eq_map_symm, Nat.card_congr (Subgroup.equivMapOfInjective _ _
      ee.symm.injective).toEquiv.symm, hcardHU]
  haveI : H.Normal := by
    refine ⟨fun a ha g => ?_⟩
    have heq : φ (g * a * g⁻¹) = φ a := by
      simp only [map_mul, map_inv]
      rw [mul_comm (φ g) (φ a), mul_assoc, mul_inv_cancel, mul_one]
    simpa [hHdef, Subgroup.mem_comap, heq] using ha
  refine ⟨IntermediateField.fixedField H, ?_, ?_, ?_⟩
  · -- degree `= e`
    rw [IntermediateField.finrank_eq_fixingSubgroup_index,
      IntermediateField.fixingSubgroup_fixedField]
    have hmul := Subgroup.index_mul_card H
    rw [hcardH, hcardG] at hmul
    have hmul' : H.index * d = e * d := by rw [hmul, ← hde, Nat.mul_comm]
    exact Nat.eq_of_mul_eq_mul_right hd0 hmul'
  · -- ramification `= e`
    sorry
  · -- uniqueness
    intro L' hL'
    have hidx : (IntermediateField.fixingSubgroup L').index = e := by
      rw [← IntermediateField.finrank_eq_fixingSubgroup_index]; exact hL'
    have hcardH' : Nat.card (IntermediateField.fixingSubgroup L') = d := by
      have hmul := Subgroup.index_mul_card (IntermediateField.fixingSubgroup L')
      rw [hidx, hcardG] at hmul
      have hmul' : e * Nat.card (IntermediateField.fixingSubgroup L') = e * d := by
        rw [hmul, ← hde, Nat.mul_comm]
      exact Nat.eq_of_mul_eq_mul_left he0 hmul'
    set S : Subgroup (ZMod q)ˣ := (IntermediateField.fixingSubgroup L').map φ with hS
    have hcardS : Nat.card S = d := by
      rw [hS, Subgroup.card_map_of_injective hφ, hcardH']
    have hSHU : S = HU := huniqU S hcardS
    have hfix : IntermediateField.fixingSubgroup L' = H := by
      rw [hHdef, ← hSHU, hS, Subgroup.comap_map_eq_self_of_injective hφ]
    rw [← IsGalois.fixedField_fixingSubgroup L', hfix]

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
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by rintro rfl; exact (by decide : ¬ Odd 2) hodd
  set n := p ^ (m + 1) with hn
  haveI : NeZero n := ⟨pow_ne_zero _ hp.ne_zero⟩
  haveI : NeZero ((n : ℕ) : ℚ) := ⟨Nat.cast_ne_zero.mpr (NeZero.ne n)⟩
  haveI : IsCyclotomicExtension {n} ℚ (CyclotomicField n ℚ) :=
    CyclotomicField.isCyclotomicExtension n ℚ
  haveI : IsGalois ℚ (CyclotomicField n ℚ) :=
    IsCyclotomicExtension.isGalois {n} ℚ (CyclotomicField n ℚ)
  haveI : FiniteDimensional ℚ (CyclotomicField n ℚ) := inferInstance
  -- Galois group of `ℚ(ζ_n)/ℚ`, isomorphic to `(ZMod n)ˣ`, which is cyclic.
  let e : (CyclotomicField n ℚ ≃ₐ[ℚ] CyclotomicField n ℚ) ≃* (ZMod n)ˣ :=
    IsCyclotomicExtension.Rat.galEquivZMod n (CyclotomicField n ℚ)
  let φ : (CyclotomicField n ℚ ≃ₐ[ℚ] CyclotomicField n ℚ) →* (ZMod n)ˣ := e
  have hφ : Function.Injective φ := e.injective
  haveI hUcyc : IsCyclic (ZMod n)ˣ := ZMod.isCyclic_units_of_prime_pow p hp hp2 (m + 1)
  haveI hGcyc : IsCyclic (CyclotomicField n ℚ ≃ₐ[ℚ] CyclotomicField n ℚ) :=
    isCyclic_of_surjective e.symm e.symm.surjective
  have hd : (p - 1) ∣ p ^ m * (p - 1) := dvd_mul_left (p - 1) (p ^ m)
  have hcardU : Nat.card (ZMod n)ˣ = p ^ m * (p - 1) := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient, hn,
      Nat.totient_prime_pow hp (Nat.succ_pos m)]
    simp
  have hcardG : Nat.card (CyclotomicField n ℚ ≃ₐ[ℚ] CyclotomicField n ℚ) = p ^ m * (p - 1) := by
    rw [Nat.card_congr e.toEquiv, hcardU]
  -- The unique subgroup `H_U` of `(ZMod n)ˣ` of cardinality `p - 1`.
  set HU : Subgroup (ZMod n)ˣ := (powMonoidHom (p - 1)).ker with hHU
  have hcardHU : Nat.card HU = p - 1 := by
    rw [hHU, IsCyclic.card_powMonoidHom_ker, hcardU, Nat.gcd_eq_right hd]
  -- Any subgroup of `(ZMod n)ˣ` of cardinality `p - 1` equals `HU`.
  have huniqU : ∀ S : Subgroup (ZMod n)ˣ, Nat.card S = p - 1 → S = HU := by
    intro S hS
    have hle : S ≤ HU := by
      intro x hx
      have hxo : (⟨x, hx⟩ : S) ^ (p - 1) = 1 :=
        orderOf_dvd_iff_pow_eq_one.mp (hS ▸ orderOf_dvd_natCard _)
      have hx1 : x ^ (p - 1) = 1 := by
        have h2 := congrArg (fun y : S => (y : (ZMod n)ˣ)) hxo
        simpa using h2
      simpa [hHU, MonoidHom.mem_ker, powMonoidHom] using hx1
    exact Subgroup.eq_of_le_of_card_ge hle (le_of_eq (hcardHU.trans hS.symm))
  -- Transport `HU` to a subgroup `H` of `G`.
  set H : Subgroup (CyclotomicField n ℚ ≃ₐ[ℚ] CyclotomicField n ℚ) := HU.comap φ with hHdef
  have hcardH : Nat.card H = p - 1 := by
    rw [hHdef, Subgroup.comap_equiv_eq_map_symm, Nat.card_congr (Subgroup.equivMapOfInjective _ _
      e.symm.injective).toEquiv.symm, hcardHU]
  haveI : H.Normal := by
    refine ⟨fun a ha g => ?_⟩
    have heq : φ (g * a * g⁻¹) = φ a := by
      simp only [map_mul, map_inv]
      rw [mul_comm (φ g) (φ a), mul_assoc, mul_inv_cancel, mul_one]
    simpa [hHdef, Subgroup.mem_comap, heq] using ha
  -- The witness subfield.
  refine ⟨IntermediateField.fixedField H, ?_, ?_, ?_⟩
  · -- degree
    rw [IntermediateField.finrank_eq_fixingSubgroup_index, IntermediateField.fixingSubgroup_fixedField]
    have hmul := Subgroup.index_mul_card H
    rw [hcardH, hcardG] at hmul
    have hpm : 0 < p - 1 := by have := hp.two_le; omega
    exact Nat.eq_of_mul_eq_mul_right hpm hmul
  · -- cyclic Galois group
    haveI hquot : IsCyclic ((CyclotomicField n ℚ ≃ₐ[ℚ] CyclotomicField n ℚ) ⧸ H) :=
      isCyclic_of_surjective (QuotientGroup.mk' H) (QuotientGroup.mk'_surjective H)
    exact isCyclic_of_surjective (IsGalois.normalAutEquivQuotient H).toMonoidHom
      (IsGalois.normalAutEquivQuotient H).surjective
  · -- uniqueness
    intro L' hL'
    have hidx : (IntermediateField.fixingSubgroup L').index = p ^ m := by
      rw [← IntermediateField.finrank_eq_fixingSubgroup_index]; exact hL'
    have hcardH' : Nat.card (IntermediateField.fixingSubgroup L') = p - 1 := by
      have hmul := Subgroup.index_mul_card (IntermediateField.fixingSubgroup L')
      rw [hidx, hcardG] at hmul
      have hpm : 0 < p ^ m := pow_pos hp.pos m
      exact Nat.eq_of_mul_eq_mul_left hpm hmul
    -- map to `(ZMod n)ˣ`
    set S : Subgroup (ZMod n)ˣ := (IntermediateField.fixingSubgroup L').map φ with hS
    have hcardS : Nat.card S = p - 1 := by
      rw [hS, Subgroup.card_map_of_injective hφ, hcardH']
    have hSHU : S = HU := huniqU S hcardS
    have hfix : IntermediateField.fixingSubgroup L' = H := by
      rw [hHdef, ← hSHU, hS, Subgroup.comap_map_eq_self_of_injective hφ]
    rw [← IsGalois.fixedField_fixingSubgroup L', hfix]

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
