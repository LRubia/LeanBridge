import Mathlib
import LeanBridge.Mono
import LeanBridge.DiscrAssoc
import LeanBridge.DiscrNormPB
import LeanBridge.DedekindTame

/-!
# Invariants of `p`-adic fields: the field and its ring of integers

This file begins the formalization of the blueprint
`numina/blueprints/padicinv/padicinv.tex` (Invariants of a finite extension of
`p`-adic fields):

* `PadicField` (blueprint `def:padic-field`): a `p`-adic field is a finite
  extension `K / ℚ_[p]`.
* `PadicField.ringOfIntegers` (`𝒪_K`): the integral closure of `ℤ_[p]` in `K`,
  together with `IsFractionRing 𝒪_K K`.
* `PadicField.instIsDiscreteValuationRing` (blueprint `prop:padic-is-dvf`):
  `𝒪_K` is a discrete valuation ring. This is the only fact left as `sorry`.

Once `𝒪_K` is a DVR it is in particular a local Dedekind domain with fraction
field `K`, so the normalized valuation `v_K : K → ℤᵐ⁰` of `def:padic-field` is
just Mathlib's `IsDedekindDomain.HeightOneSpectrum.valuation` for the maximal
ideal of `𝒪_K`; no dedicated wrapper is introduced here.
-/

noncomputable section

/-- A *`p`-adic field* is a finite extension `K / ℚ_[p]`. The prime `p` is an
`outParam`: it is recovered from the field `K` (via its `ℚ_[p]`-algebra
structure), so downstream definitions such as `𝒪[K]` need not carry `p`. -/
class PadicField (K : Type*) [Field K] (p : outParam ℕ) [Fact p.Prime] [Algebra ℚ_[p] K] : Prop
    extends Module.Finite ℚ_[p] K

namespace PadicField

variable (K : Type*) [Field K] {p : ℕ} [hp : Fact p.Prime] [Algebra ℚ_[p] K] [PadicField K p]

/-- The canonical `ℤ_[p]`-algebra structure on a `p`-adic field, obtained by
restricting scalars along `ℤ_[p] → ℚ_[p]`. -/
instance instAlgebraPadicInt : Algebra ℤ_[p] K :=
  ((algebraMap ℚ_[p] K).comp (algebraMap ℤ_[p] ℚ_[p])).toAlgebra

instance instIsScalarTower : IsScalarTower ℤ_[p] ℚ_[p] K :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

theorem algebraMap_padicInt_injective (p : ℕ) [Fact p.Prime] (K : Type*) [Field K]
    [Algebra ℚ_[p] K] : Function.Injective (algebraMap ℤ_[p] K) := by
  rw [IsScalarTower.algebraMap_eq ℤ_[p] ℚ_[p] K, RingHom.coe_comp]
  exact (algebraMap ℚ_[p] K).injective.comp (IsFractionRing.injective ℤ_[p] ℚ_[p])

omit [PadicField K p] in
theorem charZero_of_padicAlgebra (p : ℕ) [Fact p.Prime] (K : Type*) [Field K]
    [Algebra ℚ_[p] K] : CharZero K :=
  charZero_of_injective_algebraMap (algebraMap ℚ_[p] K).injective

instance instIsAlgebraic : Algebra.IsAlgebraic ℚ_[p] K :=
  Algebra.IsAlgebraic.of_finite ℚ_[p] K

instance instIsSeparable : Algebra.IsSeparable ℚ_[p] K := by
  haveI : CharZero K := charZero_of_padicAlgebra p K
  exact Algebra.IsSeparable.of_integral ℚ_[p] K

instance instIsTorsionFreePadicInt : Module.IsTorsionFree ℤ_[p] K :=
  Module.isTorsionFree_iff_algebraMap_injective.mpr (algebraMap_padicInt_injective p K)

/-- The ring of integers `𝒪[K]` of a `p`-adic field `K`: the integral closure of
`ℤ_[p]` (the integers of `ℚ_[p]`) in `K`. The prime `p` is recovered from the
`PadicField` instance, so it is not an explicit argument. -/
def ringOfIntegers (K : Type*) [Field K] {p : ℕ} [Fact p.Prime] [Algebra ℚ_[p] K]
    [PadicField K p] : Subalgebra ℤ_[p] K := integralClosure ℤ_[p] K

@[inherit_doc] scoped notation "𝒪[" K "]" => PadicField.ringOfIntegers K

instance instIsIntegralClosure : IsIntegralClosure 𝒪[K] ℤ_[p] K :=
  integralClosure.isIntegralClosure ℤ_[p] K

instance : IsFractionRing 𝒪[K] K :=
  integralClosure.isFractionRing_of_finite_extension ℚ_[p] K

instance instAlgebraIsIntegralRingOfIntegers : Algebra.IsIntegral ℤ_[p] 𝒪[K] :=
  inferInstanceAs (Algebra.IsIntegral ℤ_[p] (integralClosure ℤ_[p] K))

instance instFiniteRingOfIntegers : Module.Finite ℤ_[p] 𝒪[K] :=
  IsIntegralClosure.finite ℤ_[p] ℚ_[p] K 𝒪[K]

instance instFreeRingOfIntegers : Module.Free ℤ_[p] 𝒪[K] :=
  IsIntegralClosure.module_free ℤ_[p] ℚ_[p] K 𝒪[K]

instance : CharZero 𝒪[K] :=
  haveI : CharZero K := charZero_of_padicAlgebra p K
  inferInstance

-- local instance : NormedField K := spectralNorm.normedField ℚ_[p] K

-- instance normedAlgebra : NormedAlgebra ℚ_[p] K := spectralNorm.normedAlgebra _ _

-- theorem isNonarchimedean : IsNonarchimedean (norm : K → ℝ) :=
--   isNonarchimedean_spectralNorm (K := ℚ_[p])

-- instance isUltrametricDist : IsUltrametricDist K :=
--   IsUltrametricDist.isUltrametricDist_of_forall_norm_add_le_max_norm (isNonarchimedean K)

-- instance : ValuativeRel K := .ofValuation (NormedField.valuation)

-- theorem norm_ext (x : ℚ_[p]) : ‖algebraMap ℚ_[p] K x‖ = ‖x‖ := by simp

-- instance : ValuativeRel.IsNontrivial K := by
--   haveI := Valuation.Compatible.ofValuation <| NormedField.valuation (K:=K)
--   rw [ValuativeRel.isNontrivial_iff_isNontrivial NormedField.valuation,
--     Valuation.isNontrivial_iff_exists_lt_one]
--   choose x hx using NontriviallyNormedField.non_trivial (α := ℚ_[p])
--   use algebraMap _ K x

--   infer_instance
--   -- exact inferInstance
--   exact IsDedekindDomain.HeightOneSpectrum.instIsNontrivialWithZeroMultiplicativeIntValuation _ _


-- instance : IsNonarchimedeanLocalField K where
--   mem_nhds_iff := _
--   local_compact_nhds := _
--   condition := _

scoped notation "𝓂[" K "]" => IsLocalRing.maximalIdeal 𝒪[K]

/-! ### Proof that `𝒪_K` is a discrete valuation ring (`prop:padic-is-dvf`)

`ℚ_[p]` is a complete nontrivially-normed field, so its spectral norm extends `‖·‖` to the
finite extension `K`. An element of `K` whose spectral norm is `≤ 1` is integral over `ℤ_[p]`
(its minimal polynomial has coefficients of norm `≤ 1`, i.e. in `ℤ_[p]`); hence
`𝒪_K = integralClosure ℤ_[p] K` is exactly the closed unit ball of the spectral norm, so it is
a valuation ring. Being a local Dedekind domain that is not a field, it is a DVR. -/

/-- If the spectral norm of `x : K` over `ℚ_[p]` is `≤ 1`, then `x` is integral over `ℤ_[p]`:
the coefficients of its minimal polynomial have norm `≤ 1`, hence lie in `ℤ_[p]`. -/
theorem isIntegral_of_spectralNorm_le_one {x : K} (hx : spectralNorm ℚ_[p] K x ≤ 1) :
    IsIntegral ℤ_[p] x := by
  have hlift : minpoly ℚ_[p] x ∈ Polynomial.lifts (algebraMap ℤ_[p] ℚ_[p]) := by
    refine (Polynomial.lifts_iff_coeff_lifts _).mpr fun i ↦ ?_
    have hi := (ciSup_le_iff (spectralValueTerms_bddAbove ..)).mp hx i
    simp only [spectralValueTerms] at hi
    split_ifs at hi with h
    · conv_rhs at hi => rw [← Real.one_rpow (1 / (↑(minpoly ℚ_[p] x).natDegree - ↑i) : ℝ)]
      rw [Real.rpow_le_rpow_iff (by positivity) (by positivity) (by aesop)] at hi
      exact ⟨⟨_, hi⟩, rfl⟩
    obtain h | h := (le_of_not_gt h).eq_or_lt
    · rw [← h]
      exact ⟨1, (map_one _).trans
        (minpoly.monic (Algebra.IsAlgebraic.isAlgebraic x).isIntegral).symm⟩
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt h]
      exact ⟨0, map_zero _⟩
  obtain ⟨P, hP, _, hP'⟩ := Polynomial.lifts_and_degree_eq_and_monic hlift
    (minpoly.monic (Algebra.IsAlgebraic.isAlgebraic x).isIntegral)
  refine ⟨P, hP', ?_⟩
  rw [← Polynomial.aeval_def, ← Polynomial.aeval_map_algebraMap ℚ_[p], hP, minpoly.aeval]

/-- The spectral norm over `ℚ_[p]` is multiplicative, hence inverts. -/
theorem spectralNorm_inv (x : K) :
    spectralNorm ℚ_[p] K x⁻¹ = (spectralNorm ℚ_[p] K x)⁻¹ := by
  rcases eq_or_ne x 0 with rfl | hx0
  · simp [spectralNorm_zero]
  · have h := spectralAlgNorm_mul (K := ℚ_[p]) (L := K) x x⁻¹
    rw [mul_inv_cancel₀ hx0, spectralAlgNorm_def, spectralAlgNorm_def, spectralAlgNorm_def,
      spectralNorm_one] at h
    exact eq_inv_of_mul_eq_one_right h.symm

/-- `𝒪_K = integralClosure ℤ_[p] K` is the closed unit ball of the spectral norm, hence a
valuation ring: every `x : K` has `x` or `x⁻¹` of spectral norm `≤ 1`. -/
instance instValuationRing : ValuationRing 𝒪[K] := by
  refine ValuationSubring.instValuationRingSubtypeMem
    (A := ⟨𝒪[K].toSubring, ?_⟩)
  intro x
  obtain hx | hx := le_total (spectralNorm ℚ_[p] K x) 1
  · exact Or.inl (isIntegral_of_spectralNorm_le_one (p := p) (K := K) hx)
  · refine Or.inr (isIntegral_of_spectralNorm_le_one (p := p) (K := K) ?_)
    rw [spectralNorm_inv]
    exact inv_le_one_of_one_le₀ hx

instance isDedekind : IsDedekindDomain 𝒪[K] :=
    IsIntegralClosure.isDedekindDomain ℤ_[p] ℚ_[p] K 𝒪[K]

theorem notField (p : ℕ) [Fact p.Prime] (K : Type*) [Field K] [Algebra ℚ_[p] K] :
    ¬ IsField (integralClosure ℤ_[p] K) := by
  have hinj : Function.Injective (algebraMap ℤ_[p] (integralClosure ℤ_[p] K)) := by
    have hK := algebraMap_padicInt_injective p K
    rw [IsScalarTower.algebraMap_eq ℤ_[p] (integralClosure ℤ_[p] K) K, RingHom.coe_comp] at hK
    exact hK.of_comp
  intro hF
  exact (IsDiscreteValuationRing.not_isField ℤ_[p])
    ((Algebra.IsIntegral.isField_iff_isField hinj).mpr hF)

/-- The ring of integers of a `p`-adic field is a discrete valuation ring
(blueprint `prop:padic-is-dvf`): `𝒪_K` is a valuation ring (`instValuationRing`, hence local),
a Dedekind domain and not a field, so the DVR characterization applies. -/
instance instIsDiscreteValuationRing :
    IsDiscreteValuationRing 𝒪[K] := by
  have hD : IsDedekindDomain 𝒪[K] := inferInstance
  exact ((IsDiscreteValuationRing.TFAE 𝒪[K] (notField p K)).out 2 0).mp hD

lemma maximalIdeal_ne_bot : 𝓂[K] ≠ ⊥ :=
  Ring.ne_bot_of_isMaximal_of_not_isField (IsLocalRing.maximalIdeal.isMaximal _) <| notField p K

def valuation := IsDedekindDomain.HeightOneSpectrum.valuation (R := 𝒪[K]) K <|
  ⟨𝓂[K], IsLocalRing.maximalIdeal.isMaximal 𝒪[K] |>.isPrime, maximalIdeal_ne_bot K⟩

instance : ValuativeRel K := .ofValuation <| valuation K

instance : ValuativeRel.IsNontrivial K := by
  haveI := Valuation.Compatible.ofValuation <| valuation K
  rw [ValuativeRel.isNontrivial_iff_isNontrivial (valuation K)]
  -- exact inferInstance
  exact IsDedekindDomain.HeightOneSpectrum.instIsNontrivialWithZeroMultiplicativeIntValuation _ _

instance : NormedField K := spectralNorm.normedField ℚ_[p] K

instance : NormedAlgebra ℚ_[p] K := spectralNorm.normedAlgebra _ _

instance : ProperSpace K := FiniteDimensional.proper ℚ_[p] K

theorem Norm.isNonarchimedean : IsNonarchimedean (norm : K → ℝ) := isNonarchimedean_spectralNorm

instance : IsUltrametricDist K :=
  IsUltrametricDist.isUltrametricDist_of_forall_norm_add_le_max_norm <| Norm.isNonarchimedean K

-- theorem valuation_eq_nnnorm (x : K): valuation K x = NormedField.valuation x := by
-- instance : TopologicalSpace K := (ValuativeRel.valuation K).subgroups_basis.topology

#check norm_le_spectralNorm
#check Valuation.toTopologicalSpace_eq

-- variable (R : Type*) [Ring R] [ValuativeRel R] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
-- variable [_t : TopologicalSpace R] [IsValuativeTopology R] (v : Valuation R Γ₀) [v.Compatible]
--   [TopologicalSpace K] [IsValuativeTopology K]
-- theorem toTopologicalSpace_eq :
--     _t = v.subgroups_basis.topology := by
--   let u := IsTopologicalAddGroup.rightUniformSpace R
--   let := isUniformAddGroup_of_addCommGroup (G := R)
--   exact congrArg (fun u ↦ @UniformSpace.toTopologicalSpace R u) v.toUniformSpace_eq

-- #check (IsTopologicalAddGroup.rightUniformSpace R)
variable (L : Type) [NormedField L] in
#synth TopologicalSpace L
#check Metric.mk_uniformity_basis
#synth ContinuousConstVAdd K K
-- #print toTopologicalSpace_eq
instance : IsValuativeTopology K := by
    apply IsValuativeTopology.of_zero _
    intro s
    simp [Metric.mem_nhds_iff, Metric.ball, dist]
    rw [Filter.hasBasis_iff.mp <| ?_]
    -- simp [neg_add_eq_sub, ← (valuation R).exists_setOf_restrict_le_iff,
    --   ← restrict_lt_iff_lt_embedding]

instance : IsNonarchimedeanLocalField K where
