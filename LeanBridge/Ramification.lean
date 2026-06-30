import Mathlib

/-!
# Higher ramification groups and Hilbert's different formula

This module develops the lower-numbering ramification filtration `Vₘ` for a Galois group
acting on a Dedekind domain, and Hilbert's different formula. It is independent of the
Kronecker–Weber theorem and is intended to be reusable; the Kronecker–Weber development
(`LeanBridge.KroneckerWeber`) imports it.

Throughout, `G` is a group acting on the ring `B` (the Galois group of `L/K` acting on
`S = 𝒪_L`), and `Q` is a prime of `B`. The proofs are currently `sorry`; this module fixes
faithful statements and the canonical Mathlib types. Mathlib does not yet contain the
ramification-group filtration or Hilbert's formula, so these are the genuine leaves to develop.
-/

noncomputable section

open Polynomial

namespace Ramification

/-- The `m`-th ramification group (lower numbering): the elements of `G` acting trivially on
`B / Q^{m+1}`. With Mathlib's `Ideal.inertia`, `V_0 = E` is the inertia group and the family is
descending with trivial intersection. -/
def ramificationGroup (G : Type*) [Group G] {B : Type*} [CommRing B] [MulSemiringAction G B]
    (Q : Ideal B) (m : ℕ) : Subgroup G :=
  Ideal.inertia G (Q ^ (m + 1))

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
variable {G : Type*} [Group G] [MulSemiringAction G B]

/-- **Uniformizer criterion.** For a uniformizer `π ∈ Q ∖ Q²` and `σ` in the inertia group,
membership in `V_m` is detected on `π` alone: `σ ∈ V_m ↔ σ(π) ≡ π (mod Q^{m+1})`. -/
theorem mem_ramificationGroup_iff [IsDedekindDomain B] [IsGaloisGroup G A B]
    {Q : Ideal B} [Q.IsPrime] {π : B} (hπ : π ∈ Q) (hπ2 : π ∉ Q ^ 2)
    {σ : G} (hσ : σ ∈ ramificationGroup G Q 0) (m : ℕ) :
    σ ∈ ramificationGroup G Q m ↔ σ • π - π ∈ Q ^ (m + 1) := by
  sorry

/-- **Tame quotient embeds in the residue units.** The map `σ ↦ α_σ mod Q` is a homomorphism from
the inertia group `E = V_0` to `(S/Q)ˣ` whose kernel is `V_1`. Consequently `E/V_1` is cyclic of
order dividing `|S/Q| - 1`. -/
theorem inertia_quotient_ramificationGroup_one [IsDedekindDomain B] [IsGaloisGroup G A B]
    {Q : Ideal B} [Q.IsPrime] :
    ∃ f : ramificationGroup G Q 0 →* (B ⧸ Q)ˣ,
      f.ker = (ramificationGroup G Q 1).subgroupOf (ramificationGroup G Q 0) := by
  sorry

/-- **Wild quotients embed in the residue field.** For `m ≥ 1` the map `σ ↦ α_σ mod Q` is a
homomorphism from `V_m` to the additive group of `S/Q` with kernel `V_{m+1}`; hence `V_m/V_{m+1}`
is elementary abelian of exponent `p`. -/
theorem ramificationGroup_quotient_succ [IsDedekindDomain B] [IsGaloisGroup G A B]
    {Q : Ideal B} [Q.IsPrime] {m : ℕ} (hm : 1 ≤ m) :
    ∃ f : ramificationGroup G Q m →* Multiplicative (B ⧸ Q),
      f.ker = (ramificationGroup G Q (m + 1)).subgroupOf (ramificationGroup G Q m) := by
  sorry

/-- **`V_1` is the Sylow `p`-subgroup of inertia**, where `p` is the residue characteristic. In
particular `V_1 ≠ {1}` iff `p ∣ e`, and `p ∤ e` forces `V_1 = {1}`. -/
theorem ramificationGroup_one_isSylow [IsDedekindDomain B] [IsGaloisGroup G A B] [Finite G]
    {Q : Ideal B} [Q.IsPrime] (p : ℕ) [Fact p.Prime] [CharP (B ⧸ Q) p] :
    ∃ S : Sylow p (ramificationGroup G Q 0),
      (S : Subgroup (ramificationGroup G Q 0)) =
        (ramificationGroup G Q 1).subgroupOf (ramificationGroup G Q 0) := by
  sorry

/-- **Abelian refinement to the base residue units.** If the Galois group is abelian then the
homomorphism of `inertia_quotient_ramificationGroup_one` factors through `(R/P)ˣ ⊆ (S/Q)ˣ`; i.e.
there is a homomorphism `E → (R/P)ˣ` with kernel `V_1`. Hence `E/V_1` is cyclic of order dividing
`‖P‖ - 1`. -/
theorem inertia_quotient_le_base_residue [IsDedekindDomain B] [IsGaloisGroup G A B]
    [IsMulCommutative G] {Q : Ideal B} [Q.IsPrime] {P : Ideal A} [P.IsPrime] [Q.LiesOver P] :
    ∃ f : ramificationGroup G Q 0 →* (A ⧸ P)ˣ,
      f.ker = (ramificationGroup G Q 1).subgroupOf (ramificationGroup G Q 0) := by
  sorry

/-- **Hilbert's different formula.** If `Q^k` is the exact power of `Q` dividing the different
`diff(S | R)`, then `k = ∑_{m ≥ 0} (|V_m| - 1)`. -/
theorem hilbert_different_formula [IsDedekindDomain A] [IsDedekindDomain B] [Module.Finite A B]
    [NoZeroSMulDivisors A B] [IsGaloisGroup G A B] [Finite G] {Q : Ideal B} [Q.IsPrime]
    {P : Ideal A} [P.IsPrime] [Q.LiesOver P] :
    ∃ k : ℕ, Q ^ k ∣ differentIdeal A B ∧ ¬ Q ^ (k + 1) ∣ differentIdeal A B ∧
      k = ∑ᶠ m : ℕ, (Nat.card (ramificationGroup G Q m) - 1) := by
  sorry

end Ramification
