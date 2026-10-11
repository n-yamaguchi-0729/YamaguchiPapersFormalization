/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_ValuationSubring_isDiscreteValuationRing_of_forall_algebraMap_mem_of_isSeparable.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.Algebra.Module.Torsion.Free
import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.RingTheory.Valuation.LocalSubring
import Mathlib.RingTheory.RamificationInertia.Inertia
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Localization.Integral
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.RingTheory.DiscreteValuationRing.Basic

/-!
# Valuation Subring is Discrete Valuation Ring of forall algebra Map mem of is Separable
-/

section ProofImplementation

namespace AlgebraicCurves.Valuations.Proofs
namespace ValuationSubring_isDiscreteValuationRing_of_forall_algebraMap_mem_of_isSeparable

namespace EmbCountDvr

open IsLocalRing IsDedekindDomain

section general

variable {L : Type*} [Field L]

theorem isUnit_iff_inv_mem (V : ValuationSubring L) (x : V) (hx0 : (x : L) ≠ 0) :
    IsUnit x ↔ (x : L)⁻¹ ∈ V := by
  refine ⟨fun hx => ?_, fun hx => ?_⟩
  · obtain ⟨y, hy⟩ := hx.exists_left_inv
    have hyx : (y : L) * (x : L) = 1 := by
      have := congrArg (Subtype.val) hy
      simpa using this
    rw [← eq_inv_of_mul_eq_one_left hyx]
    exact y.2
  · exact isUnit_iff_exists_inv.mpr ⟨⟨_, hx⟩, Subtype.ext (mul_inv_cancel₀ hx0)⟩

theorem mem_maximalIdeal_iff_inv_not_mem (V : ValuationSubring L) (x : V) (hx0 : (x : L) ≠ 0) :
    x ∈ maximalIdeal V ↔ (x : L)⁻¹ ∉ V := by
  rw [IsLocalRing.mem_maximalIdeal, _root_.mem_nonunits_iff, isUnit_iff_inv_mem V x hx0]

theorem mem_nonunits_iff_eq_zero_or_inv_not_mem (V : ValuationSubring L) (x : L) :
    x ∈ V.nonunits ↔ x = 0 ∨ x⁻¹ ∉ V := by
  rw [ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal]
  constructor
  · rintro ⟨hxV, hmax⟩
    by_cases hx0 : x = 0
    · exact Or.inl hx0
    · exact Or.inr ((mem_maximalIdeal_iff_inv_not_mem V ⟨x, hxV⟩ hx0).mp hmax)
  · rintro (rfl | hinv)
    · exact ⟨V.zero_mem, by
        have : (⟨(0 : L), V.zero_mem⟩ : V) = 0 := rfl
        rw [this]; exact Ideal.zero_mem _⟩
    · have hx0 : x ≠ 0 := by rintro rfl; exact hinv (by rw [inv_zero]; exact V.zero_mem)
      have hxV : x ∈ V := (V.mem_or_inv_mem x).resolve_right hinv
      exact ⟨hxV, (mem_maximalIdeal_iff_inv_not_mem V ⟨x, hxV⟩ hx0).mpr hinv⟩

theorem inertiaDeg_maximalIdeal_eq_one_of_isLocalization {R : Type*} [CommRing R]
    (p : Ideal R) [p.IsMaximal] (Rₚ : Type*) [CommRing Rₚ] [Algebra R Rₚ]
    [IsLocalization.AtPrime Rₚ p] [IsLocalRing Rₚ] :
    (maximalIdeal Rₚ).inertiaDeg R = 1 := by
  have : (maximalIdeal Rₚ).LiesOver p :=
    ⟨(IsLocalization.AtPrime.under_maximalIdeal Rₚ p).symm⟩
  rw [Ideal.inertiaDeg_eq_of_isMaximal p (maximalIdeal Rₚ)]
  let e := IsLocalization.AtPrime.equivQuotMaximalIdeal p Rₚ
  have he : ∀ c, e c = algebraMap (R ⧸ p) (Rₚ ⧸ maximalIdeal Rₚ) c := by
    intro c
    obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective c
    rfl
  let e' : (R ⧸ p) ≃ₗ[R ⧸ p] (Rₚ ⧸ maximalIdeal Rₚ) :=
    { e with
      map_smul' := fun c x => by
        change e (c * x) = c • e x
        rw [map_mul, Algebra.smul_def, he] }
  rw [← e'.finrank_eq, Module.finrank_self]

end general

/-- Compatibility of a valuation ring with a local base ring and its maximal ideal. -/
structure Over (C : Type*) [CommRing C] [IsLocalRing C] {F : Type*} [Field F] [Algebra C F]
    (B : ValuationSubring F) : Prop where
  /-- The valuation ring contains the image of the local base ring. -/
  mem : ∀ c : C, algebraMap C F c ∈ B
  /-- The preimage of the valuation-ring nonunits is the maximal ideal of the base ring. -/
  nonunit_iff : ∀ c : C, algebraMap C F c ∈ B.nonunits ↔ c ∈ maximalIdeal C

section dict

variable {C : Type*} [CommRing C] [IsDomain C] [IsDiscreteValuationRing C]
variable (K : Type*) [Field K] [Algebra C K] [IsFractionRing C K]
variable {F : Type*} [Field F] [Algebra K F] [Algebra C F] [IsScalarTower C K F]

/-- The algebra structure on the valuation subring induced by the base-ring map landing in it. -/
abbrev overAlgebra (B : ValuationSubring F) (h : ∀ c : C, algebraMap C F c ∈ B) : Algebra C B :=
  ((algebraMap C F).codRestrict B h).toAlgebra
omit [IsDomain C] [IsDiscreteValuationRing C] in
theorem coe_algebraMap_overAlgebra (B : ValuationSubring F) (h : ∀ c : C, algebraMap C F c ∈ B)
    (c : C) :
    letI := overAlgebra B h
    ((algebraMap C B c : B) : F) = algebraMap C F c := rfl
omit [IsDomain C] [IsDiscreteValuationRing C] in
theorem isScalarTower_overAlgebra (B : ValuationSubring F) (h : ∀ c : C, algebraMap C F c ∈ B) :
    letI := overAlgebra B h
    IsScalarTower C B F := by
  let := overAlgebra B h
  exact IsScalarTower.of_algebraMap_eq fun a => rfl
omit [IsDomain C] [IsDiscreteValuationRing C] in
include K in
theorem algebraMap_injective : Function.Injective (algebraMap C F) := by
  rw [IsScalarTower.algebraMap_eq C K F]
  exact (algebraMap K F).injective.comp (IsFractionRing.injective C K)
omit [IsDomain C] [IsDiscreteValuationRing C] in
include K in
theorem algebraMap_overAlgebra_injective (B : ValuationSubring F)
    (h : ∀ c : C, algebraMap C F c ∈ B) :
    letI := overAlgebra B h
    Function.Injective (algebraMap C B) := by
  let := overAlgebra B h
  intro a b hab
  have := congrArg (fun z : B => (z : F)) hab
  exact algebraMap_injective K this

theorem comap_maximalIdeal_overAlgebra (B : ValuationSubring F) (h : Over C B) :
    letI := overAlgebra B h.mem
    (maximalIdeal B).comap (algebraMap C B) = maximalIdeal C := by
  let := overAlgebra B h.mem
  ext c
  rw [Ideal.mem_comap, ← h.nonunit_iff, ← ValuationSubring.coe_mem_nonunits_iff]
  rfl

theorem liesOver_overAlgebra (B : ValuationSubring F) (h : Over C B) :
    letI := overAlgebra B h.mem
    (maximalIdeal B).LiesOver (maximalIdeal C) := by
  let := overAlgebra B h.mem
  exact ⟨(comap_maximalIdeal_overAlgebra B h).symm⟩
omit [IsDomain C] [IsDiscreteValuationRing C] in
theorem mem_of_mem_integralClosure (B : ValuationSubring F) (h : ∀ c : C, algebraMap C F c ∈ B)
    {y : F} (hy : y ∈ integralClosure C F) : y ∈ B := by
  let := overAlgebra B h
  have := isScalarTower_overAlgebra B h
  have hyB : IsIntegral B y := ((mem_integralClosure_iff C F).mp hy).tower_top
  obtain ⟨z, hz⟩ := (isIntegrallyClosed_iff F).mp inferInstance hyB
  rw [← hz]
  exact z.2
include K in
theorem ne_top_of_over (B : ValuationSubring F) (h : Over C B) : B ≠ ⊤ := by
  intro hB
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible C
  have hϖ0 : algebraMap C F ϖ ≠ 0 := (map_ne_zero_iff _ (algebraMap_injective K)).mpr hϖ.ne_zero
  have hmem : algebraMap C F ϖ ∈ B.nonunits :=
    (h.nonunit_iff ϖ).mpr ((IsLocalRing.mem_maximalIdeal _).mpr hϖ.not_isUnit)
  rcases (mem_nonunits_iff_eq_zero_or_inv_not_mem B _).mp hmem with h0 | hinv
  · exact hϖ0 h0
  · apply hinv
    rw [hB]
    exact ValuationSubring.mem_top _

theorem maximalIdeal_ne_bot : maximalIdeal C ≠ ⊥ :=
  IsDiscreteValuationRing.not_a_field C
omit [IsDomain C] [IsDiscreteValuationRing C] in
theorem coe_algebraMap_integralClosure (c : C) :
    ((algebraMap C (integralClosure C F) c : integralClosure C F) : F) = algebraMap C F c := rfl
omit [IsDomain C] [IsDiscreteValuationRing C] in
include K in
theorem algebraMap_integralClosure_injective :
    Function.Injective (algebraMap C (integralClosure C F)) := by
  intro a b hab
  have := congrArg (fun z : integralClosure C F => (z : F)) hab
  exact algebraMap_injective K this
omit [IsDiscreteValuationRing C] in
include K in
theorem isTorsionFree_integralClosure : Module.IsTorsionFree C (integralClosure C F) := by
  rw [Module.isTorsionFree_iff_smul_eq_zero]
  intro r c hrc
  rw [Algebra.smul_def] at hrc
  rcases mul_eq_zero.mp hrc with h | h
  · exact Or.inl (algebraMap_integralClosure_injective K (by rw [h, map_zero]))
  · exact Or.inr h
include K in
theorem liesOver_maximalIdeal (v : HeightOneSpectrum (integralClosure C F)) :
    v.asIdeal.LiesOver (maximalIdeal C) := by
  have := isTorsionFree_integralClosure K (F := F) (C := C)
  refine ⟨(IsLocalRing.eq_maximalIdeal ?_).symm⟩
  have hne : v.asIdeal.under C ≠ ⊥ := fun h0 =>
    v.ne_bot (Ideal.eq_bot_of_under_eq_bot h0)
  exact Ring.DimensionLEOne.maximalOfPrime hne (Ideal.IsPrime.under C v.asIdeal)

/-- The inclusion of the integral closure into a valuation ring containing the base ring. -/
noncomputable def toOver (B : ValuationSubring F) (h : ∀ c : C, algebraMap C F c ∈ B) :
    integralClosure C F →+* B :=
  (algebraMap (integralClosure C F) F).codRestrict B fun y => mem_of_mem_integralClosure B h y.2
omit [IsDomain C] [IsDiscreteValuationRing C] in
@[scoped simp] theorem coe_toOver (B : ValuationSubring F) (h : ∀ c : C, algebraMap C F c ∈ B)
    (s : integralClosure C F) : ((toOver B h s : B) : F) = (s : F) := rfl

/-- The center of the valuation on the integral closure of the local base ring. -/
noncomputable def center (B : ValuationSubring F) (h : ∀ c : C, algebraMap C F c ∈ B) :
    Ideal (integralClosure C F) :=
  (maximalIdeal B).comap (toOver B h)
omit [IsDomain C] [IsDiscreteValuationRing C] in
theorem mem_center_iff (B : ValuationSubring F) (h : ∀ c : C, algebraMap C F c ∈ B)
    (s : integralClosure C F) :
    s ∈ center B h ↔ (s : F) ∈ B.nonunits := by
  rw [center, Ideal.mem_comap, ← ValuationSubring.coe_mem_nonunits_iff]
  rfl

scoped instance center_isPrime (B : ValuationSubring F) (h : ∀ c : C, algebraMap C F c ∈ B) :
    (center B h).IsPrime :=
  Ideal.comap_isPrime _ _

include K in
theorem center_ne_bot (B : ValuationSubring F) (h : Over C B) : center B h.mem ≠ ⊥ := by
  intro h0
  have h1 : (center B h.mem).comap (algebraMap C (integralClosure C F)) = ⊥ := by
    rw [h0]; exact Ideal.comap_bot_of_injective _ (algebraMap_integralClosure_injective K)
  have h2 : (center B h.mem).comap (algebraMap C (integralClosure C F)) = maximalIdeal C := by
    ext c
    rw [Ideal.mem_comap, mem_center_iff, coe_algebraMap_integralClosure, h.nonunit_iff]
  exact maximalIdeal_ne_bot (h2 ▸ h1)

/-- The height-one prime obtained from the center of a valuation lying over the local base
ring. -/
noncomputable def vOf (B : ValuationSubring F) (h : Over C B) :
    HeightOneSpectrum (integralClosure C F) :=
  ⟨center B h.mem, inferInstance, center_ne_bot K B h⟩

section finite

variable [FiniteDimensional K F] [Algebra.IsSeparable K F]

omit [IsDiscreteValuationRing C] [Algebra.IsSeparable K F] in
include K in
theorem isFractionRing_integralClosure : IsFractionRing (integralClosure C F) F :=
  integralClosure.isFractionRing_of_finite_extension K F
include K in
theorem isDedekindDomain_integralClosure : IsDedekindDomain (integralClosure C F) :=
  integralClosure.isDedekindDomain C K F
include K in
theorem finite_integralClosure : Module.Finite C (integralClosure C F) :=
  IsIntegralClosure.finite C K F (integralClosure C F)

/-- The valuation ring at a height-one prime of the Dedekind integral closure. -/
noncomputable def W (v : HeightOneSpectrum (integralClosure C F)) : ValuationSubring F :=
  letI := isFractionRing_integralClosure K (F := F) (C := C)
  letI := isDedekindDomain_integralClosure K (F := F) (C := C)
  HeightOneSpectrum.valuationSubringAtPrime F v

theorem W_def (v : HeightOneSpectrum (integralClosure C F)) :
    letI := isFractionRing_integralClosure K (F := F) (C := C)
    letI := isDedekindDomain_integralClosure K (F := F) (C := C)
    W K v = HeightOneSpectrum.valuationSubringAtPrime F v := rfl

end finite

end dict

end EmbCountDvr

namespace EmbCountDvr

open IsLocalRing IsDedekindDomain

section main

variable {C : Type*} [CommRing C] [IsDomain C] [IsDiscreteValuationRing C]
variable (K : Type*) [Field K] [Algebra C K] [IsFractionRing C K]
variable {F : Type*} [Field F] [Algebra K F] [Algebra C F] [IsScalarTower C K F]
variable [FiniteDimensional K F] [Algebra.IsSeparable K F]

include K in
theorem main (B : ValuationSubring F) (h : Over C B) : IsDiscreteValuationRing ↥B := by
  have := isFractionRing_integralClosure K (F := F) (C := C)
  have := isDedekindDomain_integralClosure K (F := F) (C := C)
  let v : HeightOneSpectrum (integralClosure C F) := vOf K B h
  have hle : HeightOneSpectrum.valuationSubringAtPrime F v ≤ B := by
    rintro y ⟨a, s, hs, rfl⟩
    refine B.mul_mem _ _ (mem_of_mem_integralClosure B h.mem a.2) ?_
    have hs' : s ∉ center B h.mem := hs
    have hs0 : (s : F) ≠ 0 := by
      rintro h0
      apply hs'
      have : s = 0 := Subtype.ext h0
      rw [this]; exact Ideal.zero_mem _
    have := (mem_maximalIdeal_iff_inv_not_mem B (toOver B h.mem s) hs0).not.mp
      (fun hm => hs' (Ideal.mem_comap.mpr hm))
    simpa using this
  have heq : HeightOneSpectrum.valuationSubringAtPrime F v = B :=
    ValuationSubring.eq_of_le_of_ne_top _ hle (ne_top_of_over K B h)
  rw [← heq]
  exact IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain (integralClosure C F)
    v.ne_bot (HeightOneSpectrum.valuationSubringAtPrime F v)

end main

end EmbCountDvr

open IsLocalRing in
theorem _root_.ValuationSubring.isDiscreteValuationRing_of_forall_algebraMap_mem_of_isSeparable
    {C : Type*} [CommRing C] [IsDomain C] [IsDiscreteValuationRing C]
    (K : Type*) [Field K] [Algebra C K] [IsFractionRing C K]
    {F : Type*} [Field F] [Algebra K F] [Algebra C F] [IsScalarTower C K F]
    [FiniteDimensional K F] [Algebra.IsSeparable K F]
    (B : ValuationSubring F) (hCB : ∀ c : C, algebraMap C F c ∈ B)
    (hCBmax : ∀ c : C, algebraMap C F c ∈ B.nonunits ↔ c ∈ maximalIdeal C) :
    IsDiscreteValuationRing ↥B :=
  EmbCountDvr.main K B ⟨hCB, hCBmax⟩
end ValuationSubring_isDiscreteValuationRing_of_forall_algebraMap_mem_of_isSeparable
end AlgebraicCurves.Valuations.Proofs
end ProofImplementation
