/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_ValuationSubring_exists_smul_eq_and_card_stabilizer_eq_ramificationIdx_mul_inertiaDeg.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.Algebra.Module.Torsion.Free
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.RingTheory.Valuation.LocalSubring
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Localization.Integral
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Ideal.Over
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.DedekindDomain.Basic
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.NumberTheory.RamificationInertia.Ramification
import Mathlib.RingTheory.RamificationInertia.Ramification
import Mathlib.RingTheory.RamificationInertia.Inertia
import Mathlib.Tactic.Ext
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.Algebra.GroupWithZero.Action.Defs
import Mathlib.Algebra.Ring.Action.Field
import Mathlib.Data.Set.Card
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.GroupTheory.GroupAction.Defs
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.Galois.IsGaloisGroup
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.Ideal.Pointwise
import Mathlib.RingTheory.Invariant.Basic
import Mathlib.RingTheory.Invariant.Galois
import Mathlib.RingTheory.IsGaloisGroup.Basic
import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.RingTheory.Valuation.RamificationGroup

/-!
# Valuation Subring exists smul eq and card stabilizer eq ramification Idx mul inertia Deg
-/

section ProofImplementation

namespace AlgebraicCurves.Valuations.Proofs
namespace ValuationSubring_exists_smul_eq_and_card_stabilizer_eq_ramificationIdx_mul_inertiaDeg

namespace EmbCountGal

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
  let _ := overAlgebra B h
  exact IsScalarTower.of_algebraMap_eq fun a => rfl
include K in
omit [IsDomain C] [IsDiscreteValuationRing C] in
theorem algebraMap_injective : Function.Injective (algebraMap C F) := by
  rw [IsScalarTower.algebraMap_eq C K F]
  exact (algebraMap K F).injective.comp (IsFractionRing.injective C K)
include K in
omit [IsDomain C] [IsDiscreteValuationRing C] in
theorem algebraMap_overAlgebra_injective (B : ValuationSubring F)
    (h : ∀ c : C, algebraMap C F c ∈ B) :
    letI := overAlgebra B h
    Function.Injective (algebraMap C B) := by
  let _ := overAlgebra B h
  intro a b hab
  have := congrArg (fun z : B => (z : F)) hab
  exact algebraMap_injective K this

theorem comap_maximalIdeal_overAlgebra (B : ValuationSubring F) (h : Over C B) :
    letI := overAlgebra B h.mem
    (maximalIdeal B).comap (algebraMap C B) = maximalIdeal C := by
  let _ := overAlgebra B h.mem
  ext c
  rw [Ideal.mem_comap, ← h.nonunit_iff, ← ValuationSubring.coe_mem_nonunits_iff]
  rfl

theorem liesOver_overAlgebra (B : ValuationSubring F) (h : Over C B) :
    letI := overAlgebra B h.mem
    (maximalIdeal B).LiesOver (maximalIdeal C) := by
  let _ := overAlgebra B h.mem
  exact ⟨(comap_maximalIdeal_overAlgebra B h).symm⟩
omit [IsDomain C] [IsDiscreteValuationRing C] in
theorem mem_of_mem_integralClosure (B : ValuationSubring F) (h : ∀ c : C, algebraMap C F c ∈ B)
    {y : F} (hy : y ∈ integralClosure C F) : y ∈ B := by
  let _ := overAlgebra B h
  have _ := isScalarTower_overAlgebra B h
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
include K in
omit [IsDomain C] [IsDiscreteValuationRing C] in
theorem algebraMap_integralClosure_injective :
    Function.Injective (algebraMap C (integralClosure C F)) := by
  intro a b hab
  have := congrArg (fun z : integralClosure C F => (z : F)) hab
  exact algebraMap_injective K this
include K in
omit [IsDiscreteValuationRing C] in
theorem isTorsionFree_integralClosure : Module.IsTorsionFree C (integralClosure C F) := by
  rw [Module.isTorsionFree_iff_smul_eq_zero]
  intro r c hrc
  rw [Algebra.smul_def] at hrc
  rcases mul_eq_zero.mp hrc with h | h
  · exact Or.inl (algebraMap_integralClosure_injective K (by rw [h, map_zero]))
  · exact Or.inr h

theorem liesOver_maximalIdeal (v : HeightOneSpectrum (integralClosure C F)) :
    v.asIdeal.LiesOver (maximalIdeal C) := by
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

include K in
omit [IsDiscreteValuationRing C] [Algebra.IsSeparable K F] in
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

end EmbCountGal

namespace EmbCountGal

open IsLocalRing IsDedekindDomain
open scoped Pointwise

section dict2

variable {C : Type*} [CommRing C] [IsDomain C] [IsDiscreteValuationRing C]
variable (K : Type*) [Field K] [Algebra C K] [IsFractionRing C K]
variable {F : Type*} [Field F] [Algebra K F] [Algebra C F] [IsScalarTower C K F]
variable [IsFractionRing (integralClosure C F) F] [IsDedekindDomain (integralClosure C F)]

/-- The valuation ring of a height-one prime of the integral closure. -/
noncomputable abbrev Wv (v : HeightOneSpectrum (integralClosure C F)) : ValuationSubring F :=
  HeightOneSpectrum.valuationSubringAtPrime F v
omit [IsDomain C] [IsDiscreteValuationRing C] in
theorem coe_algebraMap_Wv (v : HeightOneSpectrum (integralClosure C F)) (s : integralClosure C F) :
    ((algebraMap (integralClosure C F) (Wv v) s : Wv v) : F) = (s : F) := rfl

theorem over_Wv (v : HeightOneSpectrum (integralClosure C F)) : Over C (Wv v) := by
  have _ := liesOver_maximalIdeal v
  have h1 : ∀ c : C, algebraMap C F c =
      ((algebraMap (integralClosure C F) (Wv v) (algebraMap C (integralClosure C F) c) : Wv v) : F)
        :=
    fun c => rfl
  refine ⟨fun c => ?_, fun c => ?_⟩
  · rw [h1]; exact SetLike.coe_mem _
  · rw [h1, ValuationSubring.coe_mem_nonunits_iff,
      IsLocalization.AtPrime.to_map_mem_maximal_iff (Wv v) v.asIdeal, ← Ideal.mem_comap,
      ← Ideal.under_def, ← Ideal.LiesOver.over (P := v.asIdeal) (p := maximalIdeal C)]

theorem Wv_vOf_le (B : ValuationSubring F) (h : Over C B) : Wv (vOf K B h) ≤ B := by
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

theorem Wv_vOf_eq (B : ValuationSubring F) (h : Over C B) : Wv (vOf K B h) = B :=
  ValuationSubring.eq_of_le_of_ne_top _ (Wv_vOf_le K B h) (ne_top_of_over K B h)

theorem vOf_Wv (v : HeightOneSpectrum (integralClosure C F)) : vOf K (Wv v) (over_Wv v) = v := by
  apply HeightOneSpectrum.ext
  ext s
  change s ∈ center (Wv v) (over_Wv v).mem ↔ s ∈ v.asIdeal
  rw [mem_center_iff, ← coe_algebraMap_Wv v s, ValuationSubring.coe_mem_nonunits_iff,
    IsLocalization.AtPrime.to_map_mem_maximal_iff (Wv v) v.asIdeal]
include K in
theorem ramificationIdx_mul_inertiaDeg_Wv (v : HeightOneSpectrum (integralClosure C F))
    (hv : ∀ c : C, algebraMap C F c ∈ Wv v) :
    letI := overAlgebra (Wv v) hv
    (maximalIdeal C).ramificationIdx' (maximalIdeal (Wv v)) *
      (maximalIdeal (Wv v)).inertiaDeg C =
    (maximalIdeal C).ramificationIdx' v.asIdeal * v.asIdeal.inertiaDeg C := by
  let _ : Algebra C (Wv v) := overAlgebra (Wv v) hv
  have _ := liesOver_maximalIdeal v
  have _ : IsScalarTower C (integralClosure C F) (Wv v) :=
    IsScalarTower.of_algebraMap_eq fun a => Subtype.ext rfl
  have _ : IsDiscreteValuationRing (Wv v) :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain (integralClosure C F)
      v.ne_bot (Wv v)
  have hmapS : Ideal.map (algebraMap (integralClosure C F) (Wv v)) v.asIdeal =
      maximalIdeal (Wv v) :=
    IsLocalization.AtPrime.map_eq_maximalIdeal v.asIdeal (Wv v)
  have hmW0 : maximalIdeal (Wv v) ≠ ⊥ := IsDiscreteValuationRing.not_a_field _
  have : (maximalIdeal (Wv v)).LiesOver v.asIdeal :=
    ⟨(IsLocalization.AtPrime.under_maximalIdeal (Wv v) v.asIdeal).symm⟩
  have he : (maximalIdeal C).ramificationIdx' (maximalIdeal (Wv v)) =
      (maximalIdeal C).ramificationIdx' v.asIdeal *
        v.asIdeal.ramificationIdx' (maximalIdeal (Wv v)) :=
    Ideal.ramificationIdx'_algebra_tower (by rw [hmapS]; exact hmW0)
      (by
        rw [Ne, Ideal.map_eq_bot_iff_of_injective (algebraMap_overAlgebra_injective K _ _)]
        exact maximalIdeal_ne_bot)
      hmapS.le
  have he1 : v.asIdeal.ramificationIdx' (maximalIdeal (Wv v)) = 1 := by
    rw [← hmapS]
    exact Ideal.ramificationIdx'_map_self_eq_one
      (by rw [hmapS]; exact (maximalIdeal.isMaximal _).ne_top) (by rw [hmapS]; exact hmW0)
  have hf : (maximalIdeal (Wv v)).inertiaDeg C =
      v.asIdeal.inertiaDeg C * (maximalIdeal (Wv v)).inertiaDeg (integralClosure C F) :=
    Ideal.inertiaDeg_tower _ _
  have hf1 : (maximalIdeal (Wv v)).inertiaDeg (integralClosure C F) = 1 :=
    inertiaDeg_maximalIdeal_eq_one_of_isLocalization v.asIdeal (Wv v)
  rw [he, he1, hf, hf1, mul_one, mul_one]

end dict2

section galois

variable {C : Type*} [CommRing C] [IsDomain C] [IsDiscreteValuationRing C]
variable (K : Type*) [Field K] [Algebra C K] [IsFractionRing C K]
variable {M : Type*} [Field M] [Algebra K M] [Algebra C M] [IsScalarTower C K M]
variable [IsFractionRing (integralClosure C M) M] [IsDedekindDomain (integralClosure C M)]
variable [MulSemiringAction (M ≃ₐ[K] M) (integralClosure C M)]
variable [SMulDistribClass (M ≃ₐ[K] M) (integralClosure C M) M]

omit [IsDomain C] [IsDiscreteValuationRing C] [IsFractionRing C K]
    [IsFractionRing (integralClosure C M) M] [IsDedekindDomain (integralClosure C M)]
    [MulSemiringAction (M ≃ₐ[K] M) (integralClosure C M)]
    [SMulDistribClass (M ≃ₐ[K] M) (integralClosure C M) M] in
theorem smul_algebraMap (σ : M ≃ₐ[K] M) (c : C) : σ • algebraMap C M c = algebraMap C M c := by
  rw [AlgEquiv.smul_def, IsScalarTower.algebraMap_apply C K M, AlgEquiv.commutes]

theorem mem_smul_nonunits_iff (σ : M ≃ₐ[K] M) (V : ValuationSubring M) (x : M) :
    x ∈ (σ • V).nonunits ↔ σ⁻¹ • x ∈ V.nonunits := by
  rw [mem_nonunits_iff_eq_zero_or_inv_not_mem, mem_nonunits_iff_eq_zero_or_inv_not_mem,
    ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, smul_inv'', smul_eq_zero_iff_eq]
omit [IsFractionRing C K] [IsFractionRing (integralClosure C M) M]
    [IsDedekindDomain (integralClosure C M)]
    [MulSemiringAction (M ≃ₐ[K] M) (integralClosure C M)]
    [SMulDistribClass (M ≃ₐ[K] M) (integralClosure C M) M] in
theorem over_smul (V : ValuationSubring M) (h : Over C V) (σ : M ≃ₐ[K] M) : Over C (σ • V) := by
  refine ⟨fun c => ?_, fun c => ?_⟩
  · rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, smul_algebraMap]; exact h.mem c
  · rw [mem_smul_nonunits_iff, smul_algebraMap]; exact h.nonunit_iff c
omit [IsDomain C] [IsDiscreteValuationRing C] [Algebra C K] [IsFractionRing C K]
    [IsScalarTower C K M] [IsFractionRing (integralClosure C M) M]
    [IsDedekindDomain (integralClosure C M)] in
theorem coe_smul_integralClosure (σ : M ≃ₐ[K] M) (s : integralClosure C M) :
    ((σ • s : integralClosure C M) : M) = σ • (s : M) := by
  have h1 : ∀ t : integralClosure C M, ((t : integralClosure C M) : M) = t • (1 : M) := fun t => by
    rw [← Algebra.algebraMap_eq_smul_one]; rfl
  rw [h1, h1 s, smul_distrib_smul, smul_one]
omit [IsDomain C] [IsDiscreteValuationRing C] [Algebra C K] [IsFractionRing C K] [IsScalarTower C K
  M]
    [IsFractionRing (integralClosure C M) M] [IsDedekindDomain (integralClosure C M)] in
theorem center_smul (V : ValuationSubring M) (h : ∀ c : C, algebraMap C M c ∈ V) (σ : M ≃ₐ[K] M)
    (h' : ∀ c : C, algebraMap C M c ∈ σ • V) :
    center (σ • V) h' = σ • center V h := by
  ext s
  rw [mem_center_iff, Ideal.mem_pointwise_smul_iff_inv_smul_mem, mem_center_iff,
    mem_smul_nonunits_iff, coe_smul_integralClosure]
omit [IsDomain C] [IsDiscreteValuationRing C]
    [IsFractionRing (integralClosure C M) M] [IsDedekindDomain (integralClosure C M)] in
theorem center_congr (V₁ V₂ : ValuationSubring M) (h₁ : ∀ c : C, algebraMap C M c ∈ V₁)
    (h₂ : ∀ c : C, algebraMap C M c ∈ V₂) (hV : V₁ = V₂) : center V₁ h₁ = center V₂ h₂ := by
  subst hV; rfl

variable [FiniteDimensional K M] [IsGaloisGroup (M ≃ₐ[K] M) C (integralClosure C M)]

include K in
theorem exists_smul_eq (V V' : ValuationSubring M) (h : Over C V) (h' : Over C V') :
    ∃ σ : M ≃ₐ[K] M, σ • V' = V := by
  have _ := liesOver_maximalIdeal (vOf K V h)
  have _ := liesOver_maximalIdeal (vOf K V' h')
  obtain ⟨σ, hσ⟩ := Ideal.exists_smul_eq_of_isGaloisGroup (maximalIdeal C) (vOf K V' h').asIdeal
    (vOf K V h).asIdeal (M ≃ₐ[K] M)
  refine ⟨σ, ?_⟩
  have hO : Over C (σ • V') := over_smul K V' h' σ
  have hc : center (σ • V') hO.mem = center V h.mem := by
    rw [center_smul K V' h'.mem σ hO.mem]; exact hσ
  have hv : vOf K (σ • V') hO = vOf K V h := HeightOneSpectrum.ext hc
  rw [← Wv_vOf_eq K (σ • V') hO, hv, Wv_vOf_eq K V h]
omit [FiniteDimensional K M] [IsGaloisGroup (M ≃ₐ[K] M) C (integralClosure C M)] in
theorem stabilizer_eq (V : ValuationSubring M) (h : Over C V) :
    MulAction.stabilizer (M ≃ₐ[K] M) V =
      MulAction.stabilizer (M ≃ₐ[K] M) (center V h.mem) := by
  ext σ
  rw [MulAction.mem_stabilizer_iff, MulAction.mem_stabilizer_iff]
  have hO : Over C (σ • V) := over_smul K V h σ
  constructor
  · intro hσ
    rw [← center_smul K V h.mem σ hO.mem]
    exact center_congr _ _ _ _ hσ
  · intro hσ
    have hc : center (σ • V) hO.mem = center V h.mem := by
      rw [center_smul K V h.mem σ hO.mem]; exact hσ
    have hv : vOf K (σ • V) hO = vOf K V h := HeightOneSpectrum.ext hc
    rw [← Wv_vOf_eq K (σ • V) hO, hv, Wv_vOf_eq K V h]

variable [Module.Finite C (integralClosure C M)]

include K in
theorem card_stabilizer (V : ValuationSubring M) (h : Over C V) :
    Nat.card ↥(MulAction.stabilizer (M ≃ₐ[K] M) V) =
      (maximalIdeal C).ramificationIdx' (vOf K V h).asIdeal *
        (vOf K V h).asIdeal.inertiaDeg C := by
  have _ := liesOver_maximalIdeal (vOf K V h)
  have _ := isTorsionFree_integralClosure K (F := M) (C := C)
  rw [stabilizer_eq K V h]
  change Nat.card ↥(MulAction.stabilizer (M ≃ₐ[K] M) (vOf K V h).asIdeal) = _
  have h1 : Nat.card ↥(MulAction.orbit (M ≃ₐ[K] M) (vOf K V h).asIdeal) *
      Nat.card ↥(MulAction.stabilizer (M ≃ₐ[K] M) (vOf K V h).asIdeal) = Nat.card (M ≃ₐ[K] M) := by
    rw [← Nat.card_prod]
    exact Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup (M ≃ₐ[K] M) (vOf K V h).asIdeal)
  rw [Algebra.IsInvariant.orbit_eq_primesOver C (integralClosure C M) (M ≃ₐ[K] M) (maximalIdeal C)
    (vOf K V h).asIdeal, Nat.card_coe_set_eq] at h1
  have h2 := Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn
    (maximalIdeal C) (integralClosure C M) (M ≃ₐ[K] M)
  rw [← h1] at h2
  have h3 := mul_left_cancel₀
    (IsDedekindDomain.primesOver_ncard_ne_zero (maximalIdeal C) (integralClosure C M)) h2
  have _ := (vOf K V h).isMaximal
  rw [← h3, Ideal.ramificationIdxIn_eq_ramificationIdx (maximalIdeal C) (vOf K V h).asIdeal (M
    ≃ₐ[K] M),
    Ideal.inertiaDegIn_eq_inertiaDeg (maximalIdeal C) (vOf K V h).asIdeal (M ≃ₐ[K] M)]
  congr 1
  exact (Ideal.ramificationIdx'_eq_ramificationIdx (p := maximalIdeal C) (q := (vOf K V h).asIdeal)
    (maximalIdeal_ne_bot (C := C))).symm

end galois

section assembly

variable {C : Type*} [CommRing C] [IsDomain C] [IsDiscreteValuationRing C]
variable (K : Type*) [Field K] [Algebra C K] [IsFractionRing C K]
variable {M : Type*} [Field M] [Algebra K M] [Algebra C M] [IsScalarTower C K M]
variable [FiniteDimensional K M] [IsGalois K M]

theorem ef_congr (V₁ V₂ : ValuationSubring M) (h₁ : ∀ c : C, algebraMap C M c ∈ V₁)
    (h₂ : ∀ c : C, algebraMap C M c ∈ V₂) (hV : V₁ = V₂) :
    (letI := overAlgebra V₁ h₁
     (maximalIdeal C).ramificationIdx' (maximalIdeal V₁) * (maximalIdeal V₁).inertiaDeg C) =
    (letI := overAlgebra V₂ h₂
     (maximalIdeal C).ramificationIdx' (maximalIdeal V₂) * (maximalIdeal V₂).inertiaDeg C) := by
  subst hV; rfl
include K in
theorem main (V : ValuationSubring M) (hCV : ∀ c : C, algebraMap C M c ∈ V)
    (hCVmax : ∀ c : C, algebraMap C M c ∈ V.nonunits ↔ c ∈ maximalIdeal C) :
    (∀ V' : ValuationSubring M, (∀ c : C, algebraMap C M c ∈ V') →
        (∀ c : C, algebraMap C M c ∈ V'.nonunits ↔ c ∈ maximalIdeal C) →
        ∃ g : M ≃ₐ[K] M, g • V' = V) ∧
    Nat.card ↥(V.decompositionSubgroup K) =
      (letI : Algebra C ↥V := ((algebraMap C M).codRestrict V hCV).toAlgebra
       (maximalIdeal C).ramificationIdx' (maximalIdeal ↥V) *
         (maximalIdeal ↥V).inertiaDeg C) := by
  have _ := isFractionRing_integralClosure K (F := M) (C := C)
  have _ := isDedekindDomain_integralClosure K (F := M) (C := C)
  have _ := finite_integralClosure K (F := M) (C := C)
  let _ : MulSemiringAction (M ≃ₐ[K] M) (integralClosure C M) :=
    IsIntegralClosure.MulSemiringAction C K M (integralClosure C M)
  have _ : IsGaloisGroup (M ≃ₐ[K] M) C (integralClosure C M) :=
    IsGaloisGroup.of_isFractionRing _ _ _ K M
  have h : Over C V := ⟨hCV, hCVmax⟩
  refine ⟨fun V' h1 h2 => exists_smul_eq K V V' h ⟨h1, h2⟩, ?_⟩
  change Nat.card ↥(MulAction.stabilizer (M ≃ₐ[K] M) V) = _
  rw [card_stabilizer K V h]
  have hv : ∀ c : C, algebraMap C M c ∈ Wv (vOf K V h) := (over_Wv (vOf K V h)).mem
  rw [← ramificationIdx_mul_inertiaDeg_Wv K (vOf K V h) hv]
  exact ef_congr _ _ _ _ (Wv_vOf_eq K V h)

end assembly

end EmbCountGal

open IsLocalRing in
open scoped Pointwise in
theorem _root_.ValuationSubring.exists_smul_eq_and_card_stabilizer_eq_ramificationIdx_mul_inertiaDeg
    {C : Type*} [CommRing C] [IsDomain C] [IsDiscreteValuationRing C]
    (K : Type*) [Field K] [Algebra C K] [IsFractionRing C K]
    {M : Type*} [Field M] [Algebra K M] [Algebra C M] [IsScalarTower C K M]
    [FiniteDimensional K M] [IsGalois K M]
    (V : ValuationSubring M) (hCV : ∀ c : C, algebraMap C M c ∈ V)
    (hCVmax : ∀ c : C, algebraMap C M c ∈ V.nonunits ↔ c ∈ maximalIdeal C) :
    (∀ V' : ValuationSubring M, (∀ c : C, algebraMap C M c ∈ V') →
        (∀ c : C, algebraMap C M c ∈ V'.nonunits ↔ c ∈ maximalIdeal C) →
        ∃ g : M ≃ₐ[K] M, g • V' = V) ∧
    Nat.card ↥(V.decompositionSubgroup K) =
      (letI : Algebra C ↥V := ((algebraMap C M).codRestrict V hCV).toAlgebra
       (maximalIdeal C).ramificationIdx' (maximalIdeal ↥V) *
         (maximalIdeal ↥V).inertiaDeg C) :=
  EmbCountGal.main K V hCV hCVmax
end ValuationSubring_exists_smul_eq_and_card_stabilizer_eq_ramificationIdx_mul_inertiaDeg
end AlgebraicCurves.Valuations.Proofs
end ProofImplementation
