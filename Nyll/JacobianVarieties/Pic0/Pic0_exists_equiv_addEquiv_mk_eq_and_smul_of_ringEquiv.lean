/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_Pic0_exists_equiv_addEquiv_mk_eq_and_smul_of_ringEquiv.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Divisors.ClassGroup
import Nyll.AlgebraicCurves.Places.Place_exists_equiv_comap_eq_and_ord_eq_and_deg_eq_of_ringEquiv

/-!
# Picard groups under equivalences of function fields

Transport places, divisor classes, and scalar actions along the given field equivalence.
-/

section ProofImplementation

namespace JacobianVarieties.Pic0.Proofs.Pic0_exists_equiv_addEquiv_mk_eq_and_smul_of_ringEquiv

open AlgebraicCurve
open scoped Pointwise

noncomputable section

namespace Pic0Transport

variable {K K' F F' : Type} [Field K] [Field K'] [Field F] [Field F'] [Algebra K F] [Algebra K' F']

section Divisors

variable (Φ : Place K F ≃ Place K' F')

theorem mapDomain_apply (D : Divisor K F) (w : Place K' F') :
    Finsupp.mapDomain Φ D w = D (Φ.symm w) :=
  Finsupp.mapDomain_equiv_apply D w

theorem mapDomain_symm_mapDomain (D : Divisor K F) :
    Finsupp.mapDomain Φ.symm (Finsupp.mapDomain Φ D) = D := by
  rw [← Finsupp.mapDomain_comp, Equiv.symm_comp_self, Finsupp.mapDomain_id]

theorem mapDomain_mapDomain_symm (D' : Divisor K' F') :
    Finsupp.mapDomain Φ (Finsupp.mapDomain Φ.symm D') = D' := by
  rw [← Finsupp.mapDomain_comp, Equiv.self_comp_symm, Finsupp.mapDomain_id]

theorem degree_mapDomain (hdeg : ∀ v : Place K F, (Φ v).deg = v.deg) (D : Divisor K F) :
    Divisor.degree (Finsupp.mapDomain Φ D) = Divisor.degree D := by
  have e : ∀ {K₁ F₁ : Type} [Field K₁] [Field F₁] [Algebra K₁ F₁] (E : Divisor K₁ F₁),
      Divisor.degree E = E.sum (fun v c => c * (v.deg : ℤ)) := by
    intro K₁ F₁ _ _ _ E
    rw [Divisor.degree, Finsupp.liftAddHom_apply]; rfl
  rw [e, e, Finsupp.sum_mapDomain_index_inj Φ.injective]
  simp only [hdeg]

theorem isPrincipal_mapDomain (φ : F ≃+* F')
    (hord : ∀ (v : Place K F) (f : F), (Φ v).ord (φ f) = v.ord f)
    {D : Divisor K F} (hD : Divisor.IsPrincipal D) :
      Divisor.IsPrincipal (Finsupp.mapDomain Φ D) := by
  obtain ⟨f, hf, hDf⟩ := hD
  refine ⟨φ f, (map_ne_zero φ).mpr hf, fun w => ?_⟩
  rw [mapDomain_apply, hDf (Φ.symm w), ← hord (Φ.symm w) f, Equiv.apply_symm_apply]

theorem isPrincipal_mapDomain_symm (φ : F ≃+* F')
    (hord : ∀ (v : Place K F) (f : F), (Φ v).ord (φ f) = v.ord f)
    {D' : Divisor K' F'} (hD : Divisor.IsPrincipal D') :
      Divisor.IsPrincipal (Finsupp.mapDomain Φ.symm D') := by
  obtain ⟨f', hf, hDf⟩ := hD
  refine ⟨φ.symm f', (map_ne_zero φ.symm).mpr hf, fun v => ?_⟩
  rw [Finsupp.mapDomain_equiv_apply, Equiv.symm_symm, hDf (Φ v), ← hord v (φ.symm f'),
    RingEquiv.apply_symm_apply]

/-- Transport degree-zero divisors along a degree-preserving equivalence of places. -/
def degZeroMap (hdeg : ∀ v : Place K F, (Φ v).deg = v.deg) :
    Divisor.degZero (K := K) (F := F) →+ Divisor.degZero (K := K') (F := F') :=
  ((Finsupp.mapDomain.addMonoidHom Φ).domRestrict (Divisor.degZero (K := K) (F := F))).codRestrict _
    (fun D => by
      change Finsupp.mapDomain Φ (D : Divisor K F) ∈ Divisor.degZero
      rw [Divisor.mem_degZero, degree_mapDomain Φ hdeg]
      exact D.2)

@[scoped simp] theorem coe_degZeroMap (hdeg : ∀ v : Place K F, (Φ v).deg = v.deg)
    (D : Divisor.degZero (K := K) (F := F)) :
    (degZeroMap Φ hdeg D : Divisor K' F') = Finsupp.mapDomain Φ (D : Divisor K F) := rfl

/-- Transport degree-zero divisors back along the inverse equivalence of places. -/
def degZeroMapSymm (hdeg : ∀ v : Place K F, (Φ v).deg = v.deg) :
    Divisor.degZero (K := K') (F := F') →+ Divisor.degZero (K := K) (F := F) :=
  ((Finsupp.mapDomain.addMonoidHom Φ.symm).domRestrict
    (Divisor.degZero (K := K') (F := F'))).codRestrict _
    (fun D' => by
      change Finsupp.mapDomain Φ.symm (D' : Divisor K' F') ∈ Divisor.degZero
      rw [Divisor.mem_degZero, ← degree_mapDomain Φ hdeg, mapDomain_mapDomain_symm]
      exact D'.2)

@[scoped simp] theorem coe_degZeroMapSymm (hdeg : ∀ v : Place K F, (Φ v).deg = v.deg)
    (D' : Divisor.degZero (K := K') (F := F')) :
    (degZeroMapSymm Φ hdeg D' : Divisor K F) = Finsupp.mapDomain Φ.symm (D' : Divisor K' F') := rfl

end Divisors

section Pic

variable (Φ : Place K F ≃ Place K' F') (φ : F ≃+* F')
  (hord : ∀ (v : Place K F) (f : F), (Φ v).ord (φ f) = v.ord f)
  (hdeg : ∀ v : Place K F, (Φ v).deg = v.deg)

/-- The homomorphism on Picard groups induced by transporting places and principal divisors. -/
def picMap : Pic0 K F →+ Pic0 K' F' :=
  QuotientAddGroup.map _ _ (degZeroMap Φ hdeg) (by
    rintro ⟨D, hD0⟩ hD
    simp only [AddSubgroup.mem_addSubgroupOf] at hD ⊢
    exact isPrincipal_mapDomain Φ φ hord hD)

/-- The inverse homomorphism on Picard groups induced by the inverse equivalence of places. -/
def picMapSymm : Pic0 K' F' →+ Pic0 K F :=
  QuotientAddGroup.map _ _ (degZeroMapSymm Φ hdeg) (by
    rintro ⟨D, hD0⟩ hD
    simp only [AddSubgroup.mem_addSubgroupOf] at hD ⊢
    exact isPrincipal_mapDomain_symm Φ φ hord hD)

theorem picMap_mk (D : Divisor.degZero (K := K) (F := F)) :
    picMap Φ φ hord hdeg (Pic0.mk D) = Pic0.mk (degZeroMap Φ hdeg D) := rfl

theorem picMapSymm_mk (D' : Divisor.degZero (K := K') (F := F')) :
    picMapSymm Φ φ hord hdeg (Pic0.mk D') = Pic0.mk (degZeroMapSymm Φ hdeg D') := rfl

/-- The additive equivalence of Picard groups induced by the given equivalence of places. -/
def picEquiv : Pic0 K F ≃+ Pic0 K' F' :=
  AddMonoidHom.toAddEquiv (picMap Φ φ hord hdeg) (picMapSymm Φ φ hord hdeg)
    (by
      refine AddMonoidHom.ext fun x => ?_
      obtain ⟨D, rfl⟩ := Pic0.mk_surjective x
      rw [AddMonoidHom.comp_apply, picMap_mk, picMapSymm_mk, AddMonoidHom.id_apply]
      exact congrArg Pic0.mk (Subtype.ext (mapDomain_symm_mapDomain Φ (D : Divisor K F))))
    (by
      refine AddMonoidHom.ext fun x => ?_
      obtain ⟨D', rfl⟩ := Pic0.mk_surjective x
      rw [AddMonoidHom.comp_apply, picMapSymm_mk, picMap_mk, AddMonoidHom.id_apply]
      exact congrArg Pic0.mk (Subtype.ext (mapDomain_mapDomain_symm Φ (D' : Divisor K' F'))))

theorem picEquiv_mk (D : Divisor.degZero (K := K) (F := F)) :
    picEquiv Φ φ hord hdeg (Pic0.mk D) = Pic0.mk (degZeroMap Φ hdeg D) := rfl

end Pic

section Equivariance

variable (φ : F ≃+* F') (Φ : Place K F ≃ Place K' F')
  (hcomap : ∀ v : Place K F, (Φ v).toValuationSubring = v.toValuationSubring.comap φ.symm.toRingHom)

include hcomap in
theorem map_smul (σ : F ≃ₐ[K] F) (σ' : F' ≃ₐ[K'] F') (hσ : ∀ f : F, φ (σ f) = σ' (φ f))
    (v : Place K F) :
    Φ (σ • v) = σ' • Φ v := by
  have hσ' : ∀ f' : F', σ.symm (φ.symm f') = φ.symm (σ'.symm f') := by
    intro f'
    apply φ.injective
    apply σ'.injective
    rw [← hσ, AlgEquiv.apply_symm_apply, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply,
      AlgEquiv.apply_symm_apply]
  apply Place.ext
  ext f'
  rw [hcomap, Place.smul_toValuationSubring, Place.smul_toValuationSubring,
    ValuationSubring.mem_comap,
    ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem,
    ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem,
    hcomap, ValuationSubring.mem_comap]
  change σ⁻¹ • (φ.symm f') ∈ v.toValuationSubring ↔ φ.symm (σ'⁻¹ • f') ∈ v.toValuationSubring
  rw [AlgEquiv.smul_def, AlgEquiv.smul_def, AlgEquiv.aut_inv, AlgEquiv.aut_inv, hσ']

end Equivariance

end Pic0Transport

end

open Pic0Transport in
theorem _root_.AlgebraicCurve.Pic0.exists_equiv_addEquiv_mk_eq_and_smul_of_ringEquiv
    {K K' F F' : Type} [Field K] [Field K'] [Field F] [Field F'] [Algebra K F] [Algebra K' F']
    (e : K ≃+* K') (φ : F ≃+* F') (hφ : ∀ a : K, φ (algebraMap K F a) = algebraMap K' F' (e a)) :
    ∃ (Φ : Place K F ≃ Place K' F') (Ψ : Pic0 K F ≃+ Pic0 K' F'),
      (∀ v : Place K F, (Φ v).toValuationSubring = v.toValuationSubring.comap φ.symm.toRingHom) ∧
      (∀ D : Divisor.degZero (K := K) (F := F),
        ∃ hD : Finsupp.mapDomain Φ (D : Divisor K F) ∈ Divisor.degZero (K := K') (F := F'),
          Ψ (Pic0.mk D) = Pic0.mk ⟨_, hD⟩) ∧
      (∀ (σ : F ≃ₐ[K] F) (σ' : F' ≃ₐ[K'] F'), (∀ f : F, φ (σ f) = σ' (φ f)) →
        ∀ x : Pic0 K F, Ψ (σ • x) = σ' • Ψ x) := by
  obtain ⟨Φ, hcomap, hord, hdeg⟩ :=
    AlgebraicCurve.Place.exists_equiv_comap_eq_and_ord_eq_and_deg_eq_of_ringEquiv e φ hφ
  refine ⟨Φ, picEquiv Φ φ hord hdeg, hcomap, fun D => ⟨(degZeroMap Φ hdeg D).2, ?_⟩,
    fun σ σ' hσ x => ?_⟩
  · rfl
  · obtain ⟨D, rfl⟩ := Pic0.mk_surjective x
    rw [Pic0.smul_mk, picEquiv_mk, picEquiv_mk, Pic0.smul_mk]
    refine congrArg Pic0.mk (Subtype.ext ?_)
    rw [coe_degZeroMap, Pic0.coe_degZeroSMulHom, Pic0.coe_degZeroSMulHom, coe_degZeroMap]
    ext w
    rw [mapDomain_apply, Divisor.smul_apply, Divisor.smul_apply, mapDomain_apply]
    congr 1
    apply Φ.injective
    apply MulAction.injective σ'
    change σ' • Φ (σ⁻¹ • Φ.symm w) = σ' • Φ (Φ.symm (σ'⁻¹ • w))
    rw [← map_smul φ Φ hcomap σ σ' hσ, smul_inv_smul,
      Equiv.apply_symm_apply, Equiv.apply_symm_apply,
      smul_inv_smul]
end JacobianVarieties.Pic0.Proofs.Pic0_exists_equiv_addEquiv_mk_eq_and_smul_of_ringEquiv
end ProofImplementation
