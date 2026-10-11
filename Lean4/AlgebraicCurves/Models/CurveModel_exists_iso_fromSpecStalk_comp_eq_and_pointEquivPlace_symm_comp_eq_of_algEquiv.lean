/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_CurveModel_exists_iso_fromSpecStalk_comp_eq_and_pointEquivPlace_symm_comp_eq_of_algEquiv.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import AlgebraicCurves.Models.Basic
import AlgebraicCurves.Divisors.Correspondences
import AlgebraicCurves.Models.CurveModel_exists_hom_of_algHom

/-!
# Curve Model exists iso from Spec Stalk comp eq and point Equiv Place symm comp eq of alg
Equiv
-/

section ProofImplementation

namespace AlgebraicCurves.Models.Proofs
namespace CurveModel_exists_iso_fromSpecStalk_comp_eq_and_pointEquivPlace_symm_comp_eq_of_algEquiv
open _root_.AlgebraicCurve.Place in
attribute [-instance]
  instIsPrimeCenter
  instIsFractionRingIntegralClosureAt
  instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
  instIsDedekindDomainIntegralClosureAt
  instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
attribute [-simp] AlgebraicCurve.Place.placeOfPrime_toValuationSubring
  AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply
  AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve

end CurveModel_exists_iso_fromSpecStalk_comp_eq_and_pointEquivPlace_symm_comp_eq_of_algEquiv
end AlgebraicCurves.Models.Proofs

namespace AlgebraicCurve.CurveModel

universe u

open _root_.AlgebraicCurves.Models.Proofs in
open CurveModel_exists_iso_fromSpecStalk_comp_eq_and_pointEquivPlace_symm_comp_eq_of_algEquiv in
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve in
theorem exists_iso_fromSpecStalk_comp_eq_and_pointEquivPlace_symm_comp_eq_of_algEquiv
    {K : Type u} [Field K] [IsAlgClosed K] [CharZero K] {L : Type u} [Field L] [Algebra K L]
    (M : CurveModel K L) (V : L ≃ₐ[K] L) (hV : (V : L →ₐ[K] L).toRingHom.IsIntegral) :
    ∃ h : M.C ≅ M.C, h.hom ≫ M.toBase = M.toBase ∧
      M.C.fromSpecStalk (genericPoint M.C) ≫ h.hom =
        Spec.map (CommRingCat.ofHom
          (M.ffEquiv.toRingHom.comp ((V : L →ₐ[K] L).toRingHom.comp M.ffEquiv.symm.toRingHom))) ≫
          M.C.fromSpecStalk (genericPoint M.C) ∧
      ∀ P : Place K L,
        (M.pointEquivPlace.symm P).1 ≫ h.hom = (M.pointEquivPlace.symm (P.restrictAlong (V : L
          →ₐ[K] L) hV)).1 := by
  classical
  have hfin : ∀ W : L ≃ₐ[K] L, FiniteAlong K (W : L →ₐ[K] L) := fun W =>
    (RingHom.Finite.of_surjective ((W : L ≃ₐ[K] L) : L →ₐ[K] L).toRingHom W.surjective :)
  have hint : ∀ W : L ≃ₐ[K] L, ((W : L ≃ₐ[K] L) : L →ₐ[K] L).toRingHom.IsIntegral :=
    fun W => RingHom.isIntegral_of_surjective _ W.surjective
  obtain ⟨π, hπb, -, -, -, -, hπgen, hπpt, -⟩ := AlgebraicCurve.CurveModel.exists_hom_of_algHom M M
    (V : L →ₐ[K] L) hV (hfin V)
  obtain ⟨π', hπ'b, -, -, -, -, hπ'gen, -, -⟩ := AlgebraicCurve.CurveModel.exists_hom_of_algHom M M
    ((V.symm : L ≃ₐ[K] L) : L →ₐ[K] L) (hint V.symm) (hfin V.symm)
  obtain ⟨π₀, -, -, -, -, -, hπ₀gen, -, hπ₀uniq⟩ :=
    AlgebraicCurve.CurveModel.exists_hom_of_algHom M M ((AlgEquiv.refl : L ≃ₐ[K] L) : L →ₐ[K] L)
      (hint AlgEquiv.refl) (hfin AlgEquiv.refl)
  have hE0 : Spec.map (CommRingCat.ofHom (M.ffEquiv.toRingHom.comp (((AlgEquiv.refl : L ≃ₐ[K] L) :
    L →ₐ[K] L).toRingHom.comp M.ffEquiv.symm.toRingHom))) = 𝟙 _ := by
    have : (M.ffEquiv.toRingHom.comp ((((AlgEquiv.refl : L ≃ₐ[K] L) : L →ₐ[K] L)).toRingHom.comp
      M.ffEquiv.symm.toRingHom)) =
        RingHom.id _ := by
      ext y
      change M.ffEquiv ((AlgEquiv.refl : L ≃ₐ[K] L) (M.ffEquiv.symm y)) = y
      rw [AlgEquiv.coe_refl, id_eq, RingEquiv.apply_symm_apply]
    rw [this, CommRingCat.ofHom_id]
    exact Spec.map_id _
  rw [hE0, Category.id_comp] at hπ₀gen
  have hEE : ∀ W : L ≃ₐ[K] L, Spec.map (CommRingCat.ofHom (M.ffEquiv.toRingHom.comp (((W : L ≃ₐ[K]
    L) : L →ₐ[K] L).toRingHom.comp M.ffEquiv.symm.toRingHom))) ≫ Spec.map (CommRingCat.ofHom
    (M.ffEquiv.toRingHom.comp (((W.symm : L ≃ₐ[K] L) : L →ₐ[K] L).toRingHom.comp
    M.ffEquiv.symm.toRingHom))) = 𝟙 _ := by
    intro W
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    have : (M.ffEquiv.toRingHom.comp (((W : L ≃ₐ[K] L) : L →ₐ[K] L).toRingHom.comp
      M.ffEquiv.symm.toRingHom)).comp
        (M.ffEquiv.toRingHom.comp (((W.symm : L ≃ₐ[K] L) : L →ₐ[K] L).toRingHom.comp
          M.ffEquiv.symm.toRingHom)) = RingHom.id _ := by
      ext y
      change M.ffEquiv (W (M.ffEquiv.symm (M.ffEquiv (W.symm (M.ffEquiv.symm y))))) = y
      rw [RingEquiv.symm_apply_apply, AlgEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]
    rw [this, CommRingCat.ofHom_id]
    exact Spec.map_id _
  have h1 : 𝟙 M.C = π₀ := hπ₀uniq _ (by rw [Category.comp_id, hπ₀gen])
  have h2 : π ≫ π' = π₀ := hπ₀uniq _ (by
    rw [← Category.assoc, hπgen, Category.assoc, hπ'gen, ← Category.assoc, hEE V]
    erw [Category.id_comp]
    exact hπ₀gen.symm)
  have h3 : π' ≫ π = π₀ := hπ₀uniq _ (by
    rw [← Category.assoc, hπ'gen, Category.assoc, hπgen, ← Category.assoc]
    have := hEE V.symm
    rw [AlgEquiv.symm_symm] at this
    rw [this]
    erw [Category.id_comp]
    exact hπ₀gen.symm)
  refine ⟨⟨π, π', by rw [h2, ← h1], by rw [h3, ← h1]⟩, hπb, hπgen, ?_⟩
  intro P
  have hq : ((M.pointEquivPlace.symm P).1 ≫ π) ≫ M.toBase = 𝟙 _ := by
    rw [Category.assoc, hπb]; exact (M.pointEquivPlace.symm P).2
  have key : M.pointEquivPlace ⟨(M.pointEquivPlace.symm P).1 ≫ π, hq⟩ = P.restrictAlong (V : L
    →ₐ[K] L) hV := by
    rw [CurveModel.pointEquivPlace_apply]
    obtain ⟨hy, hyP⟩ := hπpt (pointEquivClosedPoint M.toBase (M.pointEquivPlace.symm P))
    have e : pointEquivClosedPoint M.toBase ⟨(M.pointEquivPlace.symm P).1 ≫ π, hq⟩ =
        ⟨π.base (pointEquivClosedPoint M.toBase (M.pointEquivPlace.symm P)).1, hy⟩ := by
      apply Subtype.ext
      simp only [pointEquivClosedPoint_apply_coe]
      exact Scheme.Hom.comp_apply (M.pointEquivPlace.symm P).1 π
        (IsLocalRing.closedPoint K)
    rw [e, hyP, ← CurveModel.pointEquivPlace_apply, Equiv.apply_symm_apply]
  have := congrArg (fun Q => (M.pointEquivPlace.symm Q).1) key
  simp only [Equiv.symm_apply_apply] at this
  exact this
end AlgebraicCurve.CurveModel
end ProofImplementation
