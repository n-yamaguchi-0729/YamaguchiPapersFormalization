/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_CurveModel_ffEquiv_symm_mem_and_evalAt_pointEquivPlace_eq_stalkClosedPointTo.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import AlgebraicCurves.Models.Basic
import AlgebraicCurves.Places.Evaluation

/-!
# Curve Model ff Equiv symm mem and eval At point Equiv Place eq stalk Closed Point To
-/

section ProofImplementation

namespace AlgebraicCurves.Models.Proofs
namespace CurveModel_ffEquiv_symm_mem_and_evalAt_pointEquivPlace_eq_stalkClosedPointTo

open CategoryTheory AlgebraicGeometry AlgebraicCurve

universe u v

theorem
  _root_.AlgebraicCurve.CurveModel.ffEquiv_symm_mem_and_evalAt_pointEquivPlace_eq_stalkClosedPointTo
    {K : Type u} [Field K] [IsAlgClosed K] {L : Type v} [Field L] [Algebra K L]
    (M : CurveModel K L) (pt : {q : Spec (CommRingCat.of K) ⟶ M.C // q ≫ M.toBase = 𝟙 _})
    (s : M.C.presheaf.stalk (pt.1.base (IsLocalRing.closedPoint K))) :
    ∃ h : M.ffEquiv.symm (algebraMap _ M.C.functionField s) ∈ (M.pointEquivPlace
      pt).toValuationSubring,
      IsLocalRing.residue (M.pointEquivPlace pt).toValuationSubring ⟨_, h⟩ =
        algebraMap K (M.pointEquivPlace pt).ResidueField ((Scheme.stalkClosedPointTo pt.1).hom s) ∧
      (M.pointEquivPlace pt).evalAt (M.ffEquiv.symm (algebraMap _ M.C.functionField s)) =
        (Scheme.stalkClosedPointTo pt.1).hom s := by
  classical
  let x₀ : closedPoints M.C := pointEquivClosedPoint M.toBase pt
  have hx₀ : x₀.1 = pt.1.base (IsLocalRing.closedPoint K) := rfl
  let ι : M.C.presheaf.stalk (pt.1.base (IsLocalRing.closedPoint K)) →+* L :=
    (M.ffEquiv.symm : M.C.functionField ≃+* L).toRingHom.comp (algebraMap _ M.C.functionField)
  have hιapp : ∀ r, ι r = M.ffEquiv.symm (algebraMap _ M.C.functionField r) := fun r => rfl
  have hrange : ι.range = (M.pointEquivPlace pt).toValuationSubring.toSubring := M.range_stalk_eq x₀
  have hmem : ∀ r, ι r ∈ (M.pointEquivPlace pt).toValuationSubring := fun r => by
    have h : ι r ∈ ι.range := ⟨r, rfl⟩
    rw [hrange] at h
    exact h
  have hιinj : Function.Injective ι :=
    (M.ffEquiv.symm.injective).comp (IsFractionRing.injective _ _)
  refine ⟨hmem s, ?_⟩
  set c : K := (Scheme.stalkClosedPointTo pt.1).hom s with hc
  let κ : K →+* M.C.presheaf.stalk (pt.1.base (IsLocalRing.closedPoint K)) :=
    (M.C.presheaf.germ ⊤ (pt.1.base (IsLocalRing.closedPoint K)) (TopologicalSpace.Opens.mem_top
      _)).hom.comp
      (M.toBase.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom)
  have hsec : ∀ y : Γ(Spec (CommRingCat.of K), ⊤), (pt.1.app ⊤).hom (M.toBase.appTop.hom y) = y :=
    by
    intro y
    have h := Scheme.Hom.comp_appTop pt.1 M.toBase
    rw [pt.2] at h
    have h2 := congrArg (fun φ : Γ(Spec (CommRingCat.of K), ⊤) ⟶ Γ(Spec (CommRingCat.of K), ⊤) =>
      φ.hom y) h
    simp at h2
    exact h2.symm
  have hκeval : ∀ a : K, (Scheme.stalkClosedPointTo pt.1).hom (κ a) = a := by
    intro a
    change ((M.C.presheaf.germ ⊤ (pt.1.base (IsLocalRing.closedPoint K))
      (TopologicalSpace.Opens.mem_top _)) ≫
      Scheme.stalkClosedPointTo pt.1).hom (M.toBase.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of
        K)).inv.hom a)) = a
    rw [Scheme.germ_stalkClosedPointTo pt.1 ⊤ trivial]
    simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply, Iso.trans_hom,
      Functor.mapIso_hom,
      Iso.op_hom, eqToIso.hom, hsec]
    try simp only [RingHom.id_apply]
    change ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ (Scheme.ΓSpecIso (CommRingCat.of
      K)).hom).hom a = a
    rw [Iso.inv_hom_id]
    rfl
  have hκι : ∀ a : K, ι (κ a) = algebraMap K L a := by
    intro a
    have h1 : algebraMap (M.C.presheaf.stalk (pt.1.base (IsLocalRing.closedPoint K)))
      M.C.functionField (κ a) =
        baseToFunctionField M.toBase a := by
      change (M.C.presheaf.germ ⊤ (pt.1.base (IsLocalRing.closedPoint K))
        (TopologicalSpace.Opens.mem_top _) ≫
        M.C.presheaf.stalkSpecializes _).hom (M.toBase.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of
          K)).inv.hom a)) = _
      rw [TopCat.Presheaf.germ_stalkSpecializes]
      rfl
    rw [hιapp, h1]
    apply M.ffEquiv.injective
    rw [RingEquiv.apply_symm_apply, M.ffEquiv_algebraMap]
  set m := s - κ c with hm
  have hm0 : (Scheme.stalkClosedPointTo pt.1).hom m = 0 := by
    rw [hm, map_sub, hκeval, hc, sub_self]
  have hmunit : ¬ IsUnit m := by
    intro hu
    have := hu.map (Scheme.stalkClosedPointTo pt.1).hom
    rw [hm0] at this
    exact not_isUnit_zero this
  have hιm : ¬ IsUnit (⟨ι m, hmem m⟩ : (M.pointEquivPlace pt).toValuationSubring) := by
    rintro ⟨u, hu⟩
    apply hmunit
    have hinv : ((u⁻¹ : ((M.pointEquivPlace pt).toValuationSubring)ˣ) : (M.pointEquivPlace
      pt).toValuationSubring).1 ∈ ι.range := by
      rw [hrange]; exact ((u⁻¹ : ((M.pointEquivPlace pt).toValuationSubring)ˣ) : (M.pointEquivPlace
        pt).toValuationSubring).2
    obtain ⟨m', hm'⟩ := hinv
    have hmul : ι (m * m') = ι 1 := by
      rw [map_mul, map_one, hm']
      have := congrArg (fun z : (M.pointEquivPlace pt).toValuationSubring => (z : L)) u.mul_inv
      simpa [hu] using this
    exact IsUnit.of_mul_eq_one m' (hιinj hmul)
  have hres0 : IsLocalRing.residue (M.pointEquivPlace pt).toValuationSubring ⟨ι m, hmem m⟩ = 0 := by
    rw [IsLocalRing.residue_eq_zero_iff]
    exact (IsLocalRing.mem_maximalIdeal _).mpr hιm
  have hsplit : (⟨ι s, hmem s⟩ : (M.pointEquivPlace pt).toValuationSubring) =
      algebraMap K (M.pointEquivPlace pt).toValuationSubring c + ⟨ι m, hmem m⟩ := by
    apply Subtype.ext
    change ι s = (algebraMap K (M.pointEquivPlace pt).toValuationSubring c : L) + ι m
    rw [Place.coe_algebraMap, ← hκι c, ← map_add, hm, add_sub_cancel]
  have hres : IsLocalRing.residue (M.pointEquivPlace pt).toValuationSubring ⟨ι s, hmem s⟩ =
      algebraMap K (M.pointEquivPlace pt).ResidueField c := by
    rw [hsplit, map_add, hres0, add_zero]
    rfl
  refine ⟨?_, ?_⟩
  · simpa only [hιapp] using hres
  · rw [← hιapp s, Place.evalAt_of_mem _ (hmem s), hres]
    exact Place.residueInv_algebraMap _ c
end CurveModel_ffEquiv_symm_mem_and_evalAt_pointEquivPlace_eq_stalkClosedPointTo
end AlgebraicCurves.Models.Proofs
end ProofImplementation
