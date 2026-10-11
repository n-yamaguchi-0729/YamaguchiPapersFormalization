/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_geomFibreH0Finrank_id_eq_finrank_sections.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Geometry.Picard.PolarisedAbelianScheme
import Nyll.AlgebraicCurves.Geometry.Picard.Functor
import Nyll.AlgebraicCurves.Cohomology.Cech.TwoChartCechSectionsOf
import Nyll.AlgebraicCurves.Cohomology.Sheaves.OModulePresheafOfModules
import Nyll.AlgebraicCurves.Cohomology.Sheaves.OModulePresheafEulerChar
import Nyll.SchemeTheory.Cohomology.Cech.OrderedAffineCoverCech
import Nyll.AlgebraicCurves.Cohomology.Sheaves.OModulePresheaf_nonempty_sections_top_equiv_H0_ofModules
import Nyll.AlgebraicCurves.Cohomology.Cech.OModulePresheaf_cechFinrank_ofModules_pullback_eq_of_isIso

/-!
# Scheme Modules geom Fibre H0 Finrank id eq finrank sections
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Sheaves.Proofs
namespace Scheme_Modules_geomFibreH0Finrank_id_eq_finrank_sections
attribute [-instance] AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx
attribute [-simp] AlgebraicGeometry.OModulePresheaf.prod_obj
  AlgebraicGeometry.OModulePresheaf.restrOpen_obj
  AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq
  AlgebraicGeometry.OModulePresheaf.pushforward_obj
  AlgebraicGeometry.OModulePresheaf.im_obj
  AlgebraicGeometry.OModulePresheaf.pow_obj
  AlgebraicGeometry.OModulePresheaf.fstHom_app
  AlgebraicGeometry.OModulePresheaf.ker_obj
  AlgebraicGeometry.OModulePresheaf.coker_obj
  AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec
  AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U
  AlgebraicGeometry.OModulePresheaf.sndHom_app
  AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq
  AlgebraicGeometry.OModulePresheaf.Hom.id_app
  AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply
  AlgebraicGeometry.OModulePresheaf.AffHom.comp_app
  AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec
  AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe
  AlgebraicGeometry.OModulePresheaf.AffHom.id_app
  AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec
  AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app
  AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec
  AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec
  AlgebraicGeometry.OModulePresheaf.Hom.comp_app
  AlgebraicGeometry.OModulePresheaf.SES.mk.injEq
  AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq
  AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply
  AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq
  AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq
  AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace L4B5

theorem nonempty_orderedAffineCover (X : Scheme.{u}) [CompactSpace X] : Nonempty
  X.OrderedAffineCover := by
  classical
  let 𝒱 := X.affineCover.finiteSubcover
  let : LinearOrder 𝒱.I₀ := LinearOrder.lift' (Fintype.equivFin 𝒱.I₀) (Fintype.equivFin
    𝒱.I₀).injective
  exact ⟨Scheme.OrderedAffineCover.mk (ι := 𝒱.I₀) (U := fun j => (𝒱.f j).opensRange)
    (isAffineOpen := fun j => isAffineOpen_opensRange (𝒱.f j)) (iSup_eq_top := 𝒱.iSup_opensRange)⟩

end L4B5

open L4B5 _root_.AlgebraicGeometry.Scheme.TwoAffineOpenCover in
theorem _root_.AlgebraicGeometry.Scheme.Modules.geomFibreH0Finrank_id_eq_finrank_sections
    (k : Type u) [Field k] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of k)) [IsProper f]
    (M : A.Modules) (hM : Scheme.Modules.IsInvertible M) :
    Scheme.Modules.geomFibreH0Finrank f M k (RingHom.id k) =
      (letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom f M ⊤; Module.finrank k Γ(M, ⊤)) := by
  have hι : Spec.map (CommRingCat.ofHom (RingHom.id k)) = 𝟙 (Spec (CommRingCat.of k)) := by
    rw [CommRingCat.ofHom_id]; exact Spec.map_id _
  have : IsIso (Spec.map (CommRingCat.ofHom (RingHom.id k))) := by rw [hι]; infer_instance
  have : IsIso (pullback.fst f (Spec.map (CommRingCat.ofHom (RingHom.id k)))) := inferInstance
  have hpf : pullback.fst f (Spec.map (CommRingCat.ofHom (RingHom.id k))) ≫ f =
      pullback.snd f (Spec.map (CommRingCat.ofHom (RingHom.id k))) := by
    rw [pullback.condition, hι, Category.comp_id]
  have : CompactSpace ↑A := QuasiCompact.compactSpace_of_compactSpace f
  have : CompactSpace ↑(pullback f (Spec.map (CommRingCat.ofHom (RingHom.id k)))) :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.snd f (Spec.map (CommRingCat.ofHom
      (RingHom.id k))))
  obtain ⟨𝒰⟩ := nonempty_orderedAffineCover A
  obtain ⟨𝒰₀⟩ := nonempty_orderedAffineCover (pullback f (Spec.map (CommRingCat.ofHom (RingHom.id
    k))))
  change (letI := (moduleSectionsOfHom (pullback.snd f (Spec.map (CommRingCat.ofHom (RingHom.id
    k))))
      ((Scheme.Modules.pullback (pullback.fst f (Spec.map (CommRingCat.ofHom (RingHom.id k))))).obj
        M) ⊤);
    Module.finrank k Γ((Scheme.Modules.pullback (pullback.fst f (Spec.map (CommRingCat.ofHom
      (RingHom.id k))))).obj M, ⊤)) = _
  let i0 := moduleSectionsOfHom (pullback.snd f (Spec.map (CommRingCat.ofHom (RingHom.id k))))
      ((Scheme.Modules.pullback (pullback.fst f (Spec.map (CommRingCat.ofHom (RingHom.id k))))).obj
        M) ⊤
  let i1 := moduleSectionsOfHom f M ⊤
  obtain ⟨e₀⟩ := OModulePresheaf.nonempty_sections_top_equiv_H0_ofModules
    (pullback.snd f (Spec.map (CommRingCat.ofHom (RingHom.id k))))
    ((Scheme.Modules.pullback (pullback.fst f (Spec.map (CommRingCat.ofHom (RingHom.id k))))).obj
      M) 𝒰₀
  obtain ⟨e₁⟩ := OModulePresheaf.nonempty_sections_top_equiv_H0_ofModules f M 𝒰
  have h := OModulePresheaf.cechFinrank_ofModules_pullback_eq_of_isIso f
    (pullback.fst f (Spec.map (CommRingCat.ofHom (RingHom.id k)))) M hM 𝒰₀ 𝒰 0
  rw [hpf, OModulePresheaf.cechFinrank_zero, OModulePresheaf.cechFinrank_zero] at h
  exact e₀.finrank_eq.trans (h.trans e₁.finrank_eq.symm)
end AlgebraicCurves.Geometry.Sheaves.Proofs.Scheme_Modules_geomFibreH0Finrank_id_eq_finrank_sections
end ProofImplementation

attribute [-instance] AlgebraicGeometry.OModulePresheaf.isScalarTower
  AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder
  AlgebraicGeometry.OModulePresheaf.module
  AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype
  AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx
  AlgebraicGeometry.OModulePresheaf.addCommGroup
  AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx
  AlgebraicGeometry.OModulePresheaf.moduleSections
  AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx
attribute [-simp] AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq
  AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec
  AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec
  AlgebraicGeometry.OModulePresheaf.mk.injEq
  AlgebraicGeometry.OModulePresheaf.prod_obj
  AlgebraicGeometry.OModulePresheaf.restrOpen_obj
  AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq
  AlgebraicGeometry.OModulePresheaf.pushforward_obj
  AlgebraicGeometry.OModulePresheaf.im_obj
  AlgebraicGeometry.OModulePresheaf.pow_obj
  AlgebraicGeometry.OModulePresheaf.fstHom_app
  AlgebraicGeometry.OModulePresheaf.ker_obj
  AlgebraicGeometry.OModulePresheaf.coker_obj
  AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec
  AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U
  AlgebraicGeometry.OModulePresheaf.sndHom_app
  AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq
  AlgebraicGeometry.OModulePresheaf.Hom.id_app
  AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply
  AlgebraicGeometry.OModulePresheaf.AffHom.comp_app
  AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec
  AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe
  AlgebraicGeometry.OModulePresheaf.AffHom.id_app
  AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec
  AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app
  AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec
  AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec
  AlgebraicGeometry.OModulePresheaf.Hom.comp_app
  AlgebraicGeometry.OModulePresheaf.SES.mk.injEq
  AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq
  AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply
  AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq
  AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq
  AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U
