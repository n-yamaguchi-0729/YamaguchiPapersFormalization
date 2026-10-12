/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_RelPicard_support_zeroSchemeIdeal_fibre_subset_of_support_zeroSchemeIdeal_fibre_subset_extension.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.Stalk
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
import Mathlib.AlgebraicGeometry.Morphisms.RingHomProperties
import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.RingHom.FaithfullyFlat
import Mathlib.RingTheory.RingHom.Flat
import Mathlib.RingTheory.Spectrum.Prime.Basic
import Mathlib.Topology.Sheaves.Stalks
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
import Mathlib.Topology.Sets.Opens
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Limits.Shapes.ZeroMorphisms
import Mathlib.Tactic.Algebraize
import Mathlib.Tactic.Push
import Nyll.AlgebraicCurves.Geometry.Picard.Functor
import Nyll.AlgebraicCurves.RelativeDivisors.RelEffCartierDiv
import Nyll.SchemeTheory.Cohomology.Cech.TwoAffineOpenCover
import Nyll.SchemeTheory.Modules.Monoidal
import Nyll.AlgebraicCurves.Geometry.Sheaves.ModulesSectionZeroScheme
import Nyll.SchemeTheory.Modules.TensorSections
import Nyll.SchemeTheory.Modules.PullbackLocalSection
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_zeroSchemeIdeal_comp_eq_of_isIso
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_IsInvertible_comap_zeroSchemeIdeal
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_IsInvertible_exists_isFrameOn
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_IsFrameOn_pullbackLocalSection

/-!
# Descent of zero-scheme support under field extension

Faithfully flat pullback preserves nonzero sections of invertible modules.
This descends a support bound from an extension of the residue field.
-/

section ProofImplementation

namespace JacobianVarieties.Picard.Proofs.ZeroSupportExtension
attribute [-instance]
  PresheafOfModules.PullbackMonoidal.pullback_monoidal
  PresheafOfModules.PullbackMonoidal.isIso_δ
  PresheafOfModules.pushforward_laxMonoidal
  PresheafOfModules.PullbackMonoidal.isIso_η
  PresheafOfModules.free_monoidal
  PresheafOfModules.restrictScalars_laxMonoidal
  PresheafOfModules.PullbackMonoidal.isIso_δ_gS
  PresheafOfModules.pullback_oplaxMonoidal
open _root_.PresheafOfModules.PullbackMonoidal in
attribute [-instance]
  instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb
attribute [-instance]
  PresheafOfModules.pullback_monoidal'
  AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap
  AlgebraicGeometry.Scheme.Modules.pullback_monoidal
  AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization'
  AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap
  AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal
  AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap
  AlgebraicGeometry.Scheme.Modules.sheafifyPullback_lifting
attribute [-simp] PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app

universe u


open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory
open _root_.AlgebraicGeometry
open _root_.AlgebraicGeometry.RelPicard
open _root_.NeronModelInfra


noncomputable section

namespace AlgebraicGeometry

export _root_.AlgebraicGeometry (
  Scheme.Modules.hom_ext
  Scheme.Modules.Hom.app_smul
  Surjective
  Scheme.IdealSheafData.support_comap
  Scheme.Modules.pullback
  Scheme.Hom
  Scheme.Hom.germ_stalkMap_apply
  Scheme.Modules.Hom
  Spec
  Spec.map
  Scheme
  Flat.stalkMap
  Flat
  HasRingHomProperty.Spec_iff
  Scheme.Modules.pullbackCongr
  Scheme.Modules
  HasRingHomProperty
  Scheme.Hom.comp_apply
  Scheme.IdealSheafData
  Scheme.Modules.pullbackComp
  Scheme.Modules.IsInvertible
  Scheme.Modules.pullbackUnitIso
  mapOnProdOver
  mapOnProdOver_fst
  mapOnProdOver_snd
  isPullback_mapOnProdOver
  mapOnProdOver_snd_assoc
  Scheme.TwoAffineOpenCover
  Scheme.TwoAffineOpenCover.specMap
  Scheme.Modules.zeroSchemeIdeal
  Scheme.Modules.pullbackSection
  Scheme.Modules.pullbackSection_def
  Scheme.Modules.unitSection
  Scheme.Modules.map_unitSection
  Scheme.Modules.smul_unitSection
  Scheme.Modules.IsFrameOn
  Scheme.Modules.pullbackLocalSection
  Scheme.Modules.pullbackLocalSection_smul
  Scheme.Modules.pullbackLocalSection_app
  Scheme.Modules.zeroSchemeIdeal_comp_eq_of_isIso)

namespace ZerosDescent

open _root_.AlgebraicGeometry


/-- A flat surjective scheme morphism induces injective maps on sections. -/
theorem app_injective_of_flat_of_surjective {X Y : Scheme.{u}} (π : Y ⟶ X) [Flat π] [Surjective π]
    (W : X.Opens) :
    Function.Injective (π.app W) := by
  intro a b hab
  apply TopCat.Presheaf.section_ext X.sheaf W a b
  intro w hw
  obtain ⟨y, rfl⟩ := π.surjective w
  have hinj : Function.Injective (π.stalkMap y) := by
    algebraize [(π.stalkMap y).hom]
    have : Module.FaithfullyFlat (X.presheaf.stalk (π y)) (Y.presheaf.stalk y) :=
      @Module.FaithfullyFlat.of_flat_of_isLocalHom _ _ _ _ _ _ _ (Flat.stalkMap π y)
        (π.toLRSHom.prop y)
    exact ‹RingHom.FaithfullyFlat _›.injective
  apply hinj
  change π.stalkMap y (X.presheaf.germ W (π y) hw a) = π.stalkMap y (X.presheaf.germ W (π y) hw b)
  rw [Scheme.Hom.germ_stalkMap_apply, Scheme.Hom.germ_stalkMap_apply, hab]

/-- A nonzero section of an invertible module stays nonzero under flat surjective pullback. -/
theorem pullbackSection_ne_zero {X Y : Scheme.{u}} (π : Y ⟶ X) [Flat π] [Surjective π]
    {N : X.Modules} (hN : Scheme.Modules.IsInvertible N) (τ : 𝟙_ X.Modules ⟶ N) (hτ : τ ≠ 0) :
    Scheme.Modules.pullbackSection π τ ≠ 0 := by
  classical
  have h1 : ∃ V : X.Opens, τ.app V (Scheme.Modules.unitSection V) ≠ 0 := by
    by_contra hall
    push Not at hall
    apply hτ
    apply Scheme.Modules.hom_ext
    intro V
    ext r
    have hr : r = (show Γ(X, V) from r) • Scheme.Modules.unitSection V :=
      (Scheme.Modules.smul_unitSection _).symm
    rw [hr, Scheme.Modules.Hom.app_smul, hall V, smul_zero]
    rfl
  obtain ⟨V, hV⟩ := h1
  have h2 : ∃ (W : X.Opens) (e : Γ(N, W)) (hWV : W ≤ V), Scheme.Modules.IsFrameOn e W ∧
      N.presheaf.map (homOfLE hWV).op (τ.app V (Scheme.Modules.unitSection V)) ≠ 0 := by
    by_contra hall
    push Not at hall
    apply hV
    choose W0 e0 hp hfr using fun p : V => hN.exists_isFrameOn (p : X)
    have hcov : V ≤ iSup fun p : V => W0 p ⊓ V :=
      fun q hq => TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨q, hq⟩, ⟨hp ⟨q, hq⟩, hq⟩⟩
    apply TopCat.Sheaf.eq_of_locally_eq' (⟨N.presheaf, N.isSheaf⟩ : TopCat.Sheaf Ab X)
      (fun p : V => W0 p ⊓ V) V (fun p => homOfLE inf_le_right) hcov
    intro p
    rw [map_zero]
    exact hall (W0 p ⊓ V) (N.presheaf.map (homOfLE inf_le_left).op (e0 p)) inf_le_right
      (((hfr p).map (homOfLE inf_le_left)).mono inf_le_left)
  obtain ⟨W, e, hWV, hfr, hmW⟩ := h2
  have hmW' : N.presheaf.map (homOfLE hWV).op (τ.app V (Scheme.Modules.unitSection V)) =
      τ.app W (Scheme.Modules.unitSection W) := by
    have := τ.mapPresheaf.naturality (homOfLE hWV).op
    have h := congrArg (fun φ => φ.hom (Scheme.Modules.unitSection V)) this
    change τ.app W ((𝟙_ X.Modules).presheaf.map (homOfLE hWV).op (Scheme.Modules.unitSection V)) =
      N.presheaf.map (homOfLE hWV).op (τ.app V (Scheme.Modules.unitSection V)) at h
    rw [Scheme.Modules.map_unitSection] at h
    exact h.symm
  rw [hmW'] at hmW
  have he : N.presheaf.map (homOfLE (le_refl W)).op e = e := by
    have : (homOfLE (le_refl W)).op = 𝟙 (Opposite.op W) := Subsingleton.elim _ _
    rw [this, CategoryTheory.Functor.map_id]
    rfl
  obtain ⟨g, hg, -⟩ := hfr.existsUnique (le_refl W) (le_refl W) (τ.app W
    (Scheme.Modules.unitSection W))
  rw [he] at hg
  have hg0 : g ≠ 0 := by
    rintro rfl
    rw [zero_smul] at hg
    exact hmW hg.symm
  intro h0
  have hmap : (Scheme.Modules.pullback π).map τ = 0 := by
    have : (Scheme.Modules.pullback π).map τ =
        (Scheme.Modules.pullbackUnitIso π).hom ≫ Scheme.Modules.pullbackSection π τ := by
      rw [Scheme.Modules.pullbackSection_def]
      exact (Iso.hom_inv_id_assoc (Scheme.Modules.pullbackUnitIso π)
        ((Scheme.Modules.pullback π).map τ)).symm
    rw [this, h0]
    exact comp_zero
  have h3 : Scheme.Modules.pullbackLocalSection π (τ.app W (Scheme.Modules.unitSection W)) = 0 := by
    rw [Scheme.Modules.pullbackLocalSection_app, hmap]
    rfl
  rw [← hg, Scheme.Modules.pullbackLocalSection_smul] at h3
  have hfr' : Scheme.Modules.IsFrameOn (Scheme.Modules.pullbackLocalSection π e) (π ⁻¹ᵁ W) :=
    hfr.pullbackLocalSection π
  have he' : ((Scheme.Modules.pullback π).obj N).presheaf.map (homOfLE (le_refl (π ⁻¹ᵁ W))).op
      (Scheme.Modules.pullbackLocalSection π e) = Scheme.Modules.pullbackLocalSection π e := by
    have : (homOfLE (le_refl (π ⁻¹ᵁ W))).op = 𝟙 (Opposite.op (π ⁻¹ᵁ W)) := Subsingleton.elim _ _
    rw [this, CategoryTheory.Functor.map_id]
    rfl
  have h4 := (hfr'.smul_eq_zero_iff (le_refl _) (le_refl _) (π.app W g)).mp (by rw [he']; exact h3)
  exact hg0 (app_injective_of_flat_of_surjective π W (h4.trans (map_zero (π.app W).hom).symm))

end AlgebraicGeometry.ZerosDescent

end

end JacobianVarieties.Picard.Proofs.ZeroSupportExtension

namespace AlgebraicGeometry.RelPicard

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra
open CategoryTheory.MonoidalCategory
open JacobianVarieties.Picard.Proofs.ZeroSupportExtension.AlgebraicGeometry.ZerosDescent

/-- A bound on zero-scheme supports after a field extension descends to the original fibre. -/
theorem support_zeroSchemeIdeal_fibre_subset_of_support_zeroSchemeIdeal_fibre_subset_extension
    {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R)) (U : C.Opens)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (M : (pullback c t).Modules)
    (hM : Scheme.Modules.IsInvertible M)
    {k : Type u} [Field k] (s : Spec (CommRingCat.of k) ⟶ T)
    (K : Type u) [Field K] [Algebra k K]
    (hK : ∀ τ : 𝟙_ (pullback c ((Scheme.TwoAffineOpenCover.specMap k K ≫ s) ≫ t)).Modules ⟶
        (Scheme.Modules.pullback (mapOnProdOver c (Scheme.TwoAffineOpenCover.specMap k K ≫ s)
          rfl)).obj M,
      τ ≠ 0 →
        ((Scheme.Modules.zeroSchemeIdeal τ).support : Set ↥(pullback c
          ((Scheme.TwoAffineOpenCover.specMap k K ≫ s) ≫ t))) ⊆
          ((pullback.fst c ((Scheme.TwoAffineOpenCover.specMap k K ≫ s) ≫ t)) ⁻¹ᵁ U :
            Set ↥(pullback c ((Scheme.TwoAffineOpenCover.specMap k K ≫ s) ≫ t)))) :
    ∀ τ : 𝟙_ (pullback c (s ≫ t)).Modules ⟶ (Scheme.Modules.pullback (mapOnProdOver c s rfl)).obj M,
      τ ≠ 0 →
        ((Scheme.Modules.zeroSchemeIdeal τ).support : Set ↥(pullback c (s ≫ t))) ⊆
          ((pullback.fst c (s ≫ t)) ⁻¹ᵁ U : Set ↥(pullback c (s ≫ t))) := by
  intro τ hτ
  let sp := Scheme.TwoAffineOpenCover.specMap k K
  let π : pullback c ((sp ≫ s) ≫ t) ⟶ pullback c (s ≫ t) :=
    mapOnProdOver c sp (Category.assoc sp s t).symm
  have hsq := isPullback_mapOnProdOver c sp (Category.assoc sp s t).symm
  have : Subsingleton ↥(Spec (CommRingCat.of k)) := inferInstanceAs (Subsingleton (PrimeSpectrum k))
  have : Nonempty ↥(Spec (CommRingCat.of K)) := inferInstanceAs (Nonempty (PrimeSpectrum K))
  have : Surjective sp := inferInstance
  have : Flat sp := by
    change Flat (Spec.map (CommRingCat.ofHom (algebraMap k K)))
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    exact RingHom.Flat.of_isField (Field.toIsField k) (algebraMap k K)
  have : Flat π := MorphismProperty.of_isPullback hsq.flip inferInstance
  have : Surjective π := MorphismProperty.of_isPullback hsq.flip inferInstance
  have hcomp : π ≫ mapOnProdOver c s rfl = mapOnProdOver c (sp ≫ s) rfl := by
    apply pullback.hom_ext
    · simp only [π, Category.assoc, mapOnProdOver_fst]
    · simp only [π, Category.assoc, mapOnProdOver_snd, mapOnProdOver_snd_assoc]
  let N := (Scheme.Modules.pullback (mapOnProdOver c s rfl)).obj M
  have hN : Scheme.Modules.IsInvertible N := hM.pullback _
  let eN : (Scheme.Modules.pullback (mapOnProdOver c (sp ≫ s) rfl)).obj M ≅
    (Scheme.Modules.pullback π).obj N :=
    (Scheme.Modules.pullbackCongr hcomp.symm).app M ≪≫ ((Scheme.Modules.pullbackComp π
      (mapOnProdOver c s rfl)).app M).symm
  let τK : 𝟙_ (pullback c ((sp ≫ s) ≫ t)).Modules ⟶
      (Scheme.Modules.pullback (mapOnProdOver c (sp ≫ s) rfl)).obj M :=
    Scheme.Modules.pullbackSection π τ ≫ eN.inv
  have hτK : τK ≠ 0 := by
    intro h
    apply pullbackSection_ne_zero π hN τ hτ
    calc Scheme.Modules.pullbackSection π τ = τK ≫ eN.hom := by
          simp only [τK, Category.assoc, Iso.inv_hom_id, Category.comp_id]
      _ = 0 ≫ eN.hom := by rw [h]
      _ = 0 := zero_comp
  have hZ : Scheme.Modules.zeroSchemeIdeal τK = (Scheme.Modules.zeroSchemeIdeal τ).comap π := by
    rw [Scheme.Modules.zeroSchemeIdeal_comp_eq_of_isIso, hN.comap_zeroSchemeIdeal]
  have hsub := hK τK hτK
  rw [hZ, Scheme.IdealSheafData.support_comap] at hsub
  intro p hp
  obtain ⟨p', rfl⟩ := π.surjective p
  have hp' : p' ∈ ((Scheme.Modules.zeroSchemeIdeal τ).support.preimage π.continuous :
      Set ↥(pullback c ((sp ≫ s) ≫ t))) := hp
  have h' := hsub hp'
  change (pullback.fst c (s ≫ t)).base (π.base p') ∈ U
  have : (pullback.fst c (s ≫ t)).base (π.base p') = (pullback.fst c ((sp ≫ s) ≫ t)).base p' := by
    rw [← Scheme.Hom.comp_apply, mapOnProdOver_fst]
  rw [this]
  exact h'
end AlgebraicGeometry.RelPicard
end ProofImplementation

attribute [-simp]
  AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right
  AlgebraicGeometry.Scheme.Modules.map_unitSection
  AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply
  AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero
  AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left
  AlgebraicGeometry.Scheme.Modules.tensorPow_zero
  AlgebraicGeometry.Scheme.Modules.tensorPow_succ
  AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg
  AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero
  AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub
  AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add
  PresheafOfModules.freeεIso_hom_app
  PresheafOfModules.freeμIso_hom_app
