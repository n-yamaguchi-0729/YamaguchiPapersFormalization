/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_exists_iso_pullback_of_isPullback.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.Util.WithWeakNamespace
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import AlgebraicCurves.Geometry.Sheaves.ModulesLocallyFreeOfRank
import SchemeTheory.Cohomology.Cech.TwoAffineOpenCover
import AlgebraicCurves.Geometry.Sheaves.ModulesPushforwardRestrict
import AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_IsLocallyFreeOfRank_of_forall_exists_opens
import AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_IsLocallyFreeOfRank_of_iso
import AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_IsLocallyFreeOfRank_pullback

/-!
# Iterated pullback over a Cartesian square

A Cartesian square identifies the two iterated scheme pullbacks and the corresponding
pullbacks of modules, compatibly with both projections.
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Sheaves.Proofs.Scheme_Modules_exists_iso_pullback_of_isPullback

universe u

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry
open _root_.Opposite
open _root_.TopologicalSpace

namespace AlgebraicGeometry
open _root_.AlgebraicGeometry
namespace Scheme
open _root_.AlgebraicGeometry.Scheme
namespace Modules
open _root_.AlgebraicGeometry.Scheme.Modules
open _root_.AlgebraicGeometry.Scheme.Modules
open _root_.AlgebraicGeometry.Scheme
open _root_.AlgebraicGeometry

section iso
variable {Y Y' : Scheme.{u}} (e : Y ≅ Y')

/-- Pushforward along the two directions of a scheme isomorphism gives inverse equivalences of
    module categories. -/
noncomputable def pushforwardIsoEquivalence : Y.Modules ≌ Y'.Modules :=
  CategoryTheory.Equivalence.mk (pushforward e.hom) (pushforward e.inv)
    ((pushforwardId Y).symm ≪≫ pushforwardCongr e.hom_inv_id.symm ≪≫ (pushforwardComp e.hom
        e.inv).symm)
    (pushforwardComp e.inv e.hom ≪≫ pushforwardCongr e.inv_hom_id ≪≫ pushforwardId Y')

/-- Pullback along the isomorphism identifies with pushforward along its inverse, by uniqueness
    of left adjoints. -/
noncomputable def pullbackIsoPushforwardInv : Scheme.Modules.pullback e.hom ≅ pushforward e.inv :=
  (pullbackPushforwardAdjunction e.hom).leftAdjointUniq (pushforwardIsoEquivalence
      e).symm.toAdjunction

end iso

theorem isLocallyFreeOfRank_pushforward_of_forall_exists_isPullback_aux
    {X T : Scheme.{u}} (π : X ⟶ T) (F : X.Modules) (n : ℕ)
    (h : ∀ y : T, ∃ (W : T.Opens), y ∈ W ∧ ∃ (W' X' : Scheme.{u}) (e : W' ≅ W.toScheme) (π' : X'
        ⟶ W')
      (g' : X' ⟶ X), IsPullback g' π' π (e.hom ≫ W.ι) ∧
        IsLocallyFreeOfRank n ((pushforward π').obj ((Scheme.Modules.pullback g').obj F))) :
    IsLocallyFreeOfRank n ((pushforward π).obj F) := by
  apply IsLocallyFreeOfRank.of_forall_exists_opens
  intro y
  obtain ⟨W, hy, W', X', e, π', g', hcart₀, hLF⟩ := h y
  have hcart : IsPullback g' (π' ≫ e.hom) π W.ι :=
    hcart₀.of_iso (Iso.refl _) (Iso.refl _) e (Iso.refl _) (by simp) (by simp) (by simp) (by simp)
  refine ⟨W, hy, ?_⟩
  have hres := isPullback_morphismRestrict π W
  let θ : X' ≅ (π ⁻¹ᵁ W).toScheme := IsPullback.isoIsPullback _ _ hcart hres.flip
  have hθ₁ : θ.hom ≫ (π ⁻¹ᵁ W).ι = g' := IsPullback.isoIsPullback_hom_fst _ _ hcart hres.flip
  have hθ₂ : θ.hom ≫ (π ∣_ W) = π' ≫ e.hom := IsPullback.isoIsPullback_hom_snd _ _ hcart hres.flip
  have h1 : IsLocallyFreeOfRank n
      ((pushforward (π' ≫ e.hom)).obj ((Scheme.Modules.pullback g').obj F)) := by
    have := hLF.pullback e.inv
    refine IsLocallyFreeOfRank.of_iso ?_ this
    exact ((pullbackIsoPushforwardInv e.symm).app _) ≪≫ ((pushforwardComp π' e.hom).app _)
  have h2 : IsLocallyFreeOfRank n
      ((pushforward (π ∣_ W)).obj ((Scheme.Modules.pullback (π ⁻¹ᵁ W).ι).obj F)) := by
    have h1' : IsLocallyFreeOfRank n
        ((pushforward (θ.hom ≫ (π ∣_ W))).obj
          ((Scheme.Modules.pullback (θ.hom ≫ (π ⁻¹ᵁ W).ι)).obj F)) := by
      refine IsLocallyFreeOfRank.of_iso ?_ h1
      exact (pushforwardCongr hθ₂.symm).app _ ≪≫ (pushforward _).mapIso ((pullbackCongr
          hθ₁.symm).app _)
    refine IsLocallyFreeOfRank.of_iso ?_ h1'
    refine ((pushforwardComp θ.hom (π ∣_ W)).symm.app _) ≪≫ (pushforward (π ∣_ W)).mapIso ?_
    refine (pushforward θ.hom).mapIso ((pullbackComp θ.hom (π ⁻¹ᵁ W).ι).symm.app F) ≪≫ ?_
    haveI : (Scheme.Modules.pullback θ.hom).IsEquivalence := by
      have : (pushforward θ.inv).IsEquivalence := (pushforwardIsoEquivalence
          θ.symm).isEquivalence_functor
      exact Functor.isEquivalence_of_iso (pullbackIsoPushforwardInv θ).symm
    exact (asIso ((pullbackPushforwardAdjunction θ.hom).unit.app
      ((Scheme.Modules.pullback (π ⁻¹ᵁ W).ι).obj F))).symm
  refine IsLocallyFreeOfRank.of_iso ?_ h2
  exact (pushforward (π ∣_ W)).mapIso ((restrictFunctorIsoPullback (π ⁻¹ᵁ W).ι).symm.app F) ≪≫
    (pushforwardRestrictIso π W).app F ≪≫ (restrictFunctorIsoPullback W.ι).app _

theorem exists_iso_pullback_of_isPullback_aux
    {X T X' W' Z : Scheme.{u}} (π : X ⟶ T) (π' : X' ⟶ W') (g' : X' ⟶ X) (j : W' ⟶ T)
    (hcart : IsPullback g' π' π j) (s : Z ⟶ W') :
    ∃ φ : Limits.pullback π (s ≫ j) ≅ Limits.pullback π' s,
      φ.hom ≫ Limits.pullback.snd π' s = Limits.pullback.snd π (s ≫ j) ∧
      φ.hom ≫ Limits.pullback.fst π' s ≫ g' = Limits.pullback.fst π (s ≫ j) ∧
      ∀ G : X.Modules, Nonempty ((Scheme.Modules.pullback (Limits.pullback.fst π (s ≫ j))).obj G ≅
        (Scheme.Modules.pullback φ.hom).obj
          ((Scheme.Modules.pullback (Limits.pullback.fst π' s)).obj
            ((Scheme.Modules.pullback g').obj G))) := by
  have hbig : IsPullback (Limits.pullback.fst π' s ≫ g') (Limits.pullback.snd π' s) π (s ≫ j) :=
    (IsPullback.of_hasPullback π' s).paste_horiz hcart
  let φ : Limits.pullback π (s ≫ j) ≅ Limits.pullback π' s :=
    (IsPullback.of_hasPullback π (s ≫ j)).isoIsPullback _ _ hbig
  have hφ₁ : φ.hom ≫ Limits.pullback.fst π' s ≫ g' = Limits.pullback.fst π (s ≫ j) :=
    IsPullback.isoIsPullback_hom_fst _ _ _ _
  have hφ₂ : φ.hom ≫ Limits.pullback.snd π' s = Limits.pullback.snd π (s ≫ j) :=
    IsPullback.isoIsPullback_hom_snd _ _ _ _
  refine ⟨φ, hφ₂, hφ₁, fun G => ⟨?_⟩⟩
  exact (pullbackCongr hφ₁.symm).app G ≪≫ (pullbackComp _ _).symm.app G ≪≫
    (Scheme.Modules.pullback φ.hom).mapIso ((pullbackComp _ _).symm.app G)

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry
open _root_.AlgebraicGeometry
namespace Scheme
open _root_.AlgebraicGeometry.Scheme
namespace TwoAffineOpenCover
open _root_.AlgebraicGeometry.Scheme.TwoAffineOpenCover
open _root_.AlgebraicGeometry.Scheme.TwoAffineOpenCover
open _root_.AlgebraicGeometry.Scheme
open _root_.AlgebraicGeometry

theorem exists_isPullback_snd_specMap_algebraOfHom_aux
    {R : Type u} [CommRing R] {C T : Scheme.{u}} (c : C ⟶ Spec (.of R)) (t : T ⟶ Spec (.of R))
    (W : T.Opens) (hW : IsAffineOpen W) :
    letI := algebraOfHom t W
    ∃ g' : Limits.pullback c (specMap R Γ(T, W)) ⟶ Limits.pullback c t,
      IsPullback g' (Limits.pullback.snd c (specMap R Γ(T, W))) (Limits.pullback.snd c t)
          hW.fromSpec ∧
        g' ≫ Limits.pullback.fst c t = Limits.pullback.fst c (specMap R Γ(T, W)) := by
  let := algebraOfHom t W
  have key : hW.fromSpec ≫ t = specMap R Γ(T, W) := by
    have h := IsAffineOpen.SpecMap_appLE_fromSpec t (isAffineOpen_top _) hW (le_top (a := W))
    rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv, ← Spec.map_comp] at h
    change _ = Spec.map (CommRingCat.ofHom ((Scheme.ΓSpecIso (.of R)).inv ≫ t.appLE ⊤ W le_top).hom)
    rw [CommRingCat.ofHom_hom]
    exact h.symm
  let e₁ : Limits.pullback (Limits.pullback.snd c t) hW.fromSpec ≅ Limits.pullback c (specMap R
      Γ(T, W)) :=
    pullbackLeftPullbackSndIso c t hW.fromSpec ≪≫ Limits.pullback.congrHom rfl key
  have h1 : IsPullback (Limits.pullback.fst (Limits.pullback.snd c t) hW.fromSpec)
      (Limits.pullback.snd (Limits.pullback.snd c t) hW.fromSpec) (Limits.pullback.snd c t)
          hW.fromSpec :=
    IsPullback.of_hasPullback _ _
  refine ⟨e₁.inv ≫ Limits.pullback.fst (Limits.pullback.snd c t) hW.fromSpec, ?_, ?_⟩
  swap
  · rw [Category.assoc, Iso.inv_comp_eq]
    simp only [e₁, Iso.trans_hom, Category.assoc, Limits.pullback.congrHom_hom]
    delta CategoryTheory.Limits.pullback.map
    rw [Limits.pullback.lift_fst, Category.comp_id, pullbackLeftPullbackSndIso_hom_fst]
  refine h1.of_iso e₁ (Iso.refl _) (Iso.refl _) (Iso.refl _) (by simp) ?_ (by simp) (by simp)
  simp only [e₁, Iso.trans_hom, Iso.refl_hom, Category.comp_id, Category.assoc,
      Limits.pullback.congrHom_hom]
  delta CategoryTheory.Limits.pullback.map
  rw [Limits.pullback.lift_snd, Category.comp_id, pullbackLeftPullbackSndIso_hom_snd]

theorem finiteType_algebraOfHom_aux {R : Type u} [CommRing R] {T : Scheme.{u}} (t : T ⟶ Spec
    (.of R))
    [LocallyOfFiniteType t] (W : T.Opens) (hW : IsAffineOpen W) :
    letI := algebraOfHom t W
    Algebra.FiniteType R Γ(T, W) := by
  let := algebraOfHom t W
  have h : (t.appLE ⊤ W le_top).hom.FiniteType :=
    t.finiteType_appLE (isAffineOpen_top _) hW le_top
  have h' : (Scheme.ΓSpecIso (.of R)).inv.hom.FiniteType :=
    RingHom.FiniteType.of_surjective _ (Scheme.ΓSpecIso (.of
        R)).symm.commRingCatIsoToRingEquiv.surjective
  rw [← RingHom.finiteType_algebraMap]
  exact h.comp h'

end AlgebraicGeometry.Scheme.TwoAffineOpenCover

with_weak_namespace _root_.AlgebraicCurves.Geometry.Sheaves.Proofs
open _root_.AlgebraicGeometry.Scheme.Modules
    Scheme_Modules_exists_iso_pullback_of_isPullback.AlgebraicGeometry.Scheme.Modules in
with_weak_namespace Scheme_Modules_exists_iso_pullback_of_isPullback
theorem _root_.AlgebraicGeometry.Scheme.Modules.exists_iso_pullback_of_isPullback
    {X T X' W' Z : Scheme.{u}} (π : X ⟶ T) (π' : X' ⟶ W') (g' : X' ⟶ X) (j : W' ⟶ T)
    (hcart : IsPullback g' π' π j) (s : Z ⟶ W') :
    ∃ φ : Limits.pullback π (s ≫ j) ≅ Limits.pullback π' s,
      φ.hom ≫ Limits.pullback.snd π' s = Limits.pullback.snd π (s ≫ j) ∧
      φ.hom ≫ Limits.pullback.fst π' s ≫ g' = Limits.pullback.fst π (s ≫ j) ∧
      ∀ G : X.Modules, Nonempty ((Scheme.Modules.pullback (Limits.pullback.fst π (s ≫ j))).obj G ≅
        (Scheme.Modules.pullback φ.hom).obj
          ((Scheme.Modules.pullback (Limits.pullback.fst π' s)).obj ((Scheme.Modules.pullback
              g').obj G))) :=
  exists_iso_pullback_of_isPullback_aux π π' g' j hcart s

end AlgebraicCurves.Geometry.Sheaves.Proofs.Scheme_Modules_exists_iso_pullback_of_isPullback
end ProofImplementation

attribute [-instance]
  TwoChartCech.Sections.M0_moduleA
  TwoChartCech.Sections.M1_module
  TwoChartCech.Cover.A01_algebra
  TwoChartCech.Cover.A0_algebra
  TwoChartCech.Cover.A1_commRing
  TwoChartCech.Cover.A1_algebra
  TwoChartCech.Sections.M01_module
  TwoChartCech.Sections.M0_addCommGroup
  TwoChartCech.Sections.M0_tower
  TwoChartCech.Sections.M01_addCommGroup
  TwoChartCech.Cover.A0_commRing
  TwoChartCech.Sections.M1_tower
  TwoChartCech.Sections.M01_moduleA
  TwoChartCech.Sections.M0_module
  TwoChartCech.Sections.M1_moduleA
  TwoChartCech.Sections.M1_addCommGroup
  TwoChartCech.Cover.A01_commRing
  TwoChartCech.Sections.M01_tower
  CoherentBaseChange.TwoTermComplex.C0_module
  CoherentBaseChange.TwoTermComplex.C0_addCommGroup
  CoherentBaseChange.TwoTermComplex.C1_module
  CoherentBaseChange.TwoTermComplex.C1_addCommGroup
  CoherentBaseChange.TwoTermComplex.C0_free
  CoherentBaseChange.TwoTermComplex.C1_finite
  CoherentBaseChange.TwoTermComplex.C0_finite
  CoherentBaseChange.TwoTermComplex.C1_free
attribute [-simp]
  AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq
  AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec
  AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1
  AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0
  TwoChartCech.Sections.mk.injEq
  TwoChartCech.Cover.mk.injEq
  TwoChartCech.GrothendieckComplex.mk.injEq
  TwoChartCech.Sections.mk.sizeOf_spec
  TwoChartCech.Cover.mk.sizeOf_spec
  TwoChartCech.Cover.lineBundle_r0_apply
  TwoChartCech.GrothendieckComplex.mk.sizeOf_spec
  TwoChartCech.Cover.lineBundle_r1_apply
  CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec
  CoherentBaseChange.TwoTermComplex.mk.injEq
