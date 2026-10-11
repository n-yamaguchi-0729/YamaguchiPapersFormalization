/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_Polarisation_nonempty_iso_of_locIsoOnBase_of_pullback_iso_unit_of_forall_bijective.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.Algebra.Category.Ring.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.Restrict
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.CategoryTheory.Iso
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Iso
import Mathlib.Tactic.Choose
import AlgebraicCurves.Geometry.Picard.PolarisationRosati
import AlgebraicCurves.Geometry.Picard.Functor
import SchemeTheory.Cohomology.Cech.TwoAffineOpenCover
import AlgebraicCurves.Geometry.Picard.RigidifiedLineBundle_nonempty_iso_of_pullbackAlong_openCover_of_bijective_sections

/-!
# Polarisation nonempty iso of loc Iso On Base of pullback iso unit of forall bijective
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Picard.Proofs
namespace Polarisation_nonempty_iso_of_locIsoOnBase_of_pullback_iso_unit_of_forall_bijective

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Polarisation
  AlgebraicGeometry.RelPicard NeronModelInfra

namespace P2LocIso

variable {T : Type u} [CommRing T] {B : Scheme.{u}} (h : B ⟶ Spec (CommRingCat.of T))
  (e : Spec (CommRingCat.of T) ⟶ B) (he : e ≫ h = 𝟙 _)

/-- The chosen section regarded as a morphism over the base. -/
def ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of T))) h := ⟨e, he⟩

theorem rigSection_comp_fst :
    rigSection h (𝟙 (Spec (CommRingCat.of T))) (ε h e he) ≫ pullback.fst h (𝟙 _) = e := by
  simp only [rigSection, ε, pullback.lift_fst, Category.id_comp]

/--
The rigidified line bundle obtained from an invertible module and its trivialization along the
section.
-/
noncomputable def rig (M : B.Modules) (hM : Scheme.Modules.IsInvertible M)
    (α : (Scheme.Modules.pullback e).obj M ≅ SheafOfModules.unit (Spec (CommRingCat.of
      T)).ringCatSheaf) :
    RigidifiedLineBundle h (ε h e he) (𝟙 (Spec (CommRingCat.of T))) where
  L := (Scheme.Modules.pullback (pullback.fst h (𝟙 _))).obj M
  isInvertible := hM.pullback _
  rigidified := ⟨(Scheme.Modules.pullbackComp _ _).app M ≪≫
    (Scheme.Modules.pullbackCongr (rigSection_comp_fst h e he)).app M ≪≫ α⟩

/-- Transport a pullback isomorphism along a commuting composite of scheme morphisms. -/
noncomputable def moveIso {X Y Z : Scheme.{u}} (a : X ⟶ Y) (b : Y ⟶ Z) (c : X ⟶ Z) (hc : a ≫ b = c)
    (M M' : Z.Modules) (φ : (Scheme.Modules.pullback b).obj M ≅ (Scheme.Modules.pullback b).obj M')
      :
    (Scheme.Modules.pullback c).obj M ≅ (Scheme.Modules.pullback c).obj M' :=
  ((Scheme.Modules.pullbackCongr hc).app M).symm ≪≫ ((Scheme.Modules.pullbackComp a b).app M).symm
    ≪≫
    (Scheme.Modules.pullback a).mapIso φ ≪≫ (Scheme.Modules.pullbackComp a b).app M' ≪≫
    (Scheme.Modules.pullbackCongr hc).app M'

/--
The local isomorphism of rigidified pullbacks induced by an isomorphism on an inverse-image
open.
-/
noncomputable def locIso (M M' : B.Modules) (hM : Scheme.Modules.IsInvertible M) (hM' :
  Scheme.Modules.IsInvertible M')
    (α : (Scheme.Modules.pullback e).obj M ≅ SheafOfModules.unit (Spec (CommRingCat.of
      T)).ringCatSheaf)
    (α' : (Scheme.Modules.pullback e).obj M' ≅ SheafOfModules.unit (Spec (CommRingCat.of
      T)).ringCatSheaf)
    (U : (Spec (CommRingCat.of T)).Opens)
    (φU : (Scheme.Modules.pullback (h ⁻¹ᵁ U).ι).obj M ≅ (Scheme.Modules.pullback (h ⁻¹ᵁ U).ι).obj
      M') :
    ((rig h e he M hM α).pullbackAlong (⟨U.ι, Category.comp_id _⟩ : SchemeHomOver U.ι (𝟙 _))).L ≅
      ((rig h e he M' hM' α').pullbackAlong (⟨U.ι, Category.comp_id _⟩ : SchemeHomOver U.ι (𝟙
        _))).L := by
  have hc : (pullbackRestrictIsoRestrict h U).hom ≫ (h ⁻¹ᵁ U).ι =
      baseChangeSnd h (⟨U.ι, Category.comp_id _⟩ : SchemeHomOver U.ι (𝟙 _)) ≫ pullback.fst h (𝟙 _)
        := by
    rw [pullbackRestrictIsoRestrict_hom_ι]
    simp only [baseChangeSnd, pullback.lift_fst, Category.comp_id]
  exact (Scheme.Modules.pullbackComp _ _).app M ≪≫
    moveIso _ _ _ hc M M' φU ≪≫ ((Scheme.Modules.pullbackComp _ _).app M').symm

/--
Recover an isomorphism of modules from their pullbacks along the projection over the identity
base map.
-/
noncomputable def unpull (M M' : B.Modules)
    (φ : (Scheme.Modules.pullback (pullback.fst h (𝟙 (Spec (CommRingCat.of T))))).obj M ≅
      (Scheme.Modules.pullback (pullback.fst h (𝟙 (Spec (CommRingCat.of T))))).obj M') : M ≅ M' :=
  let π := pullback.fst h (𝟙 (Spec (CommRingCat.of T)))
  let back (N : B.Modules) : (Scheme.Modules.pullback (inv π)).obj ((Scheme.Modules.pullback π).obj
    N) ≅ N :=
    (Scheme.Modules.pullbackComp (inv π) π).app N ≪≫ (Scheme.Modules.pullbackCongr
      (IsIso.inv_hom_id π)).app N ≪≫
      (Scheme.Modules.pullbackId B).app N
  (back M).symm ≪≫ (Scheme.Modules.pullback (inv π)).mapIso φ ≪≫ back M'
include he in
theorem core (hH0 : ∀ (A : Type u) [CommRing A] [Algebra T A],
      letI := Scheme.TwoAffineOpenCover.algebraOfHom
        (Limits.pullback.snd h (Scheme.TwoAffineOpenCover.specMap T A)) ⊤
      Function.Bijective (algebraMap A Γ(Limits.pullback h (Scheme.TwoAffineOpenCover.specMap T A),
        ⊤)))
    (M M' : B.Modules) (hM : Scheme.Modules.IsInvertible M) (hM' : Scheme.Modules.IsInvertible M')
    (hloc : LocIsoOnBase h M M')
    (α : (Scheme.Modules.pullback e).obj M ≅ SheafOfModules.unit (Spec (CommRingCat.of
      T)).ringCatSheaf)
    (α' : (Scheme.Modules.pullback e).obj M' ≅ SheafOfModules.unit (Spec (CommRingCat.of
      T)).ringCatSheaf) :
    Nonempty (M ≅ M') := by
  classical
  have hloc' : ∀ s : ↥(Spec (CommRingCat.of T)), ∃ U : (Spec (CommRingCat.of T)).Opens, s ∈ U ∧
      Nonempty ((Scheme.Modules.pullback (h ⁻¹ᵁ U).ι).obj M ≅ (Scheme.Modules.pullback (h ⁻¹ᵁ
        U).ι).obj M') := hloc
  choose U hyU hU using hloc'
  obtain ⟨φ⟩ := RigidifiedLineBundle.nonempty_iso_of_pullbackAlong_openCover_of_bijective_sections
    T h (ε h e he) hH0
    (𝟙 (Spec (CommRingCat.of T)))
    (ι := ↥(Spec (CommRingCat.of T))) (U := fun y => ((U y : (Spec (CommRingCat.of T)).Opens) :
      Scheme.{u}))
    (fun y => (U y).ι)
    (fun y => (⟨(U y).ι, Category.comp_id _⟩ : SchemeHomOver (U y).ι (𝟙 _)))
    (fun x => ⟨x, by simpa only [Scheme.Opens.range_ι, SetLike.mem_coe] using hyU x⟩)
    (rig h e he M hM α) (rig h e he M' hM' α')
    (fun y => ⟨locIso h e he M M' hM hM' α α' (U y) (hU y).some⟩)
  exact ⟨unpull h M M' φ⟩

end P2LocIso

end Polarisation_nonempty_iso_of_locIsoOnBase_of_pullback_iso_unit_of_forall_bijective
end AlgebraicCurves.Geometry.Picard.Proofs

namespace AlgebraicGeometry.Polarisation

universe u

open _root_.AlgebraicCurves.Geometry.Picard.Proofs in
open Polarisation_nonempty_iso_of_locIsoOnBase_of_pullback_iso_unit_of_forall_bijective in
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Polarisation in
open AlgebraicGeometry.RelPicard NeronModelInfra in
theorem nonempty_iso_of_locIsoOnBase_of_pullback_iso_unit_of_forall_bijective
    {T : Type u} [CommRing T] {B : Scheme.{u}} (h : B ⟶ Spec (CommRingCat.of T)) [QuasiCompact h]
      [QuasiSeparated h]
    (hH0 : ∀ (T' : Type u) [CommRing T'] [Algebra T T'],
      letI := Scheme.TwoAffineOpenCover.algebraOfHom
        (pullback.snd h (Scheme.TwoAffineOpenCover.specMap T T')) ⊤
      Function.Bijective (algebraMap T' Γ(pullback h (Scheme.TwoAffineOpenCover.specMap T T'), ⊤)))
    (e : Spec (CommRingCat.of T) ⟶ B) (he : e ≫ h = 𝟙 _)
    (M M' : B.Modules) (hM : Scheme.Modules.IsInvertible M) (hM' : Scheme.Modules.IsInvertible M')
    (hloc : LocIsoOnBase h M M')
    (α : (Scheme.Modules.pullback e).obj M ≅ SheafOfModules.unit (Spec (CommRingCat.of
      T)).ringCatSheaf)
    (α' : (Scheme.Modules.pullback e).obj M' ≅ SheafOfModules.unit (Spec (CommRingCat.of
      T)).ringCatSheaf) :
    Nonempty (M ≅ M') :=
  P2LocIso.core h e he hH0 M M' hM hM' hloc α α'
end AlgebraicGeometry.Polarisation
end ProofImplementation
