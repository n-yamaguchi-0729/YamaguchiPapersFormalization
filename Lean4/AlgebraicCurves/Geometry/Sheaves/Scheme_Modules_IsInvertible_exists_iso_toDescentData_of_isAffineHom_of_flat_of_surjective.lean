/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_iso_toDescentData_of_isAffineHom_of_flat_of_surjective.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import AlgebraicCurves.Geometry.Schemes.SchemeHomOver
import AlgebraicCurves.Geometry.Picard.Functor
import AlgebraicCurves.Foundations.CategoryTheory.CategoryTheory_Pseudofunctor_DescentData_exists_iso_toDescentData_obj_of_isStackFor_of_forall_exists_iso_pullFunctor_obj
import AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_IsInvertible_exists_iso_toDescentData_of_isAffine_of_isAffineHom_of_flat_of_surjective
import AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_isStackFor_openCover
import AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_IsInvertible_toDescentData_map_bijective_of_isAffineHom_of_flat_of_surjective

/-!
# Descent of invertible modules along affine faithfully flat morphisms
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Sheaves.Proofs
namespace Scheme_Modules_IsInvertible_exists_iso_toDescentData_of_isAffineHom_of_flat_of_surjective
attribute [-simp] AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app
  Algebra.DescentCofaces.i₁_apply Algebra.DescentCofaces.i₂_apply Algebra.DescentCofaces.c₁₂_tmul
  Algebra.DescentCofaces.c₂₃_tmul Algebra.DescentCofaces.c₁₃_tmul

universe u

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry
open _root_.Opposite

namespace AlgebraicGeometry
open _root_.AlgebraicGeometry
namespace Scheme
open _root_.AlgebraicGeometry.Scheme
namespace Modules
open _root_.AlgebraicGeometry.Scheme.Modules
namespace InvDescAssembly
open _root_.AlgebraicGeometry.Scheme.Modules
open _root_.AlgebraicGeometry.Scheme
open _root_.AlgebraicGeometry

theorem isInvertible_of_iso {X : Scheme.{u}} {M N : X.Modules} (e : M ≅ N)
    (h : Scheme.Modules.IsInvertible M) : Scheme.Modules.IsInvertible N := by
  refine ⟨fun x => ?_⟩
  obtain ⟨U, hx, ⟨t⟩⟩ := h.1 x
  exact ⟨U, hx, ⟨(Scheme.Modules.pullback U.ι).mapIso e.symm ≪≫ t⟩⟩

theorem isInvertible_of_forall_affineOpens {Y : Scheme.{u}} (L : Y.Modules)
    (h : ∀ U : Y.affineOpens,
      Scheme.Modules.IsInvertible ((Scheme.Modules.pullback (U : Y.Opens).ι).obj L)) :
    Scheme.Modules.IsInvertible L := by
  refine ⟨fun y => ?_⟩
  obtain ⟨U, hU, hyU, -⟩ := exists_isAffineOpen_mem_and_subset (X := Y) (x := y) (U := ⊤) trivial
  obtain ⟨W, hyW, ⟨eW⟩⟩ := (h ⟨U, hU⟩).1 ⟨y, hyU⟩
  let e : (W : Scheme.{u}) ≅ ↑(U.ι ''ᵁ W) := U.ι.isoImage W
  have fact : (U.ι ''ᵁ W).ι = e.inv ≫ W.ι ≫ U.ι := by
    rw [← Scheme.Hom.isoImage_hom_ι, Iso.inv_hom_id_assoc]
  refine ⟨U.ι ''ᵁ W, ⟨⟨y, hyU⟩, hyW, rfl⟩, ⟨?_⟩⟩
  exact (Scheme.Modules.pullbackCongr fact).app L ≪≫
    ((Scheme.Modules.pullbackComp e.inv (W.ι ≫ U.ι)).app L).symm ≪≫
    (Scheme.Modules.pullback e.inv).mapIso
      (((Scheme.Modules.pullbackComp W.ι U.ι).app L).symm ≪≫ eW) ≪≫
    Scheme.Modules.pullbackUnitIso e.inv

/-- The open cover of a scheme by all its affine open subsets. -/
noncomputable def affineOpensCover (Y : Scheme.{u}) : Y.OpenCover :=
  ⟨⟨Y.affineOpens, fun U => (U : Y.Opens), fun U => (U : Y.Opens).ι⟩,
    (Scheme.presieve₀_mem_precoverage_iff _).mpr ⟨fun y => by
      obtain ⟨U, hU, hyU, -⟩ := exists_isAffineOpen_mem_and_subset (X := Y) (x := y) (U := ⊤)
        trivial
      exact ⟨⟨U, hU⟩, by simpa using hyU⟩, fun _ => inferInstance⟩⟩

end AlgebraicGeometry.Scheme.Modules.InvDescAssembly

end Scheme_Modules_IsInvertible_exists_iso_toDescentData_of_isAffineHom_of_flat_of_surjective
end AlgebraicCurves.Geometry.Sheaves.Proofs

namespace AlgebraicGeometry.Scheme.Modules.IsInvertible

universe u

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry
open _root_.Opposite

open _root_.AlgebraicCurves.Geometry.Sheaves.Proofs in
open Scheme_Modules_IsInvertible_exists_iso_toDescentData_of_isAffineHom_of_flat_of_surjective in
open AlgebraicGeometry.Scheme.Modules.InvDescAssembly in
open _root_.CategoryTheory.Pseudofunctor.DescentData in
theorem exists_iso_toDescentData_of_isAffineHom_of_flat_of_surjective
    {Y Y' : Scheme.{u}} (q : Y' ⟶ Y) [IsAffineHom q] [Flat q] [Surjective q]
    (D : ((Scheme.Modules.pseudofunctor.{u}).comp Bicategory.Adj.forget₁).DescentData (fun _ : Unit
      => q))
    (hD : ∀ i, Scheme.Modules.IsInvertible (D.obj i)) :
    ∃ L : Y.Modules, Scheme.Modules.IsInvertible L ∧
      Nonempty ((((Scheme.Modules.pseudofunctor.{u}).comp Bicategory.Adj.forget₁).toDescentData
        (fun _ : Unit => q)).obj L ≅ D) := by
  have affineBaseChange : MorphismProperty.IsStableUnderBaseChange
      (fun {X Y : Scheme.{u}} (f : X ⟶ Y) => IsAffineHom f) :=
    isAffineHom_isStableUnderBaseChange
  obtain ⟨L, hL, e⟩ :=
    exists_iso_toDescentData_obj_of_isStackFor_of_forall_exists_iso_pullFunctor_obj
      (C := Scheme.{u}) ((Scheme.Modules.pseudofunctor.{u}).comp Bicategory.Adj.forget₁)
      (fun _ M => Scheme.Modules.IsInvertible M)
      (fun _ _ g M hM => hM.pullback g)
      (fun _ _ _ ⟨i⟩ hM => isInvertible_of_iso i hM)
      q (U := fun U : Y.affineOpens => ((U : Y.Opens) : Scheme.{u})) (fun U => (U : Y.Opens).ι)
      (AlgebraicGeometry.Scheme.Modules.isStackFor_openCover Y (affineOpensCover Y))
      (fun Z z => (AlgebraicGeometry.Scheme.Modules.isStackFor_openCover Z
        ((affineOpensCover Y).pullback₁ z)).isPrestackFor)
      (fun Z z M N hM hN => by
        have : IsAffineHom (pullback.snd q z) :=
          affineBaseChange.of_isPullback (IsPullback.of_hasPullback q z) inferInstance
        exact toDescentData_map_bijective_of_isAffineHom_of_flat_of_surjective
          (pullback.snd q z) M N hM hN)
      D
      (fun U => by
        have : IsAffine ((U : Y.Opens) : Scheme.{u}) := U.2
        have : IsAffineHom (pullback.snd q (U : Y.Opens).ι) :=
          affineBaseChange.of_isPullback
            (IsPullback.of_hasPullback q (U : Y.Opens).ι) inferInstance
        exact exists_iso_toDescentData_of_isAffine_of_isAffineHom_of_flat_of_surjective
          (pullback.snd q (U : Y.Opens).ι) _ (fun i => (hD i).pullback _))
  exact ⟨L, isInvertible_of_forall_affineOpens L hL, e⟩

end AlgebraicGeometry.Scheme.Modules.IsInvertible
end ProofImplementation
