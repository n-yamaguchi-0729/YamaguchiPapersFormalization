/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_RelPicard_isInvertible_and_nonempty_pullback_iso_foldr_sectionTwist_tensor_of_range_subset.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.Util.WithWeakNamespace
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.Data.List.FinRange
import Nyll.AlgebraicCurves.Geometry.Picard.Functor
import Nyll.JacobianVarieties.Picard.ThetaBundle
import Nyll.AlgebraicCurves.Geometry.Sheaves.IdealSheafModule
import Nyll.SchemeTheory.Modules.Monoidal
import Nyll.SchemeTheory.Modules.PullbackMonoidal
import Nyll.AlgebraicCurves.Geometry.Picard.isInvertible_sectionIdeal_of_range_subset
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_IsInvertible_tensor
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_IdealSheafData_IsInvertible_isInvertible_invModule
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_IdealSheafData_IsInvertible_isInvertible_module
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_IdealSheafData_IsInvertible_pow
import Nyll.JacobianVarieties.Picard.nonempty_pullback_sectionTwist_iso_of_range_subset
import Nyll.JacobianVarieties.Picard.nonempty_pullback_sectionIdeal_pow_module_iso_of_smoothLocus

/-!
# Base change of products of positive and negative section twists

A section supported in the smooth locus has an invertible ideal. Tensor its
positive twist and negative ideal power, then induct on the finite list of
sections to preserve invertibility and the specified pullback isomorphisms.
-/

section ProofImplementation

namespace JacobianVarieties.Picard.Proofs.FoldedTwistPullback
attribute [-instance]
  AlgebraicGeometry.RelEffCartierDiv.isIso_subschemeIota_snd_of_degree_one
  AlgebraicGeometry.isIso_ker_graphOver_subschemeIota_snd
  AlgebraicGeometry.isClosedImmersion_graphOver
attribute [-simp]
  AlgebraicGeometry.graphOver_fst_assoc
  AlgebraicGeometry.RelEffCartierDiv.toPoint_comp
  AlgebraicGeometry.RelEffCartierDiv.toPoint_comp_assoc
  AlgebraicGeometry.graphOver_fst
  AlgebraicGeometry.RelEffCartierDiv.ofPoint_I
  AlgebraicGeometry.graphOver_snd
  AlgebraicGeometry.graphOver_snd_assoc

universe u


open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory
open _root_.AlgebraicGeometry
open _root_.AlgebraicGeometry.RelPicard
open _root_.NeronModelInfra
with_weak_namespace _root_.AlgebraicGeometry.RelPicard
theorem isInvertible_and_nonempty_pullback_iso_foldr_sectionTwist_tensor_of_range_subset
    {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R)) [IsSeparated c]
    (U : C.Opens) [SmoothOfRelativeDimension 1 (U.ι ≫ c)]
    {m : ℕ} (σ : Fin m → SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (hσ : ∀ j, Set.range (σ j).1 ⊆ (U : Set C)) (pos neg : Fin m → ℕ)
    {T T' : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} {t' : T' ⟶ Spec (CommRingCat.of R)}
    (ψ : SchemeHomOver t' t) :
    Scheme.Modules.IsInvertible
        ((List.finRange m).foldr
          (fun j M =>
            (sectionTwist c (σ j) t (pos j) ⊗ ((sectionIdeal c (σ j) t) ^ (neg j)).module) ⊗ M)
          (𝟙_ (pullback c t).Modules)) ∧
      Nonempty ((Scheme.Modules.pullback (baseChangeSnd c ψ)).obj
          ((List.finRange m).foldr
            (fun j M =>
              (sectionTwist c (σ j) t (pos j) ⊗ ((sectionIdeal c (σ j) t) ^ (neg j)).module) ⊗ M)
            (𝟙_ (pullback c t).Modules)) ≅
        (List.finRange m).foldr
          (fun j M =>
            (sectionTwist c (σ j) t' (pos j) ⊗ ((sectionIdeal c (σ j) t') ^ (neg j)).module) ⊗ M)
          (𝟙_ (pullback c t').Modules)) := by
  have hI : ∀ {T₀ : Scheme.{u}} (t₀ : T₀ ⟶ Spec (CommRingCat.of R)) (j : Fin m),
      (sectionIdeal c (σ j) t₀).IsInvertible :=
    fun t₀ j => isInvertible_sectionIdeal_of_range_subset c (σ j) U (hσ j) t₀
  have hN : ∀ {T₀ : Scheme.{u}} (t₀ : T₀ ⟶ Spec (CommRingCat.of R)) (j : Fin m),
      Scheme.Modules.IsInvertible
        (sectionTwist c (σ j) t₀ (pos j) ⊗ ((sectionIdeal c (σ j) t₀) ^ (neg j)).module) :=
    fun t₀ j => Scheme.Modules.IsInvertible.tensor
      (Scheme.IdealSheafData.IsInvertible.isInvertible_invModule ((hI t₀ j).pow (pos j)))
      (Scheme.IdealSheafData.IsInvertible.isInvertible_module ((hI t₀ j).pow (neg j)))
  have eN : ∀ j : Fin m, Nonempty ((Scheme.Modules.pullback (baseChangeSnd c ψ)).obj
        (sectionTwist c (σ j) t (pos j) ⊗ ((sectionIdeal c (σ j) t) ^ (neg j)).module) ≅
      sectionTwist c (σ j) t' (pos j) ⊗ ((sectionIdeal c (σ j) t') ^ (neg j)).module) := fun j =>
    ⟨Scheme.Modules.pullbackTensorObjIso (baseChangeSnd c ψ) _ _ ≪≫
      tensorIso (nonempty_pullback_sectionTwist_iso_of_range_subset
        R c (σ j) U (hσ j) ψ (pos j)).some
        (nonempty_pullback_sectionIdeal_pow_module_iso_of_smoothLocus
          R c U (σ j) (hσ j) ψ (neg j)).some⟩
  have key : ∀ l : List (Fin m),
      Scheme.Modules.IsInvertible
          (l.foldr (fun j M =>
            (sectionTwist c (σ j) t (pos j) ⊗ ((sectionIdeal c (σ j) t) ^ (neg j)).module) ⊗ M)
            (𝟙_ (pullback c t).Modules)) ∧
        Nonempty ((Scheme.Modules.pullback (baseChangeSnd c ψ)).obj
            (l.foldr (fun j M =>
              (sectionTwist c (σ j) t (pos j) ⊗ ((sectionIdeal c (σ j) t) ^ (neg j)).module) ⊗ M)
              (𝟙_ (pullback c t).Modules)) ≅
          l.foldr (fun j M =>
            (sectionTwist c (σ j) t' (pos j) ⊗ ((sectionIdeal c (σ j) t') ^ (neg j)).module) ⊗ M)
            (𝟙_ (pullback c t').Modules)) := by
    intro l
    induction l with
    | nil =>
        exact ⟨Scheme.Modules.isInvertible_unit _,
          ⟨Scheme.Modules.pullbackTensorUnitObjIso (baseChangeSnd c ψ)⟩⟩
    | cons j l ih =>
        simp only [List.foldr_cons]
        exact ⟨(hN t j).tensor ih.1,
          ⟨Scheme.Modules.pullbackTensorObjIso (baseChangeSnd c ψ) _ _ ≪≫
            tensorIso (eN j).some ih.2.some⟩⟩
  exact key (List.finRange m)
end JacobianVarieties.Picard.Proofs.FoldedTwistPullback
end ProofImplementation

attribute [-instance]
  AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap
  AlgebraicGeometry.Scheme.Modules.pullback_monoidal
  AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization'
  AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap
  AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal
  AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap
  AlgebraicGeometry.Scheme.Modules.sheafifyPullback_lifting
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
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instNeg
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulInt
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAddCommGroup
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAdd
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSub
open _root_.AlgebraicGeometry.Scheme.IdealSheafData.IdealHom in
attribute [-instance]
  instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop
open _root_.AlgebraicGeometry.Scheme.IdealSheafData.IdealHom in
attribute [-instance]
  instSMulCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop
attribute [-instance]
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulNat
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instZero
  AlgebraicGeometry.RelEffCartierDiv.isIso_subschemeIota_snd_of_degree_one
  AlgebraicGeometry.isIso_ker_graphOver_subschemeIota_snd
  AlgebraicGeometry.isClosedImmersion_graphOver
attribute [-simp]
  PresheafOfModules.freeεIso_hom_app
  PresheafOfModules.freeμIso_hom_app
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.sub_app
  AlgebraicGeometry.Scheme.IdealSheafData.sres_sresTop
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.add_app
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.sizeOf_spec
  AlgebraicGeometry.Scheme.IdealSheafData.coe_resLE
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.smul_app
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_ofLE_app
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.ideal_range
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zero_app
  AlgebraicGeometry.Scheme.IdealSheafData.sres_sres
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.comp_app
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.neg_app
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.id_app
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_mulRight_app
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.nsmul_app
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.injEq
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zsmul_app
  AlgebraicGeometry.graphOver_fst_assoc
  AlgebraicGeometry.RelEffCartierDiv.toPoint_comp
  AlgebraicGeometry.RelEffCartierDiv.toPoint_comp_assoc
  AlgebraicGeometry.graphOver_fst
  AlgebraicGeometry.RelEffCartierDiv.ofPoint_I
  AlgebraicGeometry.graphOver_snd
  AlgebraicGeometry.graphOver_snd_assoc
