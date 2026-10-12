/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_RelPicard_isAlgEquivZero_tensor_of_pullback_baseChangeSnd_iso_of_tensor_iso_unit.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting
import Nyll.AlgebraicCurves.Geometry.Picard.Functor
import Nyll.JacobianVarieties.Picard.Representation
import Nyll.AlgebraicCurves.Geometry.Picard.AlgEquivZeroCut
import Nyll.SchemeTheory.Modules.Monoidal
import Nyll.SchemeTheory.Modules.PullbackMonoidal
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_IsInvertible_tensor

/-!
# Algebraic equivalence after tensoring with a fixed inverse

A family connecting two line bundles remains a family after tensoring with a fixed
line bundle. A trivialization at the first point gives algebraic equivalence to zero.
-/

section ProofImplementation

namespace AlgebraicGeometry.RelPicard

universe u


open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory
open _root_.AlgebraicGeometry
open _root_.NeronModelInfra


theorem isAlgEquivZero_tensor_of_pullback_baseChangeSnd_iso_of_tensor_iso_unit
    {k : Type u} [Field k] {K : Type u} [Field K]
    (κ : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of k))
    {X V : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of k)) (hV : V ⟶ Spec (CommRingCat.of K))
    [LocallyOfFiniteType hV] [GeometricallyIntegral hV]
    (F : (pullback x (hV ≫ κ)).Modules) (hF : Scheme.Modules.IsInvertible F)
    (v₀ v₁ : Spec (CommRingCat.of K) ⟶ V) (hv₀ : v₀ ≫ hV = 𝟙 _) (hv₁ : v₁ ≫ hV = 𝟙 _)
    (A B P : (pullback x κ).Modules)
    (eA : (Scheme.Modules.pullback (baseChangeSnd x
      (⟨v₀, by rw [← Category.assoc, hv₀, Category.id_comp]⟩ :
        SchemeHomOver κ (hV ≫ κ)))).obj F ≅ A)
    (eB : (Scheme.Modules.pullback (baseChangeSnd x
      (⟨v₁, by rw [← Category.assoc, hv₁, Category.id_comp]⟩ :
        SchemeHomOver κ (hV ≫ κ)))).obj F ≅ B)
    (hP : Scheme.Modules.IsInvertible P) (eP : A ⊗ P ≅ 𝟙_ (pullback x κ).Modules) :
    IsAlgEquivZero (pullback.snd x κ) (B ⊗ P) := by
  let Q : pullback (pullback.snd x κ) hV ≅ pullback x (hV ≫ κ) := pullbackLeftPullbackSndIso x κ hV
  have hvκ : ∀ (v : Spec (CommRingCat.of K) ⟶ V), v ≫ hV = 𝟙 _ → v ≫ hV ≫ κ = κ := fun v hv => by
    rw [← Category.assoc, hv, Category.id_comp]
  have sqF : ∀ (v : Spec (CommRingCat.of K) ⟶ V) (hv : v ≫ hV = 𝟙 _),
      baseChangeSnd (pullback.snd x κ) (⟨v, hv⟩ : SchemeHomOver (𝟙 _) hV) ≫ Q.hom =
        pullback.fst (pullback.snd x κ) (𝟙 _) ≫
          baseChangeSnd x (⟨v, hvκ v hv⟩ : SchemeHomOver κ (hV ≫ κ)) := by
    intro v hv
    apply pullback.hom_ext
    · simp only [Q, baseChangeSnd, Category.assoc, pullbackLeftPullbackSndIso_hom_fst,
        pullback.lift_fst,
        pullback.lift_fst_assoc, Category.comp_id]
    · simp only [Q, baseChangeSnd, Category.assoc, pullbackLeftPullbackSndIso_hom_snd,
        pullback.lift_snd]
      rw [← Category.assoc, pullback.condition, Category.assoc, Category.id_comp]
  have sqP : ∀ (v : Spec (CommRingCat.of K) ⟶ V) (hv : v ≫ hV = 𝟙 _),
      baseChangeSnd (pullback.snd x κ) (⟨v, hv⟩ : SchemeHomOver (𝟙 _) hV) ≫
        pullback.fst (pullback.snd x κ) hV =
        pullback.fst (pullback.snd x κ) (𝟙 _) := by
    intro v hv
    simp only [baseChangeSnd, pullback.lift_fst, Category.comp_id]
  have isoF : ∀ (v : Spec (CommRingCat.of K) ⟶ V) (hv : v ≫ hV = 𝟙 _),
      Nonempty ((Scheme.Modules.pullback
        (baseChangeSnd (pullback.snd x κ) (⟨v, hv⟩ : SchemeHomOver (𝟙 _) hV))).obj
        ((Scheme.Modules.pullback Q.hom).obj F) ≅
        (Scheme.Modules.pullback (pullback.fst (pullback.snd x κ) (𝟙 _))).obj
          ((Scheme.Modules.pullback
            (baseChangeSnd x (⟨v, hvκ v hv⟩ : SchemeHomOver κ (hV ≫ κ)))).obj F)) :=
    fun v hv => ⟨(Scheme.Modules.pullbackComp _ _).app F ≪≫
      (Scheme.Modules.pullbackCongr (sqF v hv)).app F ≪≫
      ((Scheme.Modules.pullbackComp _ _).app F).symm⟩
  have isoP : ∀ (v : Spec (CommRingCat.of K) ⟶ V) (hv : v ≫ hV = 𝟙 _),
      Nonempty ((Scheme.Modules.pullback
        (baseChangeSnd (pullback.snd x κ) (⟨v, hv⟩ : SchemeHomOver (𝟙 _) hV))).obj
        ((Scheme.Modules.pullback (pullback.fst (pullback.snd x κ) hV)).obj P) ≅
        (Scheme.Modules.pullback (pullback.fst (pullback.snd x κ) (𝟙 _))).obj P) :=
    fun v hv => ⟨(Scheme.Modules.pullbackComp _ _).app P ≪≫
      (Scheme.Modules.pullbackCongr (sqP v hv)).app P⟩
  refine ⟨V, hV, inferInstance, inferInstance,
    (Scheme.Modules.pullback Q.hom).obj F ⊗
      (Scheme.Modules.pullback (pullback.fst (pullback.snd x κ) hV)).obj P,
    (hF.pullback _).tensor (hP.pullback _), ⟨v₀, hv₀⟩, ⟨v₁, hv₁⟩, ⟨?_⟩, ⟨?_⟩⟩
  · exact Scheme.Modules.pullbackTensorObjIso _ _ _ ≪≫
      (((isoF v₀ hv₀).some ≪≫ (Scheme.Modules.pullback _).mapIso eA) ⊗ᵢ (isoP v₀ hv₀).some) ≪≫
      (Scheme.Modules.pullbackTensorObjIso _ A P).symm ≪≫ (Scheme.Modules.pullback _).mapIso eP ≪≫
      Scheme.Modules.pullbackTensorUnitObjIso _
  · exact Scheme.Modules.pullbackTensorObjIso _ _ _ ≪≫
      (((isoF v₁ hv₁).some ≪≫ (Scheme.Modules.pullback _).mapIso eB) ⊗ᵢ (isoP v₁ hv₁).some) ≪≫
      (Scheme.Modules.pullbackTensorObjIso _ B P).symm
end AlgebraicGeometry.RelPicard
end ProofImplementation

attribute [-instance]
  AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap
attribute [-instance]
  AlgebraicGeometry.Scheme.Modules.pullback_monoidal
attribute [-instance]
  AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization'
attribute [-instance]
  AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap
attribute [-instance]
  AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal
attribute [-instance]
  AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap
attribute [-instance]
  AlgebraicGeometry.Scheme.Modules.sheafifyPullback_lifting
attribute [-instance]
  PresheafOfModules.PullbackMonoidal.pullback_monoidal
attribute [-instance]
  PresheafOfModules.PullbackMonoidal.isIso_δ
attribute [-instance]
  PresheafOfModules.pushforward_laxMonoidal
attribute [-instance]
  PresheafOfModules.PullbackMonoidal.isIso_η
attribute [-instance]
  PresheafOfModules.free_monoidal
attribute [-instance]
  PresheafOfModules.restrictScalars_laxMonoidal
attribute [-instance]
  PresheafOfModules.PullbackMonoidal.isIso_δ_gS
attribute [-instance]
  PresheafOfModules.pullback_oplaxMonoidal
open _root_.PresheafOfModules.PullbackMonoidal in
attribute [-instance]
  instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb
attribute [-instance]
  PresheafOfModules.pullback_monoidal'
attribute [-simp] PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app
