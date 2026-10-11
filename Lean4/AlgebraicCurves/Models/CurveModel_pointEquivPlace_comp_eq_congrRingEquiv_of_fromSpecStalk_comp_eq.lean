/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_CurveModel_pointEquivPlace_comp_eq_congrRingEquiv_of_fromSpecStalk_comp_eq.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import AlgebraicCurves.Models.Basic
import AlgebraicCurves.Places.Rational.Basic

/-!
# Curve Model point Equiv Place comp eq congr Ring Equiv of from Spec Stalk comp eq
-/

section ProofImplementation

namespace AlgebraicCurves.Models.Proofs
namespace CurveModel_pointEquivPlace_comp_eq_congrRingEquiv_of_fromSpecStalk_comp_eq

section E3

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry

universe u v

namespace AlgebraicGeometry
open _root_.AlgebraicGeometry
open _root_.AlgebraicGeometry

section FFMap

variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y] (θ : X ⟶ Y) [IsIso θ]

private theorem e3_genericPoint_specializes :
    θ.base (genericPoint X) ⤳ genericPoint Y := by
  rw [genericPoint_eq_of_isOpenImmersion θ]

private noncomputable def e3_ffMap : Y.functionField ⟶ X.functionField :=
  Y.presheaf.stalkSpecializes (e3_genericPoint_specializes θ) ≫ θ.stalkMap (genericPoint X)
@[reassoc]
private theorem e3_SpecMap_ffMap_fromSpecStalk :
    Spec.map (e3_ffMap θ) ≫ Y.fromSpecStalk (genericPoint Y) = X.fromSpecStalk (genericPoint X) ≫ θ
      := by
  rw [e3_ffMap, Spec.map_comp, Category.assoc, Scheme.SpecMap_stalkSpecializes_fromSpecStalk,
    Scheme.SpecMap_stalkMap_fromSpecStalk]

private theorem e3_germ_ffMap (U : Y.Opens) (hU : genericPoint Y ∈ U) :
    Y.presheaf.germ U (genericPoint Y) hU ≫ e3_ffMap θ =
      θ.app U ≫ X.presheaf.germ (θ ⁻¹ᵁ U) (genericPoint X)
        (show θ.base (genericPoint X) ∈ U by rwa [genericPoint_eq_of_isOpenImmersion θ]) := by
  rw [e3_ffMap, TopCat.Presheaf.germ_stalkSpecializes_assoc, Scheme.Hom.germ_stalkMap]

private theorem e3_ffMap_germ_apply (U : Y.Opens) (hU : genericPoint Y ∈ U) (s : Γ(Y, U)) :
    e3_ffMap θ (Y.presheaf.germ U (genericPoint Y) hU s) =
      X.presheaf.germ (θ ⁻¹ᵁ U) (genericPoint X)
        (show θ.base (genericPoint X) ∈ U
          by rwa [genericPoint_eq_of_isOpenImmersion θ]) (θ.app U s) := by
  rw [← CommRingCat.comp_apply, e3_germ_ffMap]; rfl

private theorem e3_ffMap_germ_of_eq {Z : Scheme.{u}} (g₂ : Y ⟶ Z) (g₁ : X ⟶ Z) (e : g₁ = θ ≫ g₂)
    (U : Z.Opens) (h₂ : genericPoint Y ∈ g₂ ⁻¹ᵁ U) (h₁ : genericPoint X ∈ g₁ ⁻¹ᵁ U) (s : Γ(Z, U)) :
    e3_ffMap θ (Y.presheaf.germ (g₂ ⁻¹ᵁ U) (genericPoint Y) h₂ (g₂.app U s)) =
      X.presheaf.germ (g₁ ⁻¹ᵁ U) (genericPoint X) h₁ (g₁.app U s) := by
  subst e
  rw [e3_ffMap_germ_apply]
  rfl

end FFMap

section ChartValue

variable {R : CommRingCat.{u}} [IsLocalRing R] {X Y : Scheme.{u}}

private theorem e3_stalkClosedPointTo_germ_appIso_inv (ι : Y ⟶ X) [IsOpenImmersion ι] (l : Spec R ⟶
  Y)
    (w : Γ(Y, ⊤)) (h : (l ≫ ι).base (IsLocalRing.closedPoint R) ∈ ι ''ᵁ ⊤) :
    Scheme.stalkClosedPointTo (l ≫ ι) (X.presheaf.germ (ι ''ᵁ ⊤) _ h ((ι.appIso ⊤).inv w)) =
      Scheme.stalkClosedPointTo l (Y.presheaf.germ ⊤ _ (TopologicalSpace.Opens.mem_top _) w) := by
  rw [Scheme.stalkClosedPointTo_comp]
  have hg (y : Y) (hy : ι.base y ∈ ι ''ᵁ ⊤) :
      ι.stalkMap y (X.presheaf.germ (ι ''ᵁ ⊤) (ι.base y) hy ((ι.appIso ⊤).inv w)) =
        Y.presheaf.germ ⊤ y (TopologicalSpace.Opens.mem_top _) w := by
    rw [Scheme.Hom.germ_stalkMap_apply, Scheme.Hom.appIso_inv_app_apply]
    exact Y.presheaf.germ_res_apply _ y hy w
  exact congrArg (Scheme.stalkClosedPointTo l) (hg _ h)

private theorem e3_stalkClosedPointTo_SpecMap_germ {A : CommRingCat.{u}} (φ : A ⟶ R) (b : A) :
    Scheme.stalkClosedPointTo (Spec.map φ) ((Spec A).presheaf.germ ⊤ _
      (TopologicalSpace.Opens.mem_top _) ((Scheme.ΓSpecIso A).inv b)) =
      φ b := by
  rw [← CommRingCat.comp_apply, Scheme.germ_stalkClosedPointTo_Spec, CommRingCat.comp_apply,
    Iso.inv_hom_id_apply]

end ChartValue

end AlgebraicGeometry

open AlgebraicCurves.Models.Proofs
open CurveModel_pointEquivPlace_comp_eq_congrRingEquiv_of_fromSpecStalk_comp_eq.AlgebraicGeometry

namespace AlgebraicCurve
open _root_.AlgebraicCurve
namespace CurveModel
open _root_.AlgebraicCurve.CurveModel
open _root_.AlgebraicCurve.CurveModel
open _root_.AlgebraicCurve

variable {K : Type u} [Field K] {L₁ : Type v} [Field L₁] [Algebra K L₁] {L₂ : Type v} [Field L₂]
  [Algebra K L₂]
  (M₁ : CurveModel K L₁) (M₂ : CurveModel K L₂) (θ : M₁.C ⟶ M₂.C) [IsIso θ]

private theorem _root_.AlgebraicCurve.CurveModel.e3_ffMap_algebraMap_stalk (x₁ : M₁.C) (s :
  M₂.C.presheaf.stalk (θ.base x₁)) :
    e3_ffMap θ (algebraMap _ M₂.C.functionField s) = algebraMap _ M₁.C.functionField (θ.stalkMap x₁
      s) := by
  rw [RingHom.algebraMap_toAlgebra, RingHom.algebraMap_toAlgebra, e3_ffMap]
  change (M₂.C.presheaf.stalkSpecializes _ ≫ M₂.C.presheaf.stalkSpecializes _ ≫ θ.stalkMap _) s =
    (θ.stalkMap x₁ ≫ M₁.C.presheaf.stalkSpecializes _) s
  rw [TopCat.Presheaf.stalkSpecializes_comp_assoc]
  erw [Scheme.Hom.stalkSpecializes_stalkMap θ (genericPoint M₁.C) x₁ (genericPoint_specializes x₁)]

open _root_.AlgebraicCurve.CurveModel

private theorem e3_isLocalHom_of_field {F : Type*} [Field F] {S : Type*} [CommRing S] [Nontrivial
  S] (f : F →+* S) :
    IsLocalHom f :=
  ⟨fun a ha => isUnit_iff_ne_zero.mpr fun h0 => by simp [h0] at ha⟩

private theorem _root_.AlgebraicCurve.CurveModel.e3_ffMap_eq_of_fromSpecStalk_comp_eq (φ : L₁ ≃+*
  L₂)
    (hθgen : M₁.C.fromSpecStalk (genericPoint M₁.C) ≫ θ =
      Spec.map (CommRingCat.ofHom
        (M₁.ffEquiv.toRingHom.comp (φ.symm.toRingHom.comp M₂.ffEquiv.symm.toRingHom))) ≫
        M₂.C.fromSpecStalk (genericPoint M₂.C)) (w : M₂.C.functionField) :
    e3_ffMap θ w = M₁.ffEquiv (φ.symm (M₂.ffEquiv.symm w)) := by
  have h1 : Spec.map (e3_ffMap θ) ≫ M₂.C.fromSpecStalk _ =
      Spec.map (CommRingCat.ofHom
        (M₁.ffEquiv.toRingHom.comp (φ.symm.toRingHom.comp M₂.ffEquiv.symm.toRingHom))) ≫
        M₂.C.fromSpecStalk (genericPoint M₂.C) := by
    rw [e3_SpecMap_ffMap_fromSpecStalk, hθgen]
  have i1 : IsLocalHom (e3_ffMap θ).hom := e3_isLocalHom_of_field _
  have i2 : IsLocalHom (CommRingCat.ofHom
      (M₁.ffEquiv.toRingHom.comp (φ.symm.toRingHom.comp M₂.ffEquiv.symm.toRingHom))).hom :=
    e3_isLocalHom_of_field _
  have h2 := (SpecToEquivOfLocalRing M₂.C M₁.C.functionField).symm.injective
    (a₁ := ⟨_, e3_ffMap θ, i1⟩) (a₂ := ⟨_, _, i2⟩) h1
  obtain ⟨h₁, h3⟩ := SpecToEquivOfLocalRing_eq_iff.mp h2
  have h4 : e3_ffMap θ = CommRingCat.ofHom
      (M₁.ffEquiv.toRingHom.comp (φ.symm.toRingHom.comp M₂.ffEquiv.symm.toRingHom)) := by
    simpa using h3
  rw [h4]
  rfl

open _root_.AlgebraicCurve.CurveModel
end AlgebraicCurve.CurveModel

open _root_.AlgebraicCurve

theorem
  _root_.AlgebraicCurve.CurveModel.pointEquivPlace_comp_eq_congrRingEquiv_of_fromSpecStalk_comp_eq
    {K : Type u} [Field K] [IsAlgClosed K]
    {L₁ : Type v} [Field L₁] [Algebra K L₁] {L₂ : Type v} [Field L₂] [Algebra K L₂]
    (M₁ : CurveModel K L₁) (M₂ : CurveModel K L₂)
    (φ : L₁ ≃+* L₂) (hφ : ∀ a : K, φ (algebraMap K L₁ a) = algebraMap K L₂ a)
    (θ : M₁.C ⟶ M₂.C) [IsIso θ] (hθ : θ ≫ M₂.toBase = M₁.toBase)
    (hθgen : M₁.C.fromSpecStalk (genericPoint M₁.C) ≫ θ =
      Spec.map (CommRingCat.ofHom
        (M₁.ffEquiv.toRingHom.comp (φ.symm.toRingHom.comp M₂.ffEquiv.symm.toRingHom))) ≫
        M₂.C.fromSpecStalk (genericPoint M₂.C))
    (x : {q : Spec (CommRingCat.of K) ⟶ M₁.C // q ≫ M₁.toBase = 𝟙 _}) :
    M₂.pointEquivPlace ⟨x.1 ≫ θ, by rw [Category.assoc, hθ, x.2]⟩ =
      Place.congrRingEquiv (e := φ) (he := hφ) (M₁.pointEquivPlace x) := by
  have hff := M₁.e3_ffMap_eq_of_fromSpecStalk_comp_eq M₂ θ φ hθgen
  refine Place.ext ?_
  rw [Place.congrRingEquiv_toValuationSubring]
  have r₂ := M₂.range_stalk_eq (pointEquivClosedPoint M₂.toBase ⟨x.1 ≫ θ,
    by rw [Category.assoc, hθ, x.2]⟩)
  have r₁ := M₁.range_stalk_eq (pointEquivClosedPoint M₁.toBase x)
  have halg := M₁.e3_ffMap_algebraMap_stalk M₂ θ (x.1.base (IsLocalRing.closedPoint K))
  simp only [CurveModel.pointEquivPlace_apply]
  ext f
  rw [ValuationSubring.mem_comap]
  constructor
  · intro hf
    have hf' : f ∈ (M₂.placeOfPoint (pointEquivClosedPoint M₂.toBase
        ⟨x.1 ≫ θ, by rw [Category.assoc, hθ, x.2]⟩)).toValuationSubring.toSubring := hf
    rw [← r₂] at hf'
    obtain ⟨s, rfl⟩ := RingHom.mem_range.mp hf'
    have key : (φ.symm : L₂ →+* L₁) (M₂.ffEquiv.symm (algebraMap _ M₂.C.functionField s)) =
        M₁.ffEquiv.symm (algebraMap _ M₁.C.functionField
          (θ.stalkMap (x.1.base (IsLocalRing.closedPoint K)) s)) := by
      apply M₁.ffEquiv.injective
      rw [RingEquiv.apply_symm_apply]
      exact (hff _).symm.trans (halg s)
    change (φ.symm : L₂ →+* L₁) (M₂.ffEquiv.symm (algebraMap _ M₂.C.functionField s)) ∈
      (M₁.placeOfPoint (pointEquivClosedPoint M₁.toBase x)).toValuationSubring
    rw [key, ← ValuationSubring.mem_toSubring, ← r₁]
    exact ⟨_, rfl⟩
  · intro hf
    have hf' : (φ.symm : L₂ →+* L₁) f ∈
        (M₁.placeOfPoint (pointEquivClosedPoint M₁.toBase x)).toValuationSubring.toSubring := hf
    rw [← r₁] at hf'
    obtain ⟨t, ht⟩ := RingHom.mem_range.mp hf'
    obtain ⟨s, rfl⟩ : ∃ s : M₂.C.presheaf.stalk (θ.base (x.1.base (IsLocalRing.closedPoint K))),
        θ.stalkMap (x.1.base (IsLocalRing.closedPoint K)) s = t :=
      ⟨inv (θ.stalkMap (x.1.base (IsLocalRing.closedPoint K))) t, by
        exact Iso.inv_hom_id_apply (asIso (θ.stalkMap (x.1.base (IsLocalRing.closedPoint K)))) t⟩
    have h5 : (φ.symm : L₂ →+* L₁) (M₂.ffEquiv.symm (algebraMap _ M₂.C.functionField s)) =
        M₁.ffEquiv.symm (algebraMap _ M₁.C.functionField
          (θ.stalkMap (x.1.base (IsLocalRing.closedPoint K)) s)) := by
      apply M₁.ffEquiv.injective
      rw [RingEquiv.apply_symm_apply]
      exact (hff _).symm.trans (halg s)
    have key : f = M₂.ffEquiv.symm (algebraMap _ M₂.C.functionField s) :=
      φ.symm.injective (ht.symm.trans h5.symm)
    rw [key]
    change M₂.ffEquiv.symm (algebraMap _ M₂.C.functionField s) ∈ (M₂.placeOfPoint
      (pointEquivClosedPoint M₂.toBase
        ⟨x.1 ≫ θ, by rw [Category.assoc, hθ, x.2]⟩)).toValuationSubring
    rw [← ValuationSubring.mem_toSubring, ← r₂]
    exact ⟨s, rfl⟩

end E3
end CurveModel_pointEquivPlace_comp_eq_congrRingEquiv_of_fromSpecStalk_comp_eq
end AlgebraicCurves.Models.Proofs
end ProofImplementation
