/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_CurveModel_ramificationIndexAlong_pointEquivPlace_eq_one_of_formallyUnramified.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
import Mathlib.RingTheory.Unramified.LocalRing
import AlgebraicCurves.Models.Basic
import AlgebraicCurves.Divisors.Correspondences
import AlgebraicCurves.Places.LocalUnramifiedRamification

/-!
# Curve Model ramification Index Along point Equiv Place eq one of formally Unramified
-/

section ProofImplementation

namespace AlgebraicCurves.Models.Proofs
namespace CurveModel_ramificationIndexAlong_pointEquivPlace_eq_one_of_formallyUnramified

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve
open Topology

noncomputable section

namespace E1bSol

section FieldMap

variable {X Y Z : Scheme.{u}} [IsIntegral X] [IsIntegral Y] [IsIntegral Z]

theorem apply_genericPoint_eq (f : X ⟶ Y) [Flat f] : f.base (genericPoint X) = genericPoint Y := by
  obtain ⟨a, ha, hfa⟩ := Flat.generalizingMap f (genericPoint_specializes (f.base (genericPoint X)))
  have hgen : IsGenericPoint a (Set.univ : Set X) := by
    rw [isGenericPoint_iff_specializes]
    intro y
    simp only [Set.mem_univ, iff_true]
    exact ha.trans (genericPoint_specializes y)
  have : a = genericPoint X := hgen.eq (genericPoint_spec X)
  rw [← this]; exact hfa

/-- The homomorphism of function fields induced by a morphism preserving the generic point. -/
noncomputable def fieldMap (f : X ⟶ Y) (h : f.base (genericPoint X) = genericPoint Y) :
    Y.functionField →+* X.functionField :=
  (f.stalkMap (genericPoint X)).hom.comp
    (Y.presheaf.stalkSpecializes (specializes_of_eq h : f.base (genericPoint X) ⤳ genericPoint
      Y)).hom

theorem fieldMap_eq (f : X ⟶ Y) (h : f.base (genericPoint X) = genericPoint Y) :
    CommRingCat.ofHom (fieldMap f h) =
      Y.presheaf.stalkSpecializes (specializes_of_eq h : f.base (genericPoint X) ⤳ genericPoint Y) ≫
        f.stalkMap (genericPoint X) := rfl

theorem algebraMap_stalkMap (f : X ⟶ Y) (h : f.base (genericPoint X) = genericPoint Y)
    (p : X) (s : Y.presheaf.stalk (f.base p)) :
    algebraMap _ X.functionField (f.stalkMap p s) = fieldMap f h (algebraMap _ Y.functionField s)
      := by
  change (X.presheaf.stalkSpecializes (genericPoint_specializes p)).hom (f.stalkMap p s) =
    (f.stalkMap (genericPoint X)).hom ((Y.presheaf.stalkSpecializes _).hom
      ((Y.presheaf.stalkSpecializes (genericPoint_specializes (f.base p))).hom s))
  rw [← Scheme.Hom.stalkSpecializes_stalkMap_apply f (genericPoint X) p (genericPoint_specializes
    p) s]
  congr 1
  rw [← CommRingCat.comp_apply, TopCat.Presheaf.stalkSpecializes_comp]

theorem fieldMap_germToFunctionField (f : X ⟶ Y) (h : f.base (genericPoint X) = genericPoint Y)
    (U : Y.Opens) [hU : Nonempty (U : Scheme.{u})] [hU' : Nonempty ((f ⁻¹ᵁ U : X.Opens) :
      Scheme.{u})]
    (s : Γ(Y, U)) :
    fieldMap f h (Y.germToFunctionField U s) = X.germToFunctionField (f ⁻¹ᵁ U) (f.app U s) := by
  have hη : f.base (genericPoint X) ∈ U := by
    rw [h]
    exact ((genericPoint_spec Y).mem_open_set_iff U.2).mpr
      ⟨(Classical.arbitrary (U : Scheme.{u})).1, Set.mem_univ _, (Classical.arbitrary (U :
        Scheme.{u})).2⟩
  change (f.stalkMap (genericPoint X)).hom ((Y.presheaf.stalkSpecializes _).hom
      ((Y.presheaf.germ U (genericPoint Y) _).hom s)) = (X.presheaf.germ (f ⁻¹ᵁ U) (genericPoint X)
        _).hom (f.app U s)
  rw [TopCat.Presheaf.germ_stalkSpecializes_apply, Scheme.Hom.germ_stalkMap_apply]

theorem fieldMap_comp (f : X ⟶ Y) (g : Y ⟶ Z) (hf : f.base (genericPoint X) = genericPoint Y)
    (hg : g.base (genericPoint Y) = genericPoint Z) (hfg : (f ≫ g).base (genericPoint X) =
      genericPoint Z) :
    fieldMap (f ≫ g) hfg = (fieldMap f hf).comp (fieldMap g hg) := by
  apply RingHom.ext
  intro t
  obtain ⟨U, hU, s, rfl⟩ := TopCat.Presheaf.exists_germ_eq (F := Z.presheaf) (x := genericPoint Z) t
  have : Nonempty (U : Scheme.{u}) := ⟨⟨_, hU⟩⟩
  have hηY : g.base (genericPoint Y) ∈ U := by rw [hg]; exact hU
  have : Nonempty ((g ⁻¹ᵁ U : Y.Opens) : Scheme.{u}) := ⟨⟨_, hηY⟩⟩
  have hηX : (f ≫ g).base (genericPoint X) ∈ U := by rw [hfg]; exact hU
  have : Nonempty (((f ≫ g) ⁻¹ᵁ U : X.Opens) : Scheme.{u}) := ⟨⟨_, hηX⟩⟩
  have hηX' : f.base (genericPoint X) ∈ g ⁻¹ᵁ U := by
    change (f ≫ g).base (genericPoint X) ∈ U; exact hηX
  have : Nonempty ((f ⁻¹ᵁ (g ⁻¹ᵁ U) : X.Opens) : Scheme.{u}) := ⟨⟨_, hηX'⟩⟩
  have e1 := fieldMap_germToFunctionField (f ≫ g) hfg U s
  have e2 := fieldMap_germToFunctionField g hg U s
  have e3 := fieldMap_germToFunctionField f hf (g ⁻¹ᵁ U) (g.app U s)
  change fieldMap (f ≫ g) hfg (Z.germToFunctionField U s) = fieldMap f hf (fieldMap g hg
    (Z.germToFunctionField U s))
  rw [e1, e2, e3]
  rfl

theorem fieldMap_eq_of_fromSpecStalk_comp_eq (f : X ⟶ Y) (h : f.base (genericPoint X) =
  genericPoint Y)
    (c : Y.functionField →+* X.functionField)
    (hc : X.fromSpecStalk (genericPoint X) ≫ f = Spec.map (CommRingCat.ofHom c) ≫ Y.fromSpecStalk
      (genericPoint Y)) :
    fieldMap f h = c := by
  have key : Spec.map (CommRingCat.ofHom (fieldMap f h)) ≫ Y.fromSpecStalk (genericPoint Y) =
      Spec.map (CommRingCat.ofHom c) ≫ Y.fromSpecStalk (genericPoint Y) := by
    rw [← hc, fieldMap_eq, Spec.map_comp, Category.assoc,
      Scheme.SpecMap_stalkSpecializes_fromSpecStalk,
      Scheme.SpecMap_stalkMap_fromSpecStalk]
  have := (cancel_mono (Y.fromSpecStalk (genericPoint Y))).mp key
  have := Spec.map_injective this
  exact congrArg CommRingCat.Hom.hom this

end FieldMap

end E1bSol

end

end CurveModel_ramificationIndexAlong_pointEquivPlace_eq_one_of_formallyUnramified
end AlgebraicCurves.Models.Proofs

namespace AlgebraicCurve

noncomputable section

universe u

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.AlgebraicCurve _root_.Topology

open _root_.AlgebraicCurves.Models.Proofs in
open CurveModel_ramificationIndexAlong_pointEquivPlace_eq_one_of_formallyUnramified in
open E1bSol in
theorem CurveModel.ramificationIndexAlong_pointEquivPlace_eq_one_of_formallyUnramified
    {K : Type u} [Field K] [IsAlgClosed K]
    {L : Type u} [Field L] [Algebra K L] {L' : Type u} [Field L'] [Algebra K L']
    (M : CurveModel K L) (M' : CurveModel K L')
    (φ : L' →ₐ[K] L) (hφ : φ.toRingHom.IsIntegral)
    (πM : M.C ⟶ M'.C) (hπM : πM ≫ M'.toBase = M.toBase)
    (hgen : M.C.fromSpecStalk (genericPoint M.C) ≫ πM =
      Spec.map (CommRingCat.ofHom (M.ffEquiv.toRingHom.comp (φ.toRingHom.comp
        M'.ffEquiv.symm.toRingHom))) ≫
        M'.C.fromSpecStalk (genericPoint M'.C))
    (y : {q : Spec (CommRingCat.of K) ⟶ M.C // q ≫ M.toBase = 𝟙 _})
    (V : M.C.Opens) (hyV : y.1.base (IsLocalRing.closedPoint K) ∈ V)
    (hV : FormallyUnramified (V.ι ≫ πM)) :
    Place.ramificationIndexAlong φ (M.pointEquivPlace y) = 1 := by
  classical
  set x₀ : ↥M.C := y.1.base (IsLocalRing.closedPoint K) with hx₀
  let y' : {q : Spec (CommRingCat.of K) ⟶ M'.C // q ≫ M'.toBase = 𝟙 _} :=
    ⟨y.1 ≫ πM, by rw [Category.assoc, hπM]; exact y.2⟩
  let x : closedPoints M.C := pointEquivClosedPoint M.toBase y
  let x' : closedPoints M'.C := pointEquivClosedPoint M'.toBase y'
  have hxval : x.1 = x₀ := rfl
  have hx'val : x'.1 = πM.base x₀ := by
    change (y.1 ≫ πM).base (IsLocalRing.closedPoint K) = πM.base (y.1.base (IsLocalRing.closedPoint
      K))
    exact Scheme.Hom.comp_apply y.1 πM (show Spec (CommRingCat.of K) from IsLocalRing.closedPoint K)
  have hξ : πM.base (genericPoint M.C) = genericPoint M'.C := by
    have h := congrArg (fun (g : Spec (CommRingCat.of M.C.functionField) ⟶ M'.C) =>
      g (show Spec (CommRingCat.of M.C.functionField) from IsLocalRing.closedPoint
        M.C.functionField)) hgen
    change πM (M.C.fromSpecStalk (genericPoint M.C) (IsLocalRing.closedPoint M.C.functionField)) =
      M'.C.fromSpecStalk (genericPoint M'.C)
        ((Spec.map (CommRingCat.ofHom (M.ffEquiv.toRingHom.comp (φ.toRingHom.comp
          M'.ffEquiv.symm.toRingHom))))
          (IsLocalRing.closedPoint M.C.functionField)) at h
    erw [Scheme.fromSpecStalk_closedPoint] at h
    rw [h]
    have : (Spec.map (CommRingCat.ofHom (M.ffEquiv.toRingHom.comp (φ.toRingHom.comp
      M'.ffEquiv.symm.toRingHom)))).base
        (IsLocalRing.closedPoint M.C.functionField) = IsLocalRing.closedPoint M'.C.functionField :=
          Subsingleton.elim _ _
    rw [this, Scheme.fromSpecStalk_closedPoint]
  have hB : fieldMap πM hξ = M.ffEquiv.toRingHom.comp (φ.toRingHom.comp M'.ffEquiv.symm.toRingHom)
    :=
    fieldMap_eq_of_fromSpecStalk_comp_eq πM hξ _ hgen
  let S := M.C.presheaf.stalk x₀
  let S' := M'.C.presheaf.stalk (πM.base x₀)
  let ρ : S →+* L := M.ffEquiv.symm.toRingHom.comp (algebraMap S M.C.functionField)
  let ρ' : S' →+* L' := M'.ffEquiv.symm.toRingHom.comp (algebraMap S' M'.C.functionField)
  have hρinj : Function.Injective ρ :=
    M.ffEquiv.symm.injective.comp (IsFractionRing.injective S M.C.functionField)
  have hρ'inj : Function.Injective ρ' :=
    M'.ffEquiv.symm.injective.comp (IsFractionRing.injective S' M'.C.functionField)
  have hcompat : ∀ t : S', ρ ((πM.stalkMap x₀).hom t) = φ (ρ' t) := fun t => by
    change M.ffEquiv.symm (algebraMap S M.C.functionField ((πM.stalkMap x₀).hom t)) =
      φ (M'.ffEquiv.symm (algebraMap S' M'.C.functionField t))
    rw [algebraMap_stalkMap πM hξ x₀ t, hB]
    simp only [RingHom.coe_comp, RingEquiv.toRingHom_eq_coe, Function.comp_apply, RingHom.coe_coe,
      AlgHom.toRingHom_eq_coe, RingEquiv.symm_apply_apply]
    try rfl
  set w : Place K L := M.pointEquivPlace y with hw
  have hwx : w = M.placeOfPoint x := rfl
  let w' : Place K L' := M'.placeOfPoint ⟨πM.base x₀, hx'val ▸ x'.2⟩
  have hrange : ρ.range = w.toValuationSubring.toSubring := M.range_stalk_eq x
  have hrange' : ρ'.range = w'.toValuationSubring.toSubring := M'.range_stalk_eq ⟨πM.base x₀,
    hx'val ▸ x'.2⟩
  have hmemO : ∀ s : S, ρ s ∈ w.toValuationSubring := fun s => by
    rw [← ValuationSubring.mem_toSubring, ← hrange]; exact ⟨s, rfl⟩
  have hmemO' : ∀ s : S', ρ' s ∈ w'.toValuationSubring := fun s => by
    rw [← ValuationSubring.mem_toSubring, ← hrange']; exact ⟨s, rfl⟩
  let ρO : S →+* ↥w.toValuationSubring := ρ.codRestrict w.toValuationSubring hmemO
  let ρO' : S' →+* ↥w'.toValuationSubring := ρ'.codRestrict w'.toValuationSubring hmemO'
  have hbij : Function.Bijective ρO := by
    refine ⟨fun a b h => hρinj (congrArg Subtype.val h), fun z => ?_⟩
    have hz : (z : L) ∈ ρ.range := by rw [hrange]; exact z.2
    obtain ⟨s, hs⟩ := hz
    exact ⟨s, Subtype.ext hs⟩
  have hbij' : Function.Bijective ρO' := by
    refine ⟨fun a b h => hρ'inj (congrArg Subtype.val h), fun z => ?_⟩
    have hz : (z : L') ∈ ρ'.range := by rw [hrange']; exact z.2
    obtain ⟨s, hs⟩ := hz
    exact ⟨s, Subtype.ext hs⟩
  let eS : S ≃+* ↥w.toValuationSubring := RingEquiv.ofBijective ρO hbij
  let eS' : S' ≃+* ↥w'.toValuationSubring := RingEquiv.ofBijective ρO' hbij'
  have : Smooth M.toBase := SmoothOfRelativeDimension.smooth 1 _
  have : Smooth M'.toBase := SmoothOfRelativeDimension.smooth 1 _
  have : LocallyOfFiniteType πM := by
    have : LocallyOfFiniteType (πM ≫ M'.toBase) := by rw [hπM]; infer_instance
    exact locallyOfFiniteType_of_comp πM M'.toBase
  have hFUst : (πM.stalkMap x₀).hom.FormallyUnramified := by
    have := hV
    have h1 := FormallyUnramified.stalkMap (V.ι ≫ πM) ⟨x₀, hyV⟩
    erw [Scheme.Hom.stalkMap_comp] at h1
    have : IsIso (V.ι.stalkMap (show V.toScheme from ⟨x₀, hyV⟩)) := inferInstance
    exact (RingHom.FormallyUnramified.respectsIso.cancel_right_isIso (πM.stalkMap (V.ι.base ⟨x₀,
      hyV⟩))
      (V.ι.stalkMap ⟨x₀, hyV⟩)).mp h1
  let alg : Algebra S' S := (πM.stalkMap x₀).hom.toAlgebra
  have : IsLocalHom (algebraMap S' S) := inferInstanceAs (IsLocalHom (πM.stalkMap x₀).hom)
  have : Algebra.EssFiniteType S' S := LocallyOfFiniteType.stalkMap πM x₀
  have : Algebra.FormallyUnramified S' S := hFUst
  exact Place.ramificationIndexAlong_eq_one_of_local_map
    φ hφ w' w eS' eS hcompat

end
end AlgebraicCurve
end ProofImplementation
