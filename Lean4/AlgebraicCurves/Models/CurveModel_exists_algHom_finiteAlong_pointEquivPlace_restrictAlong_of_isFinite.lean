/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_CurveModel_exists_algHom_finiteAlong_pointEquivPlace_restrictAlong_of_isFinite.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import AlgebraicCurves.Models.Basic
import AlgebraicCurves.Divisors.Correspondences
import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-!
# Curve Model exists alg Hom finite Along point Equiv Place restrict Along of is Finite
-/

section ProofImplementation

namespace AlgebraicCurves.Models.Proofs
namespace CurveModel_exists_algHom_finiteAlong_pointEquivPlace_restrictAlong_of_isFinite

universe u

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry
open _root_.AlgebraicCurve
open _root_.TopologicalSpace
open scoped nonZeroDivisors

noncomputable section

namespace AlgebraicCurve
open _root_.AlgebraicCurve
namespace FFLeg
open _root_.AlgebraicCurve

namespace FunctionFieldPull

variable {X Y Z : Scheme.{u}}

/-- Pull a function-field element back through the specialization of generic points. -/
def pull [IrreducibleSpace X] [IrreducibleSpace Y] (f : X ⟶ Y)
    (h : f.base (genericPoint X) ⤳ genericPoint Y) : Y.functionField ⟶ X.functionField :=
  Y.presheaf.stalkSpecializes h ≫ f.stalkMap (genericPoint X)

section

variable [IrreducibleSpace X] [IrreducibleSpace Y] [IrreducibleSpace Z]

theorem pull_germ (f : X ⟶ Y) (h : f.base (genericPoint X) ⤳ genericPoint Y)
    (U : Y.Opens) (hU : genericPoint Y ∈ U) (s : Γ(Y, U)) :
    pull f h (Y.presheaf.germ U (genericPoint Y) hU s) =
      X.presheaf.germ (f ⁻¹ᵁ U) (genericPoint X) (h.mem_open U.isOpen hU) (f.app U s) := by
  simp only [pull, CommRingCat.comp_apply]
  rw [TopCat.Presheaf.germ_stalkSpecializes_apply, Scheme.Hom.germ_stalkMap_apply]

theorem pull_algebraMap (f : X ⟶ Y) (h : f.base (genericPoint X) ⤳ genericPoint Y) (x : X)
    (a : Y.presheaf.stalk (f.base x)) :
    pull f h (algebraMap (Y.presheaf.stalk (f.base x)) Y.functionField a) =
      algebraMap (X.presheaf.stalk x) X.functionField (f.stalkMap x a) := by
  simp only [pull, RingHom.algebraMap_toAlgebra, CommRingCat.comp_apply]
  rw [TopCat.Presheaf.stalkSpecializes_comp_apply (Y.presheaf)]
  have := Scheme.Hom.stalkSpecializes_stalkMap_apply f (genericPoint X) x
    ((genericPoint_spec X).specializes trivial) a
  convert this using 2

theorem pull_id : pull (𝟙 X) (specializes_refl _) = 𝟙 _ := by
  simp [pull]

theorem pull_comp (f : X ⟶ Y) (g : Y ⟶ Z) (hf : f.base (genericPoint X) ⤳ genericPoint Y)
    (hg : g.base (genericPoint Y) ⤳ genericPoint Z) :
    pull (f ≫ g) ((g.base.hom.map_specializes hf).trans hg) = pull g hg ≫ pull f hf := by
  simp only [pull, Scheme.Hom.stalkMap_comp, Category.assoc]
  rw [← Scheme.Hom.stalkSpecializes_stalkMap_assoc g (f.base (genericPoint X)) (genericPoint Y) hf]
  rw [← Category.assoc, TopCat.Presheaf.stalkSpecializes_comp]
  rfl

end

variable [IsIntegral X] [IsIntegral Y]

theorem specializes_of_iso (e : X ≅ Y) : e.hom.base (genericPoint X) ⤳ genericPoint Y :=
  (genericPoint_eq_of_isOpenImmersion e.hom).symm ▸ specializes_refl _

theorem specializes_of_iso_inv (e : X ≅ Y) : e.inv.base (genericPoint Y) ⤳ genericPoint X :=
  specializes_of_iso e.symm

/-- The function-field equivalence induced by an isomorphism of integral schemes. -/
def equivOfIso (e : X ≅ Y) : Y.functionField ≃+* X.functionField :=
  (({ hom := pull e.hom (specializes_of_iso e)
      inv := pull e.inv (specializes_of_iso_inv e)
      hom_inv_id := by
        have h := (pull_comp e.inv e.hom (specializes_of_iso_inv e) (specializes_of_iso e)).symm
        rw [h]
        have : ∀ (k : (e.inv ≫ e.hom).base (genericPoint Y) ⤳ genericPoint Y),
            pull (e.inv ≫ e.hom) k = 𝟙 _ := by
          rw [e.inv_hom_id]; intro k; exact pull_id
        exact this _
      inv_hom_id := by
        have h := (pull_comp e.hom e.inv (specializes_of_iso e) (specializes_of_iso_inv e)).symm
        rw [h]
        have : ∀ (k : (e.hom ≫ e.inv).base (genericPoint X) ⤳ genericPoint X),
            pull (e.hom ≫ e.inv) k = 𝟙 _ := by
          rw [e.hom_inv_id]; intro k; exact pull_id
        exact this _ } : Y.functionField ≅ X.functionField)).commRingCatIsoToRingEquiv

theorem equivOfIso_apply (e : X ≅ Y) (a : Y.functionField) :
    equivOfIso e a = pull e.hom (specializes_of_iso e) a := rfl

theorem equivOfIso_symm_apply (e : X ≅ Y) (a : X.functionField) :
    (equivOfIso e).symm a = pull e.inv (specializes_of_iso_inv e) a := rfl

theorem map_equivOfIso_range_stalk (e : X ≅ Y) (x : X) :
    (algebraMap (Y.presheaf.stalk (e.hom.base x)) Y.functionField).range.map
        (equivOfIso e).toRingHom =
      (algebraMap (X.presheaf.stalk x) X.functionField).range := by
  have : IsIso (e.hom.stalkMap x) := inferInstance
  ext b
  simp only [Subring.mem_map, RingHom.mem_range, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe]
  constructor
  · rintro ⟨_, ⟨a, rfl⟩, rfl⟩
    exact ⟨e.hom.stalkMap x a, (pull_algebraMap e.hom (specializes_of_iso e) x a).symm⟩
  · rintro ⟨a, rfl⟩
    obtain ⟨a', rfl⟩ : ∃ a', e.hom.stalkMap x a' = a :=
      ⟨inv (e.hom.stalkMap x) a, by
        rw [← CommRingCat.comp_apply, IsIso.inv_hom_id]; rfl⟩
    exact ⟨_, ⟨a', rfl⟩, pull_algebraMap e.hom (specializes_of_iso e) x a'⟩

theorem image_equivOfIso_range_stalk (e : X ≅ Y) (x : X) :
    (equivOfIso e) ''
        ((algebraMap (Y.presheaf.stalk (e.hom.base x)) Y.functionField).range : Set _) =
      ((algebraMap (X.presheaf.stalk x) X.functionField).range : Set _) := by
  have h := congrArg (fun S : Subring X.functionField => (S : Set X.functionField))
    (map_equivOfIso_range_stalk e x)
  simpa [Subring.coe_map] using h

theorem image_equivOfIso_symm_range_stalk (e : X ≅ Y) (x : X) :
    (equivOfIso e).symm '' ((algebraMap (X.presheaf.stalk x) X.functionField).range : Set _) =
      ((algebraMap (Y.presheaf.stalk (e.hom.base x)) Y.functionField).range : Set _) := by
  rw [← image_equivOfIso_range_stalk e x, ← Set.image_comp]
  simp

theorem pull_baseToFunctionField {K : Type u} [Field K] (f : X ⟶ Y)
    (h : f.base (genericPoint X) ⤳ genericPoint Y)
    (cX : X ⟶ Spec (CommRingCat.of K)) (cY : Y ⟶ Spec (CommRingCat.of K)) (hf : f ≫ cY = cX)
    (a : K) :
    pull f h (baseToFunctionField cY a) = baseToFunctionField cX a := by
  subst hf
  simp only [baseToFunctionField, RingHom.coe_comp, Function.comp_apply]
  change pull f h (Y.presheaf.germ ⊤ (genericPoint Y) trivial _) =
    X.presheaf.germ ⊤ (genericPoint X) trivial _
  erw [pull_germ]
  rfl

theorem equivOfIso_baseToFunctionField {K : Type u} [Field K] (e : X ≅ Y)
    (cX : X ⟶ Spec (CommRingCat.of K)) (cY : Y ⟶ Spec (CommRingCat.of K))
    (hf : e.hom ≫ cY = cX) (a : K) :
    equivOfIso e (baseToFunctionField cY a) = baseToFunctionField cX a :=
  pull_baseToFunctionField e.hom _ cX cY hf a

end FunctionFieldPull

theorem finite_of_isFractionRing_of_finite {A B K L : Type*} [CommRing A] [IsDomain A] [CommRing B]
  [IsDomain B]
    [Field K] [Field L] [Algebra A K] [IsFractionRing A K] [Algebra B L] [IsFractionRing B L]
    (f : A →+* B) (hf : Function.Injective f) (hfin : f.Finite)
    (g : K →+* L) (hg : ∀ a, g (algebraMap A K a) = algebraMap B L (f a)) :
    letI := g.toAlgebra; Module.Finite K L := by
  let algAB : Algebra A B := f.toAlgebra
  let algKL : Algebra K L := g.toAlgebra
  let algAL : Algebra A L := ((algebraMap B L).comp f).toAlgebra
  have : IsScalarTower A B L := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have : IsScalarTower A K L := IsScalarTower.of_algebraMap_eq (fun a => (hg a).symm)
  have : Module.Finite A B := hfin
  have : FaithfulSMul A B := (faithfulSMul_iff_algebraMap_injective A B).mpr hf
  have : Algebra.IsIntegral A B := Algebra.IsIntegral.of_finite A B
  have : Algebra.IsAlgebraic A B := Algebra.IsIntegral.isAlgebraic
  exact Module.Finite.of_isLocalization A B (Rₚ := K) (Sₚ := L) A⁰

theorem isIntegral_of_isFractionRing_of_finite {A B K L : Type*} [CommRing A] [IsDomain A]
  [CommRing B] [IsDomain B]
    [Field K] [Field L] [Algebra A K] [IsFractionRing A K] [Algebra B L] [IsFractionRing B L]
    (f : A →+* B) (hf : Function.Injective f) (hfin : f.Finite)
    (g : K →+* L) (hg : ∀ a, g (algebraMap A K a) = algebraMap B L (f a)) :
    g.IsIntegral := by
  let algKL : Algebra K L := g.toAlgebra
  have : Module.Finite K L := finite_of_isFractionRing_of_finite f hf hfin g hg
  have : Algebra.IsIntegral K L := Algebra.IsIntegral.of_finite K L
  intro x
  exact this.isIntegral x

private theorem _root_.ValuationSubring.ofPrime_eq_top_or_eq_self {F : Type*} [Field F] (A :
  ValuationSubring F)
    [IsPrincipalIdealRing ↥A] (P : Ideal ↥A) [hP : P.IsPrime] :
    A.ofPrime P = ⊤ ∨ A.ofPrime P = A := by
  by_cases hbot : P = ⊥
  · left; subst hbot; exact ValuationSubring.ofPrime_bot A
  · right
    have hmax : P.IsMaximal := IsPrime.to_maximal_ideal hbot
    have hPm : P = IsLocalRing.maximalIdeal ↥A := IsLocalRing.eq_maximalIdeal hmax
    revert hP
    rw [hPm]
    intro hP
    exact ValuationSubring.ofPrime_top A
alias ValuationSubring.ofPrime_eq_top_or_eq_self :=
  _root_.ValuationSubring.ofPrime_eq_top_or_eq_self

private theorem _root_.AlgebraicCurve.Place.eq_of_le_of_ne_top {K F : Type*} [Field K] [Field F]
  [Algebra K F]
    (v : Place K F) (S : ValuationSubring F) (h : v.toValuationSubring ≤ S) (hS : S ≠ ⊤) :
    v.toValuationSubring = S := by
  rcases ValuationSubring.ofPrime_eq_top_or_eq_self v.toValuationSubring
      (ValuationSubring.idealOfLE v.toValuationSubring S h) with h1 | h1
  · rw [ValuationSubring.ofPrime_idealOfLE] at h1; exact absurd h1 hS
  · rw [ValuationSubring.ofPrime_idealOfLE] at h1; exact h1.symm
alias place_eq_of_le_of_ne_top := _root_.AlgebraicCurve.Place.eq_of_le_of_ne_top
open FunctionFieldPull

section Leg

variable (k : Type) [Field k] [IsAlgClosed k]
  {L L' : Type} [Field L] [Field L'] [Algebra k L] [Algebra k L']
  (M : CurveModel k L) (M' : CurveModel k L')
  (d : M'.C ⟶ M.C) (hd : d ≫ M.toBase = M'.toBase)

omit [IsAlgClosed k] in
theorem specializes_genericPoint (hsurj : Function.Surjective d.base) :
    d.base (genericPoint M'.C) ⤳ genericPoint M.C := by
  rw [specializes_iff_mem_closure]
  have h1 : d.base '' closure {genericPoint M'.C} ⊆ closure (d.base '' {genericPoint M'.C}) :=
    image_closure_subset_closure_image d.base.hom.continuous
  rw [(genericPoint_spec M'.C).def, Set.image_singleton] at h1
  have h2 : d.base '' (Set.univ : Set M'.C) = Set.univ := by
    rw [Set.image_univ, hsurj.range_eq]
  rw [h2] at h1
  exact h1 (Set.mem_univ _)

/-- The base-field algebra homomorphism induced by a surjective morphism of curve models. -/
def phi (hsurj : Function.Surjective d.base) : L →ₐ[k] L' :=
  { toRingHom := M'.ffEquiv.symm.toRingHom.comp
      ((pull d (specializes_genericPoint k M M' d hsurj)).hom.comp M.ffEquiv.toRingHom)
    commutes' := fun a => by
      change M'.ffEquiv.symm (pull d (specializes_genericPoint k M M' d hsurj) (M.ffEquiv
        (algebraMap k L a))) = algebraMap k L' a
      rw [M.ffEquiv_algebraMap, pull_baseToFunctionField d _ M'.toBase M.toBase hd,
        RingEquiv.symm_apply_eq,
        M'.ffEquiv_algebraMap] }
omit [IsAlgClosed k] in
theorem phi_apply (hsurj : Function.Surjective d.base) (x : L) :
    phi k M M' d hd hsurj x = M'.ffEquiv.symm (pull d (specializes_genericPoint k M M' d hsurj)
      (M.ffEquiv x)) := rfl
omit [IsAlgClosed k] in
theorem phi_germ (hsurj : Function.Surjective d.base)
    (U : M.C.Opens) [Nonempty (Scheme.Opens.toScheme U)] [Nonempty (Scheme.Opens.toScheme (d ⁻¹ᵁ
      U))] (t : Γ(M.C, U)) :
    phi k M M' d hd hsurj (M.ffEquiv.symm (M.C.germToFunctionField U t)) =
      M'.ffEquiv.symm (M'.C.germToFunctionField (d ⁻¹ᵁ U) ((d.app U).hom t)) := by
  rw [phi_apply, RingEquiv.apply_symm_apply]
  congr 1
  exact pull_germ d (specializes_genericPoint k M M' d hsurj) U _ t
omit [IsAlgClosed k] in
theorem finiteAlong_phi [IsFinite d] (hsurj : Function.Surjective d.base) : FiniteAlong k (phi k M
  M' d hd hsurj) := by
  classical
  obtain ⟨U, hUaff, hUη⟩ := M.finset_subset_affineOpen {genericPoint M.C}
  have hηU : genericPoint M.C ∈ U := hUη _ (Finset.mem_singleton_self _)
  have hU : Nonempty (Scheme.Opens.toScheme U) := ⟨⟨genericPoint M.C, hηU⟩⟩
  have hη'U : genericPoint M'.C ∈ d ⁻¹ᵁ U := (specializes_genericPoint k M M' d hsurj).mem_open
    U.isOpen hηU
  have hU' : Nonempty (Scheme.Opens.toScheme (d ⁻¹ᵁ U)) := ⟨⟨genericPoint M'.C, hη'U⟩⟩
  have hUaff' : IsAffineOpen (d ⁻¹ᵁ U) := hUaff.preimage d
  have : IsFractionRing Γ(M.C, U) M.C.functionField := functionField_isFractionRing_of_isAffineOpen
    M.C U hUaff
  have : IsFractionRing Γ(M'.C, d ⁻¹ᵁ U) M'.C.functionField :=
    functionField_isFractionRing_of_isAffineOpen M'.C (d ⁻¹ᵁ U) hUaff'
  set g : M.C.functionField →+* M'.C.functionField := (pull d (specializes_genericPoint k M M' d
    hsurj)).hom with hg
  have hsq : ∀ a : Γ(M.C, U), g (algebraMap Γ(M.C, U) M.C.functionField a) =
      algebraMap Γ(M'.C, d ⁻¹ᵁ U) M'.C.functionField ((d.app U).hom a) := by
    intro a
    change pull d (specializes_genericPoint k M M' d hsurj) (M.C.germToFunctionField U a) =
      M'.C.germToFunctionField (d ⁻¹ᵁ U) ((d.app U).hom a)
    exact pull_germ d (specializes_genericPoint k M M' d hsurj) U _ a
  have hinj : Function.Injective (d.app U).hom := by
    intro a b hab
    have := congrArg (algebraMap Γ(M'.C, d ⁻¹ᵁ U) M'.C.functionField) hab
    rw [← hsq, ← hsq] at this
    exact IsFractionRing.injective Γ(M.C, U) M.C.functionField (g.injective this)
  have hfinKL := finite_of_isFractionRing_of_finite (d.app U).hom hinj (IsFinite.finite_app d U
    hUaff) g hsq
  let : Algebra M.C.functionField M'.C.functionField := g.toAlgebra
  let := algebraAlong (phi k M M' d hd hsurj)
  have : Module.Finite M.C.functionField M'.C.functionField := hfinKL
  exact Module.Finite.of_equiv_equiv M.ffEquiv.symm M'.ffEquiv.symm (by
    ext x
    change phi k M M' d hd hsurj (M.ffEquiv.symm x) = M'.ffEquiv.symm (g x)
    rw [phi_apply, RingEquiv.apply_symm_apply])
omit [IsAlgClosed k] in
theorem isIntegral_phi [IsFinite d] (hsurj : Function.Surjective d.base) : (phi k M M' d hd
  hsurj).toRingHom.IsIntegral := by
  let := algebraAlong (phi k M M' d hd hsurj)
  have : Module.Finite L L' := finiteAlong_phi k M M' d hd hsurj
  exact fun x => Algebra.IsIntegral.isIntegral x

theorem point_compat [IsFinite d] (hsurj : Function.Surjective d.base) (R : Place k L') :
    (M.pointEquivPlace.symm (R.restrictAlong (phi k M M' d hd hsurj) (isIntegral_phi k M M' d hd
      hsurj))).1 =
      (M'.pointEquivPlace.symm R).1 ≫ d := by
  classical
  set φ := phi k M M' d hd hsurj with hφ
  set hint := isIntegral_phi k M M' d hd hsurj
  set x' : closedPoints M'.C := M'.placeEquiv.symm R with hx'
  have hRx' : M'.placeOfPoint x' = R :=
    by rw [hx', ← CurveModel.placeEquiv_apply, Equiv.apply_symm_apply]
  have hxcl : IsClosed ({d.base x'.1} : Set M.C) := by
    rw [← Set.image_singleton]
    exact d.isClosedMap _ x'.2
  set x : closedPoints M.C := ⟨d.base x'.1, hxcl⟩ with hx
  have hle : (M.placeOfPoint x).toValuationSubring ≤ (R.restrictAlong φ hint).toValuationSubring :=
    by
    intro a ha
    have ha' : a ∈ (M.placeOfPoint x).toValuationSubring.toSubring := ha
    rw [← M.range_stalk_eq x] at ha'
    obtain ⟨s, rfl⟩ := RingHom.mem_range.mp ha'
    change (phi k M M' d hd hsurj) _ ∈ R.toValuationSubring
    rw [phi_apply]
    simp only [RingHom.coe_comp, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, Function.comp_apply,
      RingEquiv.apply_symm_apply]
    rw [pull_algebraMap d (specializes_genericPoint k M M' d hsurj) x'.1 s, ← hRx']
    have : M'.ffEquiv.symm (algebraMap (M'.C.presheaf.stalk x'.1) M'.C.functionField (d.stalkMap
      x'.1 s)) ∈
        (M'.placeOfPoint x').toValuationSubring.toSubring := by
      rw [← M'.range_stalk_eq x']
      exact ⟨_, rfl⟩
    exact this
  have heq : M.placeOfPoint x = R.restrictAlong φ hint :=
    Place.ext (place_eq_of_le_of_ne_top _ _ hle (R.restrictAlong φ hint).ne_top')
  apply ext_of_apply_closedPoint_eq M.toBase (M.pointEquivPlace.symm _).2
  · rw [Category.assoc, hd]; exact (M'.pointEquivPlace.symm R).2
  · have h1 : (M.pointEquivPlace.symm (R.restrictAlong φ hint)) = (pointEquivClosedPoint
      M.toBase).symm x := by
      change ((pointEquivClosedPoint M.toBase).trans M.placeEquiv).symm _ = _
      rw [Equiv.symm_trans_apply]
      congr 1
      rw [Equiv.symm_apply_eq, CurveModel.placeEquiv_apply]
      exact heq.symm
    have h2 : (M'.pointEquivPlace.symm R) = (pointEquivClosedPoint M'.toBase).symm x' := by
      change ((pointEquivClosedPoint M'.toBase).trans M'.placeEquiv).symm _ = _
      rw [Equiv.symm_trans_apply]
    rw [h1, h2]
    have e1 : (pointOfClosedPoint M.toBase x.1 x.2).base (IsLocalRing.closedPoint k) = x.1 :=
      pointOfClosedPoint_apply _ _ _ _
    have e2 : (pointOfClosedPoint M'.toBase x'.1 x'.2).base (IsLocalRing.closedPoint k) = x'.1 :=
      pointOfClosedPoint_apply _ _ _ _
    change (pointOfClosedPoint M.toBase x.1 x.2).base (IsLocalRing.closedPoint k) =
      d.base ((pointOfClosedPoint M'.toBase x'.1 x'.2).base (IsLocalRing.closedPoint k))
    rw [e1, e2]

end Leg

end AlgebraicCurve.FFLeg

open AlgebraicCurve.FFLeg

end
end CurveModel_exists_algHom_finiteAlong_pointEquivPlace_restrictAlong_of_isFinite
end AlgebraicCurves.Models.Proofs

namespace AlgebraicCurve

noncomputable section

universe u

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.AlgebraicCurve _root_.TopologicalSpace
open scoped nonZeroDivisors

open _root_.AlgebraicCurves.Models.Proofs in
open CurveModel_exists_algHom_finiteAlong_pointEquivPlace_restrictAlong_of_isFinite in
open AlgebraicCurve.FFLeg in
theorem CurveModel.exists_algHom_finiteAlong_pointEquivPlace_restrictAlong_of_isFinite
    (k : Type) [Field k] [IsAlgClosed k]
    {L L' : Type} [Field L] [Field L'] [Algebra k L] [Algebra k L']
    (M : CurveModel k L) (M' : CurveModel k L')
    (d : M'.C ⟶ M.C) (hd : d ≫ M.toBase = M'.toBase) [IsFinite d] (hsurj : Function.Surjective
      d.base) :
    ∃ (φ : L →ₐ[k] L') (_hfin : FiniteAlong k φ) (hint : φ.toRingHom.IsIntegral),
      (∀ (U : M.C.Opens) [Nonempty (Scheme.Opens.toScheme U)] [Nonempty (Scheme.Opens.toScheme (d
        ⁻¹ᵁ U))]
        (t : Γ(M.C, U)),
        φ (M.ffEquiv.symm (M.C.germToFunctionField U t)) =
          M'.ffEquiv.symm (M'.C.germToFunctionField (d ⁻¹ᵁ U) ((d.app U).hom t))) ∧
      ∀ R : Place k L',
        (M.pointEquivPlace.symm (R.restrictAlong φ hint)).1 = (M'.pointEquivPlace.symm R).1 ≫ d :=
          by
  exact ⟨phi k M M' d hd hsurj, finiteAlong_phi k M M' d hd hsurj, isIntegral_phi k M M' d hd hsurj,
    fun U _ _ t => phi_germ k M M' d hd hsurj U t, fun R => point_compat k M M' d hd hsurj R⟩
end
end AlgebraicCurve
end ProofImplementation
