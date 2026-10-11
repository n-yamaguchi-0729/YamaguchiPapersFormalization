/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_exists_place_range_stalk_eq.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Divisors.ClassGroup
import Nyll.AlgebraicCurves.Models.Basic
import Nyll.AlgebraicCurves.Geometry.Schemes.SmoothOfRelativeDimension_isDiscreteValuationRing_stalk_of_isClosed

/-!
# Exists place range stalk eq

A closed-point local ring of a smooth integral curve determines a place with the same image in the
function field.
-/

section ProofImplementation

open _root_.CategoryTheory
open _root_.AlgebraicGeometry
open _root_.AlgebraicCurve

universe u

open scoped AlgebraicCurve

namespace AlgebraicCurve

theorem baseToFunctionField_apply_eq_algebraMap_stalk
    {K : Type u} [Field K] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of K)) [IsIntegral C]
    (x : C) (a : K) :
    baseToFunctionField c a =
      algebraMap (C.presheaf.stalk x) C.functionField
        ((C.presheaf.germ ⊤ x trivial).hom (c.appTop.hom ((Scheme.ΓSpecIso
          (CommRingCat.of K)).inv.hom a))) := by
  have key : ∀ s : Γ(C, ⊤), (C.presheaf.germ ⊤ (genericPoint C) trivial).hom s =
      algebraMap (C.presheaf.stalk x) C.functionField ((C.presheaf.germ ⊤ x trivial).hom s) := by
    intro s
    simp_rw [RingHom.algebraMap_toAlgebra]
    exact (TopCat.Presheaf.germ_stalkSpecializes_apply C.presheaf
      (U := ⊤) (y := x) (x := genericPoint C) trivial
      ((genericPoint_spec C).specializes trivial) s).symm
  simp only [baseToFunctionField, RingHom.coe_comp, Function.comp_apply]
  exact key _

end AlgebraicCurve

namespace AlgebraicCurves.Places.Proofs.Exists_place_range_stalk_eq

theorem _root_.AlgebraicCurve.exists_place_range_stalk_eq
    {K : Type u} [Field K] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of K))
    [IsIntegral C] [SmoothOfRelativeDimension 1 c]
    (x : C) (hx : IsClosed ({x} : Set C)) :
    let := (AlgebraicCurve.baseToFunctionField c).toAlgebra
    ∃ v : AlgebraicCurve.Place K C.functionField,
      (algebraMap (C.presheaf.stalk x) C.functionField).range = v.toValuationSubring.toSubring := by
  let hk := (baseToFunctionField c).toAlgebra
  have hdvr : IsDiscreteValuationRing (C.presheaf.stalk x) :=
    AlgebraicGeometry.SmoothOfRelativeDimension.isDiscreteValuationRing_stalk_of_isClosed c x hx
  set O := C.presheaf.stalk x with hO
  set F := C.functionField with hF
  let A : ValuationSubring F := (ValuationRing.valuation O F).valuationSubring
  have hA : (algebraMap O F).range = A.toSubring := by
    ext f
    change f ∈ (algebraMap O F).range ↔ f ∈ (ValuationRing.valuation O F).integer
    rw [ValuationRing.range_algebraMap_eq]
  have hmemA : ∀ f : F, f ∈ A ↔ ∃ a : O, algebraMap O F a = f := fun f =>
    ValuationRing.mem_integer_iff O F f
  have hinj : Function.Injective (algebraMap O F) := IsFractionRing.injective O F
  let e : O ≃+* A :=
    RingEquiv.ofBijective
      ((algebraMap O F).codRestrict A.toSubring fun a => by
        rw [← hA]; exact ⟨a, rfl⟩)
      ⟨fun a b hab => hinj (congrArg Subtype.val hab),
        fun ⟨f, hf⟩ => by
          obtain ⟨a, rfl⟩ := (hmemA f).mp hf
          exact ⟨a, rfl⟩⟩
  refine ⟨⟨A, ?_, ?_, ?_⟩, hA⟩
  · intro a
    rw [hmemA]
    exact ⟨_, (baseToFunctionField_apply_eq_algebraMap_stalk c x a).symm⟩
  · intro htop
    apply IsDiscreteValuationRing.not_isField O
    have hsurj : Function.Surjective (algebraMap O F) := by
      intro f
      have hf : f ∈ A := by rw [htop]; trivial
      exact (hmemA f).mp hf
    exact (RingEquiv.ofBijective (algebraMap O F) ⟨hinj, hsurj⟩).toMulEquiv.isField
      (Field.toIsField F)
  · exact IsPrincipalIdealRing.of_surjective e.toRingHom e.surjective
end AlgebraicCurves.Places.Proofs.Exists_place_range_stalk_eq
end ProofImplementation
