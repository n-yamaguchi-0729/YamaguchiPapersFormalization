/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import AlgebraicCurves.Places.LocalUnramifiedRamification
import AlgebraicCurves.Places.Exists_place_range_stalk_eq
import AlgebraicCurves.Models.FunctionFieldScalarFunctoriality
import Mathlib.AlgebraicGeometry.Morphisms.Etale

/-!
# Interior valuation divisibility from an actual étale curve morphism

The source need not be proper. Its closed-point local ring supplies its
actual place, and the actual stalk map is formally unramified. The local
ramification theorem therefore applies to a root in its actual function field.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace AlgebraicCurve

universe u

private def stalkPlaceRingEquiv
    {K : Type u} [Field K] {X : Scheme.{u}} [IsIntegral X]
    [Algebra K X.functionField] (x : X) (v : Place K X.functionField)
    (hv : (algebraMap (X.presheaf.stalk x) X.functionField).range =
      v.toValuationSubring.toSubring) :
    X.presheaf.stalk x ≃+* ↥v.toValuationSubring :=
  RingEquiv.ofBijective
    ((algebraMap (X.presheaf.stalk x) X.functionField).codRestrict
      v.toValuationSubring (fun a => by
        change algebraMap (X.presheaf.stalk x) X.functionField a ∈
          v.toValuationSubring.toSubring
        rw [← hv]
        exact ⟨a, rfl⟩))
    ⟨fun a b hab => IsFractionRing.injective (X.presheaf.stalk x) X.functionField
        (congrArg Subtype.val hab),
      fun z => by
        have hz : (z : X.functionField) ∈
            (algebraMap (X.presheaf.stalk x) X.functionField).range := by
          rw [hv]
          exact z.property
        obtain ⟨a, ha⟩ := hz
        exact ⟨a, Subtype.ext ha⟩⟩

/-- A root in the actual function field of an étale curve has integral
valuation; unramifiedness forces divisibility of the order downstairs. -/
theorem ord_dvd_of_etale_functionField_root_at_closedPoint
    {K : Type u} [Field K]
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (c : X ⟶ Spec (.of K)) [SmoothOfRelativeDimension 1 c]
    (f : Y ⟶ X) [Etale f] (hf : DenseRange f)
    (y : Y) (hy : IsClosed ({y} : Set Y))
    (a : X.functionField) (b : Y.functionField) (n : ℕ)
    (hb : b ^ n = f.functionFieldMap hf a) :
    let : Algebra K X.functionField := (baseToFunctionField c).toAlgebra
    ∀ v : Place K X.functionField,
      (algebraMap (X.presheaf.stalk (f y)) X.functionField).range =
        v.toValuationSubring.toSubring → (n : ℤ) ∣ v.ord a := by
  intro algX v hv
  let : Algebra K Y.functionField := (baseToFunctionField (f ≫ c)).toAlgebra
  have : SmoothOfRelativeDimension 1 (f ≫ c) :=
    smoothOfRelativeDimension_comp 0 1 f c
  obtain ⟨w, hw⟩ := exists_place_range_stalk_eq (f ≫ c) y hy
  let φ : X.functionField →ₐ[K] Y.functionField :=
    Scheme.Hom.functionFieldAlgHomOver c f hf
  have hφ : φ.toRingHom.IsIntegral := by
    let : Algebra X.functionField Y.functionField := φ.toRingHom.toAlgebra
    have hess : (f.functionFieldMap hf).EssFiniteType := by
      unfold Scheme.Hom.functionFieldMap
      rw [CommRingCat.hom_comp, RingHom.EssFiniteType.respectsIso.cancel_left_isIso]
      exact LocallyOfFiniteType.stalkMap f (genericPoint Y)
    have hunram : (f.functionFieldMap hf).FormallyUnramified := by
      unfold Scheme.Hom.functionFieldMap
      rw [CommRingCat.hom_comp, RingHom.FormallyUnramified.respectsIso.cancel_left_isIso]
      exact FormallyUnramified.stalkMap f (genericPoint Y)
    have : Algebra.EssFiniteType X.functionField Y.functionField := hess
    have : Algebra.FormallyUnramified X.functionField Y.functionField := hunram
    have : Module.Finite X.functionField Y.functionField :=
      Algebra.FormallyUnramified.finite_of_free X.functionField Y.functionField
    exact fun z => Algebra.IsIntegral.isIntegral z
  let A := X.presheaf.stalk (f y)
  let B := Y.presheaf.stalk y
  let eA : A ≃+* ↥v.toValuationSubring := stalkPlaceRingEquiv (f y) v hv
  let eB : B ≃+* ↥w.toValuationSubring := stalkPlaceRingEquiv y w hw
  let : Algebra A B := (f.stalkMap y).hom.toAlgebra
  have : IsLocalHom (algebraMap A B) :=
    inferInstanceAs (IsLocalHom (f.stalkMap y).hom)
  have : Algebra.EssFiniteType A B := LocallyOfFiniteType.stalkMap f y
  have : Algebra.FormallyUnramified A B := FormallyUnramified.stalkMap f y
  have hcompat : ∀ x : A, ((eB (algebraMap A B x) : ↥w.toValuationSubring) : Y.functionField) =
      φ ((eA x : ↥v.toValuationSubring) : X.functionField) :=
    fun x => (f.functionFieldMap_algebraMap_stalk hf y x).symm
  exact Place.ord_dvd_of_local_unramified_root φ hφ v w eA eB hcompat a b n hb

end AlgebraicCurve
