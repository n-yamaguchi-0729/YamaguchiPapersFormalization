/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AlgebraicCurves.Models.CurveModel_exists_algHom_finiteAlong_pointEquivPlace_restrictAlong_of_isFinite
import Nyll.AlgebraicCurves.Models.CurveModel_ker_comap_eq_prod_ker_pow_ramificationIndex
import Nyll.AlgebraicCurves.Geometry.Schemes.SmoothOfRelativeDimension_isDiscreteValuationRing_stalk_of_isClosed
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.RingTheory.Unramified.LocalRing

/-!
# Ramification of actual curve covers

A finite surjective morphism of smooth proper curve models supplies its own function-field
homomorphism and place correspondence. At a point where its actual stalk map is formally
unramified, the associated place has ramification index one. The comparison follows from the
image of the maximal ideal and the discrete valuation of the target stalk.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicCurve IsLocalRing

namespace AnabelianGeometry.GeometricFundamentalGroup

open AlgebraicCurves.Models.Proofs.CurveModel_ker_comap_eq_prod_ker_pow_ramificationIndex in
/-- A finite flat cover supplies a function-field map whose ramification index is one
where the actual scheme stalk map is formally unramified. -/
theorem exists_functionFieldMap_ramification_eq_one_at_unramified_stalk
    {K F E : Type} [Field K] [IsAlgClosed K] [Field F] [Field E]
    [Algebra K F] [Algebra K E] [IsCurveOver K F] [IsCurveOver K E]
    [Algebra.EssFiniteType K F] [Algebra.EssFiniteType K E]
    (M : CurveModel K F) (N : CurveModel K E)
    (π : N.C ⟶ M.C) (hπ : π ≫ M.toBase = N.toBase)
    [IsFinite π] [Flat π] [LocallyOfFinitePresentation π]
    (hsurj : Function.Surjective π.base) :
    ∃ φ : F →ₐ[K] E, FiniteAlong K φ ∧ ∃ hint : φ.toRingHom.IsIntegral,
      (∀ w : Place K E,
        (M.pointEquivPlace.symm (w.restrictAlong φ hint)).1 =
          (N.pointEquivPlace.symm w).1 ≫ π) ∧
      ∀ w : Place K E,
        RingHom.FormallyUnramified
          (π.stalkMap (pointEquivClosedPoint N.toBase (N.pointEquivPlace.symm w)).1).hom →
          w.ramificationIndexAlong φ = 1 := by
  obtain ⟨φ, hfin, hint, -, hpoints⟩ :=
    CurveModel.exists_algHom_finiteAlong_pointEquivPlace_restrictAlong_of_isFinite
      K M N π hπ hsurj
  refine ⟨φ, hfin, hint, hpoints, ?_⟩
  let fieldAlgebra : Algebra F E := algebraAlong φ
  have fieldTower : IsScalarTower K F E := isScalarTower_along φ
  have fieldIntegral : Algebra.IsIntegral F E := isIntegral_along φ hint
  have hplace : ∀ (y : {q : Spec (CommRingCat.of K) ⟶ N.C // q ≫ N.toBase = 𝟙 _})
      (x : {q : Spec (CommRingCat.of K) ⟶ M.C // q ≫ M.toBase = 𝟙 _}),
      y.1 ≫ π = x.1 → (N.pointEquivPlace y).restrict F = M.pointEquivPlace x := by
    intro y x hxy
    have hc := hpoints (N.pointEquivPlace y)
    rw [Equiv.symm_apply_apply] at hc
    have hx : M.pointEquivPlace.symm
        ((N.pointEquivPlace y).restrictAlong φ hint) = x := Subtype.ext (hc.trans hxy)
    change (N.pointEquivPlace y).restrictAlong φ hint = M.pointEquivPlace x
    exact (M.pointEquivPlace.symm_apply_eq).mp hx
  intro w hu
  let y := N.pointEquivPlace.symm w
  let p := pointEquivClosedPoint N.toBase y
  let stalkAlgebra : Algebra (M.C.presheaf.stalk (π.base p.1)) (N.C.presheaf.stalk p.1) :=
    (π.stalkMap p.1).hom.toAlgebra
  have stalkFiniteType : Algebra.EssFiniteType (M.C.presheaf.stalk (π.base p.1))
      (N.C.presheaf.stalk p.1) := LocallyOfFiniteType.stalkMap π p.1
  have stalkUnramified : Algebra.FormallyUnramified (M.C.presheaf.stalk (π.base p.1))
      (N.C.presheaf.stalk p.1) := hu
  have stalkLocal : IsLocalHom
      (algebraMap (M.C.presheaf.stalk (π.base p.1)) (N.C.presheaf.stalk p.1)) :=
    show IsLocalHom (π.stalkMap p.1).hom from inferInstance
  have hmap := Algebra.FormallyUnramified.map_maximalIdeal
    (R := M.C.presheaf.stalk (π.base p.1)) (S := N.C.presheaf.stalk p.1)
  have he := HG1b.map_stalkMap_maximalIdeal_eq_pow M N π hπ hplace y
  have hdvr : IsDiscreteValuationRing (N.C.presheaf.stalk p.1) :=
    SmoothOfRelativeDimension.isDiscreteValuationRing_stalk_of_isClosed N.toBase p.1 p.2
  have hp : maximalIdeal (N.C.presheaf.stalk p.1) ^ w.ramificationIndex F =
      maximalIdeal (N.C.presheaf.stalk p.1) ^ 1 := by
    rw [pow_one]
    change (maximalIdeal (M.C.presheaf.stalk (π.base p.1))).map (π.stalkMap p.1).hom =
      maximalIdeal (N.C.presheaf.stalk p.1) ^
        (N.pointEquivPlace (N.pointEquivPlace.symm w)).ramificationIndex F at he
    rw [Equiv.apply_symm_apply] at he
    exact he.symm.trans hmap
  have hheight := congrArg Order.coheight hp
  rw [IsDiscreteValuationRing.coheight_pow_maximalIdeal,
    IsDiscreteValuationRing.coheight_pow_maximalIdeal] at hheight
  exact ENat.natCast_inj.mp hheight

/-- Every place in the function-field extension of an actual finite etale cover of
smooth proper curve models is unramified. -/
theorem exists_functionFieldMap_unramified_of_finite_etale
    {K F E : Type} [Field K] [IsAlgClosed K] [Field F] [Field E]
    [Algebra K F] [Algebra K E] [IsCurveOver K F] [IsCurveOver K E]
    [Algebra.EssFiniteType K F] [Algebra.EssFiniteType K E]
    (M : CurveModel K F) (N : CurveModel K E)
    (π : N.C ⟶ M.C) (hπ : π ≫ M.toBase = N.toBase)
    [IsFinite π] [Etale π] (hsurj : Function.Surjective π.base) :
    ∃ φ : F →ₐ[K] E, FiniteAlong K φ ∧ ∃ hint : φ.toRingHom.IsIntegral,
      (∀ w : Place K E,
        (M.pointEquivPlace.symm (w.restrictAlong φ hint)).1 =
          (N.pointEquivPlace.symm w).1 ≫ π) ∧
      ∀ w : Place K E, w.ramificationIndexAlong φ = 1 := by
  obtain ⟨φ, hfin, hint, hpoints, hunram⟩ :=
    exists_functionFieldMap_ramification_eq_one_at_unramified_stalk M N π hπ hsurj
  exact ⟨φ, hfin, hint, hpoints, fun w =>
    hunram w (FormallyUnramified.stalkMap π _)⟩

end AnabelianGeometry.GeometricFundamentalGroup
