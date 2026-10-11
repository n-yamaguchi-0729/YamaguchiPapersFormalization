/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import AlgebraicCurves.Models.CurveModel_exists_algHom_finiteAlong_pointEquivPlace_restrictAlong_of_isFinite
import AlgebraicCurves.Models.CurveModel_ramificationIndexAlong_pointEquivPlace_eq_one_of_formallyUnramified
import AlgebraicCurves.Cohomology.RiemannRoch.Two_mul_genusFF_sub_two_eq_of_isSeparable_of_tame
import SchemeTheory.FiniteEtale.Geometry

/-! # Riemann--Hurwitz for an actual finite étale morphism of curve models

The function-field homomorphism is induced by the scheme morphism.
Unramifiedness at every place is proved from the actual étale morphism;
there is no ramification or genus formula assumption.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicCurve
open AlgebraicCurves.Models.Proofs
open CurveModel_exists_algHom_finiteAlong_pointEquivPlace_restrictAlong_of_isFinite.AlgebraicCurve

namespace AlgebraicCurve.CurveModel

variable {K F E : Type} [Field K] [IsAlgClosed K]
  [Field F] [Field E] [Algebra K F] [Algebra K E]
  (M : CurveModel K F) (N : CurveModel K E)
  (d : N.C ⟶ M.C) (hd : d ≫ M.toBase = N.toBase)
  [IsFinite d] [Etale d]

/-- The function-field map of an actual finite étale curve morphism. -/
def finiteEtaleFieldMap : F →ₐ[K] E := by
  have : IsFiniteEtale d := {}
  have : Surjective d := IsFiniteEtale.surjective d
  exact FFLeg.phi K M N d hd d.surjective

/-- Every place is unramified for the actual induced function-field map. -/
theorem ramificationIndexAlong_finiteEtaleFieldMap (w : Place K E) :
    Place.ramificationIndexAlong (M.finiteEtaleFieldMap N d hd) w = 1 := by
  have : IsFiniteEtale d := {}
  have : Surjective d := IsFiniteEtale.surjective d
  let φ := FFLeg.phi K M N d hd d.surjective
  have hφ : φ.toRingHom.IsIntegral := FFLeg.isIntegral_phi K M N d hd d.surjective
  let ξ := FFLeg.specializes_genericPoint K M N d d.surjective
  let g : M.C.functionField →+* N.C.functionField :=
    (FFLeg.FunctionFieldPull.pull d ξ).hom
  have hg : Spec.map (CommRingCat.ofHom g) ≫ M.C.fromSpecStalk (genericPoint M.C) =
      N.C.fromSpecStalk (genericPoint N.C) ≫ d := by
    change Spec.map (M.C.presheaf.stalkSpecializes ξ ≫ d.stalkMap (genericPoint N.C)) ≫ _ = _
    rw [Spec.map_comp, Category.assoc, Scheme.SpecMap_stalkSpecializes_fromSpecStalk,
      Scheme.SpecMap_stalkMap_fromSpecStalk]
  have hgen : N.C.fromSpecStalk (genericPoint N.C) ≫ d =
      Spec.map (CommRingCat.ofHom (N.ffEquiv.toRingHom.comp
        (φ.toRingHom.comp M.ffEquiv.symm.toRingHom))) ≫
          M.C.fromSpecStalk (genericPoint M.C) := by
    have heq : N.ffEquiv.toRingHom.comp
        (φ.toRingHom.comp M.ffEquiv.symm.toRingHom) = g := by
      ext z
      change N.ffEquiv (N.ffEquiv.symm (g (M.ffEquiv (M.ffEquiv.symm z)))) = g z
      rw [RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]
    rw [heq]
    exact hg.symm
  have h := CurveModel.ramificationIndexAlong_pointEquivPlace_eq_one_of_formallyUnramified
    N M φ hφ d hd hgen (N.pointEquivPlace.symm w) ⊤ trivial (by infer_instance)
  simpa only [N.pointEquivPlace.apply_symm_apply, finiteEtaleFieldMap, φ] using h

/-- The actual étale cover degree multiplies the Euler characteristic. -/
theorem two_mul_genus_sub_two_eq_finiteEtale
    [CharZero K]
    (hF : ∃ x : F, Transcendental K x ∧
      FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F) :
    2 * (genusFF K E : ℤ) - 2 =
      (finrankAlong K (M.finiteEtaleFieldMap N d hd) : ℤ) *
        (2 * (genusFF K F : ℤ) - 2) := by
  have : IsFiniteEtale d := {}
  have : Surjective d := IsFiniteEtale.surjective d
  let φ := M.finiteEtaleFieldMap N d hd
  let : Algebra F E := algebraAlong φ
  have : IsScalarTower K F E := isScalarTower_along φ
  have : FiniteDimensional F E := FFLeg.finiteAlong_phi K M N d hd d.surjective
  have : CharZero F := ⟨fun m n h => by
    apply Nat.cast_injective (R := K)
    apply (algebraMap K F).injective
    simpa only [map_natCast] using h⟩
  have : Algebra.IsSeparable F E := inferInstance
  have he (w : Place K E) : w.ramificationIndex F = 1 := by
    change Place.ramificationIndexAlong φ w = 1
    exact M.ramificationIndexAlong_finiteEtaleFieldMap N d hd w
  have hRH := AlgebraicCurve.two_mul_genusFF_sub_two_eq_of_isSeparable_of_tame
    (K := K) (F := F) (F' := E) hF (fun w => by rw [he w, Nat.cast_one]; exact one_ne_zero)
  simpa only [he, Nat.cast_one, sub_self, finsum_zero, add_zero, finrankAlong, φ] using hRH

end AlgebraicCurve.CurveModel
