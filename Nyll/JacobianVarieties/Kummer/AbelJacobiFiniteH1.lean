/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Kummer.ActualCohomologyPullback
import Nyll.AlgebraicCurves.Geometry.Schemes.FunctionFieldConstantExtensionScalars
import Nyll.AlgebraicCurves.Geometry.Curves.SmoothProperCurve_exists_curveModel_iso_pullback_germToFunctionField_eq_of_isAlgClosed
import Nyll.JacobianVarieties.Kummer.JacobianWeilCharacters
import Nyll.JacobianVarieties.Kummer.JacobianWeilCohomologyBijective
import Nyll.JacobianVarieties.Kummer.DivisorClassCohomologyComparison
import Nyll.JacobianVarieties.Kummer.CohomologyPullbackCharacters
import Nyll.EtaleFundamentalGroups.Cohomology.GenericPointCharacterDetection
import Nyll.EtaleFundamentalGroups.Cohomology.H1CharacterComposition
import Nyll.SchemeTheory.LocalGeometry.SmoothStalkNormality

/-!
# Actual Abel--Jacobi pullback on finite-coefficient H¹

The geometric generic Weil--Kummer identity determines the actual global
derived-cohomology pullback. The auxiliary geometric model is supplied here
with its germ and field-generation data; construction of this model is separate.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.PreGaloisCategory
open AlgebraicGeometry AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve
open AlgebraicCurve NeronModelInfra GoodReductionJacobian
open EtaleFundamentalGroups.Cohomology

namespace JacobianVarieties.Kummer

open JacobianVarieties.Picard.Proofs.Pic0PointsAbelJacobi.AlgebraicGeometry.RelPicard

attribute [local instance] IsCurveOver.toHasPrincipalDivisors

/-- The actual Abel--Jacobi pullback is bijective on finite constant
roots-of-unity H¹. All auxiliary constant-extension coordinates are
constructed from the original smooth proper geometrically integral curve. -/
theorem abelJacobi_finiteH1Pullback_bijective
    {K F₀ : Type} [Field K] [IsAlgClosed K] [CharZero K]
    [Field F₀] [Algebra K F₀] [IsCurveOver K F₀]
    (M₀ : CurveModel K F₀)
    [GeometricallyIntegral M₀.toBase]
    (ε : SchemeHomOver (𝟙 (Spec (.of K))) M₀.toBase)
    (D : RelativePic0Designation K M₀.toBase)
    (hD : RepresentsRelSubPic M₀.toBase ε (algEquivZeroCut M₀.toBase ε) D)
    [Smooth D.toBase] [IsProper D.toBase] [GeometricallyConnected D.toBase]
    (aj : SchemeHomOver M₀.toBase D.toBase)
    (hclass : ∀ (L : Type) [Field L] (t : Spec (.of L) ⟶ Spec (.of K))
      (x : SchemeHomOver t M₀.toBase),
      Nonempty ((hD.poincare.pullbackAlong
        ⟨x.1 ≫ aj.1, (Category.assoc _ _ _).trans
          ((congrArg (x.1 ≫ ·) aj.2).trans x.2)⟩).L ≅
        (RelEffCartierDiv.ofPoint M₀.toBase x.1 x.2).lineBundle ⊗
          (RelEffCartierDiv.ofPoint M₀.toBase (t ≫ ε.1)
            ((Category.assoc _ _ _).trans
              ((congrArg (t ≫ ·) ε.2).trans (Category.comp_id t)))).idealModule))
    (n : ℕ+) (hn : IsUnit ((n : ℕ) : K)) :
    let A := AddCommGrpCat.of (Additive (rootsOfUnity (n : ℕ) K))
    let : ConnectedSpace D.P :=
      GeometricallyConnected.connectedSpace D.toBase D.toBase.isOpenMap
    Function.Bijective (constantCohomologyPullback aj.1 A 1) := by
  intro A hconnected
  classical
  let : Algebra K M₀.C.functionField := M₀.functionFieldAlgebra
  let Ω := AlgebraicClosure M₀.C.functionField
  let : Algebra K Ω := inferInstance
  have : IsScalarTower K M₀.C.functionField Ω := inferInstance
  have : CharZero M₀.C.functionField := ⟨fun m n h => by
    apply Nat.cast_injective (R := K)
    apply (algebraMap K M₀.C.functionField).injective
    simpa only [map_natCast] using h⟩
  have : IsSepClosure M₀.C.functionField Ω := inferInstance
  let Y := pullback M₀.toBase (specMap K Ω)
  have : IsIntegral Y :=
    SmoothProperCurve.isIntegral_pullback_Spec_field K M₀.toBase (specMap K Ω)
  let F := Y.functionField
  let : Algebra Ω F := (baseToFunctionField (pullback.snd M₀.toBase (specMap K Ω))).toAlgebra
  obtain ⟨φ, hφ, hgenφ⟩ := exists_functionField_constantExtension Ω M₀.toBase
  let ψ : F₀ →+* F := φ.comp M₀.ffEquiv.toRingHom
  let : Algebra F₀ F := ψ.toAlgebra
  let : Algebra K F := ((algebraMap Ω F).comp (algebraMap K Ω)).toAlgebra
  have : IsScalarTower K Ω F := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsScalarTower K F₀ F := IsScalarTower.of_algebraMap_eq fun c => by
    change algebraMap Ω F (algebraMap K Ω c) = φ (M₀.ffEquiv (algebraMap K F₀ c))
    rw [M₀.ffEquiv_algebraMap]
    exact (functionField_constantExtension_map_constants Ω M₀.toBase φ hφ c).symm
  obtain ⟨hcurve, hfinite, M, eC, heC, hM⟩ :=
    exists_curveModel_iso_pullback_germToFunctionField_eq_of_isAlgClosed
      K M₀.toBase Ω (specMap K Ω)
  have : IsCurveOver Ω F := hcurve
  have : Algebra.EssFiniteType Ω F := hfinite
  have : Algebra.EssFiniteType K F₀ := DictGlue.essFiniteType_of_curveModel M₀
  obtain ⟨t₀, ht₀, hf₀, _⟩ :=
    IsCurveOver.exists_separating_transcendental (K := K) (F := F₀)
  obtain ⟨t, ht, hf, _⟩ :=
    IsCurveOver.exists_separating_transcendental (K := Ω) (F := F)
  have hrange : Set.range (algebraMap F₀ F) = Set.range φ := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨M₀.ffEquiv y, rfl⟩
    · rintro ⟨y, rfl⟩
      refine ⟨M₀.ffEquiv.symm y, ?_⟩
      change φ (M₀.ffEquiv (M₀.ffEquiv.symm y)) = φ y
      rw [M₀.ffEquiv.apply_symm_apply]
  have hgen : IntermediateField.adjoin Ω (Set.range (algebraMap F₀ F)) = ⊤ := by
    rw [hrange]
    exact hgenφ
  refine actual_abelJacobi_finiteH1Pullback_bijective M₀ rfl
    ⟨t₀, ht₀, hf₀⟩ ⟨t, ht, hf⟩ hgen ε D hD aj hclass M eC heC ?_ n hn
  intro U hU hpre r
  have hpreY : Nonempty ((pullback.fst M₀.toBase (specMap K Ω)) ⁻¹ᵁ U) := by
    obtain ⟨x⟩ := hpre
    exact ⟨⟨eC.hom.base x.1, x.2⟩⟩
  have hpreM : Nonempty
      (eC.hom ⁻¹ᵁ ((pullback.fst M₀.toBase (specMap K Ω)) ⁻¹ᵁ U)) := hpre
  have hm := hM ((pullback.fst M₀.toBase (specMap K Ω)) ⁻¹ᵁ U)
    (((pullback.fst M₀.toBase (specMap K Ω)).app U).hom r)
  have hv := hm.trans (hφ U r)
  change M.ffEquiv.symm
    (M.C.germToFunctionField
      ((eC.hom ≫ pullback.fst M₀.toBase (specMap K Ω)) ⁻¹ᵁ U)
      (((eC.hom ≫ pullback.fst M₀.toBase (specMap K Ω)).app U).hom r)) =
      φ (M₀.ffEquiv (M₀.ffEquiv.symm (M₀.C.germToFunctionField U r)))
  rw [M₀.ffEquiv.apply_symm_apply]
  exact hv

end JacobianVarieties.Kummer
