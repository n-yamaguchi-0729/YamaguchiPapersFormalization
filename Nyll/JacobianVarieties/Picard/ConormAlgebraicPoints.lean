/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Picard.AlgebraicPointsEquivariance
import Nyll.JacobianVarieties.Pic0.Pic0_exists_injective_conorm_of_constantFieldExtension_of_isAlgClosed
import Nyll.AlgebraicCurves.Models.CurveModel_existsUnique_point_and_ord_eq_and_ord_eq_zero_of_iso_pullback_of_ffEquiv_symm_germToFunctionField_eq
import Nyll.JacobianVarieties.Pic0.Pic0_mem_closure_mk_single_sub_single

/-!
# Actual Picard conorm and coefficient extension of points

The established point-minus-basepoint formulas determine the comparison
on every divisor class. The geometric base-change theorem identifies
the actual lifted point with the unique valuation lift used by conorm.
The germ square is the compatibility of the chosen function-field
coordinates with the actual projection of the base-changed curve.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve
open NeronModelInfra GoodReductionJacobian AlgebraicGeometry.SmoothProperCurve
open AlgebraicCurve.CurveModel
open JacobianVarieties.Pic0.Proofs.ConormInjectivity.AlgebraicCurve.ConDesc

namespace JacobianVarieties.Picard

attribute [local instance] IsCurveOver.toHasPrincipalDivisors

/-- The Picard point comparisons supplied by the Abel--Jacobi construction
intertwine actual conorm with extension of coefficients on algebraic points. -/
theorem conorm_algPoints_of_point_formulas
    {K F K' F' : Type} [Field K] [Field F] [Field K'] [Field F']
    [Algebra K F] [Algebra K' F'] [Algebra K K'] [Algebra F F'] [Algebra K F']
    [IsScalarTower K K' F'] [IsScalarTower K F F']
    [IsAlgClosed K] [IsAlgClosed K'] [IsCurveOver K F] [IsCurveOver K' F']
    (hfg : ∃ x : F, Transcendental K x ∧
      FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    (hfg' : ∃ x : F', Transcendental K' x ∧
      FiniteDimensional (IntermediateField.adjoin K' ({x} : Set F')) F')
    (hgen : IntermediateField.adjoin K' (Set.range (algebraMap F F')) = ⊤)
    (M₀ : CurveModel K F) (M : CurveModel K' F')
    (eC : M.C ≅ pullback M₀.toBase (specMap K K'))
    (heC : eC.hom ≫ pullback.snd M₀.toBase (specMap K K') = M.toBase)
    (hsq : ∀ (U : M₀.C.Opens) [Nonempty (Scheme.Opens.toScheme U)]
        [Nonempty (Scheme.Opens.toScheme
          ((eC.hom ≫ pullback.fst M₀.toBase (specMap K K')) ⁻¹ᵁ U))]
        (s : Γ(M₀.C, U)),
      M.ffEquiv.symm (M.C.germToFunctionField
        ((eC.hom ≫ pullback.fst M₀.toBase (specMap K K')) ⁻¹ᵁ U)
        (((eC.hom ≫ pullback.fst M₀.toBase (specMap K K')).app U).hom s)) =
      algebraMap F F' (M₀.ffEquiv.symm (M₀.C.germToFunctionField U s)))
    (ε : SchemeHomOver (𝟙 (Spec (.of K))) M₀.toBase)
    {J : Scheme} {b : J ⟶ Spec (.of K)}
    (G : RelativeGroupLaw K b) (hc : G.IsCommutative)
    (aj : SchemeHomOver M₀.toBase b)
    (e₀ : Pic0 K F ≃+ G.AlgPoints hc K)
    (e : Pic0 K' F' ≃+ G.AlgPoints hc K')
    (hpoint₀ : ∀ x : SchemeHomOver (𝟙 (Spec (.of K))) M₀.toBase,
      ∃ D : Divisor.degZero (K := K) (F := F),
        (D : Divisor K F) = Finsupp.single (M₀.pointEquivPlace x) 1 -
          Finsupp.single (M₀.pointEquivPlace ε) 1 ∧
        (RelativeGroupLaw.AlgPoints.toPoint (e₀ (Pic0.mk D))).1 = x.1 ≫ aj.1)
    (hpoint : ∀ x s : SchemeHomOver (𝟙 (Spec (.of K'))) M.toBase,
      s.1 ≫ eC.hom ≫ pullback.fst M₀.toBase (specMap K K') = specMap K K' ≫ ε.1 →
      ∃ D : Divisor.degZero (K := K') (F := F'),
        (D : Divisor K' F') = Finsupp.single (M.pointEquivPlace x) 1 -
          Finsupp.single (M.pointEquivPlace s) 1 ∧
        (RelativeGroupLaw.AlgPoints.toPoint (e (Pic0.mk D))).1 =
          x.1 ≫ eC.hom ≫ pullback.fst M₀.toBase (specMap K K') ≫ aj.1)
    (z : Pic0 K F) :
    e (conPic0 hfg hfg' hgen z) =
      RelativeGroupLaw.AlgPoints.map (Algebra.ofId K K') (e₀ z) := by
  have hgeom := (
existsUnique_point_and_ord_eq_and_ord_eq_zero_of_iso_pullback_of_ffEquiv_symm_germToFunctionField_eq
    (algebraMap K K') M₀ M eC heC (algebraMap F F') hsq)
  obtain ⟨s, hs, _⟩ := hgeom.1 ε
  have hlift (x₀ : SchemeHomOver (𝟙 (Spec (.of K))) M₀.toBase)
      (x : SchemeHomOver (𝟙 (Spec (.of K'))) M.toBase)
      (hx : x.1 ≫ eC.hom ≫ pullback.fst M₀.toBase (specMap K K') =
        specMap K K' ≫ x₀.1) :
      lift hfg hfg' hgen (M₀.pointEquivPlace x₀) = M.pointEquivPlace x :=
    (eq_lift_of_comap_eq hfg hfg' hgen (hgeom.2.1 x₀ x hx).1).symm
  let f₁ := e.toAddMonoidHom.comp (conPic0 hfg hfg' hgen)
  let f₂ := (RelativeGroupLaw.AlgPoints.map (L := G) (hc := hc)
    (Algebra.ofId K K')).comp e₀.toAddMonoidHom
  change f₁ z = f₂ z
  apply AddMonoidHom.eqOn_closure (s :=
    {y : Pic0 K F | ∃ (v : Place K F)
      (h : Finsupp.single v (1 : ℤ) - Finsupp.single (M₀.pointEquivPlace ε) 1 ∈
        Divisor.degZero (K := K) (F := F)),
      y = Pic0.mk ⟨Finsupp.single v 1 - Finsupp.single (M₀.pointEquivPlace ε) 1, h⟩}) ?_
    (Pic0.mem_closure_mk_single_sub_single
      IsCurveOver.forall_deg_eq_one_of_isAlgClosed (M₀.pointEquivPlace ε) z)
  rintro _ ⟨v, hv, rfl⟩
  let x₀ := M₀.pointEquivPlace.symm v
  have hx₀ : M₀.pointEquivPlace x₀ = v := M₀.pointEquivPlace.apply_symm_apply v
  obtain ⟨x, hx, _⟩ := hgeom.1 x₀
  obtain ⟨D₀, hD₀, hp₀⟩ := hpoint₀ x₀
  obtain ⟨D, hD, hp⟩ := hpoint x s hs
  have hD₀class : D₀ =
      ⟨Finsupp.single v 1 - Finsupp.single (M₀.pointEquivPlace ε) 1, hv⟩ := by
    apply Subtype.ext
    rw [hD₀, hx₀]
  have hDcon : conDegZero hfg hfg' hgen D₀ = D := by
    apply Subtype.ext
    change (conHom hfg hfg' hgen) (D₀ : Divisor K F) = (D : Divisor K' F')
    rw [hD₀, hD, map_sub]
    change Finsupp.mapDomain (lift hfg hfg' hgen)
      (Finsupp.single (M₀.pointEquivPlace x₀) 1) -
        Finsupp.mapDomain (lift hfg hfg' hgen)
          (Finsupp.single (M₀.pointEquivPlace ε) 1) = _
    rw [Finsupp.mapDomain_single, Finsupp.mapDomain_single, hlift x₀ x hx, hlift ε s hs]
  change e (conPic0 hfg hfg' hgen (Pic0.mk _)) =
    RelativeGroupLaw.AlgPoints.map (Algebra.ofId K K') (e₀ (Pic0.mk _))
  rw [← hD₀class, conPic0_mk, hDcon]
  apply RelativeGroupLaw.AlgPoints.toPoint_injective
  apply Subtype.ext
  rw [RelativeGroupLaw.AlgPoints.toPoint_map_coe, hp, hp₀]
  simpa only [Category.assoc, specMap, Algebra.ofId] using
    congrArg (fun q => q ≫ aj.1) hx

end JacobianVarieties.Picard
