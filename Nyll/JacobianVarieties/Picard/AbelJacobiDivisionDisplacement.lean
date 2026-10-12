/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Picard.AlgebraicPointsEquivariance
import Nyll.JacobianVarieties.Picard.ConormAlgebraicPoints
import Nyll.JacobianVarieties.Picard.DivisionPointDivisors
import Nyll.EtaleFundamentalGroups.GeometricFiber.AbelianMultiplicationFieldDisplacement
import Nyll.AlgebraicCurves.Divisors.Semilinear
import Nyll.AlgebraicCurves.Models.CurveModelSemilinearFixedField

/-!
# Divisors of actual Abel--Jacobi division points

The Picard comparison and its coefficient equivariance are constructed from
the representing Picard scheme and the Abel--Jacobi point formula. A point
of the actual multiplication fibre then supplies a moving divisor and a
division function. Its coefficient displacement is proved to be the actual
multiplication-monodromy point, with no assumed action comparison.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.PreGaloisCategory
open AlgebraicGeometry AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve
open AlgebraicCurve NeronModelInfra GoodReductionJacobian
open JacobianVarieties.Pic0.Proofs.ConormInjectivity.AlgebraicCurve.ConDesc
open scoped Pointwise

namespace JacobianVarieties.Picard

attribute [local instance]
  IsCurveOver.toHasPrincipalDivisors
  AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup
  AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace
  AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor
  AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0

/-- The actual division divisor difference is the conorm of the original
multiplication-monodromy point in the Picard coordinates furnished by the
Abel--Jacobi point formula. Both the action and conorm comparisons are proved. -/
theorem exists_abelJacobi_division_divisor_displacement
    {K L Ω F₀ F : Type} [Field K] [IsAlgClosed K] [CharZero K]
    [Field L] [Algebra K L] [Field Ω] [IsAlgClosed Ω] [Algebra K Ω]
    [Algebra L Ω] [IsScalarTower K L Ω] [IsSepClosed Ω] [IsSepClosure L Ω]
    [Field F₀] [Algebra K F₀] [IsCurveOver K F₀]
    [Field F] [Algebra Ω F] [IsCurveOver Ω F]
    [Algebra F₀ F] [Algebra K F]
    [IsScalarTower K F₀ F] [IsScalarTower K Ω F]
    (hfg : ∃ t : F₀, Transcendental K t ∧
      FiniteDimensional (IntermediateField.adjoin K ({t} : Set F₀)) F₀)
    (hfg' : ∃ t : F, Transcendental Ω t ∧
      FiniteDimensional (IntermediateField.adjoin Ω ({t} : Set F)) F)
    (hgen : IntermediateField.adjoin Ω (Set.range (algebraMap F₀ F)) = ⊤)
    (M₀ : CurveModel K F₀)
    [IsProper M₀.toBase] [SmoothOfRelativeDimension 1 M₀.toBase] [GeometricallyIntegral M₀.toBase]
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
    (M : CurveModel Ω F) (eC : M.C ≅ pullback M₀.toBase (specMap K Ω))
    (heC : eC.hom ≫ pullback.snd M₀.toBase (specMap K Ω) = M.toBase)
    (hsq : ∀ (U : M₀.C.Opens) [Nonempty (Scheme.Opens.toScheme U)]
        [Nonempty (Scheme.Opens.toScheme
          ((eC.hom ≫ pullback.fst M₀.toBase (specMap K Ω)) ⁻¹ᵁ U))]
        (r : Γ(M₀.C, U)),
      M.ffEquiv.symm (M.C.germToFunctionField
        ((eC.hom ≫ pullback.fst M₀.toBase (specMap K Ω)) ⁻¹ᵁ U)
        (((eC.hom ≫ pullback.fst M₀.toBase (specMap K Ω)).app U).hom r)) =
      algebraMap F₀ F (M₀.ffEquiv.symm (M₀.C.germToFunctionField U r)))
    (u : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap K L))) M₀.toBase)
    (x s : SchemeHomOver (𝟙 (Spec (.of Ω))) M.toBase)
    (hx : x.1 ≫ eC.hom ≫ pullback.fst M₀.toBase (specMap K Ω) =
      Spec.map (CommRingCat.ofHom (algebraMap L Ω)) ≫ u.1)
    (hs : s.1 ≫ eC.hom ≫ pullback.fst M₀.toBase (specMap K Ω) =
      specMap K Ω ≫ ε.1)
    (n : ℕ+) :
    let G := RepresentsRelSubPic.relativeGroupLaw
      (P := algEquivZeroGroupCut M₀.toBase ε) hD
    let hc : G.IsCommutative := RepresentsRelSubPic.relativeGroupLaw_isCommutative
      (P := algEquivZeroGroupCut M₀.toBase ε) hD
    let j : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap K L))) D.toBase :=
      ⟨u.1 ≫ aj.1, (Category.assoc _ _ _).trans
        ((congrArg (u.1 ≫ ·) aj.2).trans u.2)⟩
    let ξ := RelativeGroupLaw.AlgPoints.mapPoint (IsScalarTower.toAlgHom K L Ω) j
    ∀ (e₀ : Pic0 K F₀ ≃+ G.AlgPoints hc K),
      (∀ a : SchemeHomOver (𝟙 (Spec (.of K))) M₀.toBase,
        ∃ Dv : Divisor.degZero (K := K) (F := F₀),
          (Dv : Divisor K F₀) = Finsupp.single (M₀.pointEquivPlace a) 1 -
            Finsupp.single (M₀.pointEquivPlace ε) 1 ∧
          (RelativeGroupLaw.AlgPoints.toPoint (e₀ (Pic0.mk Dv))).1 = a.1 ≫ aj.1) →
    ∀ (τ : FiniteEtale.fiber ξ.1 ≅ FiniteEtale.fiber (G.one (𝟙 (Spec (.of K)))).1)
      (z : (FiniteEtale.fiber ξ.1).obj (G.multiplicationCover hc n))
      (S : Finset (Place Ω F)),
    ∃ (e : Pic0 Ω F ≃+ G.AlgPoints hc Ω)
      (B E : Divisor.degZero (K := Ω) (F := F)) (f : F),
      (∀ a b : SchemeHomOver (𝟙 (Spec (.of Ω))) M.toBase,
        b.1 ≫ eC.hom ≫ pullback.fst M₀.toBase (specMap K Ω) = specMap K Ω ≫ ε.1 →
        ∃ Dv : Divisor.degZero (K := Ω) (F := F),
          (Dv : Divisor Ω F) = Finsupp.single (M.pointEquivPlace a) 1 -
            Finsupp.single (M.pointEquivPlace b) 1 ∧
          (RelativeGroupLaw.AlgPoints.toPoint (e (Pic0.mk Dv))).1 =
            a.1 ≫ eC.hom ≫ pullback.fst M₀.toBase (specMap K Ω) ≫ aj.1) ∧
      (B : Divisor Ω F) = Finsupp.single (M.pointEquivPlace x) 1 -
        Finsupp.single (M.pointEquivPlace s) 1 ∧
      e (Pic0.mk E) = G.multiplicationFiberAlgPoint hc ξ n z ∧
      (∀ v ∈ (E : Divisor Ω F).support, v ∉ S) ∧
      f ≠ 0 ∧
      (∀ v : Place Ω F, v.ord f = (n : ℤ) * (E : Divisor Ω F) v -
        (B : Divisor Ω F) v) ∧
      ∀ σ : Ω ≃ₐ[L] Ω, ∃ (θ : M.C ≅ M.C) (γ : SemilinearAut Ω F),
        θ.hom ≫ eC.hom ≫ pullback.fst M₀.toBase (specMap K Ω) =
          eC.hom ≫ pullback.fst M₀.toBase (specMap K Ω) ∧
        θ.hom ≫ M.toBase =
          M.toBase ≫ Spec.map (CommRingCat.ofHom σ.toRingHom) ∧
        SemilinearAut.baseAut γ = σ.toRingEquiv ∧
        (∀ (U : M.C.Opens) [Nonempty (Scheme.Opens.toScheme U)]
          [Nonempty (Scheme.Opens.toScheme (θ.hom ⁻¹ᵁ U))] (t : Γ(M.C, U)),
          γ • M.ffEquiv.symm (M.C.germToFunctionField U t) =
            M.ffEquiv.symm (M.C.germToFunctionField (θ.hom ⁻¹ᵁ U)
              ((θ.hom.app U).hom t))) ∧
        (∀ a b : SchemeHomOver (𝟙 (Spec (.of Ω))) M.toBase,
          b.1 ≫ θ.hom = Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ a.1 →
            M.pointEquivPlace b = γ • M.pointEquivPlace a) ∧
        γ • (B : Divisor Ω F) = (B : Divisor Ω F) ∧
        γ • Pic0.mk E - Pic0.mk E =
          conPic0 hfg hfg' hgen (e₀.symm
            (G.multiplicationMonodromy hc n
              (continuousConjAut τ
                (FiniteEtale.fundamentalGroupHom j.1
                  (Spec.map (CommRingCat.ofHom (algebraMap L Ω)))
                  (toAut (FiniteEtale.fiber
                    (Spec.map (CommRingCat.ofHom (algebraMap L Ω))))
                    (Ω ≃ₐ[L] Ω) σ)))).1) := by
  intro G hc j ξ e₀ hpoint₀ τ z S
  obtain ⟨e, hpoint, hequiv⟩ :=
    exists_pic0_algPoints_equivariant_of_abelJacobi M₀.toBase ε D hD aj hclass M eC heC
  obtain ⟨B, hB, hpB⟩ := hpoint x s hs
  have heB : e (Pic0.mk B) = RelativeGroupLaw.AlgPoints.ofPoint ξ := by
    apply RelativeGroupLaw.AlgPoints.toPoint_injective
    apply Subtype.ext
    change (RelativeGroupLaw.AlgPoints.toPoint (e (Pic0.mk B))).1 = ξ.1
    rw [hpB]
    change x.1 ≫ eC.hom ≫ pullback.fst M₀.toBase (specMap K Ω) ≫ aj.1 =
      Spec.map (CommRingCat.ofHom (algebraMap L Ω)) ≫ u.1 ≫ aj.1
    simpa only [Category.assoc] using congrArg (fun v => v ≫ aj.1) hx
  have hQ : (n : ℕ) • G.multiplicationFiberAlgPoint hc ξ n z = e (Pic0.mk B) :=
    (G.nsmul_multiplicationFiberAlgPoint hc ξ n z).trans heB.symm
  obtain ⟨E, f, heE, havoid, hf, hord⟩ :=
    exists_divisor_of_algPoint_division G hc e (n : ℕ)
      (G.multiplicationFiberAlgPoint hc ξ n z) B hQ S
  refine ⟨e, B, E, f, hpoint, hB, heE, havoid, hf, hord, ?_⟩
  intro σ
  obtain ⟨θ, γ, hproj, hbase, hγ, hfun, hplaces, he⟩ :=
    hequiv (σ.restrictScalars K)
  have hσL :
      Spec.map (CommRingCat.ofHom σ.toRingHom) ≫
        Spec.map (CommRingCat.ofHom (algebraMap L Ω)) =
      Spec.map (CommRingCat.ofHom (algebraMap L Ω)) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    apply congrArg (fun a : L →+* Ω => Spec.map (CommRingCat.ofHom a))
    exact RingHom.ext σ.commutes
  have hσK :
      Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ specMap K Ω = specMap K Ω :=
    RelativeGroupLaw.AlgPoints.specMap_comp_algebraMap (σ.restrictScalars K).toAlgHom
  have hxfix :
      Spec.map (CommRingCat.ofHom σ.toRingHom) ≫
        x.1 ≫ eC.hom ≫ pullback.fst M₀.toBase (specMap K Ω) =
      x.1 ≫ eC.hom ≫ pullback.fst M₀.toBase (specMap K Ω) := by
    rw [hx, ← Category.assoc, hσL]
  have hsfix :
      Spec.map (CommRingCat.ofHom σ.toRingHom) ≫
        s.1 ≫ eC.hom ≫ pullback.fst M₀.toBase (specMap K Ω) =
      s.1 ≫ eC.hom ≫ pullback.fst M₀.toBase (specMap K Ω) := by
    rw [hs, ← Category.assoc, hσK]
  have hγx := M.point_fixed_of_projection_fixed M₀.toBase (specMap K Ω) eC heC
    θ σ.toRingEquiv γ hproj hbase hplaces x hxfix
  have hγs := M.point_fixed_of_projection_fixed M₀.toBase (specMap K Ω) eC heC
    θ σ.toRingEquiv γ hproj hbase hplaces s hsfix
  have hγB : γ • (B : Divisor Ω F) = (B : Divisor Ω F) := by
    rw [hB, smul_sub, SemilinearAut.smul_single, SemilinearAut.smul_single, hγx, hγs]
  refine ⟨θ, γ, hproj, hbase, hγ, hfun, hplaces, hγB, ?_⟩
  apply e.injective
  rw [map_sub, he, heE,
    conorm_algPoints_of_point_formulas hfg hfg' hgen M₀ M eC heC hsq ε
      G hc aj e₀ e hpoint₀ hpoint, e₀.apply_symm_apply]
  exact G.multiplicationFiberAlgPoint_field_displacement hc j n τ σ z

end JacobianVarieties.Picard
