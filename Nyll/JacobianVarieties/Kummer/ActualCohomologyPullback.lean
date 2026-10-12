/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Kummer.ActualGenericWeilComparison
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

/-- For the actual Abel--Jacobi morphism, pullback on finite constant
roots-of-unity H¹ is bijective, by the proved geometric generic comparison. -/
theorem actual_abelJacobi_finiteH1Pullback_bijective
    {K F₀ : Type} [Field K] [IsAlgClosed K] [CharZero K]
    [Field F₀] [Algebra K F₀] [IsCurveOver K F₀]
    (M₀ : CurveModel K F₀)
    [Algebra K M₀.C.functionField]
    (hbase : algebraMap K M₀.C.functionField = baseToFunctionField M₀.toBase)
    {Ω F : Type} [Field Ω] [IsAlgClosed Ω] [Algebra K Ω]
    [Algebra M₀.C.functionField Ω] [IsScalarTower K M₀.C.functionField Ω]
    [IsSepClosed Ω] [IsSepClosure M₀.C.functionField Ω]
    [Field F] [Algebra Ω F] [IsCurveOver Ω F]
    [Algebra F₀ F] [Algebra K F]
    [IsScalarTower K F₀ F] [IsScalarTower K Ω F]
    (hfg : ∃ t : F₀, Transcendental K t ∧
      FiniteDimensional (IntermediateField.adjoin K ({t} : Set F₀)) F₀)
    (hfg' : ∃ t : F, Transcendental Ω t ∧
      FiniteDimensional (IntermediateField.adjoin Ω ({t} : Set F)) F)
    (hgen : IntermediateField.adjoin Ω (Set.range (algebraMap F₀ F)) = ⊤)
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
    (n : ℕ+) (hn : IsUnit ((n : ℕ) : K)) :
    let A := AddCommGrpCat.of (Additive (rootsOfUnity (n : ℕ) K))
    let : ConnectedSpace D.P :=
      GeometricallyConnected.connectedSpace D.toBase D.toBase.isOpenMap
    Function.Bijective (constantCohomologyPullback aj.1 A 1) := by
  intro A hconnected
  classical
  have : Algebra.EssFiniteType K F₀ := DictGlue.essFiniteType_of_curveModel M₀
  have : NeZero (n : ℕ) := ⟨n.ne_zero⟩
  have : NeZero ((n : ℕ) : K) := ⟨hn.ne_zero⟩
  let : TopologicalSpace (rootsOfUnity (n : ℕ) K) := ⊥
  have : DiscreteTopology (rootsOfUnity (n : ℕ) K) := ⟨rfl⟩
  let : TopologicalSpace (Multiplicative A) := ⊥
  have : DiscreteTopology (Multiplicative A) := ⟨rfl⟩
  have : Smooth M₀.toBase := SmoothOfRelativeDimension.smooth 1 M₀.toBase
  have : IsIntegrallyClosed Γ(Spec (.of K), ⊤) := IsIntegrallyClosed.of_equiv
    (Scheme.ΓSpecIso (.of K)).symm.commRingCatIsoToRingEquiv
  have : IsNormalIntegral M₀.C := IsNormalIntegral.of_stalks M₀.C
    (fun x => (Smooth.isDomain_and_isIntegrallyClosed_stalk M₀.toBase x).2)
  let G := RepresentsRelSubPic.relativeGroupLaw
    (P := algEquivZeroGroupCut M₀.toBase ε) hD
  let hc : G.IsCommutative := RepresentsRelSubPic.relativeGroupLaw_isCommutative
    (P := algEquivZeroGroupCut M₀.toBase ε) hD
  let η := Spec.map (CommRingCat.ofHom (algebraMap M₀.C.functionField Ω))
  let q := M₀.C.fromSpecStalk (genericPoint M₀.C)
  let ξ := η ≫ q
  obtain ⟨e₀, hpoint₀, τn, hτn, _, w, ν, hν⟩ :=
    exists_jacobian_weil_cohomology M₀ ε D hD aj hclass n
  have hνbij := jacobian_weil_cohomology_bijective hfg G hc n τn w ν hν
  let τ := Classical.choice
    (FiniteEtale.nonempty_fiber_iso (η ≫ q ≫ aj.1) (G.one (𝟙 (Spec (.of K)))).1)
  let z := τ.inv.app (G.multiplicationCover hc n) (G.multiplicationCoverUnit hc n)
  have hcompare (a : Pic0.torsion K F₀ n) :
      constantCohomologyPullback aj.1 A 1 (ν a) =
        M₀.kummerTorsionCohomology n hn ξ a := by
    obtain ⟨u, hu, hgeneric⟩ := exists_actual_abelJacobi_generic_weil_kummer
      M₀ hbase hfg hfg' hgen ε D hD aj hclass M eC heC hsq n hn w a
      e₀ τn hτn hpoint₀ τ z
    apply finiteH1_ext_genericFieldAction M₀.C Ω A
    intro σ
    let γ := toAut (FiniteEtale.fiber η) (Ω ≃ₐ[M₀.C.functionField] Ω) σ
    let δ := FiniteEtale.fundamentalGroupHom q η γ
    have hp := finiteH1CharacterEquiv_schemePullback aj.1 A ξ (ν a)
    have hpval := congrArg (fun χ => χ δ) hp
    have hcomp := h1Character_fundamentalGroupHom_comp q aj.1 η A (ν a) γ
    have hb := congrArg
      (fun χ : Aut (FiniteEtale.fiber (η ≫ q ≫ aj.1)) →ₜ* Multiplicative A =>
        χ (FiniteEtale.fundamentalGroupHom (q ≫ aj.1) η γ))
      (h1Character_basePoint A (η ≫ q ≫ aj.1)
        (G.one (𝟙 (Spec (.of K)))).1 τ (ν a))
    have hk : (finiteH1CharacterEquiv A ξ
        (M₀.kummerTorsionCohomology n hn ξ a)).toMul δ =
        M₀.kummerMonodromyCharacter n u hn ξ δ := by
      rw [← hu, M₀.kummerTorsionCohomology_kummerClass]
      change ((finiteH1CharacterEquiv A ξ)
        ((finiteH1CharacterEquiv A ξ).symm
          (Additive.ofMul (M₀.kummerMonodromyCharacter n u hn ξ)))).toMul δ = _
      rw [AddEquiv.apply_symm_apply]
      rfl
    rw [hk]
    apply Subtype.ext
    apply Units.ext
    have hchain := hpval.trans (hcomp.trans hb.symm)
    exact (congrArg (fun ζ : rootsOfUnity (n : ℕ) K => ζ.val.val) hchain).trans
      ((hν a _).trans (hgeneric σ))
  have hκbij := (M₀.kummerTorsionCohomologyEquiv n hn ξ).bijective
  constructor
  · intro x y hxy
    obtain ⟨a, rfl⟩ := hνbij.2 x
    obtain ⟨b, rfl⟩ := hνbij.2 y
    have hab : a = b := hκbij.1
      ((hcompare a).symm.trans (hxy.trans (hcompare b)))
    exact congrArg ν hab
  · intro y
    obtain ⟨a, ha⟩ := hκbij.2 y
    exact ⟨ν a, (hcompare a).trans ha⟩

end JacobianVarieties.Kummer
