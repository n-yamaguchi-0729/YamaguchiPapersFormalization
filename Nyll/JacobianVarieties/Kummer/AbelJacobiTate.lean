/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Kummer.AbelJacobiFiniteH1
import Nyll.JacobianVarieties.Kummer.CohomologyAbelianPullbackCharacters
import Nyll.EtaleFundamentalGroups.GeometricFiber.AbelianTateComparison
import Nyll.ProCGroups.Abelian.RootsOfUnityCharacterCriterion
import Nyll.ProCGroups.ProC.Quotients.ClosedNormal

/-!
# The actual Abel--Jacobi Tate isomorphism

Finite H¹ pullback detects the actual abelianized fundamental-group map.
Composing with multiplication-cover monodromy gives the actual full Tate
module. The formula on the abelianization quotient records the inducing map.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.RelPicard
open AlgebraicCurve NeronModelInfra GoodReductionJacobian
open scoped IsMulCommutative

namespace JacobianVarieties.Kummer

/-- Actual Abel--Jacobi induces the full Tate isomorphism on the
topological abelianization, with its original quotient map. -/
theorem exists_abelJacobi_fullTate_equiv
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
 :
    let G := RepresentsRelSubPic.relativeGroupLaw
      (P := algEquivZeroGroupCut M₀.toBase ε) hD
    let hc : G.IsCommutative := RepresentsRelSubPic.relativeGroupLaw_isCommutative
      (P := algEquivZeroGroupCut M₀.toBase ε) hD
    ∀ (Ω : Type) [Field Ω] [IsSepClosed Ω] (ξ : Spec (.of Ω) ⟶ M₀.C),
      ∃ e : TopologicalAbelianization (Aut (FiniteEtale.fiber ξ)) ≃ₜ*
          Multiplicative (ProCGroups.FullTateModule (G.AlgPoints hc K)),
        ∀ γ : Aut (FiniteEtale.fiber ξ),
          e (ProCGroups.Abelian.TopologicalAbelianization.mk _ γ) =
            G.fundamentalGroupEquivFullTateAt hc (ξ ≫ aj.1)
              (FiniteEtale.fundamentalGroupHom aj.1 ξ γ) := by
  intro G hc Ω hΩ hsep ξ
  have : ConnectedSpace D.P :=
    GeometricallyConnected.connectedSpace D.toBase D.toBase.isOpenMap
  let eT := G.fundamentalGroupEquivFullTateAt hc (ξ ≫ aj.1)
  have : IsMulCommutative (Aut (FiniteEtale.fiber (ξ ≫ aj.1))) :=
    ⟨⟨fun a b => eT.injective
      ((eT.map_mul a b).trans ((mul_comm (eT a) (eT b)).trans
        (eT.map_mul b a).symm))⟩⟩
  let f := ProCGroups.Abelian.TopologicalAbelianization.lift
    (FiniteEtale.fundamentalGroupHom aj.1 ξ)
  have hf (n : ℕ+) :
      let : TopologicalSpace (rootsOfUnity (n : ℕ) K) := ⊥
      let : DiscreteTopology (rootsOfUnity (n : ℕ) K) := ⟨rfl⟩
      Function.Bijective (f.compLeft (rootsOfUnity (n : ℕ) K)) := by
    intro htop hdiscrete
    have hn : IsUnit ((n : ℕ) : K) := isUnit_iff_ne_zero.mpr
      (Nat.cast_ne_zero.mpr n.ne_zero)
    let A := AddCommGrpCat.of (Additive (rootsOfUnity (n : ℕ) K))
    exact (bijective_constantH1Pullback_iff_abelianCharacterPullback aj.1 A ξ).mp
      (abelJacobi_finiteH1Pullback_bijective M₀ ε D hD aj hclass n hn)
  have : TotallyDisconnectedSpace
      (TopologicalAbelianization (Aut (FiniteEtale.fiber ξ))) :=
    ProCGroups.totallyDisconnectedSpace_quotient_closedNormal
      (Subgroup.closedCommutator (Aut (FiniteEtale.fiber ξ)))
      (Subgroup.isClosed_closedCommutator _)
  let e := ProCGroups.Duality.equivOfBijectiveRootsOfUnityPullback K f hf
  refine ⟨e.trans eT, ?_⟩
  intro γ
  change eT (f (ProCGroups.Abelian.TopologicalAbelianization.mk _ γ)) = _
  rw [ProCGroups.Abelian.TopologicalAbelianization.lift_apply_mk]

end JacobianVarieties.Kummer
