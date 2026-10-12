/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Picard.CurveModel_exists_representsRelSubPic_abelJacobi_of_isAlgClosed
import Nyll.JacobianVarieties.Picard.TorsionCardinality
import Nyll.JacobianVarieties.Picard.TorsionAlgebraicPoints
import Nyll.JacobianVarieties.Picard.CurveModel_smoothOfRelativeDimension_genusFF_of_representsRelSubPic
import Nyll.JacobianVarieties.Kummer.DivisorClassCohomologyComparison

/-!
# Genus and the cardinality of actual étale H¹

Actual Kummer cohomology identifies finite-coefficient derived H¹ with
divisor torsion. The actual Picard representation, the geometric dimension
formula, and multiplication degree compute its cardinality.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.RelPicard AlgebraicCurve
open NeronModelInfra GoodReductionJacobian
open JacobianVarieties.Picard.Proofs.Pic0PointsAbelJacobi.AlgebraicGeometry.RelPicard

namespace JacobianVarieties.Kummer

/-- The actual finite-coefficient étale H¹ of a smooth proper curve over an
algebraically closed field of characteristic zero has cardinality `n^(2g)`. -/
theorem natCard_finiteH1_eq_pow_genus
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
    (n : ℕ+) {Ω : Type} [Field Ω] [IsSepClosed Ω]
    (ξ : Spec (.of Ω) ⟶ M₀.C) :
    Nat.card (Sheaf.H.{0}
      ((constantSheaf M₀.C.smallEtaleTopology AddCommGrpCat.{0}).obj
        (AddCommGrpCat.of (Additive (rootsOfUnity (n : ℕ) K)))) 1) =
      (n : ℕ) ^ (2 * genusFF K F₀) := by
  have : Algebra.EssFiniteType K F₀ := DictGlue.essFiniteType_of_curveModel M₀
  obtain ⟨t, ht, hf, _⟩ :=
    IsCurveOver.exists_separating_transcendental (K := K) (F := F₀)
  have : SmoothOfRelativeDimension (genusFF K F₀) D.toBase :=
    M₀.smoothOfRelativeDimension_genusFF_of_representsRelSubPic
      K F₀ ⟨t, ht, hf⟩ ε D hD
  let G := RepresentsRelSubPic.relativeGroupLaw
    (P := algEquivZeroGroupCut M₀.toBase ε) hD
  let hc : G.IsCommutative := RepresentsRelSubPic.relativeGroupLaw_isCommutative
    (P := algEquivZeroGroupCut M₀.toBase ε) hD
  have hA : AbelianSchemePropertyBundle K D.toBase :=
    { smooth := inferInstance
      proper := inferInstance
      connectedFibres := fun x => D.toBase.isConnected_preimage_singleton x
      hasGroupLaw := ⟨G⟩ }
  obtain ⟨e, _, hτ⟩ :=
    JacobianVarieties.Picard.exists_pic0_addEquiv_algPoints_of_abelJacobi
      M₀ ε D hD aj hclass
  obtain ⟨τ, _, _⟩ := hτ n
  have hn : IsUnit ((n : ℕ) : K) :=
    isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr n.ne_zero)
  calc
    Nat.card (Sheaf.H.{0}
        ((constantSheaf M₀.C.smallEtaleTopology AddCommGrpCat.{0}).obj
          (AddCommGrpCat.of (Additive (rootsOfUnity (n : ℕ) K)))) 1) =
        Nat.card (Pic0.torsion K F₀ (n : ℕ)) :=
      Nat.card_congr (M₀.kummerTorsionCohomologyEquiv n hn ξ).symm.toEquiv
    _ = Nat.card (ProCGroups.torsionLevel (G.AlgPoints hc K) n) :=
      Nat.card_congr τ.toEquiv
    _ = (n : ℕ) ^ (2 * genusFF K F₀) :=
      G.natCard_torsionLevel_eq_pow hc hA (genusFF K F₀) n

end JacobianVarieties.Kummer

namespace AlgebraicCurve.CurveModel

/-- The genus cardinality formula without a chosen Picard representation or
Abel--Jacobi morphism: these are constructed from the curve and its point. -/
theorem natCard_finiteH1_eq_pow_genus
    {K F : Type} [Field K] [IsAlgClosed K] [CharZero K]
    [Field F] [Algebra K F] [IsCurveOver K F]
    (M : CurveModel K F) [GeometricallyIntegral M.toBase]
    (ε : SchemeHomOver (𝟙 (Spec (.of K))) M.toBase)
    (n : ℕ+) {Ω : Type} [Field Ω] [IsSepClosed Ω]
    (ξ : Spec (.of Ω) ⟶ M.C) :
    Nat.card (Sheaf.H.{0}
      ((constantSheaf M.C.smallEtaleTopology AddCommGrpCat.{0}).obj
        (AddCommGrpCat.of (Additive (rootsOfUnity (n : ℕ) K)))) 1) =
      (n : ℕ) ^ (2 * genusFF K F) := by
  obtain ⟨D, hD, aj, hs, hp, hg, _, hclass, _⟩ :=
    M.exists_representsRelSubPic_abelJacobi_of_isAlgClosed K F ε
  have : Smooth D.toBase := hs
  have : IsProper D.toBase := hp
  have : GeometricallyConnected D.toBase := hg
  exact JacobianVarieties.Kummer.natCard_finiteH1_eq_pow_genus
    M ε D hD aj hclass n ξ

end AlgebraicCurve.CurveModel
