/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Kummer.FiniteH1Cardinality
import Nyll.AlgebraicCurves.Models.FiniteEtaleRiemannHurwitz
import Nyll.EtaleFundamentalGroups.Cohomology.GaloisH1Descent
import Mathlib.Tactic.Linarith

/-!
# Nontrivial deck action from proper hyperbolic geometry

Riemann--Hurwitz makes the genus strictly increase in a nontrivial finite
étale cover of a proper hyperbolic curve. Actual finite-coefficient H¹
therefore cannot all descend. For a Galois cover, the proved transfer and
deck comparison then exhibit a class moved by an actual deck transformation.

This is a nontriviality theorem for the whole deck action. Faithfulness of
each nonidentity deck transformation additionally requires applying this
argument to the quotient by its cyclic subgroup.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicCurve NeronModelInfra
open CategoryTheory.PreGaloisCategory
open EtaleFundamentalGroups.Cohomology
open JacobianVarieties.Picard.Proofs.Pic0PointsAbelJacobi.AlgebraicGeometry.RelPicard

namespace AnabelianGeometry

variable {K F E : Type} [Field K] [IsAlgClosed K] [CharZero K]
  [Field F] [Field E] [Algebra K F] [Algebra K E]
  [IsCurveOver K F] [IsCurveOver K E]
  (M : CurveModel K F) (N : CurveModel K E)
  [GeometricallyIntegral M.toBase] [GeometricallyIntegral N.toBase]
  (εM : SchemeHomOver (𝟙 (Spec (.of K))) M.toBase)
  (εN : SchemeHomOver (𝟙 (Spec (.of K))) N.toBase)
  (d : N.C ⟶ M.C) (hd : d ≫ M.toBase = N.toBase)
  [IsFiniteEtale d]
  (hg : 2 ≤ genusFF K F)
  (hdeg : 1 < finrankAlong K (M.finiteEtaleFieldMap N d hd))
  (n : ℕ+) (hn : 1 < (n : ℕ))
  {Ω : Type} [Field Ω] [IsSepClosed Ω] (ξ : Spec (.of Ω) ⟶ N.C)

include εM εN hd hg hdeg hn ξ

/-- Pullback is not surjective on actual finite-coefficient H¹ for a
nontrivial finite étale cover of a proper curve of genus at least two. -/
theorem not_surjective_finiteH1Pullback_of_hyperbolic :
    ¬ Function.Surjective (constantCohomologyPullback d
      (AddCommGrpCat.of (Additive (rootsOfUnity (n : ℕ) K))) 1) := by
  have : Algebra.EssFiniteType K F := DictGlue.essFiniteType_of_curveModel M
  obtain ⟨t, ht, hf, _⟩ :=
    IsCurveOver.exists_separating_transcendental (K := K) (F := F)
  have hRH := M.two_mul_genus_sub_two_eq_finiteEtale N d hd ⟨t, ht, hf⟩
  have hgZ : (2 : ℤ) ≤ genusFF K F := by exact_mod_cast hg
  have hdZ : (1 : ℤ) < finrankAlong K (M.finiteEtaleFieldMap N d hd) := by
    exact_mod_cast hdeg
  have hgenusZ : (genusFF K F : ℤ) < genusFF K E := by nlinarith
  have hgenus : genusFF K F < genusFF K E := by exact_mod_cast hgenusZ
  let B := AddCommGrpCat.of (Additive (rootsOfUnity (n : ℕ) K))
  have hM := M.natCard_finiteH1_eq_pow_genus εM n (ξ ≫ d)
  have hN := N.natCard_finiteH1_eq_pow_genus εN n ξ
  have : Finite (Sheaf.H.{0}
      ((constantSheaf M.C.smallEtaleTopology AddCommGrpCat.{0}).obj B) 1) :=
    Nat.finite_of_card_ne_zero (by rw [hM]; exact pow_ne_zero _ n.ne_zero)
  intro hsurj
  have hle := Nat.card_le_card_of_surjective
    (constantCohomologyPullback d B 1) hsurj
  rw [hM, hN] at hle
  have hlt : (n : ℕ) ^ (2 * genusFF K F) < (n : ℕ) ^ (2 * genusFF K E) :=
    Nat.pow_lt_pow_right hn (by omega)
  exact (not_lt_of_ge hle) hlt

/-- Some actual deck transformation moves some actual H¹ class. Neither
descent nor the genus comparison is assumed: both come from geometry. -/
theorem exists_deck_moves_finiteH1
    [IsGalois (C := FiniteEtale M.C) (FiniteEtale.mk d)]
    (hcop : (Nat.card (Multiplicative
      (AddCommGrpCat.of (Additive (rootsOfUnity (n : ℕ) K))))).Coprime
        (pointedCoverOpenSubgroup (FiniteEtale.mk d) ξ).toSubgroup.index) :
    ∃ (σ : Aut (FiniteEtale.mk d))
      (c : Sheaf.H.{0}
        ((constantSheaf N.C.smallEtaleTopology AddCommGrpCat.{0}).obj
          (AddCommGrpCat.of (Additive (rootsOfUnity (n : ℕ) K)))) 1),
      constantCohomologyPullback σ.hom.left
        (AddCommGrpCat.of (Additive (rootsOfUnity (n : ℕ) K))) 1 c ≠ c := by
  classical
  by_contra h
  have hinv : ∀ (σ : Aut (FiniteEtale.mk d))
      (c : Sheaf.H.{0}
        ((constantSheaf N.C.smallEtaleTopology AddCommGrpCat.{0}).obj
          (AddCommGrpCat.of (Additive (rootsOfUnity (n : ℕ) K)))) 1),
      constantCohomologyPullback σ.hom.left
        (AddCommGrpCat.of (Additive (rootsOfUnity (n : ℕ) K))) 1 c = c := by
    intro σ c
    by_contra hne
    exact h ⟨σ, c, hne⟩
  have : ConnectedSpace (FiniteEtale.mk d).left :=
    inferInstanceAs (ConnectedSpace N.C)
  apply not_surjective_finiteH1Pullback_of_hyperbolic M N εM εN d hd hg hdeg n hn ξ
  intro c
  exact exists_constantH1Pullback_eq_of_deckInvariant
    (FiniteEtale.mk d) ξ
    (AddCommGrpCat.of (Additive (rootsOfUnity (n : ℕ) K))) hcop c
    (fun σ => hinv σ c)

end AnabelianGeometry
