/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Picard.TorsionAlgebraicPoints
import Nyll.JacobianVarieties.Picard.Exists_pic0_equiv_points_of_representsRelSubPic_of_abelJacobi
import Nyll.JacobianVarieties.Pic0.Pic0_nonempty_divisorialWeilPairingData_of_isAlgClosed
import Nyll.JacobianVarieties.WeilPairing.Divisorial
import Nyll.JacobianVarieties.Autoduality.Cohomology
import Nyll.AlgebraicCurves.FunctionFields.IsCurveOver_exists_separating_transcendental
import Nyll.EtaleFundamentalGroups.GeometricFiber.AbelianMultiplicationMonodromy
import Nyll.EtaleFundamentalGroups.GeometricFiber.AbelianMultiplicationMonodromyGroup
import Nyll.EtaleFundamentalGroups.Cohomology.FiniteH1Comparison
import Mathlib.RingTheory.RootsOfUnity.Basic

/-! # Divisorial Weil characters of actual Jacobian multiplication covers

The actual multiplication-cover monodromy is evaluated by the divisorial Weil
pairing, in the torsion coordinates of the same Picard representative. These
continuous roots-of-unity characters define classes in actual derived etale H¹.
The construction does not identify their Abel--Jacobi pullbacks with Kummer
classes; that requires the separate geometric torsor comparison.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.RelPicard AlgebraicCurve
open NeronModelInfra GoodReductionJacobian EtaleFundamentalGroups.Cohomology

namespace JacobianVarieties.Kummer

open JacobianVarieties.Picard.Proofs.Pic0PointsAbelJacobi.AlgebraicGeometry.RelPicard

private def weilMonodromyCharacter
    {K F : Type} [Field K] [IsAlgClosed K] [CharZero K]
    [Field F] [Algebra K F] [HasPrincipalDivisors K F]
    {J : Scheme} {b : J ⟶ Spec (.of K)}
    [Smooth b] [IsProper b] [GeometricallyConnected b]
    (G : RelativeGroupLaw K b) (hc : G.IsCommutative) (n : ℕ+)
    (τ : Pic0.torsion K F (n : ℕ) ≃+ ProCGroups.torsionLevel (G.AlgPoints hc K) n)
    (w : DivisorialWeilPairingData K F (n : ℕ)) (x : Pic0.torsion K F (n : ℕ)) :
    let : TopologicalSpace (rootsOfUnity (n : ℕ) K) := ⊥
    π₁ᵉᵗ((G.one (𝟙 (Spec (.of K)))).1) →ₜ* rootsOfUnity (n : ℕ) K := by
  let : TopologicalSpace (rootsOfUnity (n : ℕ) K) := ⊥
  let : TopologicalSpace (ProCGroups.torsionLevel (G.AlgPoints hc K) n) :=
    ProCGroups.FullTateModule.torsionLevelTopology (G.AlgPoints hc K) n
  have : DiscreteTopology (ProCGroups.torsionLevel (G.AlgPoints hc K) n) := ⟨rfl⟩
  let value (y : ProCGroups.torsionLevel (G.AlgPoints hc K) n) : rootsOfUnity (n : ℕ) K :=
    ⟨Units.mk0 (w.pair x (τ.symm y)) (w.pair_ne_zero x (τ.symm y)),
      (mem_rootsOfUnity' (n : ℕ) _).mpr
        (HomPic0Gm.apply_pow_eq_one (w.toChar x) (τ.symm y))⟩
  refine
    { toFun := fun g => value (G.multiplicationMonodromy hc n g)
      map_one' := ?_
      map_mul' := ?_
      continuous_toFun := (continuous_of_discreteTopology : Continuous value).comp
        (G.multiplicationMonodromy_continuous hc n) }
  · apply Subtype.ext
    apply Units.ext
    change w.pair x (τ.symm (G.multiplicationMonodromy hc n 1)) = 1
    rw [G.multiplicationMonodromy_one, map_zero, w.pair_zero_right]
  · intro g h
    apply Subtype.ext
    apply Units.ext
    change w.pair x (τ.symm (G.multiplicationMonodromy hc n (g * h))) =
      w.pair x (τ.symm (G.multiplicationMonodromy hc n g)) *
        w.pair x (τ.symm (G.multiplicationMonodromy hc n h))
    rw [G.multiplicationMonodromy_mul, map_add, w.pair_add_right]

private def weilMonodromyHom
    {K F : Type} [Field K] [IsAlgClosed K] [CharZero K]
    [Field F] [Algebra K F] [HasPrincipalDivisors K F]
    {J : Scheme} {b : J ⟶ Spec (.of K)}
    [Smooth b] [IsProper b] [GeometricallyConnected b]
    (G : RelativeGroupLaw K b) (hc : G.IsCommutative) (n : ℕ+)
    (τ : Pic0.torsion K F (n : ℕ) ≃+ ProCGroups.torsionLevel (G.AlgPoints hc K) n)
    (w : DivisorialWeilPairingData K F (n : ℕ)) :
    let : TopologicalSpace (rootsOfUnity (n : ℕ) K) := ⊥
    let : DiscreteTopology (rootsOfUnity (n : ℕ) K) := ⟨rfl⟩
    Pic0.torsion K F (n : ℕ) →+
      Additive (π₁ᵉᵗ((G.one (𝟙 (Spec (.of K)))).1) →ₜ* rootsOfUnity (n : ℕ) K) := by
  let : TopologicalSpace (rootsOfUnity (n : ℕ) K) := ⊥
  have : DiscreteTopology (rootsOfUnity (n : ℕ) K) := ⟨rfl⟩
  refine
    { toFun := fun x => Additive.ofMul (weilMonodromyCharacter G hc n τ w x)
      map_zero' := ?_
      map_add' := ?_ }
  · apply ContinuousMonoidHom.ext
    intro g
    apply Subtype.ext
    apply Units.ext
    exact w.pair_zero_left (τ.symm (G.multiplicationMonodromy hc n g))
  · intro x y
    apply ContinuousMonoidHom.ext
    intro g
    apply Subtype.ext
    apply Units.ext
    exact w.pair_add_left x y (τ.symm (G.multiplicationMonodromy hc n g))

/-- The same actual Picard scheme carries derived H¹ classes whose characters
evaluate the actual multiplication-cover action by divisor evaluation. Neither
a perfect-pairing hypothesis nor a comparison with Abel--Jacobi pullback is an
input. -/
theorem exists_jacobian_weil_cohomology
    {K F : Type} [Field K] [IsAlgClosed K] [CharZero K] [Field F] [Algebra K F]
    [IsCurveOver K F] (M : CurveModel K F)
    (ε : SchemeHomOver (𝟙 (Spec (.of K))) M.toBase)
    (D : RelativePic0Designation K M.toBase)
    (hD : RepresentsRelSubPic M.toBase ε (algEquivZeroCut M.toBase ε) D)
    [Smooth D.toBase] [IsProper D.toBase] [GeometricallyConnected D.toBase]
    (aj : SchemeHomOver M.toBase D.toBase)
    (hclass : ∀ (L : Type) [Field L] (t : Spec (.of L) ⟶ Spec (.of K))
      (x : SchemeHomOver t M.toBase),
      Nonempty ((hD.poincare.pullbackAlong
        ⟨x.1 ≫ aj.1, (Category.assoc _ _ _).trans
          ((congrArg (x.1 ≫ ·) aj.2).trans x.2)⟩).L ≅
        (RelEffCartierDiv.ofPoint M.toBase x.1 x.2).lineBundle ⊗
          (RelEffCartierDiv.ofPoint M.toBase (t ≫ ε.1)
            ((Category.assoc _ _ _).trans
              ((congrArg (t ≫ ·) ε.2).trans (Category.comp_id t)))).idealModule))
    (n : ℕ+) :
    let G := RepresentsRelSubPic.relativeGroupLaw
      (P := algEquivZeroGroupCut M.toBase ε) hD
    let hc : G.IsCommutative := RepresentsRelSubPic.relativeGroupLaw_isCommutative
      (P := algEquivZeroGroupCut M.toBase ε) hD
    let : TopologicalSpace (rootsOfUnity (n : ℕ) K) := ⊥
    let : DiscreteTopology (rootsOfUnity (n : ℕ) K) := ⟨rfl⟩
    let A := AddCommGrpCat.of (Additive (rootsOfUnity (n : ℕ) K))
    let : TopologicalSpace (Multiplicative A) := ⊥
    let : DiscreteTopology (Multiplicative A) := ⟨rfl⟩
    let : ConnectedSpace D.P := GeometricallyConnected.connectedSpace D.toBase D.toBase.isOpenMap
    ∃ e : Pic0 K F ≃+ G.AlgPoints hc K,
      (∀ x : SchemeHomOver (𝟙 (Spec (.of K))) M.toBase,
        ∃ Dv : Divisor.degZero (K := K) (F := F),
          (Dv : Divisor K F) = Finsupp.single (M.pointEquivPlace x) 1 -
            Finsupp.single (M.pointEquivPlace ε) 1 ∧
          (RelativeGroupLaw.AlgPoints.toPoint (e (Pic0.mk Dv))).1 = x.1 ≫ aj.1) ∧
      ∃ τ : Pic0.torsion K F (n : ℕ) ≃+ ProCGroups.torsionLevel (G.AlgPoints hc K) n,
        (∀ x, (τ x).1 = e x.1) ∧
        (∀ x, (G.torsionLevelEquivSchemeKerPoints hc n (τ x)).1 ≫
          pullback.fst (G.schemeNsmul (n : ℕ)) (G.one (𝟙 (Spec (.of K)))).1 =
            (RelativeGroupLaw.AlgPoints.toPoint (e x.1)).1) ∧
        ∃ w : DivisorialWeilPairingData K F (n : ℕ),
          ∃ ν : Pic0.torsion K F (n : ℕ) →+
              Sheaf.H.{0} ((constantSheaf D.P.smallEtaleTopology AddCommGrpCat.{0}).obj A) 1,
            ∀ (x : Pic0.torsion K F (n : ℕ))
              (g : π₁ᵉᵗ((G.one (𝟙 (Spec (.of K)))).1)),
              ((finiteH1CharacterEquiv A (G.one (𝟙 (Spec (.of K)))).1 (ν x)).toMul g :
                rootsOfUnity (n : ℕ) K).val.val =
                  w.pair x (τ.symm (G.multiplicationMonodromy hc n g)) := by
  intro G hc htop hdiscrete A hAtop hAdiscrete hconnected
  have : Algebra.EssFiniteType K F :=
    DictGlue.essFiniteType_of_curveModel M
  obtain ⟨z, hz, hfin, _⟩ := IsCurveOver.exists_separating_transcendental (K := K) (F := F)
  obtain ⟨w⟩ := Pic0.nonempty_divisorialWeilPairingData_of_isAlgClosed K F
    ⟨z, hz, hfin⟩ (n : ℕ)
  obtain ⟨e, hpoint, htorsion⟩ :=
    JacobianVarieties.Picard.exists_pic0_addEquiv_algPoints_of_abelJacobi M ε D hD aj hclass
  obtain ⟨τ, hτ, hker⟩ := htorsion n
  let κ : Pic0.torsion K F (n : ℕ) →+
      Additive (π₁ᵉᵗ((G.one (𝟙 (Spec (.of K)))).1) →ₜ* Multiplicative A) :=
    weilMonodromyHom G hc n τ w
  let ν := (finiteH1CharacterEquiv A (G.one (𝟙 (Spec (.of K)))).1).symm.toAddMonoidHom.comp κ
  refine ⟨e, hpoint, τ, hτ, hker, w, ν, ?_⟩
  intro x g
  change ((finiteH1CharacterEquiv A (G.one (𝟙 (Spec (.of K)))).1
    ((finiteH1CharacterEquiv A (G.one (𝟙 (Spec (.of K)))).1).symm (κ x))).toMul g :
      rootsOfUnity (n : ℕ) K).val.val = _
  rw [AddEquiv.apply_symm_apply]
  rfl

end JacobianVarieties.Kummer
