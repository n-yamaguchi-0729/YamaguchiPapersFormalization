/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Kummer.OpenDivisorCohomologyComparison
import Nyll.JacobianVarieties.Kummer.OpenBoundaryRelation
import Nyll.JacobianVarieties.Kummer.BoundaryResidueCardinality

/-!
# The residue sequence on actual open-curve cohomology

The residue map is defined on genuine derived étale H¹ through the proved
comparison with actual Kummer covers. Its kernel is the proper divisorial
Kummer quotient, and its image is the sum-zero boundary module. The
comparison of the first map with geometric pullback, inverse-limit
exactness, and arithmetic equivariance are separate steps.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory AlgebraicCurve
open scoped BigOperators

namespace AnabelianGeometry.WeightFiltration

/-- Actual finite-coefficient derived cohomology with constant roots of unity. -/
abbrev FiniteKummerH1 (K : Type) [Field K] (X : Scheme) (n : ℕ+) :=
  Sheaf.H.{0} ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{0}).obj
    (AddCommGrpCat.of (Additive (rootsOfUnity (n : ℕ) K)))) 1

variable {K F : Type} [Field K] [IsAlgClosed K] [Field F] [Algebra K F]
  (M : CurveModel K F) (n : ℕ+)
  {X : Scheme} [IsIntegral X] [CompactSpace X]
  (j : X ⟶ M.C) [IsOpenImmersion j] (hj : DenseRange j)
  (hn : IsUnit ((n : ℕ) : K))
  {Ω : Type} [Field Ω] [IsSepClosed Ω] (xi : Spec (.of Ω) ⟶ X)

/-- Boundary residues of an actual étale cohomology class. -/
def finiteResidue :
    FiniteKummerH1 K X n →+ (M.openBoundaryPlaces j → ZMod (n : ℕ)) :=
  (Pic0.openKummerResidueQuotient (M.openBoundaryPlaces j) n).toAdditive.comp
    (CurveModel.OpenKummer.quotientCohomologyEquiv M n j hj hn xi).symm.toAddMonoidHom

/-- Proper divisorial Kummer classes, regarded as actual classes on the open curve. -/
def properKummerToFiniteH1 :
    Additive (Pic0.kummerUnits K F n ⧸ Pic0.kummerPowers K F n) →+
      FiniteKummerH1 K X n :=
  (CurveModel.OpenKummer.quotientCohomologyEquiv M n j hj hn xi).toAddMonoidHom.comp
    (Pic0.kummerQuotientToOpen (M.openBoundaryPlaces j) n).toAdditive

/-- The residue map retains the valuation formula of the actual cover. -/
theorem finiteResidue_comparison
    (q : Additive (Pic0.openKummerUnits K F (M.openBoundaryPlaces j) n ⧸
      Pic0.openKummerPowers K F (M.openBoundaryPlaces j) n)) :
    finiteResidue M n j hj hn xi
      (CurveModel.OpenKummer.quotientCohomologyEquiv M n j hj hn xi q) =
        Multiplicative.toAdd
          (Pic0.openKummerResidueQuotient (M.openBoundaryPlaces j) n q.toMul) := by
  change (Pic0.openKummerResidueQuotient (M.openBoundaryPlaces j) n).toAdditive
    ((CurveModel.OpenKummer.quotientCohomologyEquiv M n j hj hn xi).symm
      ((CurveModel.OpenKummer.quotientCohomologyEquiv M n j hj hn xi) q)) = _
  rw [AddEquiv.symm_apply_apply]
  rfl

/-- The proper Kummer term embeds into actual open-curve H¹. -/
theorem properKummerToFiniteH1_injective :
    Function.Injective (properKummerToFiniteH1 M n j hj hn xi) :=
  (CurveModel.OpenKummer.quotientCohomologyEquiv M n j hj hn xi).injective.comp
    (Pic0.kummerQuotientToOpen_injective (M.openBoundaryPlaces j) n)

/-- Exactness at actual open-curve H¹, not at an assumed cohomology model. -/
theorem finiteResidue_eq_zero_iff (x : FiniteKummerH1 K X n) :
    finiteResidue M n j hj hn xi x = 0 ↔
      ∃ q, properKummerToFiniteH1 M n j hj hn xi q = x := by
  let e := CurveModel.OpenKummer.quotientCohomologyEquiv M n j hj hn xi
  constructor
  · intro hx
    have hu : (e.symm x).toMul ∈
        (Pic0.openKummerResidueQuotient (M.openBoundaryPlaces j) n).ker := hx
    rw [← Pic0.kummerQuotientToOpen_range (M.openBoundaryPlaces j) n] at hu
    obtain ⟨q, hq⟩ := hu
    refine ⟨Additive.ofMul q, ?_⟩
    apply e.symm.injective
    change e.symm (e (Additive.ofMul
      (Pic0.kummerQuotientToOpen (M.openBoundaryPlaces j) n q))) = e.symm x
    rw [e.symm_apply_apply]
    exact hq
  · rintro ⟨q, rfl⟩
    change finiteResidue M n j hj hn xi
      (e (Additive.ofMul
        (Pic0.kummerQuotientToOpen (M.openBoundaryPlaces j) n q.toMul))) = 0
    rw [finiteResidue_comparison]
    have hq : Pic0.kummerQuotientToOpen (M.openBoundaryPlaces j) n q.toMul ∈
        (Pic0.openKummerResidueQuotient (M.openBoundaryPlaces j) n).ker := by
      rw [← Pic0.kummerQuotientToOpen_range (M.openBoundaryPlaces j) n]
      exact ⟨q.toMul, rfl⟩
    exact hq

/-- The image of the proper term is exactly the residue kernel. -/
theorem properKummerToFiniteH1_range :
    (@AddMonoidHom.range
      (Additive (Pic0.kummerUnits K F n ⧸ Pic0.kummerPowers K F n)) inferInstance
      (FiniteKummerH1 K X n) inferInstance (properKummerToFiniteH1 M n j hj hn xi)) =
      (finiteResidue M n j hj hn xi).ker := by
  ext x
  exact (finiteResidue_eq_zero_iff M n j hj hn xi x).symm

variable [IsCurveOver K F] [Fintype (M.openBoundaryPlaces j)]

/-- Residues of every actual open-curve H¹ class satisfy the sum relation. -/
theorem sum_finiteResidue_eq_zero (x : FiniteKummerH1 K X n) :
    ∑ v, finiteResidue M n j hj hn xi x v = 0 := by
  obtain ⟨q, rfl⟩ :=
    (CurveModel.OpenKummer.quotientCohomologyEquiv M n j hj hn xi).surjective x
  obtain ⟨u, hu⟩ := QuotientGroup.mk_surjective q.toMul
  have hq : q = Additive.ofMul (QuotientGroup.mk u) := hu.symm
  rw [hq, finiteResidue_comparison]
  exact M.sum_openKummerResidue_eq_zero_set (M.openBoundaryPlaces j) n u

/-- Every sum-zero boundary vector is the residue of an actual class.
A boundary point is needed here; the empty-boundary sequence is different. -/
theorem exists_finiteH1_of_sum_eq_zero
    (ε : NeronModelInfra.SchemeHomOver (𝟙 (Spec (.of K))) M.toBase)
    (v₀ : M.openBoundaryPlaces j)
    (a : M.openBoundaryPlaces j → ZMod (n : ℕ)) (ha : ∑ v, a v = 0) :
    ∃ x : FiniteKummerH1 K X n, finiteResidue M n j hj hn xi x = a := by
  obtain ⟨u, hu⟩ := M.exists_openKummerUnits_of_sum_eq_zero
    ε (M.openBoundaryPlaces j) v₀ n hn.ne_zero a ha
  refine ⟨CurveModel.OpenKummer.quotientCohomologyEquiv M n j hj hn xi
    (Additive.ofMul (QuotientGroup.mk u)), ?_⟩
  rw [finiteResidue_comparison]
  exact congrArg Multiplicative.toAdd hu

/-- Exactness at the boundary term of the actual finite-coefficient sequence. -/
theorem finiteResidue_range
    (ε : NeronModelInfra.SchemeHomOver (𝟙 (Spec (.of K))) M.toBase)
    (v₀ : M.openBoundaryPlaces j) :
    (finiteResidue M n j hj hn xi).range =
      JacobianVarieties.Kummer.boundaryResidueGroup (M.openBoundaryPlaces j) n := by
  ext a
  constructor
  · rintro ⟨x, rfl⟩
    exact sum_finiteResidue_eq_zero M n j hj hn xi x
  · intro ha
    exact exists_finiteH1_of_sum_eq_zero M n j hj hn xi ε v₀ a ha

end AnabelianGeometry.WeightFiltration
