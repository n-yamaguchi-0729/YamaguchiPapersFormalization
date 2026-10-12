/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Albanese.GenusOneAbelJacobiIsomorphism
import Nyll.JacobianVarieties.Picard.RepresentsRelSubPicGroup
import Nyll.JacobianVarieties.Picard.Designation
import Nyll.JacobianVarieties.Picard.Representation
import Nyll.AlgebraicCurves.Cohomology.Finite_H0_H1_structureSheaf_of_isAlgClosed
import Nyll.AlgebraicCurves.Geometry.Curves.SmoothProperCurve_exists_curveModel_iso_germToFunctionField_eq_of_isAlgClosed
import Nyll.AlgebraicCurves.Geometry.Picard.AlgEquivZeroGroupCut
import Nyll.AlgebraicCurves.Geometry.Schemes.SchemeHomOver
import Nyll.AlgebraicCurves.Geometry.AbelianSchemes.AbelianSchemePropertyBundle
import Nyll.AlgebraicCurves.Geometry.AbelianSchemes.Theorems.RelativeGroupLaw_comp_mul_eq_mul_comp_of_comp_one_eq_one_of_abelianSchemePropertyBundle

/-!
# The Albanese variety of a genus-one curve

The actual structure-sheaf cohomology comparison constructs a genus-one curve
model. Its actual Abel--Jacobi isomorphism supplies a proper smooth connected
commutative group. Inverting this same isomorphism constructs every pointed
Albanese factorization; the proved rigidity theorem gives its group law.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicCurve NeronModelInfra
open GoodReductionJacobian AlgebraicGeometry.RelPicard

namespace JacobianVarieties.Albanese

/-- A pointed smooth proper integral genus-one curve, with genus measured by
actual coherent cohomology, has an actual Albanese isomorphism, and every pointed
morphism to an abelian variety factors uniquely as a homomorphism. -/
theorem exists_albanese_isIso_of_finrank_H1_eq_one
    {K : Type} [Field K] [IsAlgClosed K] [CharZero K]
    (X : Scheme) [IsIntegral X] (c : X ⟶ Spec (.of K))
    [IsProper c] [SmoothOfRelativeDimension 1 c] (V : X.TwoAffineOpenCover)
    (hg : Module.finrank K (V.structureSheafSections c).H1 = 1)
    (ε : SchemeHomOver (𝟙 (Spec (.of K))) c) :
    ∃ (A : Scheme) (f : A ⟶ Spec (.of K)) (G : RelativeGroupLaw K f),
      G.IsCommutative ∧ ∃ aj : SchemeHomOver c f,
      Smooth f ∧ IsProper f ∧ GeometricallyConnected f ∧ IsIso aj.1 ∧
      ε.1 ≫ aj.1 = (G.one (𝟙 (Spec (.of K)))).1 ∧
      ∀ (B : Scheme) (b : B ⟶ Spec (.of K)) (H : RelativeGroupLaw K b),
        AbelianSchemePropertyBundle K b →
        ∀ (q : SchemeHomOver c b),
          NeronModelInfra.schemeHomOverComp ε q = H.one (𝟙 (Spec (.of K))) →
          ∃! φ : SchemeHomOver f b,
            aj.1 ≫ φ.1 = q.1 ∧
            ∀ {T : Scheme} (t : T ⟶ Spec (.of K)) (x y : SchemeHomOver t f),
              NeronModelInfra.schemeHomOverComp (G.mul t x y) φ =
                H.mul t (NeronModelInfra.schemeHomOverComp x φ)
                  (NeronModelInfra.schemeHomOverComp y φ) := by
  let fieldAlgebra : Algebra K X.functionField := (baseToFunctionField c).toAlgebra
  have comparison : Module.finrank K (V.structureSheafSections c).H1 =
      genusFF K X.functionField := (finite_H0_H1_structureSheaf_of_isAlgClosed V c).2.2.2
  have genusOne : genusFF K X.functionField = 1 := comparison.symm.trans hg
  obtain ⟨fieldCurve, fieldFiniteType, M, i, hi, _⟩ :=
    SmoothProperCurve.exists_curveModel_iso_germToFunctionField_eq_of_isAlgClosed K X c
  let s : SchemeHomOver (𝟙 (Spec (.of K))) M.toBase :=
    ⟨ε.1 ≫ i.inv, by rw [Category.assoc, ← hi, i.inv_hom_id_assoc]; exact ε.2⟩
  obtain ⟨D, hD, a, hsm, hpr, hgc, ha, hiso⟩ :=
    M.exists_abelJacobi_isIso_of_genus_one genusOne s
  let hG : RepresentsRelSubPic M.toBase s
      (algEquivZeroGroupCut M.toBase s).toSubPicCondition D := hD
  let G : RelativeGroupLaw K D.toBase := hG.relativeGroupLaw
  have hc : G.IsCommutative := hG.relativeGroupLaw_isCommutative
  have : Smooth D.toBase := hsm
  have : IsProper D.toBase := hpr
  have : GeometricallyConnected D.toBase := hgc
  have : IsIso a.1 := hiso
  have : ConnectedSpace D.P := GeometricallyConnected.connectedSpace D.toBase D.toBase.isOpenMap
  let aj : SchemeHomOver c D.toBase :=
    ⟨i.inv ≫ a.1, by rw [Category.assoc, a.2, ← hi, i.inv_hom_id_assoc]⟩
  have hajiso : IsIso aj.1 := inferInstanceAs (IsIso (i.inv ≫ a.1))
  have hajε : ε.1 ≫ aj.1 = (G.one (𝟙 (Spec (.of K)))).1 := by
    change ε.1 ≫ (i.inv ≫ a.1) = _
    rw [← Category.assoc]
    exact ha.trans hG.relativeGroupLaw_one.symm
  refine ⟨D.P, D.toBase, G, hc, aj, hsm, hpr, hgc, hajiso, hajε, ?_⟩
  intro B b H hB q hq
  let φ : SchemeHomOver D.toBase b :=
    ⟨inv aj.1 ≫ q.1, by
      rw [Category.assoc, q.2]
      exact (congrArg (fun r : X ⟶ Spec (.of K) => inv aj.1 ≫ r) aj.2.symm).trans
        (IsIso.inv_hom_id_assoc aj.1 D.toBase)⟩
  have hφ : NeronModelInfra.schemeHomOverComp (G.one (𝟙 (Spec (.of K)))) φ =
      H.one (𝟙 (Spec (.of K))) := by
    apply Subtype.ext
    change (G.one (𝟙 (Spec (.of K)))).1 ≫ (inv aj.1 ≫ q.1) = _
    rw [← hajε, Category.assoc, IsIso.hom_inv_id_assoc]
    exact congrArg Subtype.val hq
  refine ⟨φ, ⟨?_, ?_⟩, ?_⟩
  · change aj.1 ≫ (inv aj.1 ≫ q.1) = q.1
    exact IsIso.hom_inv_id_assoc aj.1 q.1
  · exact G.comp_mul_eq_mul_comp_of_comp_one_eq_one_of_abelianSchemePropertyBundle
      K H hB φ hφ
  · intro ψ hψ
    apply Subtype.ext
    apply (cancel_epi aj.1).mp
    exact hψ.1.trans (IsIso.hom_inv_id_assoc aj.1 q.1).symm

end JacobianVarieties.Albanese
