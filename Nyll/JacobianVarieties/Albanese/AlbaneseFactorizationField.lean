/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Albanese.SeparableAlbaneseFactorization
import Nyll.JacobianVarieties.Albanese.AlbaneseSeparableDescent
import Nyll.JacobianVarieties.Albanese.AbelJacobiPointClassUnique
import Nyll.JacobianVarieties.Picard.AbelJacobiPointClassBaseChange
import Nyll.JacobianVarieties.Picard.Exists_representsRelSubPic_baseChange
import Nyll.JacobianVarieties.Picard.Exists_abelJacobi_of_representsRelSubPic
import Nyll.JacobianVarieties.Pic0.RelativePic0DesignationBaseChange
import Nyll.JacobianVarieties.Picard.Representation
import Nyll.JacobianVarieties.Picard.Smooth_of_representsRelSubPic_algEquivZeroCut_of_finiteMapData
import Nyll.JacobianVarieties.Picard.IsProper_and_geometricallyConnected_of_representsRelSubPic_algEquivZeroCut_of_finiteMapData
import Nyll.AlgebraicCurves.Geometry.Curves.SmoothProperCurveBase
import Nyll.AlgebraicCurves.Geometry.Curves.SmoothProperCurve_exists_finiteMapData_le_isUnit
import Nyll.AlgebraicCurves.Geometry.Curves.SmoothProperCurve_exists_genus_forall_geometricFibre_riemannRoch_imp_eq_of_finiteMapData
import Nyll.AlgebraicCurves.Geometry.Schemes.SchemeHomOverBaseChange
import Nyll.AlgebraicCurves.Geometry.Schemes.isReduced_of_smooth_of_field
import Nyll.AlgebraicCurves.Geometry.AbelianSchemes.GroupLaw.BaseChange
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-! # Actual Abel--Jacobi factorization over an arbitrary field

The factorization over a finite separable extension is identified with the
native scalar extension of one fixed Abel--Jacobi morphism. Faithfully flat
descent then gives a factorization over the original field.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve
open NeronModelInfra GoodReductionJacobian

namespace JacobianVarieties.Albanese

private theorem pointed_baseChange
    {K L : Type u} [Field K] [Field L] [Algebra K L] {C B : Scheme.{u}}
    {c : C ⟶ Spec (CommRingCat.of K)} {b : B ⟶ Spec (CommRingCat.of K)}
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) c)
    (G : RelativeGroupLaw K b) (q : SchemeHomOver c b)
    (hq : NeronModelInfra.schemeHomOverComp ε q = G.one (𝟙 _)) :
    NeronModelInfra.schemeHomOverComp (sectionBaseChange L ε)
      (fibreRestrictAlong (specMap K L) b c q) =
      (G.baseChange (specMap K L)).one (𝟙 _) := by
  apply (RelativeGroupLaw.baseChangePointEquiv (specMap K L) (𝟙 _)).injective
  change RelativeGroupLaw.baseChangePointToBase (specMap K L)
      (NeronModelInfra.schemeHomOverComp (sectionBaseChange L ε)
        (fibreRestrictAlong (specMap K L) b c q)) =
    RelativeGroupLaw.baseChangePointToBase (specMap K L)
      ((G.baseChange (specMap K L)).one (𝟙 _))
  rw [RelativeGroupLaw.baseChangePointToBase_comp_fibreRestrictAlong,
    RelativeGroupLaw.baseChangePointToBase_one]
  apply Subtype.ext
  change ((sectionBaseChange L ε).1 ≫ pullback.fst c (specMap K L)) ≫ q.1 =
    (G.one (𝟙 _ ≫ specMap K L)).1
  have hbase : ε.1 ≫ q.1 = (G.one (𝟙 _)).1 := congrArg Subtype.val hq
  rw [sectionBaseChange_coe_fst, Category.assoc, hbase]
  exact congrArg Subtype.val
    (G.one_natural (𝟙 _) (𝟙 _ ≫ specMap K L) (specMap K L)
      (by rw [Category.comp_id, Category.id_comp]))

private theorem exists_native_local_factorization
    (K : Type u) [Field K] {C : Scheme.{u}}
    (c : C ⟶ Spec (CommRingCat.of K)) [IsProper c]
    [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) c)
    (D : RelativePic0Designation K c) [Smooth D.toBase] [IsSeparated D.toBase]
    (hD : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D)
    (aj : SchemeHomOver c D.toBase)
    (hclass : ∀ (F : Type u) [Field F]
      (t : Spec (CommRingCat.of F) ⟶ Spec (CommRingCat.of K))
      (x : SchemeHomOver t c),
      Nonempty ((hD.poincare.pullbackAlong
        ⟨x.1 ≫ aj.1, (Category.assoc _ _ _).trans
          ((congrArg (x.1 ≫ ·) aj.2).trans x.2)⟩).L ≅
        (RelEffCartierDiv.ofPoint c x.1 x.2).lineBundle ⊗
          (RelEffCartierDiv.ofPoint c (t ≫ ε.1)
            ((Category.assoc _ _ _).trans
              ((congrArg (t ≫ ·) ε.2).trans (Category.comp_id t)))).idealModule))
    {B : Scheme.{u}} (b : B ⟶ Spec (CommRingCat.of K)) [Smooth b] [IsProper b]
    [GeometricallyIntegral b] (G : RelativeGroupLaw K b) (q : SchemeHomOver c b)
    (hq : NeronModelInfra.schemeHomOverComp ε q = G.one (𝟙 _)) :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra K L) (_ : Module.Finite K L)
      (_ : Algebra.IsSeparable K L)
      (ψ : SchemeHomOver (D.baseChange L).toBase (pullback.snd b (specMap K L))),
      (fibreRestrictAlong (specMap K L) D.toBase c aj).1 ≫ ψ.1 =
        (fibreRestrictAlong (specMap K L) b c q).1 := by
  obtain ⟨L, hL, hKL, hfin, hsep, hlocal⟩ :=
    exists_finite_separable_abelJacobi_factorization K c ε
  let s := specMap K L
  let cL := SmoothProperCurve.baseChange K c L
  let εL := sectionBaseChange L ε
  let bL := pullback.snd b s
  let qL : SchemeHomOver cL bL := fibreRestrictAlong s b c q
  let lawL : RelativeGroupLaw L bL := G.baseChange s
  have : IsReduced (D.baseChange L).P :=
    isReduced_of_smooth_of_field (D.baseChange L).toBase
  obtain ⟨hDL, hPL⟩ := exists_representsRelSubPic_baseChange K c ε D hD L
  obtain ⟨aj', _, hclass', hfactor⟩ := hlocal (D.baseChange L) hDL
  let ajL : SchemeHomOver cL (D.baseChange L).toBase :=
    fibreRestrictAlong s D.toBase c aj
  have hnative := abelJacobi_point_class_baseChange K c ε D hD aj hclass L hDL hPL
  have hAJ : ajL = aj' := by
    apply abelJacobi_eq_of_geometric_point_class L cL εL (D.baseChange L) hDL
      (AlgebraicClosure L) ajL aj'
    · exact hnative (AlgebraicClosure L) (specMap L (AlgebraicClosure L))
    · exact hclass' (AlgebraicClosure L) (specMap L (AlgebraicClosure L))
  obtain ⟨ψ, hψ⟩ := hfactor (pullback b s) bL lawL qL (pointed_baseChange ε G q hq)
  refine ⟨L, hL, hKL, hfin, hsep, ψ, ?_⟩
  change ajL.1 ≫ ψ.1 = qL.1
  rw [hAJ]
  exact hψ

/-- Over any field, one actual Abel--Jacobi morphism factors every pointed
morphism to a smooth proper geometrically integral group scheme. The
factorization is constructed over a finite separable extension by divisor sums
and descended to the original field. -/
theorem exists_abelJacobi_factorization_of_field
    {K : Type u} [Field K] {C : Scheme.{u}}
    (c : C ⟶ Spec (CommRingCat.of K)) [IsProper c]
    [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) c)
    (D : RelativePic0Designation K c) [LocallyOfFiniteType D.toBase]
    (hD : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D) :
    ∃ aj : SchemeHomOver c D.toBase,
      ε.1 ≫ aj.1 = D.zeroSection ∧
      (∀ (F : Type u) [Field F] (t : Spec (CommRingCat.of F) ⟶ Spec (CommRingCat.of K))
        (x : SchemeHomOver t c),
        Nonempty ((hD.poincare.pullbackAlong
          ⟨x.1 ≫ aj.1, (Category.assoc _ _ _).trans
            ((congrArg (x.1 ≫ ·) aj.2).trans x.2)⟩).L ≅
          (RelEffCartierDiv.ofPoint c x.1 x.2).lineBundle ⊗
            (RelEffCartierDiv.ofPoint c (t ≫ ε.1)
              ((Category.assoc _ _ _).trans
                ((congrArg (t ≫ ·) ε.2).trans (Category.comp_id t)))).idealModule)) ∧
      ∀ (B : Scheme.{u}) (b : B ⟶ Spec (CommRingCat.of K)) [Smooth b] [IsProper b]
        [GeometricallyIntegral b] (G : RelativeGroupLaw K b) (q : SchemeHomOver c b),
        NeronModelInfra.schemeHomOverComp ε q = G.one (𝟙 _) →
          ∃ ψ : SchemeHomOver D.toBase b, aj.1 ≫ ψ.1 = q.1 := by
  have hF : ∀ m₀ : ℕ, ∃ F : FiniteMapData c ε, m₀ ≤ F.m := by
    intro m₀
    obtain ⟨F, hm, _⟩ := exists_finiteMapData_le_isUnit K c ε m₀
    exact ⟨F, hm⟩
  have : Smooth D.toBase :=
    smooth_of_representsRelSubPic_algEquivZeroCut_of_finiteMapData K c ε hF D hD
  obtain ⟨F, _⟩ := hF 0
  obtain ⟨g, hg⟩ :=
    exists_genus_forall_geometricFibre_riemannRoch_imp_eq_of_finiteMapData K c ε F
  obtain ⟨hproper, hconnected⟩ :=
    isProper_and_geometricallyConnected_of_representsRelSubPic_algEquivZeroCut_of_finiteMapData
      K c ε hF g hg D hD
  obtain ⟨aj, haj, hclass⟩ := exists_abelJacobi_of_representsRelSubPic K c ε D hD
  refine ⟨aj, haj, hclass, ?_⟩
  intro B b _ _ _ G q hq
  obtain ⟨L, hL, hKL, hfin, hsep, ψ, hψ⟩ :=
    exists_native_local_factorization K c ε D hD aj hclass b G q hq
  exact exists_factorization_of_finite_separable_baseChange
    K c ε D hD aj hclass b G q hq L ψ hψ

end JacobianVarieties.Albanese
