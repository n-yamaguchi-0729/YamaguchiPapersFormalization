/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Picard.UnpointedPointedGroup
import Nyll.JacobianVarieties.Picard.Existence
import Nyll.JacobianVarieties.Albanese.AbelJacobiMorphismDetectionField
import Nyll.AlgebraicCurves.Geometry.AbelianSchemes.AbelianSchemePropertyBundle
import Nyll.AlgebraicCurves.Geometry.Picard.RelativeGroupLaw
import Nyll.AlgebraicCurves.Geometry.Curves.GeometricallyIrreducible_geometricallyConnected
import Nyll.AlgebraicCurves.Geometry.Curves.geometricallyIntegral_of_smooth_of_geometricallyConnected

/-!
# Abel–Jacobi maps into one unpointed Jacobian

Every basepoint gives an actual point-minus-basepoint classifying morphism into
the same Jacobian constructed without a rational point. The fixed comparison of
Picard representations transports both the morphism and its identity formula.
-/

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.RelPicard
open NeronModelInfra GoodReductionJacobian

noncomputable section

namespace JacobianVarieties.Picard.Unpointed

variable {K : Type u} [Field K] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of K))
  [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIrreducible c]
  (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) c)

local instance curveIntegral : GeometricallyIntegral c := by
  have _ : GeometricallyConnected c := GeometricallyIrreducible.geometricallyConnected c
  exact geometricallyIntegral_of_smooth_of_geometricallyConnected c

/-- All chosen pointed data are supplied by actual Picard existence and the
proved point-minus-basepoint construction. -/
structure PointedAbelJacobiData where
  /-- The Picard scheme supplied by pointed representability. -/
  designation : RelativePic0Designation K c
  /-- Its classification of actual rigidified line bundles. -/
  representation : RepresentsRelSubPic c ε (algEquivZeroCut c ε) designation
  /-- The constructed point-minus-basepoint morphism. -/
  map : SchemeHomOver c designation.toBase
  /-- The original basepoint is carried to the Picard zero section. -/
  basepoint : ε.1 ≫ map.1 = designation.zeroSection
  /-- The actual Poincare class is the point-minus-basepoint line bundle. -/
  pointClass : ∀ (L : Type u) [Field L] (t : Spec (CommRingCat.of L) ⟶ Spec (CommRingCat.of K))
      (x : SchemeHomOver t c),
    Nonempty ((representation.poincare.pullbackAlong
        ⟨x.1 ≫ map.1, (Category.assoc _ _ _).trans ((congrArg (x.1 ≫ ·) map.2).trans x.2)⟩).L ≅
      (RelEffCartierDiv.ofPoint c x.1 x.2).lineBundle ⊗
        (RelEffCartierDiv.ofPoint c (t ≫ ε.1)
          ((Category.assoc _ _ _).trans
              ((congrArg (t ≫ ·) ε.2).trans (Category.comp_id t)))).idealModule)
  /-- Rigidity and geometric point generation detect every pointed factorization
  through this same constructed morphism. -/
  factorization_unique : ∀ (B : Scheme.{u}) (b : B ⟶ Spec (CommRingCat.of K))
      (G : RelativeGroupLaw K b), AbelianSchemePropertyBundle K b →
      ∀ (q : SchemeHomOver c b),
        NeronModelInfra.schemeHomOverComp ε q = G.one (𝟙 (Spec (CommRingCat.of K))) →
        ∀ (φ ψ : SchemeHomOver designation.toBase b),
          map.1 ≫ φ.1 = q.1 → map.1 ≫ ψ.1 = q.1 → φ = ψ

theorem nonempty_pointedAbelJacobiData : Nonempty (PointedAbelJacobiData c ε) := by
  obtain ⟨D, ⟨h⟩, hs, hp, hg⟩ := exists_representsRelSubPic_of_field K c ε
  obtain ⟨_, aj, _, _, hz, hclass, hdetect⟩ :=
    exists_abelJacobi_detects_pointed_factorizations_of_field K c ε D h hs hp hg
  exact ⟨⟨D, h, aj, hz, hclass, hdetect⟩⟩

/-- One choice of the actual pointed construction for a specified basepoint. -/
def pointedAbelJacobiData : PointedAbelJacobiData c ε :=
  Classical.choice (nonempty_pointedAbelJacobiData c ε)

/-- The comparison used to transport the actual pointed construction. -/
def abelJacobiComparison : Jacobian K c ≅ (pointedAbelJacobiData c ε).designation.P :=
  pointedComparison c ε (pointedAbelJacobiData c ε).representation

/-- The actual Abel–Jacobi map into the Jacobian whose carrier is independent
of the selected rational basepoint. -/
def abelJacobi : SchemeHomOver c (toBase K c) := by
  let M : PointedAbelJacobiData c ε := pointedAbelJacobiData c ε
  let e : Jacobian K c ≅ M.designation.P := abelJacobiComparison c ε
  have he : e.inv ≫ toBase K c = M.designation.toBase := by
    rw [← pointedComparison_over c ε M.representation]
    exact e.inv_hom_id_assoc _
  exact ⟨M.map.1 ≫ e.inv, by rw [Category.assoc, he]; exact M.map.2⟩

theorem abelJacobi_comp_comparison :
    (abelJacobi c ε).1 ≫ (abelJacobiComparison c ε).hom =
      (pointedAbelJacobiData c ε).map.1 := by
  change ((pointedAbelJacobiData c ε).map.1 ≫ (abelJacobiComparison c ε).inv) ≫
    (abelJacobiComparison c ε).hom = _
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- The selected basepoint maps to the identity of the same fixed group law. -/
theorem abelJacobi_basepoint :
    ε.1 ≫ (abelJacobi c ε).1 = ((groupLaw K c).one (𝟙 (Spec (CommRingCat.of K)))).1 := by
  apply (cancel_mono (abelJacobiComparison c ε).hom).1
  rw [Category.assoc, abelJacobi_comp_comparison]
  exact (pointedAbelJacobiData c ε).basepoint.trans
    (pointedComparison_zero c ε (pointedAbelJacobiData c ε).representation).symm

/-- After the actual Picard comparison, every field-valued point classifies
the line bundle of that point minus the chosen basepoint. -/
theorem abelJacobi_classifies_point_difference
    (L : Type u) [Field L] (t : Spec (CommRingCat.of L) ⟶ Spec (CommRingCat.of K))
    (x : SchemeHomOver t c) :
    let M := pointedAbelJacobiData c ε
    let z : SchemeHomOver t M.designation.toBase :=
      ⟨x.1 ≫ (abelJacobi c ε).1 ≫ (abelJacobiComparison c ε).hom, by
        rw [abelJacobi_comp_comparison, Category.assoc, M.map.2, x.2]⟩
    Nonempty ((M.representation.poincare.pullbackAlong z).L ≅
      (RelEffCartierDiv.ofPoint c x.1 x.2).lineBundle ⊗
        (RelEffCartierDiv.ofPoint c (t ≫ ε.1)
          ((Category.assoc _ _ _).trans
            ((congrArg (t ≫ ·) ε.2).trans (Category.comp_id t)))).idealModule) := by
  intro M z
  have hz : z = ⟨x.1 ≫ M.map.1,
      (Category.assoc _ _ _).trans ((congrArg (x.1 ≫ ·) M.map.2).trans x.2)⟩ := by
    apply Subtype.ext
    exact congrArg (x.1 ≫ ·) (abelJacobi_comp_comparison c ε)
  rw [hz]
  exact M.pointClass L t x

/-- Every pointed map has at most one factorization through the actual selected
Abel–Jacobi map into the fixed unpointed Jacobian. -/
theorem abelJacobi_factorization_unique
    {B : Scheme.{u}} (b : B ⟶ Spec (CommRingCat.of K))
    (G : RelativeGroupLaw K b) (hB : AbelianSchemePropertyBundle K b)
    (q : SchemeHomOver c b)
    (hq : NeronModelInfra.schemeHomOverComp ε q = G.one (𝟙 (Spec (CommRingCat.of K))))
    (φ ψ : SchemeHomOver (toBase K c) b)
    (hφ : (abelJacobi c ε).1 ≫ φ.1 = q.1)
    (hψ : (abelJacobi c ε).1 ≫ ψ.1 = q.1) : φ = ψ := by
  let M : PointedAbelJacobiData c ε := pointedAbelJacobiData c ε
  let e : Jacobian K c ≅ M.designation.P := abelJacobiComparison c ε
  have he : e.inv ≫ toBase K c = M.designation.toBase := by
    rw [← pointedComparison_over c ε M.representation]
    exact e.inv_hom_id_assoc _
  let φ' : SchemeHomOver M.designation.toBase b :=
    ⟨e.inv ≫ φ.1, by rw [Category.assoc, φ.2, he]⟩
  let ψ' : SchemeHomOver M.designation.toBase b :=
    ⟨e.inv ≫ ψ.1, by rw [Category.assoc, ψ.2, he]⟩
  have hφ' : M.map.1 ≫ φ'.1 = q.1 := by
    change M.map.1 ≫ e.inv ≫ φ.1 = q.1
    exact (Category.assoc _ _ _).symm.trans hφ
  have hψ' : M.map.1 ≫ ψ'.1 = q.1 := by
    change M.map.1 ≫ e.inv ≫ ψ.1 = q.1
    exact (Category.assoc _ _ _).symm.trans hψ
  have h := M.factorization_unique B b G hB q hq φ' ψ' hφ' hψ'
  apply Subtype.ext
  apply (cancel_epi e.inv).1
  exact congrArg Subtype.val h

end JacobianVarieties.Picard.Unpointed
