/-
Copyright (c) 2026 Naganori Yamaguchi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
https://github.com/n-yamaguchi-0729
-/

import Nyll.JacobianVarieties.Picard.UnpointedAbelJacobi
import Nyll.JacobianVarieties.Albanese.AlbaneseFactorizationField
import Nyll.JacobianVarieties.Albanese.AbelJacobiPointClassUnique
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Nyll.AlgebraicCurves.Geometry.Picard.RelativeGroupLawGrpObj
import Nyll.AlgebraicCurves.Geometry.Curves.GeometricallyIrreducible_geometricallyConnected
import Nyll.AlgebraicCurves.Geometry.Curves.geometricallyIntegral_of_smooth_of_geometricallyConnected
import Nyll.AlgebraicCurves.Geometry.Schemes.SchemeHomOver
import Nyll.AlgebraicCurves.Geometry.AbelianSchemes.AbelianSchemePropertyBundle
import Nyll.AlgebraicCurves.Geometry.Picard.RelativeGroupLaw

/-! The actual Albanese factorization for the fixed, unpointed Jacobian. -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard
open NeronModelInfra GoodReductionJacobian

namespace JacobianVarieties.Picard.Unpointed

theorem exists_unique_abelJacobi_factorization
    {K : Type u} [Field K] {C : Scheme.{u}}
    (c : C ⟶ Spec (CommRingCat.of K)) [IsProper c]
    [SmoothOfRelativeDimension 1 c] [GeometricallyIrreducible c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) c)
    {B : Scheme.{u}} (b : B ⟶ Spec (CommRingCat.of K))
    [Smooth b] [IsProper b] [GeometricallyIntegral b]
    (G : RelativeGroupLaw K b) (q : SchemeHomOver c b)
    (hq : NeronModelInfra.schemeHomOverComp ε q = G.one (𝟙 _)) :
    ∃! φ : SchemeHomOver (toBase K c) b, (abelJacobi c ε).1 ≫ φ.1 = q.1 := by
  have : GeometricallyConnected c := GeometricallyIrreducible.geometricallyConnected c
  have : GeometricallyIntegral c := geometricallyIntegral_of_smooth_of_geometricallyConnected c
  have : Smooth (toBase K c) := smooth K c
  have : IsProper (toBase K c) := proper K c
  let M : PointedAbelJacobiData c ε := pointedAbelJacobiData c ε
  let e : Jacobian K c ≅ M.designation.P := abelJacobiComparison c ε
  have he : e.hom ≫ M.designation.toBase = toBase K c :=
    pointedComparison_over c ε M.representation
  have hei : e.inv ≫ toBase K c = M.designation.toBase := by
    rw [← he, e.inv_hom_id_assoc]
  have : Smooth M.designation.toBase := by rw [← hei]; infer_instance
  have : IsProper M.designation.toBase := by rw [← hei]; infer_instance
  obtain ⟨aj, -, hclass, hfactor⟩ :=
    JacobianVarieties.Albanese.exists_abelJacobi_factorization_of_field c ε
      M.designation M.representation
  have haj : aj = M.map := abelJacobi_eq_of_geometric_point_class K c ε
    M.designation M.representation (AlgebraicClosure K) aj M.map
    (hclass (AlgebraicClosure K) _) (M.pointClass (AlgebraicClosure K) _)
  obtain ⟨ψ, hψ⟩ := hfactor B b G q hq
  rw [haj] at hψ
  let φ : SchemeHomOver (toBase K c) b :=
    ⟨e.hom ≫ ψ.1, by rw [Category.assoc, ψ.2, he]⟩
  have hφ : (abelJacobi c ε).1 ≫ φ.1 = q.1 := by
    change (abelJacobi c ε).1 ≫ e.hom ≫ ψ.1 = q.1
    rw [← Category.assoc, abelJacobi_comp_comparison]
    exact hψ
  have : GeometricallyConnected b := GeometricallyIrreducible.geometricallyConnected b
  let hB : AbelianSchemePropertyBundle K b :=
    ⟨inferInstance, inferInstance, b.isConnected_preimage_singleton, ⟨G⟩⟩
  refine ⟨φ, hφ, ?_⟩
  intro φ' hφ'
  exact abelJacobi_factorization_unique c ε b G hB q hq φ' φ hφ' hφ

end JacobianVarieties.Picard.Unpointed
