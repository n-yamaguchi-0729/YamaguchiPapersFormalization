/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import AlgebraicCurves.Models.Basic
import AlgebraicCurves.Models.CurveModel_exists_semilinearAut_baseAut_eq_and_pointEquivPlace_eq_smul
import AlgebraicCurves.Divisors.Semilinear
import AlgebraicCurves.Geometry.Curves.SmoothProperCurveBase
import AlgebraicCurves.Geometry.Schemes.SchemeHomOver
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback

/-! # Actual coefficient actions on scalar-extension curve models

The coefficient automorphism induces an isomorphism of the actual pullback curve.
Transporting this morphism through the chosen curve-model isomorphism supplies
its semilinear action on the function field, with the same action on germs and
point valuations. No Picard comparison is an input.

The imported function-field and valuation theorem retains its Anthropic FLT
provenance in its source. The pullback construction here is an original proof.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.SmoothProperCurve NeronModelInfra
open scoped Pointwise

namespace AlgebraicCurve.CurveModel

private theorem coefficient_spec_comp
    {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] (σ : Ω ≃ₐ[K] Ω) :
    Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ specMap K Ω = specMap K Ω := by
  rw [← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  ext a
  exact σ.commutes a

/-- A coefficient automorphism acts on the actual scalar-extension curve and its
function field. The action fixes the projection to the original curve and retains
the induced formulas on germs and on point valuations. -/
theorem exists_baseChange_semilinear_action
    {K Ω F : Type} [Field K] [Field Ω] [IsAlgClosed Ω] [Algebra K Ω]
    [Field F] [Algebra Ω F] {C : Scheme} (c : C ⟶ Spec (.of K))
    (M : CurveModel Ω F) (e : M.C ≅ pullback c (specMap K Ω))
    (he : e.hom ≫ pullback.snd c (specMap K Ω) = M.toBase)
    (σ : Ω ≃ₐ[K] Ω) :
    ∃ (θ : M.C ≅ M.C) (g : SemilinearAut Ω F),
      θ.hom ≫ e.hom ≫ pullback.fst c (specMap K Ω) =
        e.hom ≫ pullback.fst c (specMap K Ω) ∧
      θ.hom ≫ M.toBase = M.toBase ≫ Spec.map (CommRingCat.ofHom σ.toRingHom) ∧
      SemilinearAut.baseAut g = σ.toRingEquiv ∧
      (∀ (U : M.C.Opens) [Nonempty (Scheme.Opens.toScheme U)]
        [Nonempty (Scheme.Opens.toScheme (θ.hom ⁻¹ᵁ U))] (t : Γ(M.C, U)),
        g • M.ffEquiv.symm (M.C.germToFunctionField U t) =
          M.ffEquiv.symm (M.C.germToFunctionField (θ.hom ⁻¹ᵁ U) ((θ.hom.app U).hom t))) ∧
      ∀ x y : SchemeHomOver (𝟙 (Spec (.of Ω))) M.toBase,
        y.1 ≫ θ.hom = Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ x.1 →
          M.pointEquivPlace y = g • M.pointEquivPlace x := by
  let s := specMap K Ω
  let a := Spec.map (CommRingCat.ofHom σ.toRingHom)
  have ha : a ≫ s = s := coefficient_spec_comp σ
  have : IsIso (CommRingCat.ofHom σ.toRingHom) :=
    inferInstanceAs (IsIso σ.toRingEquiv.toCommRingCatIso.hom)
  have : IsIso a := inferInstance
  let u := pullback.map c s c s (𝟙 C) a (𝟙 (Spec (.of K)))
    (by rw [Category.id_comp, Category.comp_id])
    (by rw [Category.comp_id]; exact ha.symm)
  have hu₁ : u ≫ pullback.fst c s = pullback.fst c s := by
    rw [pullback.lift_fst, Category.comp_id]
  have hu₂ : u ≫ pullback.snd c s = pullback.snd c s ≫ a := pullback.lift_snd _ _ _
  let θ := e ≪≫ asIso u ≪≫ e.symm
  have hθbase : θ.hom ≫ M.toBase = M.toBase ≫ a := by
    change (e.hom ≫ u ≫ e.inv) ≫ M.toBase = _
    rw [Category.assoc, Category.assoc, ← he, e.inv_hom_id_assoc, hu₂,
      ← Category.assoc, he]
  obtain ⟨g, hg, hfun, hpoint⟩ :=
    M.exists_semilinearAut_baseAut_eq_and_pointEquivPlace_eq_smul
      σ.toRingEquiv θ.hom hθbase
  refine ⟨θ, g, ?_, hθbase, hg, hfun, hpoint⟩
  change (e.hom ≫ u ≫ e.inv) ≫ e.hom ≫ pullback.fst c s = _
  rw [Category.assoc, Category.assoc, e.inv_hom_id_assoc, hu₁]

end AlgebraicCurve.CurveModel
