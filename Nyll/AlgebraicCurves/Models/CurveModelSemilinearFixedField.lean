/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AlgebraicCurves.Models.Basic
import Nyll.AlgebraicCurves.Divisors.Semilinear

/-!
# The original function field is fixed by coefficient actions

If a geometric coefficient automorphism fixes the projection to the original
curve, its actual semilinear function-field action fixes every function
coming from that curve. The proof uses the action on germs and the actual
commutative square, not a fixed-field assumption.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped Pointwise

namespace AlgebraicCurve.CurveModel

attribute [local instance]
  AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup
  AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace

/-- The geometric projection square and germ formulas force the semilinear
action to fix the original function-field image. -/
theorem semilinear_fixes_functionField_image
    {K F : Type} [Field K] [Field F] [Algebra K F]
    (M : CurveModel K F) {X : Scheme} [IsIntegral X]
    (p : M.C ⟶ X) (hp : p.base (genericPoint M.C) = genericPoint X)
    (φ : X.functionField →+* F) (θ : M.C ≅ M.C)
    (hθ : θ.hom ≫ p = p) (g : SemilinearAut K F)
    (hφ : ∀ (U : X.Opens) [Nonempty U] [Nonempty (p ⁻¹ᵁ U)] (s : Γ(X, U)),
      φ (X.germToFunctionField U s) =
        M.ffEquiv.symm (M.C.germToFunctionField (p ⁻¹ᵁ U) ((p.app U).hom s)))
    (hg : ∀ (V : M.C.Opens) [Nonempty V] [Nonempty (θ.hom ⁻¹ᵁ V)]
      (t : Γ(M.C, V)),
      g • M.ffEquiv.symm (M.C.germToFunctionField V t) =
        M.ffEquiv.symm (M.C.germToFunctionField (θ.hom ⁻¹ᵁ V)
          ((θ.hom.app V).hom t)))
    (r : X.functionField) :
    g • φ r = φ r := by
  obtain ⟨U, hU, s, hs⟩ := X.presheaf.exists_germ_eq r
  have hne : Nonempty U := ⟨⟨genericPoint X, hU⟩⟩
  have hpre : Nonempty (p ⁻¹ᵁ U) := by
    refine ⟨⟨genericPoint M.C, ?_⟩⟩
    change p.base (genericPoint M.C) ∈ U
    rw [hp]
    exact hU
  have hpreθ : Nonempty (θ.hom ⁻¹ᵁ (p ⁻¹ᵁ U)) := by
    refine ⟨⟨genericPoint M.C, ?_⟩⟩
    change p.base (θ.hom.base (genericPoint M.C)) ∈ U
    rw [genericPoint_eq_of_isOpenImmersion θ.hom, hp]
    exact hU
  have hcomp : Nonempty ((θ.hom ≫ p) ⁻¹ᵁ U) := by
    rw [hθ]
    exact hpre
  have hs' : X.germToFunctionField U s = r := hs
  rw [← hs', hφ, hg]
  change M.ffEquiv.symm (M.C.germToFunctionField ((θ.hom ≫ p) ⁻¹ᵁ U)
    (((θ.hom ≫ p).app U).hom s)) =
      M.ffEquiv.symm (M.C.germToFunctionField (p ⁻¹ᵁ U) ((p.app U).hom s))
  have hcomparison (q : M.C ⟶ X) (hq : q = p) [Nonempty (q ⁻¹ᵁ U)] :
      M.C.germToFunctionField (q ⁻¹ᵁ U) ((q.app U).hom s) =
        M.C.germToFunctionField (p ⁻¹ᵁ U) ((p.app U).hom s) := by
    subst q
    rfl
  exact congrArg M.ffEquiv.symm (hcomparison (θ.hom ≫ p) hθ)

/-- A point whose projection is fixed by the coefficient automorphism
has a fixed place under the actual semilinear action. -/
theorem point_fixed_of_projection_fixed
    {K₀ K F : Type} [Field K₀] [Field K] [IsAlgClosed K]
    [Field F] [Algebra K F]
    (M : CurveModel K F) {C : Scheme} (c : C ⟶ Spec (.of K₀))
    (s : Spec (.of K) ⟶ Spec (.of K₀))
    (e : M.C ≅ pullback c s)
    (he : e.hom ≫ pullback.snd c s = M.toBase)
    (θ : M.C ≅ M.C) (σ : K ≃+* K) (g : SemilinearAut K F)
    (hθp : θ.hom ≫ e.hom ≫ pullback.fst c s = e.hom ≫ pullback.fst c s)
    (hθb : θ.hom ≫ M.toBase =
      M.toBase ≫ Spec.map (CommRingCat.ofHom σ.toRingHom))
    (hgpoint : ∀ x y : {q : Spec (.of K) ⟶ M.C // q ≫ M.toBase = 𝟙 _},
      y.1 ≫ θ.hom = Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ x.1 →
        M.pointEquivPlace y = g • M.pointEquivPlace x)
    (x : {q : Spec (.of K) ⟶ M.C // q ≫ M.toBase = 𝟙 _})
    (hx : Spec.map (CommRingCat.ofHom σ.toRingHom) ≫
      x.1 ≫ e.hom ≫ pullback.fst c s = x.1 ≫ e.hom ≫ pullback.fst c s) :
    g • M.pointEquivPlace x = M.pointEquivPlace x := by
  have hh : x.1 ≫ θ.hom = Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ x.1 := by
    apply (cancel_mono e.hom).mp
    apply pullback.hom_ext
    · simpa only [Category.assoc, hθp] using hx.symm
    · simp only [Category.assoc, he, hθb]
      rw [← Category.assoc, x.2, Category.id_comp, Category.comp_id]
  exact (hgpoint x x hh).symm

end AlgebraicCurve.CurveModel
