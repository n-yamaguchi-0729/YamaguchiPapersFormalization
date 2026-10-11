/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Normalization.GenericFieldSource
import Nyll.SchemeTheory.FunctionFields.Functoriality

/-! # Naturality of the actual generic-field source identification -/

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace EtaleFundamentalGroups

universe u

private theorem eqToHom_stalk_eq_specializes
    (X : Scheme.{u}) {x y : X} (h : x = y) :
    eqToHom (congrArg (fun z => X.presheaf.stalk z) h) =
      X.presheaf.stalkSpecializes (specializes_of_eq h.symm) := by
  subst y
  simp only [eqToHom_refl, TopCat.Presheaf.stalkSpecializes_refl]

/-- The canonical function-field map is compatible with the original
generic-point morphisms of schemes. -/
theorem Spec_functionFieldMap_fromSpecStalk
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (f : Y ⟶ X) (hf : DenseRange f) :
    Spec.map (CommRingCat.ofHom (f.functionFieldMap hf)) ≫
        X.fromSpecStalk (genericPoint X) =
      Y.fromSpecStalk (genericPoint Y) ≫ f := by
  unfold Scheme.Hom.functionFieldMap
  change Spec.map (eqToHom _ ≫ f.stalkMap (genericPoint Y)) ≫
    X.fromSpecStalk (genericPoint X) = _
  rw [eqToHom_stalk_eq_specializes X
    (f.map_genericPoint_of_denseRange hf).symm,
    Spec.map_comp, Category.assoc, Scheme.SpecMap_stalkSpecializes_fromSpecStalk,
    Scheme.SpecMap_stalkMap_fromSpecStalk]


/-- Composition of the literal function-field maps, detected at the
actual generic-point morphism. -/
theorem functionFieldMap_comp_of_dense
    {X Y Z : Scheme.{u}} [IsIntegral X] [IsIntegral Y] [IsIntegral Z]
    (f : Y ⟶ X) (hf : DenseRange f) (g : Z ⟶ Y) (hg : DenseRange g) :
    let hgf : DenseRange (g ≫ f) := hf.comp hg f.continuous
    (g.functionFieldMap hg).comp (f.functionFieldMap hf) =
      (g ≫ f).functionFieldMap hgf := by
  intro hgf
  have h : CommRingCat.ofHom ((g.functionFieldMap hg).comp (f.functionFieldMap hf)) =
      CommRingCat.ofHom ((g ≫ f).functionFieldMap hgf) := by
    apply Spec.map_injective
    apply (cancel_mono (X.fromSpecStalk (genericPoint X))).mp
    change Spec.map (CommRingCat.ofHom (f.functionFieldMap hf) ≫
      CommRingCat.ofHom (g.functionFieldMap hg)) ≫ _ = _
    rw [Spec.map_comp, Category.assoc, Spec_functionFieldMap_fromSpecStalk f hf,
      ← Category.assoc, Spec_functionFieldMap_fromSpecStalk g hg,
      Category.assoc, Spec_functionFieldMap_fromSpecStalk (g ≫ f) hgf]
  exact congrArg CommRingCat.Hom.hom h

/-- Identifying an actual generic field source with the function field of
its target respects the actual extension map from the base. -/
theorem genericFieldSourceRingEquiv_comp_functionFieldMap
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (f : Y ⟶ X) (hf : DenseRange f)
    {L : Type u} [Field L] [Algebra X.functionField L]
    (p : Spec (.of L) ⟶ Y) [IsDominant p] [IsPreimmersion p]
    (hp : p ≫ f = Spec.map (CommRingCat.ofHom (algebraMap X.functionField L)) ≫
      X.fromSpecStalk (genericPoint X)) :
    (genericFieldSourceRingEquiv p).toRingHom.comp (f.functionFieldMap hf) =
      algebraMap X.functionField L := by
  have hr : Spec.map (CommRingCat.ofHom (genericFieldSourceRingEquiv p).toRingHom) ≫
      Y.fromSpecStalk (genericPoint Y) = p :=
    genericFieldSourceIso_hom_fromSpecStalk p
  have hcat : CommRingCat.ofHom
      ((genericFieldSourceRingEquiv p).toRingHom.comp (f.functionFieldMap hf)) =
      CommRingCat.ofHom (algebraMap X.functionField L) := by
    apply Spec.map_injective
    apply (cancel_mono (X.fromSpecStalk (genericPoint X))).mp
    rw [show CommRingCat.ofHom
        ((genericFieldSourceRingEquiv p).toRingHom.comp (f.functionFieldMap hf)) =
        CommRingCat.ofHom (f.functionFieldMap hf) ≫
          CommRingCat.ofHom (genericFieldSourceRingEquiv p).toRingHom from rfl,
      Spec.map_comp, Category.assoc, Spec_functionFieldMap_fromSpecStalk f hf,
      ← Category.assoc, hr, hp]
  exact congrArg CommRingCat.Hom.hom hcat

/-- An actual root in the generic source field becomes an actual root in
the covering scheme's function field under this proved comparison. -/
theorem genericFieldSourceRingEquiv_symm_pow
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (f : Y ⟶ X) (hf : DenseRange f)
    {L : Type u} [Field L] [Algebra X.functionField L]
    (p : Spec (.of L) ⟶ Y) [IsDominant p] [IsPreimmersion p]
    (hp : p ≫ f = Spec.map (CommRingCat.ofHom (algebraMap X.functionField L)) ≫
      X.fromSpecStalk (genericPoint X))
    (a : X.functionField) (b : L) (n : ℕ)
    (hb : b ^ n = algebraMap X.functionField L a) :
    ((genericFieldSourceRingEquiv p).symm b) ^ n = f.functionFieldMap hf a := by
  apply (genericFieldSourceRingEquiv p).injective
  rw [map_pow, RingEquiv.apply_symm_apply, hb]
  exact (DFunLike.congr_fun
    (genericFieldSourceRingEquiv_comp_functionFieldMap f hf p hp) a).symm

end EtaleFundamentalGroups
