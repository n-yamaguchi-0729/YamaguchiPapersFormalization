/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AlgebraicCurves.Models.Basic
import Mathlib.AlgebraicGeometry.Stalk
import Mathlib.AlgebraicGeometry.Pullbacks

/-!
# The actual geometric generic point on a scalar-extension curve

The structure morphism at the generic stalk is the spectrum of the actual
base-field embedding. The pullback universal property then constructs the
rational point over an extension of the function field.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicCurve

/-- The generic point lies over the actual base-field homomorphism into
the function field. -/
theorem fromSpecStalk_generic_comp_toBase
    {K : Type} [Field K] {X : Scheme} [IsIntegral X]
    (c : X ⟶ Spec (.of K)) :
    X.fromSpecStalk (genericPoint X) ≫ c =
      Spec.map (CommRingCat.ofHom (baseToFunctionField c)) := by
  have h :
      X.fromSpecStalk (genericPoint X) ≫ c ≫ (Spec (.of K)).toSpecΓ =
        Spec.map (X.presheaf.germ ⊤ (genericPoint X) trivial) ≫
          Spec.map c.appTop := by
    rw [Scheme.toSpecΓ_naturality, Scheme.fromSpecStalk_toSpecΓ_assoc]
  rw [← SpecMap_ΓSpecIso_hom] at h
  calc
    X.fromSpecStalk (genericPoint X) ≫ c =
        (Spec.map (X.presheaf.germ ⊤ (genericPoint X) trivial) ≫
          Spec.map c.appTop) ≫ Spec.map (Scheme.ΓSpecIso (.of K)).inv := by
      rw [← h, Category.assoc, Category.assoc, ← Spec.map_comp,
        Iso.inv_hom_id, Spec.map_id, Category.comp_id]
    _ = Spec.map (CommRingCat.ofHom (baseToFunctionField c)) := by
      rw [← Spec.map_comp, ← Spec.map_comp]
      rfl

namespace CurveModel

/-- Construct the actual geometric generic point as a rational point of
the scalar-extension curve, with its exact projection. -/
theorem exists_geometricGenericPoint
    {K F Ω F' : Type} [Field K] [Field F] [Algebra K F]
    [Field Ω] [Algebra K Ω] [Field F'] [Algebra Ω F']
    (M₀ : CurveModel K F) (M : CurveModel Ω F')
    (e : M.C ≅ pullback M₀.toBase
      (Spec.map (CommRingCat.ofHom (algebraMap K Ω))))
    (he : e.hom ≫ pullback.snd M₀.toBase
      (Spec.map (CommRingCat.ofHom (algebraMap K Ω))) = M.toBase)
    (ι : M₀.C.functionField →+* Ω)
    (hι : ∀ a : K, ι (baseToFunctionField M₀.toBase a) = algebraMap K Ω a) :
    ∃ x : {q : Spec (.of Ω) ⟶ M.C // q ≫ M.toBase = 𝟙 _},
      x.1 ≫ e.hom ≫ pullback.fst M₀.toBase
          (Spec.map (CommRingCat.ofHom (algebraMap K Ω))) =
        Spec.map (CommRingCat.ofHom ι) ≫ M₀.C.fromSpecStalk (genericPoint M₀.C) := by
  let s := Spec.map (CommRingCat.ofHom (algebraMap K Ω))
  let q := Spec.map (CommRingCat.ofHom ι) ≫
    M₀.C.fromSpecStalk (genericPoint M₀.C)
  have hq : q ≫ M₀.toBase = s := by
    change (Spec.map (CommRingCat.ofHom ι) ≫
      M₀.C.fromSpecStalk (genericPoint M₀.C)) ≫ M₀.toBase = s
    rw [Category.assoc, fromSpecStalk_generic_comp_toBase,
      ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    apply congrArg (fun a : K →+* Ω => Spec.map (CommRingCat.ofHom a))
    exact RingHom.ext hι
  let l : Spec (.of Ω) ⟶ pullback M₀.toBase s :=
    pullback.lift q (𝟙 (Spec (.of Ω))) (hq.trans (Category.id_comp s).symm)
  have hl : (l ≫ e.inv) ≫ M.toBase = 𝟙 (Spec (.of Ω)) := by
    rw [Category.assoc, ← he, e.inv_hom_id_assoc]
    exact pullback.lift_snd _ _ _
  refine ⟨⟨l ≫ e.inv, hl⟩, ?_⟩
  change (l ≫ e.inv) ≫ e.hom ≫ pullback.fst M₀.toBase s = q
  rw [Category.assoc, e.inv_hom_id_assoc]
  exact pullback.lift_fst _ _ _

end CurveModel

/-- Absolute Galois automorphisms fix the actual generic projection. -/
theorem generic_projection_fixed
    {X : Scheme} [IsIntegral X] {Ω : Type} [Field Ω]
    [Algebra X.functionField Ω] (σ : Ω ≃ₐ[X.functionField] Ω) :
    Spec.map (CommRingCat.ofHom σ.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap X.functionField Ω)) ≫
        X.fromSpecStalk (genericPoint X) =
      Spec.map (CommRingCat.ofHom (algebraMap X.functionField Ω)) ≫
        X.fromSpecStalk (genericPoint X) := by
  have h :
      Spec.map (CommRingCat.ofHom σ.toRingHom) ≫
        Spec.map (CommRingCat.ofHom (algebraMap X.functionField Ω)) =
      Spec.map (CommRingCat.ofHom (algebraMap X.functionField Ω)) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    apply congrArg (fun a : X.functionField →+* Ω => Spec.map (CommRingCat.ofHom a))
    exact RingHom.ext σ.commutes
  rw [← Category.assoc, h]

end AlgebraicCurve
