/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import EtaleFundamentalGroups.FiniteEtale.FiniteField.PureInseparableAffine
import EtaleFundamentalGroups.FiniteEtale.FiniteField.AffineSchemeModel

/-!
# Affine descent across purely inseparable constant extensions
-/

noncomputable section
universe u
open CategoryTheory Limits AlgebraicGeometry
namespace EtaleFundamentalGroups

/-- A finite étale cover of an affine scheme descends across an arbitrary
purely inseparable extension of constants. -/
theorem exists_affine_model_of_purelyInseparable_extension
    (k L : Type u) [Field k] [Field L] [Algebra k L] [IsPurelyInseparable k L]
    (X : Scheme.{u}) [IsAffine X] (f : X ⟶ Spec (.of k))
    (Z : FiniteEtale (pullback (Spec.map (CommRingCat.ofHom (algebraMap k L))) f)) :
    ∃ M : FiniteEtale X,
      Nonempty ((FiniteEtale.pullback
        (pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap k L))) f)).obj M ≅ Z) := by
  obtain ⟨H, hH, N, ⟨e⟩⟩ := FiniteEtale.exists_finiteIntermediateField_affine_scheme_model k L X f Z
  let : FiniteDimensional k H := hH
  obtain ⟨M, ⟨eH⟩⟩ := exists_affine_purelyInseparable_model k H X f N
  let φL := Spec.map (CommRingCat.ofHom (algebraMap k L))
  let φH := Spec.map (CommRingCat.ofHom (algebraMap k H))
  let c : pullback φL f ⟶ pullback φH f :=
    pullback.map φL f φH f (Spec.map (CommRingCat.ofHom H.val.toRingHom))
      (𝟙 X) (𝟙 _) (by rw [Category.comp_id, ← Spec.map_comp]; rfl)
      (by rw [Category.comp_id, Category.id_comp])
  have hc : c ≫ pullback.snd φH f = pullback.snd φL f := by
    simp only [c, pullback.map, pullback.lift_snd, Category.comp_id]
  refine ⟨M, ⟨?_⟩⟩
  exact (FiniteEtale.finiteEtalePullbackCompObjIso c (pullback.snd φH f)
    (pullback.snd φL f) hc M).symm ≪≫
      (FiniteEtale.pullback c).mapIso eH ≪≫ e

end EtaleFundamentalGroups
