/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_exists_iso_pullback_residue_of_iso_pullback.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-!
# exists iso pullback residue of iso pullback
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Schemes.Proofs.exists_iso_pullback_residue_of_iso_pullback

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem _root_.AlgebraicGeometry.exists_iso_pullback_residue_of_iso_pullback
    {A A₁ : Type u} [CommRing A] [IsLocalRing A] [CommRing A₁] [IsLocalRing A₁]
    (ι₁ : A₁ →+* A) [IsLocalHom ι₁] (hres₁ : Function.Surjective ((IsLocalRing.residue A).comp ι₁))
    {X X₁ : Scheme.{u}} (toBase : X ⟶ Spec (CommRingCat.of A)) (f₁ : X₁ ⟶ Spec (CommRingCat.of A₁))
    (e₁ : X ≅ pullback f₁ (Spec.map (CommRingCat.ofHom ι₁)))
    (he₁ : e₁.hom ≫ pullback.snd f₁ (Spec.map (CommRingCat.ofHom ι₁)) = toBase) :
    ∃ ρ : pullback toBase (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A))) ≅
        pullback f₁ (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A₁))),
      ρ.hom ≫ pullback.fst f₁ (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A₁))) =
        pullback.fst toBase (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A))) ≫
          e₁.hom ≫ pullback.fst f₁ (Spec.map (CommRingCat.ofHom ι₁)) := by
  have hκcomp : (IsLocalRing.ResidueField.map ι₁).comp (IsLocalRing.residue A₁) =
    (IsLocalRing.residue A).comp ι₁ :=
    IsLocalRing.ResidueField.map_comp_residue ι₁
  have hbij : Function.Bijective (IsLocalRing.ResidueField.map ι₁) := by
    refine ⟨(IsLocalRing.ResidueField.map ι₁).injective, ?_⟩
    have h : Function.Surjective ((IsLocalRing.ResidueField.map ι₁).comp (IsLocalRing.residue A₁))
      := by rw [hκcomp]; exact hres₁
    rw [RingHom.coe_comp] at h
    exact Function.Surjective.of_comp h
  have hε1 : (RingEquiv.ofBijective (IsLocalRing.ResidueField.map ι₁) hbij).symm.toRingHom.comp
    (IsLocalRing.ResidueField.map ι₁) = RingHom.id _ := by
    ext x; exact (RingEquiv.ofBijective (IsLocalRing.ResidueField.map ι₁) hbij).symm_apply_apply x
  have hε2 : (IsLocalRing.ResidueField.map ι₁).comp (RingEquiv.ofBijective
    (IsLocalRing.ResidueField.map ι₁) hbij).symm.toRingHom = RingHom.id _ := by
    ext x; exact (RingEquiv.ofBijective (IsLocalRing.ResidueField.map ι₁) hbij).apply_symm_apply x
  have hκ1 : (Spec.map (CommRingCat.ofHom (IsLocalRing.ResidueField.map ι₁))) ≫ (Spec.map
    (CommRingCat.ofHom (IsLocalRing.residue A₁))) = (Spec.map (CommRingCat.ofHom
    (IsLocalRing.residue A))) ≫ (Spec.map (CommRingCat.ofHom ι₁)) := by
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp,
      hκcomp]
  have hκ2 : (Spec.map (CommRingCat.ofHom (IsLocalRing.ResidueField.map ι₁))) ≫ (Spec.map
    (CommRingCat.ofHom (RingEquiv.ofBijective (IsLocalRing.ResidueField.map ι₁)
    hbij).symm.toRingHom)) = 𝟙 _ := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hε2, CommRingCat.ofHom_id, Spec.map_id]
  have hκ3 : (Spec.map (CommRingCat.ofHom (RingEquiv.ofBijective (IsLocalRing.ResidueField.map ι₁)
    hbij).symm.toRingHom)) ≫ (Spec.map (CommRingCat.ofHom (IsLocalRing.ResidueField.map ι₁))) = 𝟙 _
    := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hε1, CommRingCat.ofHom_id, Spec.map_id]
  have hκ4 : (Spec.map (CommRingCat.ofHom (RingEquiv.ofBijective (IsLocalRing.ResidueField.map ι₁)
    hbij).symm.toRingHom)) ≫ (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A))) ≫ (Spec.map
    (CommRingCat.ofHom ι₁)) = (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A₁))) := by
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, ←
      hκcomp,
      ← RingHom.comp_assoc, hε1, RingHom.id_comp]
  have wF : (pullback.fst toBase (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A))) ≫ e₁.hom ≫
    pullback.fst f₁ (Spec.map (CommRingCat.ofHom ι₁))) ≫ f₁ =
      (pullback.snd toBase (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A))) ≫ (Spec.map
        (CommRingCat.ofHom (IsLocalRing.ResidueField.map ι₁)))) ≫ (Spec.map (CommRingCat.ofHom
        (IsLocalRing.residue A₁))) := by
    calc (pullback.fst toBase (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A))) ≫ e₁.hom ≫
      pullback.fst f₁ (Spec.map (CommRingCat.ofHom ι₁))) ≫ f₁
        = pullback.fst toBase (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A))) ≫ e₁.hom ≫
          (pullback.fst f₁ (Spec.map (CommRingCat.ofHom ι₁)) ≫ f₁) := by
          simp only [Category.assoc]
      _ = pullback.fst toBase (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A))) ≫ (e₁.hom ≫
        pullback.snd f₁ (Spec.map (CommRingCat.ofHom ι₁))) ≫ (Spec.map (CommRingCat.ofHom ι₁)) := by
          rw [pullback.condition]; simp only [Category.assoc]
      _ = (pullback.fst toBase (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A))) ≫ toBase) ≫
        (Spec.map (CommRingCat.ofHom ι₁)) := by rw [he₁, Category.assoc]
      _ = pullback.snd toBase (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A))) ≫ ((Spec.map
        (CommRingCat.ofHom (IsLocalRing.residue A))) ≫ (Spec.map (CommRingCat.ofHom ι₁))) :=
        by rw [pullback.condition, Category.assoc]
      _ = (pullback.snd toBase (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A))) ≫ (Spec.map
        (CommRingCat.ofHom (IsLocalRing.ResidueField.map ι₁)))) ≫ (Spec.map (CommRingCat.ofHom
        (IsLocalRing.residue A₁))) := by rw [← hκ1, Category.assoc]
  have wG0 : pullback.fst f₁ (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A₁))) ≫ f₁ =
    (pullback.snd f₁ (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A₁))) ≫ (Spec.map
    (CommRingCat.ofHom (RingEquiv.ofBijective (IsLocalRing.ResidueField.map ι₁)
    hbij).symm.toRingHom)) ≫ (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A)))) ≫ (Spec.map
    (CommRingCat.ofHom ι₁)) := by
    rw [pullback.condition]
    simp only [Category.assoc]
    rw [hκ4]
  have wG : (pullback.lift (pullback.fst f₁ (Spec.map (CommRingCat.ofHom (IsLocalRing.residue
    A₁)))) (pullback.snd f₁ (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A₁))) ≫ (Spec.map
    (CommRingCat.ofHom (RingEquiv.ofBijective (IsLocalRing.ResidueField.map ι₁)
    hbij).symm.toRingHom)) ≫ (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A)))) wG0 ≫ e₁.inv)
    ≫ toBase =
      (pullback.snd f₁ (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A₁))) ≫ (Spec.map
        (CommRingCat.ofHom (RingEquiv.ofBijective (IsLocalRing.ResidueField.map ι₁)
        hbij).symm.toRingHom))) ≫ (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A))) := by
    rw [Category.assoc, ← he₁, e₁.inv_hom_id_assoc, pullback.lift_snd, Category.assoc]
  refine ⟨⟨pullback.lift (pullback.fst toBase (Spec.map (CommRingCat.ofHom (IsLocalRing.residue
    A))) ≫ e₁.hom ≫ pullback.fst f₁ (Spec.map (CommRingCat.ofHom ι₁))) (pullback.snd toBase
    (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A))) ≫ (Spec.map (CommRingCat.ofHom
    (IsLocalRing.ResidueField.map ι₁)))) wF,
    pullback.lift (pullback.lift (pullback.fst f₁ (Spec.map (CommRingCat.ofHom (IsLocalRing.residue
      A₁)))) (pullback.snd f₁ (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A₁))) ≫ (Spec.map
      (CommRingCat.ofHom (RingEquiv.ofBijective (IsLocalRing.ResidueField.map ι₁)
      hbij).symm.toRingHom)) ≫ (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A)))) wG0 ≫ e₁.inv)
      (pullback.snd f₁ (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A₁))) ≫ (Spec.map
        (CommRingCat.ofHom (RingEquiv.ofBijective (IsLocalRing.ResidueField.map ι₁)
        hbij).symm.toRingHom))) wG, ?_, ?_⟩, ?_⟩
  · apply pullback.hom_ext
    · rw [Category.id_comp, Category.assoc, pullback.lift_fst]
      have hFG0 : pullback.lift (pullback.fst toBase (Spec.map (CommRingCat.ofHom
        (IsLocalRing.residue A))) ≫ e₁.hom ≫ pullback.fst f₁ (Spec.map (CommRingCat.ofHom ι₁)))
        (pullback.snd toBase (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A))) ≫ (Spec.map
        (CommRingCat.ofHom (IsLocalRing.ResidueField.map ι₁)))) wF ≫
          pullback.lift (pullback.fst f₁ (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A₁))))
            (pullback.snd f₁ (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A₁))) ≫ (Spec.map
            (CommRingCat.ofHom (RingEquiv.ofBijective (IsLocalRing.ResidueField.map ι₁)
            hbij).symm.toRingHom)) ≫ (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A)))) wG0 =
          pullback.fst toBase (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A))) ≫ e₁.hom := by
        apply pullback.hom_ext
        · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst, Category.assoc]
        · rw [Category.assoc, pullback.lift_snd, ← Category.assoc, pullback.lift_snd,
            Category.assoc,
            ← Category.assoc (Spec.map (CommRingCat.ofHom (IsLocalRing.ResidueField.map ι₁))), hκ2,
              Category.id_comp, Category.assoc, he₁, pullback.condition]
      rw [← Category.assoc, hFG0, Category.assoc, e₁.hom_inv_id, Category.comp_id]
    · rw [Category.id_comp, Category.assoc, pullback.lift_snd, ← Category.assoc, pullback.lift_snd,
        Category.assoc, hκ2, Category.comp_id]
  · apply pullback.hom_ext
    · rw [Category.id_comp, Category.assoc, pullback.lift_fst, ← Category.assoc, pullback.lift_fst,
        Category.assoc, e₁.inv_hom_id_assoc, pullback.lift_fst]
    · rw [Category.id_comp, Category.assoc, pullback.lift_snd, ← Category.assoc, pullback.lift_snd,
        Category.assoc, hκ3, Category.comp_id]
  · exact pullback.lift_fst _ _ _
end AlgebraicCurves.Geometry.Schemes.Proofs.exists_iso_pullback_residue_of_iso_pullback
end ProofImplementation
