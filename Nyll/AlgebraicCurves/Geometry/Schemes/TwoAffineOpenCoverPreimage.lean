/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicGeometry_TwoAffineOpenCoverPreimage.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Geometry.Schemes.TwoAffineOpenCoverH1BaseChange

/-!
# Two Affine Open Cover Preimage
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.TwoAffineOpenCover

variable {X Y : Scheme.{u}}

/-- The inverse-image two-affine-open cover along an affine morphism. -/
def preimage (𝒱 : X.TwoAffineOpenCover) (g : Y ⟶ X) [IsAffineHom g] : Y.TwoAffineOpenCover where
  U0 := g ⁻¹ᵁ 𝒱.U0
  U1 := g ⁻¹ᵁ 𝒱.U1
  isAffineOpen_U0 := 𝒱.isAffineOpen_U0.preimage g
  isAffineOpen_U1 := 𝒱.isAffineOpen_U1.preimage g
  sup_eq_top := by rw [← Scheme.Hom.preimage_sup, 𝒱.sup_eq_top]; rfl
  isAffineOpen_inf := by rw [← Scheme.Hom.preimage_inf]; exact 𝒱.isAffineOpen_inf.preimage g

@[simp] theorem preimage_U0 (𝒱 : X.TwoAffineOpenCover) (g : Y ⟶ X) [IsAffineHom g] :
    (𝒱.preimage g).U0 = g ⁻¹ᵁ 𝒱.U0 := rfl

@[simp] theorem preimage_U1 (𝒱 : X.TwoAffineOpenCover) (g : Y ⟶ X) [IsAffineHom g] :
    (𝒱.preimage g).U1 = g ⁻¹ᵁ 𝒱.U1 := rfl

variable {R : Type u} [CommRing R] {S : Type u} [CommRing S]

theorem pullback_eq_preimage (𝒱 : X.TwoAffineOpenCover) (c : X ⟶ Spec (.of R))
    (A : Type u) [CommRing A] [Algebra R A] :
    𝒱.pullback c A =
      @preimage _ _ 𝒱 (Limits.pullback.fst c (specMap R A)) (isAffineHom_fst c A) := rfl

/-- The morphism of two-affine-open covers induced by an affine morphism over the base. -/
def HomOver.ofPreimage {τ : R →+* S} (𝒱 : X.TwoAffineOpenCover) (c : X ⟶ Spec (.of R))
    (c' : Y ⟶ Spec (.of S)) (g : Y ⟶ X) [IsAffineHom g]
    (hg : g ≫ c = c' ≫ Spec.map (CommRingCat.ofHom τ)) :
    HomOver τ 𝒱 c (𝒱.preimage g) c' where
  hom := g
  comm := hg
  U0_le := le_rfl
  U1_le := le_rfl

@[simp] theorem HomOver.ofPreimage_hom {τ : R →+* S} (𝒱 : X.TwoAffineOpenCover) (c : X ⟶ Spec (.of
  R))
    (c' : Y ⟶ Spec (.of S)) (g : Y ⟶ X) [IsAffineHom g]
    (hg : g ≫ c = c' ≫ Spec.map (CommRingCat.ofHom τ)) :
    (HomOver.ofPreimage 𝒱 c c' g hg).hom = g := rfl

/-- The morphism of two-affine-open covers obtained by extension of the base algebra. -/
def HomOver.pullback {𝒱 : X.TwoAffineOpenCover} {c : X ⟶ Spec (.of R)} {𝒲 : Y.TwoAffineOpenCover}
    {c' : Y ⟶ Spec (.of R)} (f : HomOver (RingHom.id R) 𝒱 c 𝒲 c')
    (A : Type u) [CommRing A] [Algebra R A] :
    HomOver (RingHom.id A) (𝒱.pullback c A) (Limits.pullback.snd c (specMap R A))
      (𝒲.pullback c' A) (Limits.pullback.snd c' (specMap R A)) where
  hom := Limits.pullback.map c' (specMap R A) c (specMap R A) f.hom (𝟙 _) (𝟙 _)
    (by rw [Category.comp_id, f.comm, CommRingCat.ofHom_id];
        erw [Spec.map_id]; try rw [Category.comp_id]) (by simp)
  comm := by
    rw [Limits.pullback.lift_snd, CommRingCat.ofHom_id]
    erw [Spec.map_id]
    try rw [Category.comp_id, Category.comp_id]
  U0_le := by
    change Limits.pullback.fst c' (specMap R A) ⁻¹ᵁ 𝒲.U0 ≤
      Limits.pullback.map c' (specMap R A) c (specMap R A) f.hom (𝟙 _) (𝟙 _) _ _ ⁻¹ᵁ
        (Limits.pullback.fst c (specMap R A) ⁻¹ᵁ 𝒱.U0)
    rw [← Scheme.Hom.comp_preimage, Limits.pullback.lift_fst, Scheme.Hom.comp_preimage]
    exact Scheme.Hom.preimage_mono _ f.U0_le
  U1_le := by
    change Limits.pullback.fst c' (specMap R A) ⁻¹ᵁ 𝒲.U1 ≤
      Limits.pullback.map c' (specMap R A) c (specMap R A) f.hom (𝟙 _) (𝟙 _) _ _ ⁻¹ᵁ
        (Limits.pullback.fst c (specMap R A) ⁻¹ᵁ 𝒱.U1)
    rw [← Scheme.Hom.comp_preimage, Limits.pullback.lift_fst, Scheme.Hom.comp_preimage]
    exact Scheme.Hom.preimage_mono _ f.U1_le

theorem HomOver.pullback_hom {𝒱 : X.TwoAffineOpenCover} {c : X ⟶ Spec (.of R)} {𝒲 :
  Y.TwoAffineOpenCover}
    {c' : Y ⟶ Spec (.of R)} (f : HomOver (RingHom.id R) 𝒱 c 𝒲 c') (A : Type u) [CommRing A]
      [Algebra R A] :
    (f.pullback A).hom ≫ Limits.pullback.fst c (specMap R A) = Limits.pullback.fst c' (specMap R A)
      ≫ f.hom :=
  Limits.pullback.lift_fst _ _ _

theorem HomOver.pullback_hom_comp_stage_hom {𝒱 : X.TwoAffineOpenCover} {c : X ⟶ Spec (.of R)}
    {𝒲 : Y.TwoAffineOpenCover} {c' : Y ⟶ Spec (.of R)} (f : HomOver (RingHom.id R) 𝒱 c 𝒲 c')
    {A : Type u} [CommRing A] [Algebra R A] {B : Type u} [CommRing B] [Algebra R B] (g : A →ₐ[R] B)
      :
    (f.pullback B).hom ≫ (HomOver.stage 𝒱 c g).hom = (HomOver.stage 𝒲 c' g).hom ≫ (f.pullback
      A).hom := by
  apply Limits.pullback.hom_ext <;>
    simp only [HomOver.pullback, HomOver.stage, RelPicard.baseChangeSnd, Category.assoc,
      Limits.pullback.lift_fst,
      Limits.pullback.lift_fst_assoc, Limits.pullback.lift_snd, Limits.pullback.lift_snd_assoc,
        Category.comp_id]

end AlgebraicGeometry.Scheme.TwoAffineOpenCover

end
