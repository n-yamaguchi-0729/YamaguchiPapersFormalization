/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Purity.IdealQuotientMayerVietorisExt
import Mathlib.RingTheory.Ideal.Operations

/-!
# Power-compatible Mayer--Vietoris complexes of ideal quotients

This file makes the finite-stage ideal-quotient Mayer--Vietoris sequence
functorial in inclusions of both ideals. In particular, the sequences for
the powers of two fixed ideals form a diagram indexed by `ℕᵒᵖ`. This is the
source-level compatibility needed before applying contravariant Ext and
filtered colimits in a local-cohomology Mayer--Vietoris construction.
-/

noncomputable section

open CategoryTheory Limits Opposite

namespace EtaleFundamentalGroups

universe u

variable {R : Type u} [CommRing R]

/-- The product of the quotient maps induced by inclusions of two ideals. -/
def idealQuotientMayerVietorisProductMap
    {I J I' J' : Ideal R} (hI : I ≤ I') (hJ : J ≤ J') :
    ((R ⧸ I) × (R ⧸ J)) →ₗ[R] ((R ⧸ I') × (R ⧸ J')) :=
  (idealQuotientMapOfLE hI).prodMap (idealQuotientMapOfLE hJ)

@[simp]
theorem idealQuotientMayerVietorisProductMap_apply
    {I J I' J' : Ideal R} (hI : I ≤ I') (hJ : J ≤ J')
    (z : (R ⧸ I) × (R ⧸ J)) :
    idealQuotientMayerVietorisProductMap hI hJ z =
      (idealQuotientMapOfLE hI z.1, idealQuotientMapOfLE hJ z.2) :=
  rfl

/-- Quotient maps induced by ideal inclusions compose. -/
theorem idealQuotientMapOfLE_comp
    {I I' I'' : Ideal R} (h : I ≤ I') (h' : I' ≤ I'') :
    (idealQuotientMapOfLE h').comp (idealQuotientMapOfLE h) =
      idealQuotientMapOfLE (h.trans h') := by
  apply LinearMap.ext
  intro z
  induction z using Submodule.Quotient.induction_on with
  | _ r => rfl

/-- The quotient map induced by a reflexive inclusion is the identity. -/
theorem idealQuotientMapOfLE_refl (I : Ideal R) :
    idealQuotientMapOfLE (le_refl I) = LinearMap.id := by
  apply LinearMap.ext
  intro z
  induction z using Submodule.Quotient.induction_on with
  | _ r => rfl

/-- The diagonal maps in the ideal-quotient Mayer--Vietoris complexes are
natural in inclusions of both ideals. -/
theorem idealQuotientMayerVietorisDiagonal_naturality
    {I J I' J' : Ideal R} (hI : I ≤ I') (hJ : J ≤ J') :
    (idealQuotientMayerVietorisDiagonal I' J').comp
        (idealQuotientMapOfLE (inf_le_inf hI hJ)) =
      (idealQuotientMayerVietorisProductMap hI hJ).comp
        (idealQuotientMayerVietorisDiagonal I J) := by
  apply LinearMap.ext
  intro z
  induction z using Submodule.Quotient.induction_on with
  | _ r => rfl

/-- The difference maps in the ideal-quotient Mayer--Vietoris complexes are
natural in inclusions of both ideals. -/
theorem idealQuotientMayerVietorisDifference_naturality
    {I J I' J' : Ideal R} (hI : I ≤ I') (hJ : J ≤ J') :
    (idealQuotientMayerVietorisDifference I' J').comp
        (idealQuotientMayerVietorisProductMap hI hJ) =
      (idealQuotientMapOfLE (sup_le_sup hI hJ)).comp
        (idealQuotientMayerVietorisDifference I J) := by
  apply LinearMap.ext
  rintro ⟨x, y⟩
  induction x using Submodule.Quotient.induction_on with
  | _ r =>
    induction y using Submodule.Quotient.induction_on with
    | _ s => rfl

/-- Inclusions of two pairs of ideals induce a morphism between their
ideal-quotient Mayer--Vietoris short complexes. -/
def idealQuotientMayerVietorisHom
    {I J I' J' : Ideal R} (hI : I ≤ I') (hJ : J ≤ J') :
    idealQuotientMayerVietorisShortComplex I J ⟶
      idealQuotientMayerVietorisShortComplex I' J' :=
  ShortComplex.homMk
    (ModuleCat.ofHom (idealQuotientMapOfLE (inf_le_inf hI hJ)))
    (ModuleCat.ofHom (idealQuotientMayerVietorisProductMap hI hJ))
    (ModuleCat.ofHom (idealQuotientMapOfLE (sup_le_sup hI hJ)))
    (by
      apply ModuleCat.hom_ext
      change
        (idealQuotientMayerVietorisDiagonal I' J').comp
            (idealQuotientMapOfLE (inf_le_inf hI hJ)) =
          (idealQuotientMayerVietorisProductMap hI hJ).comp
            (idealQuotientMayerVietorisDiagonal I J)
      exact idealQuotientMayerVietorisDiagonal_naturality hI hJ)
    (by
      apply ModuleCat.hom_ext
      change
        (idealQuotientMayerVietorisDifference I' J').comp
            (idealQuotientMayerVietorisProductMap hI hJ) =
          (idealQuotientMapOfLE (sup_le_sup hI hJ)).comp
            (idealQuotientMayerVietorisDifference I J)
      exact idealQuotientMayerVietorisDifference_naturality hI hJ)

/-- The morphism induced by reflexive inclusions is the identity morphism of
the Mayer--Vietoris short complex. -/
@[simp]
theorem idealQuotientMayerVietorisHom_refl (I J : Ideal R) :
    idealQuotientMayerVietorisHom (le_refl I) (le_refl J) =
      𝟙 (idealQuotientMayerVietorisShortComplex I J) := by
  apply ShortComplex.hom_ext
  · change ModuleCat.ofHom (idealQuotientMapOfLE (le_refl (I ⊓ J))) =
      𝟙 (ModuleCat.of R (R ⧸ (I ⊓ J)))
    rw [idealQuotientMapOfLE_refl, ModuleCat.ofHom_id]
  · change ModuleCat.ofHom (idealQuotientMayerVietorisProductMap (le_refl I) (le_refl J)) =
      𝟙 (ModuleCat.of R ((R ⧸ I) × (R ⧸ J)))
    simp only [idealQuotientMayerVietorisProductMap, idealQuotientMapOfLE_refl,
      LinearMap.prodMap_id, ModuleCat.ofHom_id]
  · change ModuleCat.ofHom (idealQuotientMapOfLE (le_refl (I ⊔ J))) =
      𝟙 (ModuleCat.of R (R ⧸ (I ⊔ J)))
    rw [idealQuotientMapOfLE_refl, ModuleCat.ofHom_id]

/-- Mayer--Vietoris morphisms induced by inclusions compose. -/
@[reassoc]
theorem idealQuotientMayerVietorisHom_comp
    {I₀ J₀ I₁ J₁ I₂ J₂ : Ideal R}
    (hI₀₁ : I₀ ≤ I₁) (hJ₀₁ : J₀ ≤ J₁)
    (hI₁₂ : I₁ ≤ I₂) (hJ₁₂ : J₁ ≤ J₂) :
    idealQuotientMayerVietorisHom hI₀₁ hJ₀₁ ≫
        idealQuotientMayerVietorisHom hI₁₂ hJ₁₂ =
      idealQuotientMayerVietorisHom (hI₀₁.trans hI₁₂)
        (hJ₀₁.trans hJ₁₂) := by
  apply ShortComplex.hom_ext
  · change ModuleCat.ofHom _ ≫ ModuleCat.ofHom _ = ModuleCat.ofHom _
    rw [← ModuleCat.ofHom_comp, idealQuotientMapOfLE_comp]
  · change ModuleCat.ofHom _ ≫ ModuleCat.ofHom _ = ModuleCat.ofHom _
    rw [← ModuleCat.ofHom_comp]
    apply congrArg ModuleCat.ofHom
    unfold idealQuotientMayerVietorisProductMap
    rw [LinearMap.prodMap_comp, idealQuotientMapOfLE_comp,
      idealQuotientMapOfLE_comp]
  · change ModuleCat.ofHom _ ≫ ModuleCat.ofHom _ = ModuleCat.ofHom _
    rw [← ModuleCat.ofHom_comp, idealQuotientMapOfLE_comp]

/-- The standard quotient Mayer--Vietoris short complexes for simultaneous
powers `Iⁿ` and `Jⁿ`, together with their source-produced transition maps. -/
def idealQuotientMayerVietorisPowersDiagram (I J : Ideal R) :
    ℕᵒᵖ ⥤ ShortComplex (ModuleCat.{u} R) where
  obj n := idealQuotientMayerVietorisShortComplex
    (I ^ unop n) (J ^ unop n)
  map {m n} f := idealQuotientMayerVietorisHom
    (Ideal.pow_le_pow_right f.unop.down.down)
    (Ideal.pow_le_pow_right f.unop.down.down)
  map_id n := by
    apply idealQuotientMayerVietorisHom_refl
  map_comp f g := by
    rw [idealQuotientMayerVietorisHom_comp]

/-- Every object of the powers diagram is the standard short exact
ideal-quotient Mayer--Vietoris sequence. -/
theorem idealQuotientMayerVietorisPowersDiagram_obj_shortExact
    (I J : Ideal R) (n : ℕᵒᵖ) :
    ((idealQuotientMayerVietorisPowersDiagram I J).obj n).ShortExact :=
  idealQuotientMayerVietorisShortComplex_shortExact _ _

end EtaleFundamentalGroups

end
