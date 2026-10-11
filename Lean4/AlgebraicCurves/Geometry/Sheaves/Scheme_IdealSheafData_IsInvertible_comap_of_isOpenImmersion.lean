/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_comap_of_isOpenImmersion.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.RingTheory.Localization.Defs
import Mathlib.Algebra.GroupWithZero.NonZeroDivisors
import AlgebraicCurves.RelativeDivisors.Cartier

/-!
# Scheme Ideal Sheaf Data Is Invertible comap of is Open Immersion
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Sheaves.Proofs
namespace Scheme_IdealSheafData_IsInvertible_comap_of_isOpenImmersion

universe u

open CategoryTheory AlgebraicGeometry

theorem _root_.AlgebraicGeometry.Scheme.IdealSheafData.IsInvertible.comap_of_isOpenImmersion
    {X Y : Scheme.{u}} {I : X.IdealSheafData} (hI : I.IsInvertible) (j : Y ⟶ X) [IsOpenImmersion j]
      :
    (I.comap j).IsInvertible := by
  intro y
  obtain ⟨U, f, hxf, g, hg, hIg⟩ := hI (j y)
  obtain ⟨_, ⟨V₀, hV₀, rfl⟩, hyV₀, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ y) isOpen_univ
  let V₀' : Y.affineOpens := ⟨V₀, hV₀⟩
  let W₀ : X.affineOpens := ⟨j ''ᵁ V₀, hV₀.image_of_isOpenImmersion j⟩
  have hxW₀ : j y ∈ (W₀ : X.Opens) := ⟨y, hyV₀, rfl⟩
  obtain ⟨h, h', hhh', hxh⟩ :=
    exists_basicOpen_le_affine_inter (X.affineBasicOpen f).2 W₀.2 (j y) ⟨hxf, hxW₀⟩
  have hW : (X.affineBasicOpen h : X.Opens) ≤ X.affineBasicOpen f := X.basicOpen_le h
  let gh : Γ(X, X.affineBasicOpen h) := (X.presheaf.map (homOfLE hW).op).hom g
  have hgh : gh ∈ nonZeroDivisors Γ(X, X.affineBasicOpen h) := by
    let := (X.affineBasicOpen f).2.isLocalization_basicOpen h
    exact IsLocalization.nonZeroDivisors_le_comap (M := .powers h) (S := Γ(X, X.basicOpen h)) hg
  have hIh : I.ideal (X.affineBasicOpen h) = Ideal.span {gh} := by
    rw [← I.map_ideal (U := X.affineBasicOpen h) (V := X.affineBasicOpen f) hW, hIg, Ideal.map_span,
      Set.image_singleton]
    rfl
  let f' : Γ(Y, V₀) := (j.appIso V₀).hom h'
  have hf' : (j.appIso V₀).inv f' = h' := by
    change ((j.appIso V₀).hom ≫ (j.appIso V₀).inv) h' = h'
    rw [Iso.hom_inv_id]; rfl
  have himg : j ''ᵁ Y.basicOpen f' = X.basicOpen h := by
    rw [Scheme.image_basicOpen, hf', ← hhh']
  have hyf' : y ∈ Y.basicOpen f' := by
    have : j y ∈ j ''ᵁ Y.basicOpen f' := by rw [himg]; exact hxh
    obtain ⟨y', hy', hyy'⟩ := this
    rwa [← j.isOpenEmbedding.injective hyy']
  have heqA : (⟨j ''ᵁ (Y.affineBasicOpen (U := V₀') f' : Y.Opens),
      (Y.affineBasicOpen (U := V₀') f').2.image_of_isOpenImmersion j⟩ : X.affineOpens) =
        X.affineBasicOpen h :=
    Subtype.ext himg
  refine ⟨V₀', f', hyf', ?_⟩
  let e₁ : Γ(X, X.affineBasicOpen h) ⟶ Γ(X, j ''ᵁ (Y.affineBasicOpen (U := V₀') f' : Y.Opens)) :=
    X.presheaf.map (eqToHom (congrArg Subtype.val heqA)).op
  have : IsIso e₁ := by dsimp only [e₁]; infer_instance
  let e₂ := j.appIso (Y.affineBasicOpen (U := V₀') f' : Y.Opens)
  let g' : Γ(Y, Y.affineBasicOpen (U := V₀') f') := e₂.hom (e₁.hom gh)
  refine ⟨g', ?_, ?_⟩
  · have hinj₁ : Function.Injective (e₂.inv.hom) := (ConcreteCategory.bijective_of_isIso e₂.inv).1
    have hinj₂ : Function.Injective ((inv e₁).hom) := (ConcreteCategory.bijective_of_isIso (inv
      e₁)).1
    refine mem_nonZeroDivisors_of_injective hinj₁ ?_
    refine mem_nonZeroDivisors_of_injective hinj₂ ?_
    have h1 : e₂.inv.hom g' = e₁.hom gh := by
      change (e₂.hom ≫ e₂.inv) (e₁.hom gh) = e₁.hom gh
      rw [Iso.hom_inv_id]; rfl
    have h2 : (inv e₁).hom (e₁.hom gh) = gh := by
      change (e₁ ≫ inv e₁) gh = gh
      rw [IsIso.hom_inv_id]; rfl
    rw [h1, h2]
    exact hgh
  · rw [Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion]
    have hle : (⟨j ''ᵁ (Y.affineBasicOpen (U := V₀') f' : Y.Opens),
        (Y.affineBasicOpen (U := V₀') f').2.image_of_isOpenImmersion j⟩ : X.affineOpens) ≤
          X.affineBasicOpen h :=
      le_of_eq heqA
    have hIj : I.ideal ⟨j ''ᵁ (Y.affineBasicOpen (U := V₀') f' : Y.Opens),
        (Y.affineBasicOpen (U := V₀') f').2.image_of_isOpenImmersion j⟩ = Ideal.span {e₁.hom gh} :=
          by
      rw [← I.map_ideal' (U := ⟨j ''ᵁ (Y.affineBasicOpen (U := V₀') f' : Y.Opens), _⟩)
        (V := X.affineBasicOpen h) (eqToHom (congrArg Subtype.val heqA)).op, hIh, Ideal.map_span,
          Set.image_singleton]
    rw [hIj]
    have h1 : e₂.inv.hom g' = e₁.hom gh := by
      change (e₂.hom ≫ e₂.inv) (e₁.hom gh) = e₁.hom gh
      rw [Iso.hom_inv_id]; rfl
    apply le_antisymm
    · intro x hx
      rw [Ideal.mem_comap, Ideal.mem_span_singleton'] at hx
      obtain ⟨a, ha⟩ := hx
      rw [Ideal.mem_span_singleton']
      refine ⟨e₂.hom.hom a, ?_⟩
      have hx' : x = e₂.hom.hom (e₂.inv.hom x) := by
        change x = (e₂.inv ≫ e₂.hom) x
        rw [Iso.inv_hom_id]; rfl
      rw [hx', ← ha, map_mul]
    · rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, h1]
      exact Ideal.subset_span rfl
end Scheme_IdealSheafData_IsInvertible_comap_of_isOpenImmersion
end AlgebraicCurves.Geometry.Sheaves.Proofs
end ProofImplementation
