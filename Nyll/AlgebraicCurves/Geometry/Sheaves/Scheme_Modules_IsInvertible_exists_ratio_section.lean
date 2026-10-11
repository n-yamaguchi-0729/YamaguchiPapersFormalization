/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_ratio_section.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Geometry.Sheaves.ModulesSectionZeroScheme
import Nyll.SchemeTheory.Modules.TensorSections
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_IsInvertible_isFrameOn_app_of_disjoint_support_zeroSchemeIdeal

/-!
# Ratios of sections of an invertible module

Two global sections of an invertible module have a ratio on any open disjoint from
the support of the zero-scheme ideal of the denominator section.
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Sheaves.Proofs.Scheme_Modules_IsInvertible_exists_ratio_section

universe u

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open _root_.Opposite

namespace AlgebraicGeometry
open _root_.AlgebraicGeometry
namespace Scheme
open _root_.AlgebraicGeometry.Scheme
namespace Modules
open _root_.AlgebraicGeometry.Scheme.Modules
namespace RATIO
open _root_.AlgebraicGeometry.Scheme.Modules
open _root_.AlgebraicGeometry.Scheme
open _root_.AlgebraicGeometry

noncomputable section

variable {X : Scheme.{u}}

lemma ringMap_map {W₁ W₂ W₃ : X.Opens} (k₁ : op W₁ ⟶ op W₂) (k₂ : op W₂ ⟶ op W₃) (k : op W₁ ⟶ op W₃)
    (a : Γ(X, W₁)) : X.presheaf.map k₂ (X.presheaf.map k₁ a) = X.presheaf.map k a := by
  rw [show k = k₁ ≫ k₂ from Quiver.Hom.unop_inj (Subsingleton.elim _ _), X.presheaf.map_comp]
  rfl

lemma map_map (M : X.Modules) {W₁ W₂ W₃ : X.Opens} (k₁ : op W₁ ⟶ op W₂) (k₂ : op W₂ ⟶ op W₃)
    (k : op W₁ ⟶ op W₃) (m : Γ(M, W₁)) : M.presheaf.map k₂ (M.presheaf.map k₁ m) =
        M.presheaf.map k m := by
  rw [show k = k₁ ≫ k₂ from Quiver.Hom.unop_inj (Subsingleton.elim _ _), M.presheaf.map_comp]
  rfl

lemma app_map {M N : X.Modules} (φ : M ⟶ N) {W' W : X.Opens} (i : W' ⟶ W) (m : Γ(M, W)) :
    φ.app W' (M.presheaf.map i.op m) = N.presheaf.map i.op (φ.app W m) := by
  have hnat := φ.mapPresheaf.naturality i.op
  have hx := ConcreteCategory.congr_hom hnat m
  simp only [ConcreteCategory.comp_apply, Scheme.Modules.mapPresheaf_app] at hx
  exact hx

variable {M : X.Modules}

/-- The global module section obtained by evaluating a unit-module morphism at one. -/
abbrev σ (s : 𝟙_ X.Modules ⟶ M) : Γ(M, ⊤) := s.app ⊤ (toUnitSection ⊤ 1)

lemma restrictSection_eq (s : 𝟙_ X.Modules ⟶ M) (U : X.Opens) :
    restrictSection s U = M.presheaf.map (homOfLE (le_top : U.ι ''ᵁ ⊤ ≤ ⊤)).op (σ s) := by
  change s.app (U.ι ''ᵁ ⊤) (toUnitSection (U.ι ''ᵁ ⊤) 1) = _
  have h0 : toUnitSection (U.ι ''ᵁ ⊤) (1 : Γ(X, U.ι ''ᵁ ⊤)) =
      (𝟙_ X.Modules).presheaf.map (homOfLE (le_top : U.ι ''ᵁ ⊤ ≤ ⊤)).op (toUnitSection ⊤ 1) := by
    change toUnitSection (U.ι ''ᵁ ⊤) (1 : Γ(X, U.ι ''ᵁ ⊤)) =
      toUnitSection _ (X.presheaf.map (homOfLE (le_top : U.ι ''ᵁ ⊤ ≤ ⊤)).op (1 : Γ(X, ⊤)))
    rw [map_one]
  rw [h0, app_map]

theorem main (hM : Scheme.Modules.IsInvertible M) (s t : 𝟙_ X.Modules ⟶ M) :
    ∃ r : Γ(X, (Scheme.Modules.zeroSchemeIdeal t).support.compl),
      ∀ (U : X.affineOpens) (hU : U.1 ≤ (Scheme.Modules.zeroSchemeIdeal t).support.compl)
        (τ : M.restrict U.1.ι ≅ 𝟙_ (U.1 : Scheme.{u}).Modules),
        (X.presheaf.map (homOfLE hU).op).hom r * Scheme.Modules.coeff t U.1 τ.hom =
          Scheme.Modules.coeff s U.1 τ.hom := by
  set V : X.Opens := (Scheme.Modules.zeroSchemeIdeal t).support.compl with hV
  have hdisj : Disjoint (V : Set X) (Scheme.Modules.zeroSchemeIdeal t).support := by
    rw [Set.disjoint_iff]
    rintro x ⟨hxV, hxZ⟩
    exact hxV hxZ
  have hframe :=
    open _root_.AlgebraicGeometry.Scheme.Modules.IsInvertible in
    isFrameOn_app_of_disjoint_support_zeroSchemeIdeal hM t V hdisj
  obtain ⟨r, hr, -⟩ := hframe.existsUnique (W := V) le_top le_rfl
    (M.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op (σ s))
  refine ⟨r, fun U hU τ => ?_⟩
  have hW'V : U.1.ι ''ᵁ ⊤ ≤ V := by rw [Scheme.Opens.ι_image_top]; exact hU
  have hr' : (X.presheaf.map (homOfLE hW'V).op r) •
      M.presheaf.map (homOfLE (le_top : U.1.ι ''ᵁ ⊤ ≤ ⊤)).op (σ t) =
        M.presheaf.map (homOfLE (le_top : U.1.ι ''ᵁ ⊤ ≤ ⊤)).op (σ s) := by
    have h := congrArg (M.presheaf.map (homOfLE hW'V).op) hr
    rw [Scheme.Modules.map_smul, map_map M _ _ (homOfLE (le_top : U.1.ι ''ᵁ ⊤ ≤ ⊤)).op,
      map_map M _ _ (homOfLE (le_top : U.1.ι ''ᵁ ⊤ ≤ ⊤)).op] at h
    exact h
  let A := Γ((U.1 : Scheme.{u}), (⊤ : (U.1 : Scheme.{u}).Opens))
  let N := Γ(M.restrict U.1.ι, (⊤ : (U.1 : Scheme.{u}).Opens))
  have hXN : ∀ (a : Γ(X, U.1.ι ''ᵁ ⊤)) (m : Γ(M, U.1.ι ''ᵁ ⊤)), a • m = @HSMul.hSMul A N N _ a m
      := by
    intro a m
    change _ = (((U.1.ι.appIso ⊤).inv a : Γ(X, U.1.ι ''ᵁ ⊤)) • m : Γ(M, U.1.ι ''ᵁ ⊤))
    (simp [Scheme.Opens.ι_appIso]; rfl)
  have key : restrictSection s U.1 =
      @HSMul.hSMul A N N _ (X.presheaf.map (homOfLE hW'V).op r) (restrictSection t U.1) := by
    rw [restrictSection_eq s U.1, restrictSection_eq t U.1, ← hXN]
    exact hr'.symm
  change (X.presheaf.map (homOfLE hU).op).hom r *
      U.1.topIso.hom (ofUnitSection ⊤ (τ.hom.app ⊤ (restrictSection t U.1))) =
    U.1.topIso.hom (ofUnitSection ⊤ (τ.hom.app ⊤ (restrictSection s U.1)))
  erw [key, Scheme.Modules.Hom.app_smul, ofUnitSection_smul, map_mul]
  congr 1
  rw [Scheme.Opens.topIso_hom]
  exact (ringMap_map _ _ _ _).symm

end

end AlgebraicGeometry.Scheme.Modules.RATIO

theorem _root_.AlgebraicGeometry.Scheme.Modules.IsInvertible.exists_ratio_section
    {X : Scheme.{u}} {M : X.Modules} (hM : Scheme.Modules.IsInvertible M)
    (s t : 𝟙_ X.Modules ⟶ M) :
    ∃ r : Γ(X, (Scheme.Modules.zeroSchemeIdeal t).support.compl),
      ∀ (U : X.affineOpens) (hU : U.1 ≤ (Scheme.Modules.zeroSchemeIdeal t).support.compl)
        (τ : M.restrict U.1.ι ≅ 𝟙_ (U.1 : Scheme.{u}).Modules),
        (X.presheaf.map (homOfLE hU).op).hom r * Scheme.Modules.coeff t U.1 τ.hom =
          Scheme.Modules.coeff s U.1 τ.hom :=
  AlgebraicGeometry.Scheme.Modules.RATIO.main hM s t
end AlgebraicCurves.Geometry.Sheaves.Proofs.Scheme_Modules_IsInvertible_exists_ratio_section
end ProofImplementation

attribute [-instance]
  AlgebraicGeometry.ChowDatum.hι_closed
  AlgebraicGeometry.ChowDatumProj.hιN_closed
  AlgebraicGeometry.ChowDatumProj.hp_proper
  AlgebraicGeometry.ChowDatum.hp_isoU
  AlgebraicGeometry.ChowDatum.hp_proper
  AlgebraicGeometry.ProjSpace.algebraAway
  AlgebraicGeometry.ProjSpace.instIsProperProdOverπ
  AlgebraicGeometry.ChowDatumProj.hp_isoU
  AlgebraicGeometry.ProjSpace.isProper_π
  AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial
attribute [-simp]
  AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right
  AlgebraicGeometry.Scheme.Modules.map_unitSection
  AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply
  AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero
  AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left
  AlgebraicGeometry.Scheme.Modules.tensorPow_zero
  AlgebraicGeometry.Scheme.Modules.tensorPow_succ
  AlgebraicGeometry.Scheme.Modules.ProjPresentation.mk.injEq
  AlgebraicGeometry.Scheme.Modules.ProjPresentation.mk.sizeOf_spec
  AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec
  AlgebraicGeometry.ChowDatum.mk.sizeOf_spec
  AlgebraicGeometry.ChowDatumProj.mk.injEq
  AlgebraicGeometry.ChowDatum.mk.injEq
