/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_IsInvertible_isFrameOn_app_of_disjoint_support_zeroSchemeIdeal.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.Util.WithWeakNamespace
import Nyll.SchemeTheory.Modules.Monoidal
import Nyll.AlgebraicCurves.Geometry.Picard.Functor
import Nyll.AlgebraicCurves.Geometry.Sheaves.ModulesTensorPow
import Nyll.SchemeTheory.Modules.TensorSections
import Nyll.SchemeTheory.Modules.ProjectivePresentation
import Nyll.AlgebraicCurves.Geometry.Sheaves.ModulesSectionZeroScheme
import Nyll.SchemeTheory.Modules.FrameLocality
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_IsInvertible_coeffIdeal_le_and_ideal_zeroSchemeIdeal_eq

/-!
# A frame away from the zero scheme of a section

A section of an invertible module is a frame on any open disjoint from the support
of its zero-scheme ideal.
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Sheaves.Proofs
namespace Scheme_Modules_IsInvertible_isFrameOn_app_of_disjoint_support_zeroSchemeIdeal

universe u

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory
open _root_.AlgebraicGeometry

open scoped CategoryTheory.MonObj

open Opposite TopologicalSpace

namespace AlgebraicGeometry
open _root_.AlgebraicGeometry
namespace Scheme
open _root_.AlgebraicGeometry.Scheme
namespace Modules
open _root_.AlgebraicGeometry.Scheme.Modules
open _root_.AlgebraicGeometry.Scheme.Modules
open _root_.AlgebraicGeometry.Scheme
open _root_.AlgebraicGeometry

namespace FrameOffZero

noncomputable section

variable {X : Scheme.{u}}

lemma map_congr (M : X.Modules) {W₁ W₂ : X.Opens} (k₁ k₂ : op W₂ ⟶ op W₁) (m : Γ(M, W₂)) :
    M.presheaf.map k₁ m = M.presheaf.map k₂ m := by
  rw [show k₁ = k₂ from Quiver.Hom.unop_inj (Subsingleton.elim _ _)]

lemma ringMap_congr {W₁ W₂ : X.Opens} (k₁ k₂ : op W₂ ⟶ op W₁) (a : Γ(X, W₂)) :
    X.presheaf.map k₁ a = X.presheaf.map k₂ a := by
  rw [show k₁ = k₂ from Quiver.Hom.unop_inj (Subsingleton.elim _ _)]

lemma ringMap_map {W₁ W₂ W₃ : X.Opens} (k₁ : op W₁ ⟶ op W₂) (k₂ : op W₂ ⟶ op W₃) (k : op W₁ ⟶ op W₃)
    (a : Γ(X, W₁)) : X.presheaf.map k₂ (X.presheaf.map k₁ a) = X.presheaf.map k a := by
  rw [show k = k₁ ≫ k₂ from Quiver.Hom.unop_inj (Subsingleton.elim _ _), X.presheaf.map_comp]
  rfl

lemma map_map (M : X.Modules) {W₁ W₂ W₃ : X.Opens} (k₁ : op W₁ ⟶ op W₂) (k₂ : op W₂ ⟶ op W₃)
    (k : op W₁ ⟶ op W₃) (m : Γ(M, W₁)) : M.presheaf.map k₂ (M.presheaf.map k₁ m) =
        M.presheaf.map k m := by
  rw [show k = k₁ ≫ k₂ from Quiver.Hom.unop_inj (Subsingleton.elim _ _), M.presheaf.map_comp]
  rfl

lemma image_preimage_eq_of_le {V W : X.Opens} (hW : W ≤ V) : V.ι ''ᵁ (V.ι ⁻¹ᵁ W) = W := by
  rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι, inf_eq_right.2 hW]

lemma app_map {M N : X.Modules} (φ : M ⟶ N) {W' W : X.Opens} (i : W' ⟶ W) (m : Γ(M, W)) :
    φ.app W' (M.presheaf.map i.op m) = N.presheaf.map i.op (φ.app W m) := by
  have hnat := φ.mapPresheaf.naturality i.op
  have hx := ConcreteCategory.congr_hom hnat m
  simp only [ConcreteCategory.comp_apply, Scheme.Modules.mapPresheaf_app] at hx
  exact hx

/-- The property that the restricted distinguished section generates every section uniquely. -/
def Q (M : X.Modules) (σ : Γ(M, ⊤)) (W : X.Opens) : Prop :=
  Function.Bijective fun g : Γ(X, W) => g • (M.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op σ :
      Γ(M, W))

section local_computation

variable {M : X.Modules} (s : 𝟙_ X.Modules ⟶ M) (U : X.Opens)
  (τ : M.restrict U.ι ≅ 𝟙_ (U : Scheme.{u}).Modules)

/-- The global section obtained by evaluating the unit-module morphism on one. -/
abbrev σ : Γ(M, ⊤) := s.app ⊤ (toUnitSection ⊤ 1)

/-- The local frame obtained from the inverse trivialization and the unit section. -/
abbrev fr : Γ(M.restrict U.ι, ⊤) := τ.inv.app ⊤ (unitSection ⊤)

/-- The scalar coordinate of the distinguished section in the chosen local trivialization. -/
abbrev cU : Γ((U : Scheme.{u}), ⊤) := ofUnitSection ⊤ (τ.hom.app ⊤ (restrictSection s U))

lemma fr_isFrameOn : IsFrameOn (fr U τ) ⊤ :=
  (isFrameOn_unitSection (X := (U : Scheme.{u})) (U := ⊤) ⊤).map_iso τ.symm

lemma restrictSection_eq_smul : restrictSection s U = cU s U τ • fr U τ := by
  have h1 : τ.inv.app ⊤ (τ.hom.app ⊤ (restrictSection s U)) = restrictSection s U := by
    change (τ.hom.app ⊤ ≫ τ.inv.app ⊤) (restrictSection s U) = restrictSection s U
    rw [← Scheme.Modules.Hom.comp_app, τ.hom_inv_id, Scheme.Modules.Hom.id_app]
    rfl
  have h2 : τ.hom.app ⊤ (restrictSection s U) = cU s U τ • unitSection ⊤ := by
    rw [smul_unitSection]
    rfl
  rw [← h1, h2, Scheme.Modules.Hom.app_smul]

lemma map_σ_eq (W : (U : Scheme.{u}).Opens) :
    (M.presheaf.map (homOfLE (le_top : U.ι ''ᵁ W ≤ ⊤)).op (σ s) : Γ(M, U.ι ''ᵁ W)) =
      ((M.restrict U.ι).presheaf.map (homOfLE (le_top : W ≤ ⊤)).op (restrictSection s U) :
        Γ(M.restrict U.ι, W)) := by
  have h1 : restrictSection s U = M.presheaf.map (homOfLE (le_top : U.ι ''ᵁ ⊤ ≤ ⊤)).op (σ s) := by
    change s.app (U.ι ''ᵁ ⊤) (toUnitSection (U.ι ''ᵁ ⊤) 1) = _
    have h0 : toUnitSection (U.ι ''ᵁ ⊤) (1 : Γ(X, U.ι ''ᵁ ⊤)) =
        (𝟙_ X.Modules).presheaf.map (homOfLE (le_top : U.ι ''ᵁ ⊤ ≤ ⊤)).op (toUnitSection ⊤ 1) := by
      change toUnitSection (U.ι ''ᵁ ⊤) (1 : Γ(X, U.ι ''ᵁ ⊤)) =
        toUnitSection _ (X.presheaf.map (homOfLE (le_top : U.ι ''ᵁ ⊤ ≤ ⊤)).op (1 : Γ(X, ⊤)))
      rw [map_one]
    rw [h0, app_map]
  rw [h1, Scheme.Modules.restrict_map]
  exact (map_map M _ _ _ _).symm

end local_computation

theorem main {M : X.Modules} (hM : IsInvertible M) (s : 𝟙_ X.Modules ⟶ M)
    (V : X.Opens) (hV : Disjoint (V : Set X) (zeroSchemeIdeal s).support) :
    IsFrameOn (s.app ⊤ (toUnitSection ⊤ 1)) V := by
  intro W hWtop hWV
  suffices key : ∀ x ∈ W, ∃ U' : X.Opens, x ∈ U' ∧ ∀ W' : X.Opens, W' ≤ U' → Q M (σ s) W' by
    exact bijective_smul_of_forall_exists_bijective_smul M (σ s) W key
  intro x hxW
  have hx : x ∉ ((zeroSchemeIdeal s).support : Set X) := Set.disjoint_left.mp hV (hWV hxW)
  obtain ⟨U, hxU, -, ⟨τ⟩⟩ := hM.exists_restrict_iso (V := ⊤) (x := x) trivial
  have hloc := ((hM.coeffIdeal_le_and_ideal_zeroSchemeIdeal_eq s).2 U τ).1
  have hxc : x ∈ X.basicOpen (coeff s U.1 τ.hom) := by
    have h1 : x ∉ X.zeroLocus (((zeroSchemeIdeal s).ideal U : Ideal Γ(X, U.1)) : Set Γ(X, U.1)) :=
      fun h => hx ((Scheme.IdealSheafData.mem_support_iff_of_mem hxU).mpr h)
    rw [hloc, Scheme.zeroLocus_span, Scheme.mem_zeroLocus_iff] at h1
    push Not at h1
    obtain ⟨f, hf, hxf⟩ := h1
    rw [Set.mem_singleton_iff] at hf
    exact hf ▸ hxf
  refine ⟨U.1 ⊓ X.basicOpen (coeff s U.1 τ.hom), ⟨hxU, hxc⟩, ?_⟩
  suffices himg : ∀ W : (U.1 : Scheme.{u}).Opens, U.1.ι ''ᵁ W ≤ X.basicOpen (coeff s U.1 τ.hom) →
      Q M (σ s) (U.1.ι ''ᵁ W) by
    intro W' hW'
    have e : U.1.ι ''ᵁ (U.1.ι ⁻¹ᵁ W') = W' := image_preimage_eq_of_le (hW'.trans inf_le_left)
    have h := himg (U.1.ι ⁻¹ᵁ W') (e.symm ▸ hW'.trans inf_le_right)
    rw [e] at h
    exact h
  intro W hWc
  let A := Γ((U.1 : Scheme.{u}), W)
  let N := Γ(M.restrict U.1.ι, W)
  have hXN : ∀ (a : Γ(X, U.1.ι ''ᵁ W)) (m : Γ(M, U.1.ι ''ᵁ W)), a • m = @HSMul.hSMul A N N _ a m
      := by
    intro a m
    change _ = (((U.1.ι.appIso W).inv a : Γ(X, U.1.ι ''ᵁ W)) • m : Γ(M, U.1.ι ''ᵁ W))
    rw [Scheme.Opens.ι_appIso]
    rfl
  have hσ : (M.presheaf.map (homOfLE (le_top : U.1.ι ''ᵁ W ≤ ⊤)).op (σ s) : N) =
      @HSMul.hSMul A N N _ ((U.1 : Scheme.{u}).presheaf.map (homOfLE (le_top : W ≤ ⊤)).op (cU s
          U.1 τ))
        ((M.restrict U.1.ι).presheaf.map (homOfLE (le_top : W ≤ ⊤)).op (fr U.1 τ)) := by
    rw [map_σ_eq, restrictSection_eq_smul s U.1 τ, Scheme.Modules.map_smul]
  have hunit : IsUnit ((U.1 : Scheme.{u}).presheaf.map (homOfLE (le_top : W ≤ ⊤)).op (cU s U.1
      τ)) := by
    have hc : (X.presheaf.map (homOfLE (hWc.trans (X.basicOpen_le _))).op (coeff s U.1 τ.hom) :
        Γ(X, U.1.ι ''ᵁ W)) = (U.1 : Scheme.{u}).presheaf.map (homOfLE (le_top : W ≤ ⊤)).op (cU s
            U.1 τ) := by
      change X.presheaf.map _ (U.1.topIso.hom (cU s U.1 τ)) = X.presheaf.map _ (cU s U.1 τ)
      rw [Scheme.Opens.topIso_hom]
      exact ringMap_map _ _ _ _
    rw [← hc]
    have h1 : IsUnit (X.presheaf.map (homOfLE (X.basicOpen_le (coeff s U.1 τ.hom))).op (coeff s
        U.1 τ.hom)) :=
      RingedSpace.isUnit_res_basicOpen (X := X.toLocallyRingedSpace.toRingedSpace) (coeff s U.1
          τ.hom)
    have h2 := h1.map (X.presheaf.map (homOfLE hWc).op).hom
    have h3 : (X.presheaf.map (homOfLE hWc).op).hom
        (X.presheaf.map (homOfLE (X.basicOpen_le (coeff s U.1 τ.hom))).op (coeff s U.1 τ.hom)) =
        X.presheaf.map (homOfLE (hWc.trans (X.basicOpen_le _))).op (coeff s U.1 τ.hom) :=
      ringMap_map _ _ _ _
    rw [h3] at h2
    exact h2
  have hfr := (fr_isFrameOn U.1 τ) (W := W) le_top le_top
  have hmul : Function.Bijective fun g : A =>
      g * (U.1 : Scheme.{u}).presheaf.map (homOfLE (le_top : W ≤ ⊤)).op (cU s U.1 τ) :=
    (Units.mulRight hunit.unit).bijective
  have hcomp := hfr.comp hmul
  have hfun : (fun g : Γ(X, U.1.ι ''ᵁ W) =>
      g • (M.presheaf.map (homOfLE (le_top : U.1.ι ''ᵁ W ≤ ⊤)).op (σ s) : Γ(M, U.1.ι ''ᵁ W))) =
      (fun a : A => a • ((M.restrict U.1.ι).presheaf.map (homOfLE (le_top : W ≤ ⊤)).op (fr U.1
          τ) : N)) ∘
        (fun g : A => g * (U.1 : Scheme.{u}).presheaf.map (homOfLE (le_top : W ≤ ⊤)).op (cU s
            U.1 τ)) := by
    funext g
    rw [hXN, hσ]
    change (show A from g) •
        (((U.1 : Scheme.{u}).presheaf.map (homOfLE (le_top : W ≤ ⊤)).op (cU s U.1 τ) : A) •
          ((M.restrict U.1.ι).presheaf.map (homOfLE (le_top : W ≤ ⊤)).op (fr U.1 τ) : N)) =
      ((show A from g) *
        ((U.1 : Scheme.{u}).presheaf.map (homOfLE (le_top : W ≤ ⊤)).op (cU s U.1 τ) : A)) •
          ((M.restrict U.1.ι).presheaf.map (homOfLE (le_top : W ≤ ⊤)).op (fr U.1 τ) : N)
    exact (mul_smul (show A from g)
      ((U.1 : Scheme.{u}).presheaf.map (homOfLE (le_top : W ≤ ⊤)).op (cU s U.1 τ) : A)
      ((M.restrict U.1.ι).presheaf.map (homOfLE (le_top : W ≤ ⊤)).op (fr U.1 τ) : N)).symm
  change Function.Bijective fun g : Γ(X, U.1.ι ''ᵁ W) =>
      g • (M.presheaf.map (homOfLE (le_top : U.1.ι ''ᵁ W ≤ ⊤)).op (σ s) : Γ(M, U.1.ι ''ᵁ W))
  rw [hfun]
  exact hcomp

end

end FrameOffZero

end AlgebraicGeometry.Scheme.Modules

with_weak_namespace _root_.AlgebraicCurves.Geometry.Sheaves.Proofs
with_weak_namespace Scheme_Modules_IsInvertible_isFrameOn_app_of_disjoint_support_zeroSchemeIdeal
with_weak_namespace AlgebraicGeometry.Scheme
open Modules in
with_weak_namespace _root_.AlgebraicGeometry.Scheme.Modules.IsInvertible
theorem isFrameOn_app_of_disjoint_support_zeroSchemeIdeal {X : Scheme.{u}} {M : X.Modules} (hM :
    Scheme.Modules.IsInvertible M) (s : 𝟙_ X.Modules ⟶ M)
    (V : X.Opens) (hV : Disjoint (V : Set X) (Scheme.Modules.zeroSchemeIdeal s).support) :
    Scheme.Modules.IsFrameOn (s.app ⊤ (Scheme.Modules.toUnitSection ⊤ 1)) V :=
  FrameOffZero.main hM s V hV
end Scheme_Modules_IsInvertible_isFrameOn_app_of_disjoint_support_zeroSchemeIdeal
end AlgebraicCurves.Geometry.Sheaves.Proofs
end ProofImplementation

attribute [local instance] MvPolynomial.gradedAlgebra
