/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_IsInvertible_ideal_zeroSchemeIdeal_eq_span_of_app_eq_smul.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Geometry.Picard.Functor
import Nyll.SchemeTheory.Modules.TensorSections
import Nyll.AlgebraicCurves.Geometry.Sheaves.ModulesSectionZeroScheme
import Nyll.AlgebraicCurves.Geometry.Sheaves.ModulesIhomSections
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_IsFrameOn_nonempty_pullback_iso_unit
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_IsInvertible_coeffIdeal_le_and_ideal_zeroSchemeIdeal_eq

/-!
# Scheme Modules Is Invertible ideal zero Scheme Ideal eq span of app eq smul
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Sheaves.Proofs
namespace Scheme_Modules_IsInvertible_ideal_zeroSchemeIdeal_eq_span_of_app_eq_smul

universe u

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory
open _root_.AlgebraicGeometry

namespace AlgebraicGeometry
open _root_.AlgebraicGeometry
namespace Scheme
open _root_.AlgebraicGeometry.Scheme
namespace Modules
open _root_.AlgebraicGeometry.Scheme.Modules
namespace ZFrameAux
open _root_.AlgebraicGeometry.Scheme.Modules
open _root_.AlgebraicGeometry.Scheme
open _root_.AlgebraicGeometry

variable {X : Scheme.{u}}

lemma app_map {M N : X.Modules} (φ : M ⟶ N) {U V : X.Opens} (i : V ⟶ U) (x : Γ(M, U)) :
    φ.app V (M.presheaf.map i.op x) = N.presheaf.map i.op (φ.app U x) := by
  simpa using ConcreteCategory.congr_hom (φ.mapPresheaf.naturality i.op) x

lemma map_toUnitSection_one {U V : X.Opens} (i : V ⟶ U) :
    (𝟙_ X.Modules).presheaf.map i.op (Scheme.Modules.toUnitSection U 1) =
      Scheme.Modules.toUnitSection V 1 := by
  apply Scheme.Modules.ofUnitSection_injective
  rw [Scheme.Modules.ofUnitSection_map, Scheme.Modules.ofUnitSection_toUnitSection,
    Scheme.Modules.ofUnitSection_toUnitSection, map_one]

lemma presheaf_map_map {A B C : X.Opens} (f : B ⟶ A) (g : C ⟶ B) (k : C ⟶ A) (x : Γ(X, A)) :
    X.presheaf.map g.op (X.presheaf.map f.op x) = X.presheaf.map k.op x := by
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp, Subsingleton.elim (g ≫ f) k]

end AlgebraicGeometry.Scheme.Modules.ZFrameAux

open AlgebraicGeometry.Scheme.Modules.ZFrameAux in
theorem
  _root_.AlgebraicGeometry.Scheme.Modules.IsInvertible.ideal_zeroSchemeIdeal_eq_span_of_app_eq_smul
    {X : Scheme.{u}} {N : X.Modules} (hN : Scheme.Modules.IsInvertible N)
    {V : X.Opens} (Ω : Γ(N, V)) (hΩ : Scheme.Modules.IsFrameOn Ω V)
    (σ : 𝟙_ X.Modules ⟶ N) (c : Γ(X, V))
    (hσ : σ.app V (Scheme.Modules.toUnitSection V 1) = c • Ω)
    (U : X.affineOpens) (hUV : U.1 ≤ V) :
    (Scheme.Modules.zeroSchemeIdeal σ).ideal U = Ideal.span {X.presheaf.map (homOfLE hUV).op c} :=
      by
  obtain ⟨e⟩ := hΩ.nonempty_pullback_iso_unit U.1 hUV hUV
  let τ : N.restrict U.1.ι ≅ 𝟙_ (U.1 : Scheme.{u}).Modules := Scheme.Modules.restrictIsoOfLE le_rfl
    e
  rw [((hN.coeffIdeal_le_and_ideal_zeroSchemeIdeal_eq σ).2 U τ).1]
  have hi : U.1.ι ''ᵁ ⊤ ≤ V := (le_of_eq U.1.ι_image_top).trans hUV
  let c' : Γ((U.1 : Scheme.{u}), ⊤) := (X.presheaf.map (homOfLE hi).op c : Γ(X, U.1.ι ''ᵁ ⊤))
  let Ω' : Γ(N.restrict U.1.ι, ⊤) := (N.presheaf.map (homOfLE hi).op Ω : Γ(N, U.1.ι ''ᵁ ⊤))
  have hres : Scheme.Modules.restrictSection σ U.1 = c' • Ω' := by
    refine Eq.trans ?_ (Scheme.Modules.restrict_smul_eq ⊤ c' Ω').symm
    change σ.app (U.1.ι ''ᵁ ⊤) (Scheme.Modules.toUnitSection _ 1) =
      X.presheaf.map (homOfLE hi).op c • N.presheaf.map (homOfLE hi).op Ω
    rw [← map_toUnitSection_one (homOfLE hi), app_map, hσ, Scheme.Modules.map_smul]
  have htt_smul : ∀ (g : Γ((U.1 : Scheme.{u}), ⊤)) (y : Γ(N.restrict U.1.ι, ⊤)),
      τ.hom.app ⊤ (g • y) = g • τ.hom.app ⊤ y := fun g y => Scheme.Modules.Hom.app_smul τ.hom g y
  have htt_surj : Function.Surjective (τ.hom.app ⊤) := fun z => ⟨τ.inv.app ⊤ z, by
    change (τ.inv.app ⊤ ≫ τ.hom.app ⊤) z = z
    rw [← Scheme.Modules.Hom.comp_app, τ.inv_hom_id, Scheme.Modules.Hom.id_app]; rfl⟩
  have hΩ' : Scheme.Modules.IsFrameOn (N.presheaf.map (homOfLE hi).op Ω) (U.1.ι ''ᵁ ⊤) :=
    (hΩ.map (homOfLE hi)).mono hi
  let u : Γ((U.1 : Scheme.{u}), ⊤) := Scheme.Modules.ofUnitSection ⊤ (τ.hom.app ⊤ Ω')
  have hu : IsUnit u := by
    obtain ⟨y, hy⟩ := htt_surj (Scheme.Modules.toUnitSection ⊤ 1)
    obtain ⟨gX, hg⟩ := (hΩ' le_rfl le_rfl).2 (show Γ(N, U.1.ι ''ᵁ ⊤) from y)
    let g : Γ((U.1 : Scheme.{u}), ⊤) := (id gX : Γ((U.1 : Scheme.{u}), ⊤))
    have hg' : (show Γ((U.1 : Scheme.{u}), ⊤) from g) • Ω' = y := by
      rw [Scheme.Modules.restrict_smul_eq]
      change gX • N.presheaf.map (𝟙 (Opposite.op (U.1.ι ''ᵁ ⊤)))
        (N.presheaf.map (homOfLE hi).op Ω) = y at hg
      rw [N.presheaf.map_id] at hg
      exact hg
    refine isUnit_iff_exists_inv'.mpr ⟨g, ?_⟩
    have h1 := congrArg (fun m => Scheme.Modules.ofUnitSection ⊤ (τ.hom.app ⊤ m)) hg'
    simp only at h1
    rw [htt_smul, Scheme.Modules.ofUnitSection_smul, hy,
      Scheme.Modules.ofUnitSection_toUnitSection] at h1
    exact h1
  have hcoeff : Scheme.Modules.coeff σ U.1 τ.hom = U.1.topIso.hom (c' * u) := by
    unfold Scheme.Modules.coeff
    rw [hres, htt_smul, Scheme.Modules.ofUnitSection_smul]
  rw [hcoeff, map_mul, Ideal.span_singleton_mul_right_unit (hu.map _)]
  congr 2
  change U.1.topIso.hom (X.presheaf.map (homOfLE hi).op c) = _
  rw [Scheme.Opens.topIso_hom]
  exact presheaf_map_map (homOfLE hi) _ (homOfLE hUV) c
end Scheme_Modules_IsInvertible_ideal_zeroSchemeIdeal_eq_span_of_app_eq_smul
end AlgebraicCurves.Geometry.Sheaves.Proofs
end ProofImplementation

attribute [-instance] SheafOfModules.isIso_ihomModelToIhom
attribute [-simp] PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom
  SheafOfModules.ihomSectionsEquivFamily_unit
  AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app
  AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right
  AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left
  AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply
  SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app
  AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply
  AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply
  AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply
  AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply
