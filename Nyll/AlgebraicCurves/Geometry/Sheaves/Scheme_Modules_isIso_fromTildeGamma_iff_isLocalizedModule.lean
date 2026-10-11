/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_isIso_fromTildeGamma_iff_isLocalizedModule.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Foundations.CategoryTheory.TopCat_Sheaf_isIso_of_isIso_app_of_isBasis
import Mathlib.AlgebraicGeometry.Modules.Tilde

/-!
# Affine modules detected by localization of sections

Characterizes the global-sections comparison by localization on basic open sets.
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Sheaves.Proofs
namespace Scheme_Modules_isIso_fromTildeGamma_iff_isLocalizedModule

universe u

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace AlgebraicGeometry.Scheme.Modules

theorem _root_.AlgebraicGeometry.Scheme.Modules.isIso_fromTildeGamma_iff_isLocalizedModule {R :
  CommRingCat.{u}}
    (M : (Spec (.of R)).Modules) :
    IsIso M.fromTildeΓ ↔ ∀ f : R, IsLocalizedModule (Submonoid.powers (M := R) f)
      ((modulesSpecToSheaf.obj M).1.map
        (homOfLE (le_top : PrimeSpectrum.basicOpen f ≤ ⊤)).op).hom := by
  let N : (Spec R).Modules := M
  change IsIso N.fromTildeΓ ↔ ∀ f : R, IsLocalizedModule (Submonoid.powers (M := R) f)
    ((modulesSpecToSheaf.obj N).1.map
      (homOfLE (le_top : PrimeSpectrum.basicOpen f ≤ ⊤)).op).hom
  constructor
  · intro hiso f
    let U := PrimeSpectrum.basicOpen f
    let P : ModuleCat R := ((modulesSpecToSheaf (R := R)).obj N).presheaf.obj (op ⊤)
    let Q : ModuleCat R := ((modulesSpecToSheaf (R := R)).obj N).presheaf.obj (op U)
    let L : ModuleCat R := ((modulesSpecToSheaf (R := R)).obj (tilde P)).presheaf.obj (op U)
    let r : P →ₗ[R] Q := (((modulesSpecToSheaf (R := R)).obj N).1.map
      (homOfLE (le_top : U ≤ ⊤)).op).hom
    let l : P →ₗ[R] L := (tilde.toOpen (R := R) P U).hom
    have : IsIso ((modulesSpecToSheaf (R := R)).map N.fromTildeΓ).1 := by
      have : IsIso ((modulesSpecToSheaf (R := R)).map N.fromTildeΓ) := inferInstance
      exact inferInstanceAs
        (IsIso ((TopCat.Sheaf.forget (ModuleCat R) (Spec R)).map
          ((modulesSpecToSheaf (R := R)).map N.fromTildeΓ)))
    let e : L ≃ₗ[R] Q :=
      (asIso (((modulesSpecToSheaf (R := R)).map N.fromTildeΓ).1.app (op U))).toLinearEquiv
    have happ := Scheme.Modules.toOpen_fromTildeΓ_app N U
    have hre : r = e.toLinearMap ∘ₗ l :=
      (congrArg (fun φ : P ⟶ Q => φ.hom) happ).symm
    have : IsLocalizedModule (Submonoid.powers (M := R) f) l := inferInstance
    change IsLocalizedModule (Submonoid.powers (M := R) f) r
    rw [hre]
    exact IsLocalizedModule.of_linearEquiv (R := R) (Submonoid.powers (M := R) f) l e
  · intro hloc
    suffices IsIso ((modulesSpecToSheaf (R := R)).map N.fromTildeΓ) from
      (SpecModulesToSheafFullyFaithful (R := R)).isIso_of_isIso_map _
    apply TopCat.Sheaf.isIso_of_isIso_app_of_isBasis (B := fun f : R => PrimeSpectrum.basicOpen f)
      PrimeSpectrum.isBasis_basic_opens
    intro f
    let U := PrimeSpectrum.basicOpen f
    let P : ModuleCat R := ((modulesSpecToSheaf (R := R)).obj N).presheaf.obj (op ⊤)
    let Q : ModuleCat R := ((modulesSpecToSheaf (R := R)).obj N).presheaf.obj (op U)
    let L : ModuleCat R := ((modulesSpecToSheaf (R := R)).obj (tilde P)).presheaf.obj (op U)
    let r : P →ₗ[R] Q := (((modulesSpecToSheaf (R := R)).obj N).1.map
      (homOfLE (le_top : U ≤ ⊤)).op).hom
    let l : P →ₗ[R] L := (tilde.toOpen (R := R) P U).hom
    let g : L →ₗ[R] Q :=
      (((modulesSpecToSheaf (R := R)).map N.fromTildeΓ).1.app (op U)).hom
    have : IsLocalizedModule (Submonoid.powers (M := R) f) l := inferInstance
    have : IsLocalizedModule (Submonoid.powers (M := R) f) r := hloc f
    have hg : g ∘ₗ l = r :=
      congrArg (fun φ : P ⟶ Q => φ.hom) (Scheme.Modules.toOpen_fromTildeΓ_app N U)
    let e : L ≃ₗ[R] Q :=
      IsLocalizedModule.linearEquiv (R := R) (Submonoid.powers (M := R) f) l r
    have he' : e.toLinearMap ∘ₗ l = r :=
      LinearMap.ext fun x => IsLocalizedModule.linearEquiv_apply (R := R)
        (Submonoid.powers (M := R) f) l r x
    have he : g = e.toLinearMap :=
      IsLocalizedModule.linearMap_ext (R := R) (S := Submonoid.powers (M := R) f)
        (f := l) (f' := r) (hg.trans he'.symm)
    have hb : Function.Bijective
        (((modulesSpecToSheaf (R := R)).map N.fromTildeΓ).1.app (op U)) := by
      change Function.Bijective g
      rw [he]
      exact e.bijective
    exact (ConcreteCategory.isIso_iff_bijective _).mpr hb
end Scheme_Modules_isIso_fromTildeGamma_iff_isLocalizedModule
end AlgebraicCurves.Geometry.Sheaves.Proofs
end ProofImplementation
