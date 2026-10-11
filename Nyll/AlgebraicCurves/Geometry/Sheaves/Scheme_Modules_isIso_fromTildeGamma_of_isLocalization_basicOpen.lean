/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_isIso_fromTildeGamma_of_isLocalization_basicOpen.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.AlgebraicGeometry.Modules.Tilde
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_isIso_fromTildeGamma_iff_isLocalizedModule

/-!
# Sheafification from localized global sections

Localization conditions on restrictions to basic opens identify the module sheaf
with the sheaf associated to its global sections on an affine scheme.
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Sheaves.Proofs
namespace Scheme_Modules_isIso_fromTildeGamma_of_isLocalization_basicOpen

universe u

open _root_.CategoryTheory
open _root_.AlgebraicGeometry
open _root_.Opposite
open _root_.TopologicalSpace

namespace AlgebraicGeometry
open _root_.AlgebraicGeometry
namespace Scheme
open _root_.AlgebraicGeometry.Scheme
namespace Modules
open _root_.AlgebraicGeometry.Scheme.Modules
open _root_.AlgebraicGeometry.Scheme.Modules
open _root_.AlgebraicGeometry.Scheme
open _root_.AlgebraicGeometry

namespace TildeOfLoc

variable {R : CommRingCat.{u}} (M : (Spec (.of R)).Modules)

/-- The `R`-module of sections of `M` over `W`, using the module-valued presheaf on `Spec R`. -/
noncomputable abbrev Γ' (W : (Spec (.of R)).Opens) : ModuleCat R := (modulesSpecToSheaf.obj M).1.obj
    (op W)

/-- The `R`-linear restriction map from global sections to sections over `W`. -/
noncomputable abbrev res' (W : (Spec (.of R)).Opens) : Γ' M ⊤ →ₗ[R] Γ' M W :=
  ((modulesSpecToSheaf.obj M).1.map (homOfLE (le_top : W ≤ ⊤)).op).hom

theorem res'_apply (W : (Spec (.of R)).Opens) (y : Γ(M, ⊤)) :
    res' M W y = (M.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op) y := rfl

theorem smul_def (W : (Spec (.of R)).Opens) (r : R) (m : Γ' M W) :
    r • m = (((Spec (.of R)).presheaf.map (homOfLE (le_top : W ≤ ⊤)).op).hom
      ((StructureSheaf.globalSectionsIso R).hom.hom r)) • (show Γ(M, W) from m) := rfl

omit M in
theorem globalSectionsIso_hom_apply (r : R) :
    (StructureSheaf.globalSectionsIso R).hom.hom r = (Scheme.ΓSpecIso (.of R)).inv.hom r := rfl

omit M in
theorem res_top_top (s : Γ(Spec (.of R), ⊤)) :
    ((Spec (.of R)).presheaf.map (homOfLE (le_top : (⊤ : (Spec (.of R)).Opens) ≤ ⊤)).op).hom s = s
        := by
  rw [Subsingleton.elim (homOfLE (le_top : (⊤ : (Spec (.of R)).Opens) ≤ ⊤)) (𝟙 _), op_id,
    CategoryTheory.Functor.map_id]
  rfl

/-- Numerator and kernel conditions for restricting global sections to `W` and clearing denominators
  with powers of `g`. -/
def LocClauses (W : (Spec (.of R)).Opens) (g : Γ(Spec (.of R), ⊤)) : Prop :=
  (∀ x : Γ(M, W), ∃ (n : ℕ) (y : Γ(M, ⊤)),
      M.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op y
        = ((Spec (.of R)).presheaf.map (homOfLE (le_top : W ≤ ⊤)).op).hom (g ^ n) • x)
    ∧ (∀ y : Γ(M, ⊤), M.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op y = 0 → ∃ n : ℕ, (g ^ n) • y = 0)

theorem isLocalizedModule_of_locClauses (f : R) (W : (Spec (.of R)).Opens)
    (hunit : IsUnit (algebraMap R (Module.End R (Γ' M W)) f))
    (h : LocClauses M W ((Scheme.ΓSpecIso (.of R)).inv.hom f)) :
    IsLocalizedModule (Submonoid.powers f) (res' M W) := by
  obtain ⟨h1, h2⟩ := h
  refine IsLocalizedModule.mk ?_ ?_ ?_
  · rintro ⟨c, n, rfl⟩
    rw [map_pow]
    exact hunit.pow n
  · intro x
    obtain ⟨n, y, hy⟩ := h1 x
    refine ⟨(y, ⟨f ^ n, n, rfl⟩), ?_⟩
    change (f ^ n) • x = res' M W y
    rw [res'_apply, hy, smul_def, globalSectionsIso_hom_apply, map_pow]
  · intro y₁ y₂ hyy
    have h0 : res' M W (y₁ - y₂) = 0 := by
      rw [map_sub, sub_eq_zero]; exact hyy
    obtain ⟨n, hn⟩ := h2 (y₁ - y₂) h0
    refine ⟨⟨f ^ n, n, rfl⟩, ?_⟩
    change (f ^ n) • y₁ = (f ^ n) • y₂
    rw [← sub_eq_zero, ← smul_sub, smul_def, globalSectionsIso_hom_apply, map_pow, res_top_top]
    exact hn

end TildeOfLoc

end AlgebraicGeometry.Scheme.Modules

open _root_.AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules in
theorem _root_.AlgebraicGeometry.Scheme.Modules.isIso_fromTildeGamma_of_isLocalization_basicOpen
    {R : CommRingCat.{u}} (M : (Spec (.of R)).Modules)
    (hloc : ∀ g : Γ(Spec (.of R), ⊤),
      (∀ x : Γ(M, (Spec (.of R)).basicOpen g), ∃ (n : ℕ) (y : Γ(M, ⊤)),
          M.presheaf.map (homOfLE ((Spec (.of R)).basicOpen_le g)).op y
            = ((Spec (.of R)).presheaf.map (homOfLE ((Spec (.of R)).basicOpen_le g)).op).hom (g ^ n)
                • x)
        ∧ (∀ y : Γ(M, ⊤), M.presheaf.map (homOfLE ((Spec (.of R)).basicOpen_le g)).op y = 0 →
            ∃ n : ℕ, (g ^ n) • y = 0)) :
    IsIso M.fromTildeΓ := by
  rw [AlgebraicGeometry.Scheme.Modules.isIso_fromTildeGamma_iff_isLocalizedModule]
  intro f
  have hW : (Spec (.of R)).basicOpen ((Scheme.ΓSpecIso (.of R)).inv.hom f) = PrimeSpectrum.basicOpen
      f :=
    basicOpen_eq_of_affine (R := .of R) f
  have h : TildeOfLoc.LocClauses M ((Spec (.of R)).basicOpen ((Scheme.ΓSpecIso (.of R)).inv.hom f))
      ((Scheme.ΓSpecIso (.of R)).inv.hom f) :=
    hloc _
  rw [hW] at h
  exact TildeOfLoc.isLocalizedModule_of_locClauses M f (PrimeSpectrum.basicOpen f)
    (Scheme.Modules.isUnit_algebraMap_end_of_le_basicOpen (M := M) f le_rfl) h
end Scheme_Modules_isIso_fromTildeGamma_of_isLocalization_basicOpen
end AlgebraicCurves.Geometry.Sheaves.Proofs
end ProofImplementation
