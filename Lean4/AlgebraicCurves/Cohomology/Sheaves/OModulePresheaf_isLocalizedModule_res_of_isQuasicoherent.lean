/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_OModulePresheaf_isLocalizedModule_res_of_isQuasicoherent.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import AlgebraicCurves.Cohomology.Sheaves.OModulePresheafSectionsLinearRes
import Mathlib.Algebra.Module.LocalizedModule.Basic

/-!
# OModule Presheaf is Localized Module res of is Quasicoherent
-/

section ProofImplementation

namespace AlgebraicCurves.Cohomology.Sheaves.Proofs
namespace OModulePresheaf_isLocalizedModule_res_of_isQuasicoherent

universe u

open CategoryTheory AlgebraicGeometry

theorem _root_.AlgebraicGeometry.OModulePresheaf.isLocalizedModule_res_of_isQuasicoherent
    {R : Type u} [CommRing R] {V : Scheme.{u}} {π : V ⟶ Spec (.of R)} (F : OModulePresheaf π)
    (hq : F.IsQuasicoherent) (U : V.affineOpens) (f : Γ(V, U.1)) :
    letI := F.moduleRestrict (V.basicOpen_le f)
    IsLocalizedModule (Submonoid.powers f) (F.resₗ (V.basicOpen_le f)) := by
  let := F.moduleRestrict (V.basicOpen_le f)
  obtain ⟨hsurj, hker⟩ := hq U f
  have := U.2.isLocalization_basicOpen f
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨_, n, rfl⟩
    obtain ⟨u, hu⟩ := IsLocalization.map_units (M := Submonoid.powers f) Γ(V, V.basicOpen f) ⟨f ^
      n, n, rfl⟩
    have key : Function.Bijective fun y : F.obj (V.basicOpen f) => (u : Γ(V, V.basicOpen f)) • y :=
      MulAction.bijective u
    refine (Module.End.isUnit_iff _).mpr ?_
    convert key using 1
    funext y
    change ((f ^ n : Γ(V, U.1)) • y) = (u : Γ(V, V.basicOpen f)) • y
    rw [hu]
    rfl
  · intro y
    obtain ⟨n, x, hx⟩ := hsurj y
    exact ⟨(x, ⟨f ^ n, n, rfl⟩), hx.symm⟩
  · intro x₁ x₂ h
    have h0 : F.res (V.basicOpen_le f) (x₁ - x₂) = 0 := by
      rw [map_sub, sub_eq_zero]; exact h
    obtain ⟨n, hn⟩ := hker _ h0
    refine ⟨⟨f ^ n, n, rfl⟩, ?_⟩
    change (f ^ n : Γ(V, U.1)) • x₁ = (f ^ n : Γ(V, U.1)) • x₂
    rwa [smul_sub, sub_eq_zero] at hn
end OModulePresheaf_isLocalizedModule_res_of_isQuasicoherent
end AlgebraicCurves.Cohomology.Sheaves.Proofs
end ProofImplementation
