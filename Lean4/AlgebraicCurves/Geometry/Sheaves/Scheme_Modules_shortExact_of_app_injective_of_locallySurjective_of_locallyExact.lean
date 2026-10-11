/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_shortExact_of_app_injective_of_locallySurjective_of_locallyExact.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_Hom_mono_iff_injective
import AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_Hom_epi_iff_locallySurjective

/-!
# Short exactness from sectionwise and local conditions

Sectionwise injectivity, local surjectivity, and local lifting of kernel sections
establish short exactness of a complex of module sheaves.
-/

section ProofImplementation

namespace AlgebraicGeometry.Scheme.Modules

universe u

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
  _root_.Opposite _root_.TopologicalSpace

theorem shortExact_of_app_injective_of_locallySurjective_of_locallyExact
    {X : Scheme.{u}} (S : ShortComplex X.Modules)
    (hf : ∀ U : X.Opens, Function.Injective (S.f.app U))
    (hg : ∀ (U : X.Opens) (s : Γ(S.X₃, U)), ∀ x ∈ U, ∃ (V : X.Opens) (i : V ≤ U),
      x ∈ V ∧ S.X₃.presheaf.map (homOfLE i).op s ∈ Set.range (S.g.app V))
    (hfg : ∀ (U : X.Opens) (m : Γ(S.X₂, U)), S.g.app U m = 0 → ∀ x ∈ U, ∃ (V : X.Opens) (i : V ≤ U),
      x ∈ V ∧ S.X₂.presheaf.map (homOfLE i).op m ∈ Set.range (S.f.app V)) :
    S.ShortExact where
  mono_f := (Scheme.Modules.Hom.mono_iff_injective S.f).2 hf
  epi_g := (Scheme.Modules.Hom.epi_iff_locallySurjective S.g).2 hg
  exact := by
    rw [ShortComplex.exact_iff_epi_kernel_lift, Scheme.Modules.Hom.epi_iff_locallySurjective]
    intro U s x hx
    have hι : ∀ V : X.Opens, Function.Injective ((kernel.ι S.g).app V) :=
      (Scheme.Modules.Hom.mono_iff_injective _).1 inferInstance
    have h0 : S.g.app U ((kernel.ι S.g).app U s) = 0 := by
      change ((kernel.ι S.g).app U ≫ S.g.app U) s = 0
      rw [← Scheme.Modules.Hom.comp_app, kernel.condition, Scheme.Modules.Hom.zero_app]
      rfl
    obtain ⟨V, i, hxV, e, he⟩ := hfg U _ h0 x hx
    refine ⟨V, i, hxV, e, hι V ?_⟩
    have h1 : (kernel.ι S.g).app V ((kernel.lift S.g S.f S.zero).app V e) = S.f.app V e := by
      change ((kernel.lift S.g S.f S.zero).app V ≫ (kernel.ι S.g).app V) e = S.f.app V e
      rw [← Scheme.Modules.Hom.comp_app, kernel.lift_ι]
    have h2 : (kernel.ι S.g).app V ((kernel S.g).presheaf.map (homOfLE i).op s) =
        S.X₂.presheaf.map (homOfLE i).op ((kernel.ι S.g).app U s) := by
      have := congr($((kernel.ι S.g).mapPresheaf.naturality (homOfLE i).op) s)
      simpa using this
    rw [h1, h2, he]
end AlgebraicGeometry.Scheme.Modules
end ProofImplementation
