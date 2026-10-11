/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_shortExact_map_pushforward_of_forall_exists_surjective_app.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_Hom_mono_iff_injective
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_exists_app_eq_of_exact_of_app_eq_zero
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_shortExact_of_app_injective_of_locallySurjective_of_locallyExact

/-!
# Short exactness after pushforward

Local surjectivity of the second map on inverse images of opens ensures that pushforward
preserves the short exact complex.
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Sheaves.Proofs
namespace Scheme_Modules_shortExact_map_pushforward_of_forall_exists_surjective_app

universe u

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry
open _root_.Opposite
open _root_.TopologicalSpace

namespace AlgebraicGeometry
open _root_.AlgebraicGeometry
namespace Scheme
open _root_.AlgebraicGeometry.Scheme
namespace Modules
open _root_.AlgebraicGeometry.Scheme.Modules
namespace PushSES
open _root_.AlgebraicGeometry.Scheme.Modules
open _root_.AlgebraicGeometry.Scheme
open _root_.AlgebraicGeometry

variable {X T : Scheme.{u}} (π : X ⟶ T) (S : ShortComplex X.Modules)

theorem g_app_eq (U : T.Opens) (m : Γ(S.X₂, π ⁻¹ᵁ U)) :
    (S.map (Scheme.Modules.pushforward π)).g.app U m = S.g.app (π ⁻¹ᵁ U) m := rfl

theorem f_app_eq (U : T.Opens) (m : Γ(S.X₁, π ⁻¹ᵁ U)) :
    (S.map (Scheme.Modules.pushforward π)).f.app U m = S.f.app (π ⁻¹ᵁ U) m := rfl

theorem shortExact (hS : S.ShortExact)
    (hsurj : ∀ (U : T.Opens), ∀ y ∈ U, ∃ V : T.Opens, y ∈ V ∧ V ≤ U ∧
      Function.Surjective (S.g.app (π ⁻¹ᵁ V))) :
    (S.map (Scheme.Modules.pushforward π)).ShortExact := by
  have := hS.mono_f
  refine Scheme.Modules.shortExact_of_app_injective_of_locallySurjective_of_locallyExact _ ?_ ?_ ?_
  · intro U
    exact (Scheme.Modules.Hom.mono_iff_injective S.f).mp hS.mono_f (π ⁻¹ᵁ U)
  · intro U s x hx
    obtain ⟨V, hxV, hVU, hV⟩ := hsurj U x hx
    obtain ⟨m, hm⟩ := hV (S.X₃.presheaf.map (homOfLE (show π ⁻¹ᵁ V ≤ π ⁻¹ᵁ U from fun _ h => hVU
        h)).op s)
    exact ⟨V, hVU, hxV, m, hm⟩
  · intro U m hm x hx
    obtain ⟨e, he⟩ := Scheme.Modules.exists_app_eq_of_exact_of_app_eq_zero S hS.exact (π ⁻¹ᵁ U) m hm
    refine ⟨U, le_rfl, hx, e, ?_⟩
    change S.f.app (π ⁻¹ᵁ U) e = ((Scheme.Modules.pushforward π).obj S.X₂).presheaf.map (homOfLE
        le_rfl).op m
    have hid : ((Scheme.Modules.pushforward π).obj S.X₂).presheaf.map
        (homOfLE (le_refl U)).op = 𝟙 _ := by
      rw [show (homOfLE (le_refl U)).op = 𝟙 (op U) from Subsingleton.elim _ _]
      exact CategoryTheory.Functor.map_id _ _
    rw [he, hid]
    rfl

end AlgebraicGeometry.Scheme.Modules.PushSES

theorem
  _root_.AlgebraicGeometry.Scheme.Modules.shortExact_map_pushforward_of_forall_exists_surjective_app
    {X T : Scheme.{u}} (π : X ⟶ T) (S : ShortComplex X.Modules) (hS : S.ShortExact)
    (hsurj : ∀ (U : T.Opens), ∀ y ∈ U, ∃ V : T.Opens, y ∈ V ∧ V ≤ U ∧
      Function.Surjective (S.g.app (π ⁻¹ᵁ V))) :
    (S.map (Scheme.Modules.pushforward π)).ShortExact :=
  AlgebraicGeometry.Scheme.Modules.PushSES.shortExact π S hS hsurj
end Scheme_Modules_shortExact_map_pushforward_of_forall_exists_surjective_app
end AlgebraicCurves.Geometry.Sheaves.Proofs
end ProofImplementation
