/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_RelEffCartierDiv_exists_supportedIn_of_forall_finset.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.AlgebraicGeometry.Sites.Representability
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import AlgebraicCurves.RelativeDivisors.RelEffCartierDivSupportedIn

/-!
Place relative divisors in an open that contains each finite set of interest.
-/

section ProofImplementation

namespace AlgebraicCurves.RelativeDivisors.Proofs
namespace RelEffCartierDiv_exists_supportedIn_of_forall_finset

universe u

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry

namespace AlgebraicGeometry
open _root_.AlgebraicGeometry
namespace RelEffCartierDiv
open _root_.AlgebraicGeometry.RelEffCartierDiv
open _root_.AlgebraicGeometry.RelEffCartierDiv
open _root_.AlgebraicGeometry

theorem exists_supportedIn_of_forall_finset_aux
    {𝒞 S : Scheme.{u}} (f : 𝒞 ⟶ S)
    (hcov : ∀ (V : S.affineOpens) (F : Finset 𝒞), (∀ x ∈ F, f x ∈ (V : S.Opens)) →
      ∃ U : 𝒞.Opens, IsAffineOpen U ∧ U ≤ f ⁻¹ᵁ (V : S.Opens) ∧ ∀ x ∈ F, x ∈ U)
    (r : ℕ) {T : Scheme.{u}} {g : T ⟶ S} (D : RelEffCartierDiv f r g) (t : T) :
    ∃ (W : T.Opens) (_ : t ∈ W) (V : S.affineOpens) (U : 𝒞.affineOpens)
      (_ : (U : 𝒞.Opens) ≤ f ⁻¹ᵁ (V : S.Opens)),
      (D.pullbackAlong W.ι rfl).SupportedIn U := by
  have := D.isFinite
  let q : D.I.subscheme ⟶ T := D.I.subschemeι ≫ pullback.snd f g
  have hfib : (q ⁻¹' {t}).Finite := q.finite_preimage_singleton t
  let F : Finset 𝒞 := (hfib.image fun z => pullback.fst f g (D.I.subschemeι z)).toFinset
  have hF : ∀ x ∈ F, f x = g t := by
    intro x hx
    obtain ⟨z, hz, rfl⟩ := (Set.Finite.mem_toFinset _).mp hx
    have hzt : q z = t := hz
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pullback.condition,
      Scheme.Hom.comp_apply, Scheme.Hom.comp_apply]
    exact congrArg g hzt
  obtain ⟨_, ⟨V, hV, rfl⟩, htV, -⟩ :=
    S.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (g t)) isOpen_univ
  obtain ⟨U, hU, hUV, hFU⟩ := hcov ⟨V, hV⟩ F fun x hx => by
    change f x ∈ V
    rw [hF x hx]
    exact htV
  refine ⟨D.supportedInLocus U, ?_, ⟨V, hV⟩, ⟨U, hU⟩, hUV, ?_⟩
  · rw [mem_supportedInLocus_iff]
    intro z hz
    exact hFU _ ((Set.Finite.mem_toFinset _).mpr ⟨z, hz, rfl⟩)
  · exact (supportedIn_pullbackAlong_iff _ _ _ _).mpr (by rw [Scheme.Opens.range_ι])

end AlgebraicGeometry.RelEffCartierDiv

theorem _root_.AlgebraicGeometry.RelEffCartierDiv.exists_supportedIn_of_forall_finset
    {𝒞 S : Scheme.{u}} (f : 𝒞 ⟶ S)
    (hcov : ∀ (V : S.affineOpens) (F : Finset 𝒞), (∀ x ∈ F, f x ∈ (V : S.Opens)) →
      ∃ U : 𝒞.Opens, IsAffineOpen U ∧ U ≤ f ⁻¹ᵁ (V : S.Opens) ∧ ∀ x ∈ F, x ∈ U)
    (r : ℕ) {T : Scheme.{u}} {g : T ⟶ S} (D : RelEffCartierDiv f r g) (t : T) :
    ∃ (W : T.Opens) (_ : t ∈ W) (V : S.affineOpens) (U : 𝒞.affineOpens)
      (_ : (U : 𝒞.Opens) ≤ f ⁻¹ᵁ (V : S.Opens)),
      (D.pullbackAlong W.ι rfl).SupportedIn U :=
  AlgebraicGeometry.RelEffCartierDiv.exists_supportedIn_of_forall_finset_aux f hcov r D t
end AlgebraicCurves.RelativeDivisors.Proofs.RelEffCartierDiv_exists_supportedIn_of_forall_finset
end ProofImplementation
