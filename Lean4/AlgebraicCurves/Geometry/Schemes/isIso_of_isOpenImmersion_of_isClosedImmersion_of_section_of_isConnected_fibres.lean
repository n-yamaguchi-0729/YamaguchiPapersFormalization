/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_isIso_of_isOpenImmersion_of_isClosedImmersion_of_section_of_isConnected_fibres.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.IsIso
import Mathlib.Topology.Connected.Clopen

/-!
# is Iso of is Open Immersion of is Closed Immersion of section of is Connected fibres
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Schemes.Proofs
namespace isIso_of_isOpenImmersion_of_isClosedImmersion_of_section_of_isConnected_fibres

open CategoryTheory AlgebraicGeometry

namespace Ws23G2

universe u

theorem eq_univ_of_isClopen_of_section {X S : Scheme.{u}} (g : X ⟶ S) (Z : Set X) (hZ : IsClopen Z)
    (hconn : ∀ s : S, _root_.IsPreconnected (g.base ⁻¹' {s}))
    (σ : S ⟶ X) (hσ : σ ≫ g = 𝟙 S) (hσZ : ∀ s : S, σ.base s ∈ Z) : Z = Set.univ := by
  refine Set.eq_univ_of_forall fun x => ?_
  have hfib : (g.base ⁻¹' {g.base x}) ⊆ Z := by
    refine (hconn (g.base x)).subset_isClopen hZ ⟨σ.base (g.base x), ?_, hσZ _⟩
    change g.base (σ.base (g.base x)) = g.base x
    have := congrArg (fun φ => φ.base (g.base x)) hσ
    simpa using this
  exact hfib (Set.mem_preimage.2 rfl)

end Ws23G2

end isIso_of_isOpenImmersion_of_isClosedImmersion_of_section_of_isConnected_fibres
end AlgebraicCurves.Geometry.Schemes.Proofs

namespace AlgebraicGeometry



open _root_.AlgebraicCurves.Geometry.Schemes.Proofs in
open isIso_of_isOpenImmersion_of_isClosedImmersion_of_section_of_isConnected_fibres in
open CategoryTheory AlgebraicGeometry in
theorem isIso_of_isOpenImmersion_of_isClosedImmersion_of_section_of_isConnected_fibres
    {X Y Z : Scheme} (p : X ⟶ Y) (hconn : ∀ y : Y, _root_.IsConnected (p.base ⁻¹' {y}))
    (e : Y ⟶ X) (he : e ≫ p = 𝟙 Y)
    (ι : Z ⟶ X) [IsOpenImmersion ι] [IsClosedImmersion ι]
    (hZ : ∃ e₀ : Y ⟶ Z, e₀ ≫ ι = e) :
    IsIso ι := by
  obtain ⟨e₀, he₀⟩ := hZ
  have hrange : Set.range ι.base = Set.univ := by
    refine Ws23G2.eq_univ_of_isClopen_of_section p (Set.range ι.base)
      ⟨ι.isClosedEmbedding.isClosed_range, ι.isOpenEmbedding.isOpen_range⟩
      (fun y => (hconn y).isPreconnected) e he (fun y => ?_)
    refine ⟨e₀.base y, ?_⟩
    have := congrArg (fun φ => φ.base y) he₀
    simpa using this
  let _ : Surjective ι := ⟨Set.range_eq_univ.1 hrange⟩
  exact (isIso_iff_isOpenImmersion_and_surjective ι).mpr ⟨inferInstance, inferInstance⟩
end AlgebraicGeometry
end ProofImplementation
