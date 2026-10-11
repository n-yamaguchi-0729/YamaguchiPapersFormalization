/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.FiniteEtale.ClopenPullback
public import Nyll.SchemeTheory.Topology.ConnectedComponentsMap
public import Mathlib.AlgebraicGeometry.Properties

/-!
# Connected components under equivalence of finite étale covers

Clopen descent gives a bijection on clopen subsets. For quasi-compact and
quasi-separated schemes, the resulting map on connected components is a
homeomorphism, as asserted in Stacks Project, Tag `0BQA`.
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.FiniteEtale

variable {X Y : Scheme.{u}}

private theorem bijective_clopen_preimage (f : X ⟶ Y)
    [(pullback f).IsEquivalence] :
    Function.Bijective (fun U : Clopens Y ↦
      (⟨f ⁻¹' (U : Set Y), U.isClopen.preimage f.continuous⟩ : Clopens X)) := by
  constructor
  · intro U V h
    obtain ⟨W, _, hW⟩ := existsUnique_clopen_preimage_of_pullback_isEquivalence f
      ⟨f ⁻¹' (U : Set Y), U.isClopen.preimage f.continuous⟩
    have hpre : f ⁻¹' (U : Set Y) = f ⁻¹' (V : Set Y) :=
      congrArg (fun A : Clopens X ↦ (A : Set X)) h
    exact (hW U rfl).trans (hW V hpre.symm).symm
  · intro U
    obtain ⟨V, hV, _⟩ := existsUnique_clopen_preimage_of_pullback_isEquivalence f U
    exact ⟨V, Clopens.ext hV⟩

/-- Equivalence on finite étale covers preserves and reflects connectedness. -/
theorem connectedSpace_iff_of_pullback_isEquivalence
    (f : X ⟶ Y) [(pullback f).IsEquivalence] :
    ConnectedSpace X ↔ ConnectedSpace Y :=
  SchemeTheory.connectedSpace_iff_of_clopen_preimage f.continuous
    (bijective_clopen_preimage f)

/-- **Stacks Project, Tag 0BQA.** An equivalence on finite étale covers of qcqs
schemes induces a homeomorphism on their spaces of connected components. -/
@[stacks 0BQA "The homeomorphism on connected components."]
theorem connectedComponentsMap_isHomeomorph_of_pullback_isEquivalence
    [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace Y] [QuasiSeparatedSpace Y]
    (f : X ⟶ Y) [(pullback f).IsEquivalence] :
    IsHomeomorph f.continuous.connectedComponentsMap :=
  SchemeTheory.connectedComponentsMap_isHomeomorph_of_clopen_preimage f.continuous
    (bijective_clopen_preimage f)

end AlgebraicGeometry.FiniteEtale
