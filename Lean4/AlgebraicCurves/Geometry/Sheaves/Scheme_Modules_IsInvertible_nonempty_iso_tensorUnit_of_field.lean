/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_IsInvertible_nonempty_iso_tensorUnit_of_field.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import AlgebraicCurves.Geometry.Picard.Functor
import SchemeTheory.Modules.Monoidal

/-!
# Invertible modules over the spectrum of a field

An invertible scheme module on the spectrum of a field is isomorphic to the tensor unit.
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Sheaves.Proofs
namespace Scheme_Modules_IsInvertible_nonempty_iso_tensorUnit_of_field

universe u

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory
open _root_.AlgebraicGeometry

theorem _root_.AlgebraicGeometry.Scheme.Modules.IsInvertible.nonempty_iso_tensorUnit_of_field
    (k : Type u) [Field k] (L : (Spec (CommRingCat.of k)).Modules) (hL :
        Scheme.Modules.IsInvertible L) :
    Nonempty (L ≅ 𝟙_ (Spec (CommRingCat.of k)).Modules) := by
  obtain ⟨U, hxU, ⟨e⟩⟩ := hL.exists_trivialization (IsLocalRing.closedPoint k)
  have hrange : Set.range (𝟙 (Spec (CommRingCat.of k)) : Spec (CommRingCat.of k) ⟶ _).base ⊆
      Set.range U.ι.base := by
    rintro y -
    rw [Scheme.Opens.range_ι]
    have : y = IsLocalRing.closedPoint k := Subsingleton.elim _ _
    rw [this]; exact hxU
  let g : Spec (CommRingCat.of k) ⟶ U := IsOpenImmersion.lift U.ι (𝟙 _) hrange
  have hg : g ≫ U.ι = 𝟙 _ := IsOpenImmersion.lift_fac _ _ _
  exact ⟨(Scheme.Modules.pullbackId _).symm.app L ≪≫
    (Scheme.Modules.pullbackCongr hg.symm).app L ≪≫
    ((Scheme.Modules.pullbackComp g U.ι).app L).symm ≪≫
    (Scheme.Modules.pullback g).mapIso e ≪≫
    Scheme.Modules.pullbackUnitIso g⟩
end Scheme_Modules_IsInvertible_nonempty_iso_tensorUnit_of_field
end AlgebraicCurves.Geometry.Sheaves.Proofs
end ProofImplementation
