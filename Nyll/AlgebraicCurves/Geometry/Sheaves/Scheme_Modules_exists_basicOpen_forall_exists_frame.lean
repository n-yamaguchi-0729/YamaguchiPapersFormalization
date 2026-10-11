/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_exists_basicOpen_forall_exists_frame.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyClosed
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.Topology.Bases
import Mathlib.Topology.Closure

/-!
# Local frames on a common basic open subset
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Sheaves.Proofs
namespace Scheme_Modules_exists_basicOpen_forall_exists_frame

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

theorem _root_.AlgebraicGeometry.Scheme.Modules.exists_basicOpen_forall_exists_frame
    {R : Type u} [CommRing R] {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) [UniversallyClosed f]
    (M : X.Modules) {ι : Type*} [Finite ι] (m : ι → Γ(M, ⊤)) (𝔭 : PrimeSpectrum R)
    (hgen : ∀ x : X, f x = 𝔭 → ∃ (i : ι) (U : X.Opens), x ∈ U ∧ ∀ V : X.Opens, V ≤ U →
      Function.Bijective fun g : Γ(X, V) =>
        g • (M.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op (m i) : Γ(M, V))) :
    ∃ g : R, g ∉ 𝔭.asIdeal ∧ ∀ x : X, f x ∈ PrimeSpectrum.basicOpen g →
      ∃ (i : ι) (U : X.Opens), x ∈ U ∧ ∀ V : X.Opens, V ≤ U →
        Function.Bijective fun g : Γ(X, V) =>
          g • (M.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op (m i) : Γ(M, V)) := by
  classical
  let W : Set X := {x | ∃ (i : ι) (U : X.Opens), x ∈ U ∧ ∀ V : X.Opens, V ≤ U →
    Function.Bijective fun g : Γ(X, V) =>
      g • (M.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op (m i) : Γ(M, V))}
  have hW : IsOpen W := by
    rw [isOpen_iff_forall_mem_open]
    rintro x ⟨i, U, hxU, hU⟩
    exact ⟨U, fun y hy => ⟨i, U, hy, hU⟩, U.isOpen, hxU⟩
  let Z : Set (PrimeSpectrum R) := f.base '' Wᶜ
  have hZ : IsClosed Z := f.isClosedMap _ hW.isClosed_compl
  have h𝔭Z : 𝔭 ∈ Zᶜ := by
    rintro ⟨x, hx, hfx⟩
    exact hx (hgen x hfx)
  obtain ⟨_, ⟨g, rfl⟩, hg𝔭, hgZ⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open h𝔭Z hZ.isOpen_compl
  refine ⟨g, hg𝔭, fun x hx => ?_⟩
  by_contra hx'
  exact hgZ hx ⟨x, hx', rfl⟩
end Scheme_Modules_exists_basicOpen_forall_exists_frame
end AlgebraicCurves.Geometry.Sheaves.Proofs
end ProofImplementation
