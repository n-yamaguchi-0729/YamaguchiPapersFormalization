/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_isOpen_irreducibleComponent_of_isDomain_stalk.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.AlgebraicGeometry.Stalk
import Mathlib.RingTheory.Spectrum.Prime.Noetherian
import Mathlib.Tactic.Set
import Mathlib.Topology.Inseparable
import Mathlib.Topology.Irreducible
import Mathlib.Topology.NoetherianSpace
import Mathlib.Topology.Sober

/-!
# is Open irreducible Component of is Domain stalk
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Schemes.Proofs.isOpen_irreducibleComponent_of_isDomain_stalk

universe u

open CategoryTheory AlgebraicGeometry

namespace FltWs29
namespace C2
open CategoryTheory AlgebraicGeometry TopologicalSpace Topology

theorem eq_irreducibleComponent_of_mem {X : Scheme.{u}} {x : X} (hx : IsDomain (X.presheaf.stalk x))
    {Z : Set X} (hZ : Z ∈ irreducibleComponents X) (hxZ : x ∈ Z) : Z = irreducibleComponent x := by
  have hZ' := irreducibleComponent_mem_irreducibleComponents x
  obtain ⟨ξ, hξ⟩ := QuasiSober.sober hZ.1 (isClosed_of_mem_irreducibleComponents Z hZ)
  obtain ⟨ξ', hξ'⟩ := QuasiSober.sober hZ'.1 isClosed_irreducibleComponent
  have h1 : ξ ⤳ x := hξ.specializes hxZ
  have h2 : ξ' ⤳ x := hξ'.specializes mem_irreducibleComponent
  have hr : Set.range (X.fromSpecStalk x).base = {y | y ⤳ x} := Scheme.range_fromSpecStalk
  obtain ⟨p, hp⟩ : ξ ∈ Set.range (X.fromSpecStalk x).base := by rw [hr]; exact h1
  obtain ⟨p', hp'⟩ : ξ' ∈ Set.range (X.fromSpecStalk x).base := by rw [hr]; exact h2
  let _ : IsDomain (X.presheaf.stalk x) := hx
  set g : X := (X.fromSpecStalk x).base (genericPoint (Spec (X.presheaf.stalk x))) with hg
  have hc : Continuous (X.fromSpecStalk x).base := (X.fromSpecStalk x).continuous
  have hg1 : g ⤳ ξ := hp ▸ (genericPoint_specializes p).map hc
  have hg2 : g ⤳ ξ' := hp' ▸ (genericPoint_specializes p').map hc
  have hcl : IsIrreducible (closure ({g} : Set X)) := isIrreducible_singleton.closure
  have hsub : Z ⊆ closure {g} := by
    rw [← hξ.def]; exact specializes_iff_closure_subset.mp hg1
  have hsub' : irreducibleComponent x ⊆ closure {g} := by
    rw [← hξ'.def]; exact specializes_iff_closure_subset.mp hg2
  have e1 : closure {g} = Z := Set.Subset.antisymm (hZ.2 hcl hsub) hsub
  have e2 : closure {g} = irreducibleComponent x := Set.Subset.antisymm (hZ'.2 hcl hsub') hsub'
  exact e1.symm.trans e2

theorem exists_open_subset_irreducibleComponent {X : Scheme.{u}} [IsLocallyNoetherian X]
    (hX : ∀ x : X, IsDomain (X.presheaf.stalk x)) (z : X) :
    ∃ O : Set X, IsOpen O ∧ z ∈ O ∧ O ⊆ irreducibleComponent z := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hzU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ z) isOpen_univ
  let _ : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  let φ : ↥(Spec Γ(X, U)) → (U : Set X) := fun q => ⟨hU.fromSpec.base q, by
    have : hU.fromSpec.base q ∈ Set.range hU.fromSpec.base := ⟨q, rfl⟩
    rwa [hU.range_fromSpec] at this⟩
  have hφc : Continuous φ := hU.fromSpec.continuous.subtype_mk _
  have hφs : Function.Surjective φ := by
    rintro ⟨y, hy⟩
    have : y ∈ Set.range hU.fromSpec.base := by rw [hU.range_fromSpec]; exact hy
    obtain ⟨q, rfl⟩ := this
    exact ⟨q, rfl⟩
  let _ : NoetherianSpace (U : Set X) := noetherianSpace_of_surjective φ hφc hφs
  set z' : (U : Set X) := ⟨z, hzU⟩
  set F : Set (U : Set X) := ⋃ C ∈ {C ∈ irreducibleComponents (U : Set X) | z' ∉ C}, C with hF
  have hFfin : {C ∈ irreducibleComponents (U : Set X) | z' ∉ C}.Finite :=
    NoetherianSpace.finite_irreducibleComponents.subset (Set.sep_subset _ _)
  have hFcl : IsClosed F := hFfin.isClosed_biUnion fun C hC =>
    isClosed_of_mem_irreducibleComponents C hC.1
  have hzF : z' ∉ F := by
    simp only [hF, Set.mem_iUnion, Set.mem_ofPred_eq, not_exists, and_imp]
    exact fun C _ hzC hzC' => hzC hzC'
  refine ⟨Subtype.val '' Fᶜ, U.isOpen.isOpenMap_subtype_val _ hFcl.isOpen_compl, ⟨z', hzF, rfl⟩, ?_⟩
  rintro _ ⟨y, hyF, rfl⟩
  have hC := irreducibleComponent_mem_irreducibleComponents y
  have hzC : z' ∈ irreducibleComponent y := by
    by_contra h
    exact hyF (Set.mem_biUnion (x := irreducibleComponent y) ⟨hC, h⟩ mem_irreducibleComponent)
  have hS : IsIrreducible (Subtype.val '' irreducibleComponent y : Set X) :=
    hC.1.image _ continuous_subtype_val.continuousOn
  obtain ⟨W, hWpre, hSW, hWmax⟩ := exists_preirreducible _ hS.2
  have hWirr : IsIrreducible W := ⟨⟨z, hSW ⟨z', hzC, rfl⟩⟩, hWpre⟩
  have hWcomp : W ∈ irreducibleComponents X :=
    ⟨hWirr, fun u hu hWu => (hWmax u hu.2 hWu).le⟩
  have hWeq : W = irreducibleComponent z := eq_irreducibleComponent_of_mem (hX z) hWcomp (hSW ⟨z',
    hzC, rfl⟩)
  rw [← hWeq]
  exact hSW ⟨y, mem_irreducibleComponent, rfl⟩

theorem main {X : Scheme.{u}} [IsLocallyNoetherian X] (hX : ∀ x : X, IsDomain (X.presheaf.stalk x))
  (x : X) :
    IsOpen (irreducibleComponent x) ∧ ∀ Z ∈ irreducibleComponents X, x ∈ Z → Z =
      irreducibleComponent x := by
  refine ⟨?_, fun Z hZ hxZ => eq_irreducibleComponent_of_mem (hX x) hZ hxZ⟩
  rw [isOpen_iff_forall_mem_open]
  intro z hz
  have hzx : irreducibleComponent x = irreducibleComponent z :=
    eq_irreducibleComponent_of_mem (hX z) (irreducibleComponent_mem_irreducibleComponents x) hz
  obtain ⟨O, hO, hzO, hOsub⟩ := exists_open_subset_irreducibleComponent hX z
  exact ⟨O, hzx ▸ hOsub, hO, hzO⟩

end FltWs29.C2

theorem _root_.AlgebraicGeometry.isOpen_irreducibleComponent_of_isDomain_stalk
    {X : Scheme.{u}} [IsLocallyNoetherian X] (hX : ∀ x : X, IsDomain (X.presheaf.stalk x)) (x : X) :
    IsOpen (irreducibleComponent x) ∧ ∀ Z ∈ irreducibleComponents X, x ∈ Z → Z =
      irreducibleComponent x :=
  FltWs29.C2.main hX x
end AlgebraicCurves.Geometry.Schemes.Proofs.isOpen_irreducibleComponent_of_isDomain_stalk
end ProofImplementation
