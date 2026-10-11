/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_CoherentBaseChange_TwoTermComplex_natCast_finrank_ker_baseChange_sub_natCast_finrank_quotient_range_eq_chi.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import SchemeTheory.Cohomology.Sheaves.CoherentBaseChange
import Mathlib.RingTheory.TensorProduct.Finite
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.RankNullity
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Util.WithWeakNamespace

/-!
The Euler characteristic of a two-term complex from its field-base-change kernel and cokernel.
-/

section ProofImplementation

namespace AlgebraicCurves.Cohomology.Cech.Proofs.NatCastFinrankBaseChangeEulerChar

universe u v w

open scoped TensorProduct
open _root_.CoherentBaseChange

namespace CoherentBaseChange
open _root_.CoherentBaseChange
namespace TwoTermComplex
open _root_.CoherentBaseChange.TwoTermComplex
namespace ChiFieldAux
open _root_.CoherentBaseChange.TwoTermComplex
open _root_.CoherentBaseChange

variable {R : Type u} [CommRing R] (G : CoherentBaseChange.TwoTermComplex.{u, v} R)
  (K : Type w) [Field K] [Algebra R K]

/-- The rank of the differential after extending scalars to the field. -/
noncomputable def rk : ℕ := Module.finrank K (LinearMap.range (G.d.baseChange K))

theorem h0_add_rk :
    Module.finrank K (LinearMap.ker (G.d.baseChange K)) + rk G K =
      Module.finrank K (K ⊗[R] G.C0) := by
  have h := LinearMap.finrank_range_add_finrank_ker (G.d.baseChange K)
  unfold rk; omega

theorem rk_add_h1 :
    rk G K + Module.finrank K ((K ⊗[R] G.C1) ⧸ LinearMap.range (G.d.baseChange K)) =
      Module.finrank K (K ⊗[R] G.C1) := by
  have h := Submodule.finrank_quotient_add_finrank (LinearMap.range (G.d.baseChange K))
  unfold rk; omega

theorem main :
    (Module.finrank K (LinearMap.ker (G.d.baseChange K)) : ℤ) -
      Module.finrank K ((K ⊗[R] G.C1) ⧸ LinearMap.range (G.d.baseChange K)) = G.chi := by
  have : Nontrivial R := (algebraMap R K).domain_nontrivial
  have h0 := h0_add_rk G K
  have h1 := rk_add_h1 G K
  rw [Module.finrank_baseChange] at h0 h1
  change _ = (Module.finrank R G.C0 : ℤ) - (Module.finrank R G.C1 : ℤ)
  have h0' : (Module.finrank K (LinearMap.ker (G.d.baseChange K)) : ℤ) + (rk G K : ℤ) =
      (Module.finrank R G.C0 : ℤ) := by exact_mod_cast h0
  have h1' : (rk G K : ℤ) + (Module.finrank K ((K ⊗[R] G.C1) ⧸
      LinearMap.range (G.d.baseChange K)) : ℤ) = (Module.finrank R G.C1 : ℤ) := by exact_mod_cast h1
  omega

end CoherentBaseChange.TwoTermComplex.ChiFieldAux

with_weak_namespace CoherentBaseChange
open TwoTermComplex in
with_weak_namespace _root_.CoherentBaseChange.TwoTermComplex
theorem natCast_finrank_ker_baseChange_sub_natCast_finrank_quotient_range_eq_chi
    {R : Type u} [CommRing R] (G : CoherentBaseChange.TwoTermComplex.{u, v} R)
    (K : Type w) [Field K] [Algebra R K] :
    (Module.finrank K (LinearMap.ker (G.d.baseChange K)) : ℤ) -
      Module.finrank K ((K ⊗[R] G.C1) ⧸ LinearMap.range (G.d.baseChange K)) = G.chi := by
  exact ChiFieldAux.main G K
end AlgebraicCurves.Cohomology.Cech.Proofs.NatCastFinrankBaseChangeEulerChar
end ProofImplementation
