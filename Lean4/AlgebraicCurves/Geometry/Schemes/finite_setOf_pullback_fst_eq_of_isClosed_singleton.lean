/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_finite_setOf_pullback_fst_eq_of_isClosed_singleton.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.RingTheory.Artinian.Module
import Mathlib.RingTheory.TensorProduct.Finite
import Mathlib.Tactic.Set

/-!
# finite set Of pullback fst eq of is Closed singleton
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Schemes.Proofs.finite_setOf_pullback_fst_eq_of_isClosed_singleton

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct

theorem _root_.AlgebraicGeometry.finite_setOf_pullback_fst_eq_of_isClosed_singleton
    {κ Ω : Type u} [Field κ] [Field Ω] [Algebra κ Ω]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of κ)) [LocallyOfFiniteType f]
    (z : X) (hz : IsClosed ({z} : Set X)) :
    {w : ↥(Limits.pullback f (Spec.map (CommRingCat.ofHom (algebraMap κ Ω)))) |
      (Limits.pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap κ Ω)))) w = z}.Finite := by
  classical
  set s := Spec.map (CommRingCat.ofHom (algebraMap κ Ω)) with hs
  have hr := Scheme.Pullback.range_snd (X.fromSpecResidueField z) (pullback.fst f s)
  rw [Scheme.range_fromSpecResidueField] at hr
  have hset : {w : ↥(pullback f s) | pullback.fst f s w = z} =
      Set.range (pullback.snd (X.fromSpecResidueField z) (pullback.fst f s)) := by
    rw [hr]; ext w; simp
  rw [hset]
  let φ : CommRingCat.of κ ⟶ X.residueField z := Spec.preimage (X.fromSpecResidueField z ≫ f)
  have hφ : Spec.map φ = X.fromSpecResidueField z ≫ f := Spec.map_preimage _
  let _ : Algebra κ (X.residueField z) := φ.hom.toAlgebra
  have hφ' : Spec.map (CommRingCat.ofHom (algebraMap κ (X.residueField z))) =
    X.fromSpecResidueField z ≫ f := by
    rw [← hφ]; rfl
  let _ : IsClosedImmersion (X.fromSpecResidueField z) :=
    isClosed_singleton_iff_isClosedImmersion.mp hz
  have hfin : IsFinite (X.fromSpecResidueField z ≫ f) :=
    isFinite_iff_locallyOfFiniteType_of_jacobsonSpace.mpr inferInstance
  let _ : Module.Finite κ (X.residueField z) := by
    rw [← hφ] at hfin
    exact (IsFinite.SpecMap_iff φ).mp hfin
  let e : pullback (X.fromSpecResidueField z) (pullback.fst f s) ≅
      Spec (CommRingCat.of (X.residueField z ⊗[κ] Ω)) :=
    pullbackRightPullbackFstIso f s (X.fromSpecResidueField z) ≪≫
      pullback.congrHom hφ'.symm rfl ≪≫ pullbackSpecIso κ (X.residueField z) Ω
  let _ : IsArtinianRing (Ω ⊗[κ] X.residueField z) := IsArtinianRing.of_finite Ω _
  let _ : Finite (PrimeSpectrum (Ω ⊗[κ] X.residueField z)) := inferInstance
  let _ : Finite (PrimeSpectrum (X.residueField z ⊗[κ] Ω)) :=
    Finite.of_equiv _ (PrimeSpectrum.comapEquiv (Algebra.TensorProduct.comm κ (X.residueField z)
      Ω).toRingEquiv).toEquiv.symm
  let _ : Finite ↥(Spec (CommRingCat.of (X.residueField z ⊗[κ] Ω))) :=
    inferInstanceAs (Finite (PrimeSpectrum (X.residueField z ⊗[κ] Ω)))
  let _ : Finite ↥(pullback (X.fromSpecResidueField z) (pullback.fst f s)) :=
    Finite.of_equiv _ (Scheme.homeoOfIso e).symm.toEquiv
  exact Set.finite_range _
end AlgebraicCurves.Geometry.Schemes.Proofs.finite_setOf_pullback_fst_eq_of_isClosed_singleton
end ProofImplementation
