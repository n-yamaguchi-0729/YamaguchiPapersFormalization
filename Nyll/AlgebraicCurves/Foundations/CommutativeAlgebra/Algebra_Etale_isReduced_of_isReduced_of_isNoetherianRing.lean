/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_Algebra_Etale_isReduced_of_isReduced_of_isNoetherianRing.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.AlgebraicGeometry.Geometrically.Reduced
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.RingTheory.Etale.Basic
import Mathlib.RingTheory.Smooth.Flat
import Mathlib.RingTheory.Unramified.Field

/-!
# Algebra Etale is Reduced of is Reduced of is Noetherian Ring
-/

section ProofImplementation

namespace AlgebraicCurves.Foundations.CommutativeAlgebra.Proofs
namespace Algebra_Etale_isReduced_of_isReduced_of_isNoetherianRing

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace EtaleReducedAux

theorem geometricallyReduced_specMap (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
  [Algebra.Etale R S] :
    GeometricallyReduced (Spec.map (CommRingCat.ofHom (algebraMap R S))) := by
  constructor
  intro K _ y Z fst snd hP
  obtain ⟨φ, rfl⟩ : ∃ φ, Spec.map φ = y := ⟨Spec.preimage y, Spec.map_preimage y⟩
  let : Algebra R K := φ.hom.toAlgebra
  have hP' : IsPullback fst snd (Spec.map (CommRingCat.ofHom (algebraMap R S)))
      (Spec.map (CommRingCat.ofHom (algebraMap R K))) := hP
  have : _root_.IsReduced (K ⊗[R] S) := Algebra.FormallyUnramified.isReduced_of_field K (K ⊗[R] S)
  have : _root_.IsReduced (S ⊗[R] K) :=
    isReduced_of_injective (Algebra.TensorProduct.comm R S K).toRingHom (Algebra.TensorProduct.comm
      R S K).injective
  have : AlgebraicGeometry.IsReduced (Spec (CommRingCat.of (S ⊗[R] K))) := (affine_isReduced_iff
    _).mpr ‹_›
  exact isReduced_of_isOpenImmersion (hP'.isoPullback ≪≫ pullbackSpecIso R S K).hom

end EtaleReducedAux

theorem _root_.Algebra.Etale.isReduced_of_isReduced_of_isNoetherianRing
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    [IsNoetherianRing R] [_root_.IsReduced R] [Algebra.Etale R S] :
    _root_.IsReduced S := by
  have : Flat (Spec.map (CommRingCat.ofHom (algebraMap R S))) := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    exact RingHom.flat_algebraMap_iff.mpr inferInstance
  have := EtaleReducedAux.geometricallyReduced_specMap R S
  have h := GeometricallyReduced.isReduced_of_flat_of_isLocallyNoetherian
    (Spec.map (CommRingCat.ofHom (algebraMap R S)))
  exact (affine_isReduced_iff (CommRingCat.of S)).mp h
end Algebra_Etale_isReduced_of_isReduced_of_isNoetherianRing
end AlgebraicCurves.Foundations.CommutativeAlgebra.Proofs
end ProofImplementation
