/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_flat_and_surjective_of_forall_exists_iso_morphismRestrict_eq_pullback_fst.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
import Mathlib.AlgebraicGeometry.Morphisms.Basic
import Mathlib.AlgebraicGeometry.Morphisms.RingHomProperties
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.Tactic.Choose

/-!
# flat and surjective of forall exists iso morphism Restrict eq pullback fst
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Schemes.Proofs
namespace flat_and_surjective_of_forall_exists_iso_morphismRestrict_eq_pullback_fst

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace S1C
namespace TorsorFlat

theorem of_forall_exists_iso_morphismRestrict_eq_pullback_fst (P : MorphismProperty Scheme.{u})
    [IsZariskiLocalAtTarget P] [P.IsStableUnderBaseChange]
    {S D B G : Scheme.{u}} (g : G ⟶ S) (hg : P g) (b : B ⟶ S) (π : D ⟶ B)
    (hloc : ∀ p : B, ∃ U : B.Opens, p ∈ U ∧
      ∃ e : (π ⁻¹ᵁ U : Scheme.{u}) ≅ pullback (U.ι ≫ b) g,
        e.hom ≫ pullback.fst (U.ι ≫ b) g = π ∣_ U) :
    P π := by
  choose U hpU e he using hloc
  have hU : iSup U = ⊤ := top_le_iff.mp fun p _ => TopologicalSpace.Opens.mem_iSup.mpr ⟨p, hpU p⟩
  refine IsZariskiLocalAtTarget.of_iSup_eq_top U hU fun p => ?_
  rw [← he p, P.cancel_left_of_respectsIso]
  exact P.pullback_fst _ _ hg

end S1C.TorsorFlat

theorem
  _root_.AlgebraicGeometry.flat_and_surjective_of_forall_exists_iso_morphismRestrict_eq_pullback_fst
    {S D B G : Scheme.{u}} (g : G ⟶ S) [Flat g] [Surjective g] (b : B ⟶ S) (π : D ⟶ B)
    (hloc : ∀ p : B, ∃ U : B.Opens, p ∈ U ∧
      ∃ e : (π ⁻¹ᵁ U : Scheme.{u}) ≅ pullback (U.ι ≫ b) g,
        e.hom ≫ pullback.fst (U.ι ≫ b) g = π ∣_ U) :
    Flat π ∧ Surjective π := by
  have hFlat : HasAffineProperty (@Flat.{u}) (sourceAffineLocally RingHom.Flat) :=
    HasRingHomProperty.HasAffineProperty (P := @Flat.{u}) (Q := RingHom.Flat)
  have : IsZariskiLocalAtTarget (@Flat.{u}) := (HasAffineProperty.iff.mp hFlat).1
  exact ⟨S1C.TorsorFlat.of_forall_exists_iso_morphismRestrict_eq_pullback_fst (@Flat.{u}) g ‹_› b π
    hloc,
    S1C.TorsorFlat.of_forall_exists_iso_morphismRestrict_eq_pullback_fst @Surjective g ‹_› b π hloc⟩
end flat_and_surjective_of_forall_exists_iso_morphismRestrict_eq_pullback_fst
end AlgebraicCurves.Geometry.Schemes.Proofs
end ProofImplementation
