/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Anthropic FLT source material is identified by code comparison;
the exact source-file correspondence remains unresolved.
Upstream repository: https://github.com/anthropics/fermats-last-theorem
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Cohomology.LogDeRham

/-!
# Place exists irreducible d Coord eq D and has Pole Order LE iff
-/

section ProofImplementation

namespace AlgebraicCurves.Places.Proofs.Place_exists_irreducible_dCoord_eq_D_and_hasPoleOrderLE_iff

open KaehlerDifferential

theorem _root_.AlgebraicCurve.Place.exists_irreducible_dCoord_eq_D_and_hasPoleOrderLE_iff
    {K F : Type*} [Field K] [Field F] [Algebra K F] (v : AlgebraicCurve.Place K F) :
    ∃ π : v.toValuationSubring, Irreducible π ∧
      v.dCoord = KaehlerDifferential.D K F (π : F) ∧
      (∀ (n : ℕ) (ω : Ω[F⁄K]), v.HasPoleOrderLE n ω ↔
        ∃ f : F, (π : F) ^ n * f ∈ v.toValuationSubring ∧ ω = f • v.dCoord) ∧
      (∀ (n : ℕ) (g : F), v.FnPoleOrderLE n g ↔ (π : F) ^ n * g ∈ v.toValuationSubring) ∧
      (∀ (ω : Ω[F⁄K]) (a : K), v.HasLogResidue ω a ↔
        ∃ f : F, ω = f • v.dCoord ∧ v.HasValue ((π : F) * f) a) := by
  exact ⟨_, (IsDiscreteValuationRing.exists_irreducible v.toValuationSubring).choose_spec, rfl,
    fun _ _ => Iff.rfl, fun _ _ => Iff.rfl, fun _ _ => Iff.rfl⟩
end AlgebraicCurves.Places.Proofs.Place_exists_irreducible_dCoord_eq_D_and_hasPoleOrderLE_iff
end ProofImplementation
