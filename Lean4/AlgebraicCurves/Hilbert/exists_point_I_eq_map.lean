/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_HilbertFunctor_exists_point_I_eq_map.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
import AlgebraicCurves.Hilbert.Functor.Basic
import AlgebraicCurves.Hilbert.exists_linearEquiv_baseChange_piece_map

/-!
# exists point I eq map
-/

section ProofImplementation

namespace AlgebraicCurves.Hilbert.Proofs.S_AlgebraicGeometry_HilbertFunctor_exists_point_I_eq_map

open MvPolynomial AlgebraicGeometry.HilbertFunctor
open scoped TensorProduct

theorem _root_.AlgebraicGeometry.HilbertFunctor.exists_point_I_eq_map
    (n : ℕ) (h : ℕ → ℕ) (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (P : Point A n h) :
    ∃ Q : Point B n h, Q.I = P.I.map (MvPolynomial.map (algebraMap A B)) := by
  obtain ⟨hhom, hpiece⟩ :=
    AlgebraicGeometry.HilbertFunctor.exists_linearEquiv_baseChange_piece_map n A B P.I P.homogeneous
  have hfin : ∀ d, Module.Finite B (piece (P.I.map (MvPolynomial.map (algebraMap A B))) d) := by
    intro d
    obtain ⟨e, -⟩ := hpiece d
    have := P.finite_piece d
    exact Module.Finite.equiv e
  have hproj : ∀ d, Module.Projective B (piece (P.I.map (MvPolynomial.map (algebraMap A B))) d) :=
    by
    intro d
    obtain ⟨e, -⟩ := hpiece d
    have := P.projective_piece d
    have : Module.Projective B (B ⊗[A] piece P.I d) := Module.Projective.tensorProduct
    exact Module.Projective.of_equiv e
  have hrank : ∀ (d : ℕ) (q : PrimeSpectrum B),
      Module.rankAtStalk (piece (P.I.map (MvPolynomial.map (algebraMap A B))) d) q = h d := by
    intro d q
    obtain ⟨e, -⟩ := hpiece d
    have := P.finite_piece d
    have := P.projective_piece d
    rw [← congrArg (fun g => g q) (Module.rankAtStalk_eq_of_equiv e), Module.rankAtStalk_baseChange,
      P.rankAtStalk_piece]
  exact ⟨{ I := P.I.map (MvPolynomial.map (algebraMap A B))
           homogeneous := hhom
           finite_piece := hfin
           projective_piece := hproj
           rankAtStalk_piece := hrank }, rfl⟩
end AlgebraicCurves.Hilbert.Proofs.S_AlgebraicGeometry_HilbertFunctor_exists_point_I_eq_map
end ProofImplementation
