/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AnabelianGeometry.GeometricFundamentalGroup.LaurentKummerAlgebra
import Nyll.EtaleFundamentalGroups.GaloisCovers.Basic
import Nyll.EtaleFundamentalGroups.FiniteEtale.Connected
import Nyll.SchemeTheory.Pi1.FiniteEtale.Basic
import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
import Mathlib.RingTheory.Spectrum.Prime.FreeLocus

/-!
# Actual connected finite-etale Kummer covers of every positive degree

Taking the spectrum of the explicit Kummer algebra produces the cover. Its source is
connected because the algebra is a domain, and its actual geometric fibre has the
prescribed cardinality by the power basis and the finite-etale rank comparison.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.FiniteEtale

namespace AnabelianGeometry.GeometricFundamentalGroup

universe u

/-- Every positive degree occurs for an actual connected finite-etale cover of the Laurent
chart, uniformly at every separably closed geometric point. -/
theorem exists_connected_finite_etale_laurent_of_degree
    (K : Type u) [Field K] [CharZero K] {n : ℕ} (hn : 0 < n) :
    ∃ Y : FiniteEtale (Spec (CommRingCat.of (LaurentPolynomial K))),
      ConnectedSpace Y.left ∧
      ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω]
        (ξ : Spec (CommRingCat.of Ω) ⟶ Spec (CommRingCat.of (LaurentPolynomial K))),
        Nat.card ((fiber ξ).obj Y) = n := by
  let A := LaurentPolynomial K
  let S := LaurentKummerAlgebra K n
  have hdomain : IsDomain S := isDomain_laurentKummerAlgebra K hn
  obtain ⟨hfinite, hfree, hrank⟩ := finite_free_finrank_laurentKummerAlgebra K hn
  have hetale : Algebra.Etale A S := etale_laurentKummerAlgebra K hn
  let π : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of A) :=
    Spec.map (CommRingCat.ofHom (algebraMap A S))
  have hπ : IsFiniteEtale π := by
    rw [IsFiniteEtale.SpecMap_iff, CommRingCat.hom_ofHom,
      RingHom.finiteEtale_algebraMap_iff]
    constructor
  let Y : FiniteEtale (Spec (CommRingCat.of A)) := FiniteEtale.mk π
  have connected : ConnectedSpace Y.left := by
    change ConnectedSpace (PrimeSpectrum S)
    infer_instance
  refine ⟨Y, connected, ?_⟩
  intro Ω fieldΩ closedΩ ξ
  rw [natCard_fiber_eq_finrank ξ Y]
  change π.finrank (ξ (IsLocalRing.closedPoint Ω)) = n
  exact (Scheme.Hom.finrank_SpecMap_algebraMap A S _).trans
    ((congrFun (Module.rankAtStalk_eq_finrank_of_free (R := A) (M := S)) _).trans hrank)

end AnabelianGeometry.GeometricFundamentalGroup
