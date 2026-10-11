/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Purity.FiniteEtaleQuotientLift
import Mathlib.RingTheory.Etale.Finite

/-!
# Essential surjectivity of finite-etale base change to a quotient

For a complete Noetherian local ring, every finite-etale algebra over a
quotient by an ideal in the maximal ideal comes by base change from the
original ring.  This file packages the algebraic lifting theorem as the
canonical categorical `EssSurj` statement for finite-etale algebras.
-/

noncomputable section

namespace EtaleFundamentalGroups

open CategoryTheory IsLocalRing

universe u

/-- Finite-etale base change from a complete Noetherian local ring to any
quotient by an ideal contained in the maximal ideal is essentially
surjective. -/
theorem finiteEtale_baseChange_essSurj_of_quotient
    {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [IsAdicComplete (maximalIdeal R) R]
    (I : Ideal R) (hI : I ≤ maximalIdeal R) :
    (CommAlgCat.FiniteEtale.baseChange.{u} R (R ⧸ I)).EssSurj := by
  refine ⟨fun D ↦ ?_⟩
  obtain ⟨C, hCcomm, hCalgebra, hCfinite, hCetale, hbase⟩ :=
    exists_finiteEtale_lift_of_quotient I hI
      (D := D.obj)
  let : CommRing C := hCcomm
  let : Algebra R C := hCalgebra
  let : Module.Finite R C := hCfinite
  let : Algebra.Etale R C := hCetale
  let C' : CommAlgCat.FiniteEtale.{u} R :=
    CommAlgCat.FiniteEtale.of R C
  exact ⟨C', ⟨CommAlgCat.FiniteEtale.isoMk (Classical.choice hbase)⟩⟩

end EtaleFundamentalGroups

end
