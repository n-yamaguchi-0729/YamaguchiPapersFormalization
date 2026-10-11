/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Yamaguchi26AbfaithfulGalois.FormalHilbert90.FiniteH1Surjectivity
import GaloisCohomology.Kummer.Concrete.CyclotomicOpenCocycleLifting
import Mathlib.Topology.Instances.ZMod

/-!
# Cyclotomic orientations satisfy formal Hilbert 90

The orientation is the actual cyclotomic character on the field automorphisms.
Hilbert 90 supplies the cohomology reduction on every open subgroup.
-/

namespace Yamaguchi26AbfaithfulGalois
universe u v
variable (p : ℕ) [Fact p.Prime]
variable (K : Type u) (Ω : Type v) [Field K] [Field Ω] [Algebra K Ω]

/-- The field-theoretic cyclotomic character as a continuous orientation. -/
noncomputable def galoisCyclotomicOrientation : Orientation p Gal(Ω/K) where
  toMonoidHom :=
    (cyclotomicCharacter Ω p).comp (MulSemiringAction.toRingAut Gal(Ω/K) Ω)
  continuous_toFun := cyclotomicCharacter.continuous p K Ω

/-- Cyclotomic formal Hilbert 90 for a separably closed Galois extension. -/
theorem formalHilbert90_galoisCyclotomicOrientation
    [IsGalois K Ω] [IsSepClosed Ω] [NeZero (p : Ω)] :
    FormalHilbert90 (galoisCyclotomicOrientation p K Ω) := by
  intro H n hn
  cases n with
  | zero => omega
  | succ k =>
    apply h1_reduction_surjective_of_finiteCocycle_lifting
    intro c
    obtain ⟨d, hdlc, hd, hred⟩ := KummerTheory.exists_cyclotomic_cocycle_lift_open
      p H k c.toFun c.cocycle
      ((IsLocallyConstant.iff_continuous c.toFun).mpr c.continuous_toFun)
    exact ⟨⟨d, (IsLocallyConstant.iff_continuous d).mp hdlc, hd⟩, hred⟩

end Yamaguchi26AbfaithfulGalois
