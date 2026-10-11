/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Cohomology.GaloisH1Descent
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Mathlib.Data.Nat.GCD.Basic

/-! # Finite coefficients coprime to the actual covering index -/

noncomputable section

open CategoryTheory CategoryTheory.PreGaloisCategory AlgebraicGeometry

namespace EtaleFundamentalGroups.Cohomology

/-- The actual covering stabilizer has positive finite index, proved from
its finite geometric orbit. -/
theorem pointedCoverOpenSubgroup_index_pos
    {S : Scheme} [ConnectedSpace S] (A : FiniteEtale S)
    {Ω : Type} [Field Ω] [IsSepClosed Ω]
    (geom : Spec (.of Ω) ⟶ A.left) :
    0 < (pointedCoverOpenSubgroup A geom).toSubgroup.index := by
  let G := Aut (FiniteEtale.fiber (geom ≫ A.hom))
  let H : OpenSubgroup G := pointedCoverOpenSubgroup A geom
  have : Finite (G ⧸ H.toSubgroup) :=
    Finite.of_equiv (MulAction.orbit G (FiniteEtale.liftedFiberPoint A geom))
      (MulAction.orbitEquivQuotientStabilizer G (FiniteEtale.liftedFiberPoint A geom))
  change 0 < Nat.card (G ⧸ H.toSubgroup)
  exact Nat.card_pos

/-- Nontrivial roots-of-unity coefficients can always be chosen coprime
to the actual covering index; no prime-existence or coprimality hypothesis
is left to the geometric application. -/
theorem exists_rootsOfUnity_coefficient_coprime_index
    (K : Type) [Field K] [IsAlgClosed K] [CharZero K]
    {S : Scheme} [ConnectedSpace S] (A : FiniteEtale S)
    {Ω : Type} [Field Ω] [IsSepClosed Ω]
    (geom : Spec (.of Ω) ⟶ A.left) :
    ∃ n : ℕ+, 1 < (n : ℕ) ∧
      (Nat.card (Multiplicative
        (AddCommGrpCat.of (Additive (rootsOfUnity (n : ℕ) K))))).Coprime
          (pointedCoverOpenSubgroup A geom).toSubgroup.index := by
  let d := (pointedCoverOpenSubgroup A geom).toSubgroup.index
  have hd : 0 < d := pointedCoverOpenSubgroup_index_pos A geom
  let n : ℕ+ := ⟨d + 1, Nat.zero_lt_succ d⟩
  refine ⟨n, Nat.succ_lt_succ hd, ?_⟩
  have : NeZero ((n : ℕ) : K) := ⟨by exact_mod_cast n.ne_zero⟩
  change (Nat.card (rootsOfUnity (n : ℕ) K)).Coprime d
  rw [HasEnoughRootsOfUnity.natCard_rootsOfUnity]
  exact Nat.coprime_self_add_left.mpr (Nat.coprime_one_left d)

end EtaleFundamentalGroups.Cohomology
