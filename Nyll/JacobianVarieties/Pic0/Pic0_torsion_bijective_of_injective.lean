/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_Pic0_torsion_bijective_of_injective.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.JacobianVarieties.Autoduality.Cohomology
import Mathlib.GroupTheory.FiniteAbelian.Duality
import Mathlib.RingTheory.RootsOfUnity.EnoughRootsOfUnity
import Mathlib.SetTheory.Cardinal.Finite

/-!
An injective map from Picard torsion to its character group is bijective under the
finite-cardinality and roots-of-unity hypotheses.
-/

section ProofImplementation

namespace JacobianVarieties.Pic0.Proofs.Pic0_torsion_bijective_of_injective


noncomputable section

namespace AlgebraicCurve
open _root_.AlgebraicCurve
open _root_.AlgebraicCurve

namespace WC6Sol

/-- A homomorphism from a group to a monoid factors uniquely through its units. -/
def monoidHomUnitsEquiv (G M : Type*) [Group G] [Monoid M] :
    (G →* M) ≃ (G →* Mˣ) where
  toFun := MonoidHom.toHomUnits
  invFun φ := (Units.coeHom M).comp φ
  left_inv _ := MonoidHom.ext fun _ => rfl
  right_inv _ := MonoidHom.ext fun _ => Units.ext rfl

theorem card_addChar_eq_of_exponent {A K : Type*} [AddCommGroup A] [Field K]
    [Finite A] [HasEnoughRootsOfUnity K (Monoid.exponent (Multiplicative A))] :
    Nat.card (AddChar A K) = Nat.card A := by
  rw [Nat.card_congr
    (AddChar.toMonoidHomEquiv.trans (monoidHomUnitsEquiv (Multiplicative A) K))]
  exact CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity (Multiplicative A) K

theorem card_addChar_eq {A K : Type*} [AddCommGroup A] [Field K] [Finite A]
    {n : ℕ} [NeZero n] [HasEnoughRootsOfUnity K n] (hn : ∀ a : A, n • a = 0) :
    Nat.card (AddChar A K) = Nat.card A := by
  have hdvd : Monoid.exponent (Multiplicative A) ∣ n :=
    Monoid.exponent_dvd_of_forall_pow_eq_one fun a => by
      rw [← ofAdd_toAdd a, ← ofAdd_nsmul, hn, ofAdd_zero]
  have : HasEnoughRootsOfUnity K (Monoid.exponent (Multiplicative A)) :=
    HasEnoughRootsOfUnity.of_dvd K hdvd
  exact card_addChar_eq_of_exponent

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem card_homPic0Gm_eq {n : ℕ} [NeZero n] [HasEnoughRootsOfUnity K n]
    [Finite (Pic0.torsion K F n)] :
    Nat.card (HomPic0Gm K F n) = Nat.card (Pic0.torsion K F n) :=
  card_addChar_eq HomPic0Gm.nsmul_eq_zero

end WC6Sol

end AlgebraicCurve

open _root_.AlgebraicCurve

theorem _root_.AlgebraicCurve.Pic0.torsion.bijective_of_injective {K F : Type*} [Field K] [Field F]
    [Algebra K F] {n : ℕ} [NeZero n] [HasEnoughRootsOfUnity K n] [Finite (Pic0.torsion K F n)]
    (f : Pic0.torsion K F n →+ Additive (HomPic0Gm K F n)) (hf : Function.Injective f) :
    Function.Bijective f := by
  have hcard : Nat.card (Additive (HomPic0Gm K F n)) = Nat.card (Pic0.torsion K F n) :=
    AlgebraicCurve.WC6Sol.card_homPic0Gm_eq
  have hfinH : Finite (HomPic0Gm K F n) :=
    Nat.finite_of_card_ne_zero (by
      rw [AlgebraicCurve.WC6Sol.card_homPic0Gm_eq (K := K) (F := F) (n := n)]
      exact Nat.card_pos.ne')
  have hfinA : Finite (Additive (HomPic0Gm K F n)) := hfinH
  exact (Nat.bijective_iff_injective_and_card f).mpr ⟨hf, hcard.symm⟩

end
end JacobianVarieties.Pic0.Proofs.Pic0_torsion_bijective_of_injective
end ProofImplementation
