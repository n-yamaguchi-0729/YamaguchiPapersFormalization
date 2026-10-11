/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.Algebra.Category.ModuleCat.Ext.HasExt
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Tactic.Abel
import Mathlib.RingTheory.Ideal.Quotient.Defs

/-!
# Mayer--Vietoris Ext sequence for two ideal quotients

For ideals `I` and `J`, the standard sequence

`0 → R/(I ∩ J) → R/I ⊕ R/J → R/(I + J) → 0`

is short exact.  Applying contravariant derived Ext gives its six-term
exact sequence.  This is the finite-stage algebraic input for a future
Mayer--Vietoris construction in local cohomology; no comparison with the
legacy Ext colimit used by `localCohomology` is asserted here.
-/

noncomputable section

open CategoryTheory Limits

namespace EtaleFundamentalGroups

universe u

variable {R : Type u} [CommRing R]

/-- The linear map between ideal quotients induced by an inclusion. -/
def idealQuotientMapOfLE {I J : Ideal R} (h : I ≤ J) :
    (R ⧸ I) →ₗ[R] (R ⧸ J) :=
  Submodule.mapQ I J LinearMap.id h

@[simp]
theorem idealQuotientMapOfLE_mk {I J : Ideal R} (h : I ≤ J) (r : R) :
    idealQuotientMapOfLE h (Submodule.Quotient.mk r) =
      Submodule.Quotient.mk r := by
  rfl

/-- The diagonal map from the quotient by the intersection to the product
of the two quotients. -/
def idealQuotientMayerVietorisDiagonal (I J : Ideal R) :
    (R ⧸ I ⊓ J) →ₗ[R] (R ⧸ I) × (R ⧸ J) :=
  (idealQuotientMapOfLE inf_le_left).prod
    (idealQuotientMapOfLE inf_le_right)

/-- The difference map from the product of the two quotients to the quotient
by their sum. -/
def idealQuotientMayerVietorisDifference (I J : Ideal R) :
    ((R ⧸ I) × (R ⧸ J)) →ₗ[R] (R ⧸ I ⊔ J) :=
  (idealQuotientMapOfLE le_sup_left).comp
      (LinearMap.fst R (R ⧸ I) (R ⧸ J)) -
    (idealQuotientMapOfLE le_sup_right).comp
      (LinearMap.snd R (R ⧸ I) (R ⧸ J))

theorem idealQuotientMayerVietorisDifference_comp_diagonal
    (I J : Ideal R) :
    (idealQuotientMayerVietorisDifference I J).comp
        (idealQuotientMayerVietorisDiagonal I J) = 0 := by
  apply LinearMap.ext
  intro z
  induction z using Submodule.Quotient.induction_on with
  | _ r =>
      change (Ideal.Quotient.mk (I ⊔ J)) r -
        (Ideal.Quotient.mk (I ⊔ J)) r = 0
      simp

theorem idealQuotientMayerVietorisDiagonal_injective (I J : Ideal R) :
    Function.Injective (idealQuotientMayerVietorisDiagonal I J) := by
  intro x y hxy
  induction x using Submodule.Quotient.induction_on with
  | _ r =>
    induction y using Submodule.Quotient.induction_on with
    | _ s =>
      apply (Submodule.Quotient.eq (I ⊓ J)).mpr
      have hI : r - s ∈ I := by
        have h := congrArg Prod.fst hxy
        exact (Submodule.Quotient.eq I).mp h
      have hJ : r - s ∈ J := by
        have h := congrArg Prod.snd hxy
        exact (Submodule.Quotient.eq J).mp h
      exact ⟨hI, hJ⟩

theorem idealQuotientMayerVietorisDifference_surjective (I J : Ideal R) :
    Function.Surjective (idealQuotientMayerVietorisDifference I J) := by
  intro z
  induction z using Submodule.Quotient.induction_on with
  | _ r =>
      refine ⟨(Submodule.Quotient.mk r, 0), ?_⟩
      change (Ideal.Quotient.mk (I ⊔ J)) r - 0 =
        (Ideal.Quotient.mk (I ⊔ J)) r
      simp

theorem idealQuotientMayerVietoris_functionExact (I J : Ideal R) :
    Function.Exact (idealQuotientMayerVietorisDiagonal I J)
      (idealQuotientMayerVietorisDifference I J) := by
  rw [LinearMap.exact_iff]
  ext z
  constructor
  · intro hz
    rcases z with ⟨x, y⟩
    induction x using Submodule.Quotient.induction_on with
    | _ r =>
      induction y using Submodule.Quotient.induction_on with
      | _ s =>
        have hrs : r - s ∈ I ⊔ J :=
          Ideal.Quotient.eq_zero_iff_mem.mp hz
        rw [Submodule.mem_sup] at hrs
        obtain ⟨i, hi, j, hj, hij⟩ := hrs
        refine ⟨Submodule.Quotient.mk (r - i), ?_⟩
        change
          ((Ideal.Quotient.mk I) (r - i),
            (Ideal.Quotient.mk J) (r - i)) =
          ((Ideal.Quotient.mk I) r, (Ideal.Quotient.mk J) s)
        apply Prod.ext
        · apply (Submodule.Quotient.eq I).mpr
          have heq : (r - i) - r = -i := by abel
          rw [heq]
          exact I.neg_mem hi
        · apply (Submodule.Quotient.eq J).mpr
          have hri : r - i = s + j := by
            calc
              r - i = (r - s) + s - i := by abel
              _ = (i + j) + s - i := by rw [hij]
              _ = s + j := by abel
          rw [hri]
          simpa using hj
  · rintro ⟨w, rfl⟩
    change
      idealQuotientMayerVietorisDifference I J
          (idealQuotientMayerVietorisDiagonal I J w) = 0
    exact LinearMap.congr_fun
      (idealQuotientMayerVietorisDifference_comp_diagonal I J) w

/-- The standard Mayer--Vietoris short complex of ideal quotients. -/
def idealQuotientMayerVietorisShortComplex (I J : Ideal R) :
    ShortComplex (ModuleCat.{u} R) :=
  ShortComplex.moduleCatMk
    (idealQuotientMayerVietorisDiagonal I J)
    (idealQuotientMayerVietorisDifference I J)
    (idealQuotientMayerVietorisDifference_comp_diagonal I J)

/-- The standard Mayer--Vietoris sequence of ideal quotients is short exact. -/
theorem idealQuotientMayerVietorisShortComplex_shortExact (I J : Ideal R) :
    (idealQuotientMayerVietorisShortComplex I J).ShortExact := by
  exact ModuleCat.shortComplex_shortExact _
    (idealQuotientMayerVietoris_functionExact I J)
    (idealQuotientMayerVietorisDiagonal_injective I J)
    (idealQuotientMayerVietorisDifference_surjective I J)

/-- Contravariant derived Ext sends the ideal-quotient Mayer--Vietoris
short exact sequence to its exact six-term sequence in adjacent degrees. -/
theorem idealQuotientMayerVietorisExtSequence_exact
    (I J : Ideal R) (M : ModuleCat.{u} R) (i : ℕ) :
    (CategoryTheory.Abelian.Ext.contravariantSequence
      (idealQuotientMayerVietorisShortComplex_shortExact I J)
      M i (i + 1) (by omega)).Exact :=
  CategoryTheory.Abelian.Ext.contravariantSequence_exact
    (idealQuotientMayerVietorisShortComplex_shortExact I J)
    M i (i + 1) (by omega)

end EtaleFundamentalGroups

end
