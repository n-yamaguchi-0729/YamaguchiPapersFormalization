/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Kummer.DivisorClasses
import Mathlib.Data.ZMod.Basic

/-!
# Boundary residues of divisorial Kummer classes

For a set of omitted places, a function is unramified away from the boundary
when its orders there are divisible by the exponent. Boundary orders modulo
the exponent define a homomorphism on functions modulo powers. Its zero
residue representatives are exactly the everywhere-unramified functions
used in the proper Kummer comparison.

This file is divisor theory. The comparison with actual derived H¹ of an
open curve, and the image description by the degree-zero residue relation,
are separate results and are not assumed here.
-/

noncomputable section

namespace AlgebraicCurve.Pic0

variable (K F : Type*) [Field K] [Field F] [Algebra K F]

/-- Functions whose orders away from the omitted places are divisible by
the positive exponent. -/
def openKummerUnits (S : Set (Place K F)) (n : ℕ+) : Subgroup Fˣ where
  carrier := {u | ∀ v : Place K F, v ∉ S → (n : ℤ) ∣ v.ord (u : F)}
  one_mem' := by
    intro v _
    rw [Units.val_one, v.ord_one]
    exact dvd_zero _
  mul_mem' := by
    intro u w hu hw v hv
    rw [Units.val_mul, v.ord_mul (Units.ne_zero u) (Units.ne_zero w)]
    exact dvd_add (hu v hv) (hw v hv)
  inv_mem' := by
    intro u hu v hv
    rw [Units.val_inv_eq_inv_val, v.ord_inv]
    exact dvd_neg.mpr (hu v hv)

/-- Actual powers, viewed inside functions unramified away from the boundary. -/
def openKummerPowers (S : Set (Place K F)) (n : ℕ+) :
    Subgroup (openKummerUnits K F S n) :=
  (powMonoidHom (n : ℕ) : Fˣ →* Fˣ).range.comap
    (openKummerUnits K F S n).subtype

variable {K F}

/-- Boundary orders modulo the exponent, with the additive target written
multiplicatively to match multiplication of functions. -/
def openKummerResidue (S : Set (Place K F)) (n : ℕ+) :
    openKummerUnits K F S n →* Multiplicative (S → ZMod (n : ℕ)) where
  toFun u := Multiplicative.ofAdd (fun v => (v.val.ord (u.val : F) : ZMod (n : ℕ)))
  map_one' := by
    apply Multiplicative.toAdd.injective
    funext v
    change (v.val.ord (1 : F) : ZMod (n : ℕ)) = 0
    rw [v.val.ord_one, Int.cast_zero]
  map_mul' u w := by
    apply Multiplicative.toAdd.injective
    funext v
    change (v.val.ord ((u.val : F) * (w.val : F)) : ZMod (n : ℕ)) =
      (v.val.ord (u.val : F) : ZMod (n : ℕ)) +
        (v.val.ord (w.val : F) : ZMod (n : ℕ))
    rw [v.val.ord_mul (Units.ne_zero u.val) (Units.ne_zero w.val), Int.cast_add]

/-- Vanishing of all boundary residues fills in exactly the missing
divisibility conditions at the omitted places. -/
theorem openKummerResidue_eq_one_iff
    (S : Set (Place K F)) (n : ℕ+) (u : openKummerUnits K F S n) :
    openKummerResidue S n u = 1 ↔ u.val ∈ kummerUnits K F n := by
  constructor
  · intro h v
    by_cases hv : v ∈ S
    · have hzero := congrFun (congrArg Multiplicative.toAdd h) ⟨v, hv⟩
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd (v.ord (u.val : F)) (n : ℕ)).mp hzero
    · exact u.property v hv
  · intro h
    apply Multiplicative.toAdd.injective
    funext v
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd
      (v.val.ord (u.val : F)) (n : ℕ)).mpr (h v.val)

/-- Powers have zero boundary residue, so the residue map descends to
genuine Kummer classes rather than depending on a chosen function. -/
theorem openKummerPowers_le_residue_ker
    (S : Set (Place K F)) (n : ℕ+) :
    openKummerPowers K F S n ≤ (openKummerResidue S n).ker := by
  intro u hu
  change ∃ w : Fˣ, w ^ (n : ℕ) = u.val at hu
  obtain ⟨w, hw⟩ := hu
  apply (openKummerResidue_eq_one_iff S n u).mpr
  intro v
  have hval : (u.val : F) = (w : F) ^ (n : ℕ) := by
    exact (congrArg Units.val hw).symm
  rw [hval, ← zpow_natCast, v.ord_zpow]
  exact dvd_mul_right _ _

/-- Residues of functions unramified away from the boundary, modulo actual
powers of functions. -/
def openKummerResidueQuotient (S : Set (Place K F)) (n : ℕ+) :
    openKummerUnits K F S n ⧸ openKummerPowers K F S n →*
      Multiplicative (S → ZMod (n : ℕ)) :=
  QuotientGroup.lift (openKummerPowers K F S n) (openKummerResidue S n)
    (openKummerPowers_le_residue_ker S n)

/-- The quotient residue map is computed by the orders of any representative. -/
theorem openKummerResidueQuotient_mk
    (S : Set (Place K F)) (n : ℕ+) (u : openKummerUnits K F S n) :
    openKummerResidueQuotient S n (QuotientGroup.mk u) =
      openKummerResidue S n u := rfl

/-- Forget the divisibility conditions at the omitted places. -/
def kummerUnitsToOpen (S : Set (Place K F)) (n : ℕ+) :
    kummerUnits K F n →* openKummerUnits K F S n where
  toFun u := ⟨u.val, fun v _ => u.property v⟩
  map_one' := rfl
  map_mul' _ _ := rfl

/-- The inclusion of proper divisorial Kummer classes into open classes.
Both quotients use actual powers in the same function field. -/
def kummerQuotientToOpen (S : Set (Place K F)) (n : ℕ+) :
    kummerUnits K F n ⧸ kummerPowers K F n →*
      openKummerUnits K F S n ⧸ openKummerPowers K F S n :=
  QuotientGroup.map (kummerPowers K F n) (openKummerPowers K F S n)
    (kummerUnitsToOpen S n) (fun _ hu => hu)

/-- Filling in the boundary introduces no extra identifications between
proper Kummer classes. -/
theorem kummerQuotientToOpen_injective (S : Set (Place K F)) (n : ℕ+) :
    Function.Injective (kummerQuotientToOpen S n) := by
  intro x y h
  obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective x
  obtain ⟨v, rfl⟩ := QuotientGroup.mk_surjective y
  apply QuotientGroup.eq_iff_div_mem.mpr
  change (QuotientGroup.mk (kummerUnitsToOpen S n u) :
      openKummerUnits K F S n ⧸ openKummerPowers K F S n) =
    QuotientGroup.mk (kummerUnitsToOpen S n v) at h
  have hmem : kummerUnitsToOpen S n u / kummerUnitsToOpen S n v ∈
      openKummerPowers K F S n := QuotientGroup.eq_iff_div_mem.mp h
  change (u / v).val ∈ (powMonoidHom (n : ℕ) : Fˣ →* Fˣ).range
  exact hmem

/-- Exactness at open divisorial Kummer classes: zero boundary residue is
equivalent to coming from the proper curve's divisorial Kummer quotient. -/
theorem kummerQuotientToOpen_range
    (S : Set (Place K F)) (n : ℕ+) :
    (kummerQuotientToOpen S n).range =
      (openKummerResidueQuotient S n).ker := by
  apply Subgroup.ext
  intro x
  constructor
  · rintro ⟨y, rfl⟩
    obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective y
    change openKummerResidue S n (kummerUnitsToOpen S n u) = 1
    exact (openKummerResidue_eq_one_iff S n _).mpr u.property
  · intro hx
    obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective x
    have hu : u.val ∈ kummerUnits K F n :=
      (openKummerResidue_eq_one_iff S n u).mp hx
    refine ⟨QuotientGroup.mk (⟨u.val, hu⟩ : kummerUnits K F n), ?_⟩
    rfl

end AlgebraicCurve.Pic0
