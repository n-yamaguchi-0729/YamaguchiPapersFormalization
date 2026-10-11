/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Kummer.NormalCrossings.Scheme
import Nyll.SchemeTheory.LocalGeometry.HeightTwo.NonunitLocalization
import Nyll.SchemeTheory.Divisors.NormalCrossings.BranchSelection

/-!
# Height-two arithmetic specializations of normal-crossings branches

At a strict-normal-crossings point, a height-one boundary prime is one of
the active parameter ideals.  A positive integer which is noninvertible on
that branch then produces a height-two prime containing the branch.  This
is the intrinsic codimension-two reduction used by local ramification
arguments; the height-two prime is a conclusion, not input data.
-/

noncomputable section

open EtaleFundamentalGroups

namespace AlgebraicGeometry.Scheme.IdealSheafData

universe u uk

variable {X : Scheme.{u}} {I : X.IdealSheafData} {x : X}

/-- A positive integer which is noninvertible on a height-one branch at a
strict-normal-crossings point cuts out a height-two specialization of that
branch.  No finite-type, Nagata, or arithmetic-base hypothesis is used. -/
theorem IsStrictNormalCrossingsAt.exists_heightTwoPrime_of_branch_nonunit_natCast
    (hI : I.IsStrictNormalCrossingsAt x)
    (q : Ideal (X.presheaf.stalk x)) [q.IsPrime]
    (hqheight : q.height = 1)
    (hIq : I.stalkIdeal x ≤ q)
    (e : ℕ) (he : 0 < e)
    [CharZero (X.presheaf.stalk x ⧸ q)]
    (he_nonunit : ¬ IsUnit (e : X.presheaf.stalk x ⧸ q)) :
    ∃ (P : Ideal (X.presheaf.stalk x)) (_ : P.IsPrime),
      q < P ∧ P.height = 2 ∧
        ¬ IsUnit
          (algebraMap (X.presheaf.stalk x) (Localization.AtPrime P)
            (e : X.presheaf.stalk x)) := by
  let A := X.presheaf.stalk x
  let hregular : IsRegularLocalRing A := hI.1
  let : IsLocalRing A := hregular.toIsLocalRing
  let : IsNoetherianRing A := hregular.toIsNoetherian
  obtain ⟨d, r, t, _hrpos, _hr, _hparams, hideal, hdomain,
      hprime, _hquotient⟩ := hI.localParameterGeometry
  let : IsDomain A := hdomain
  have hprod : boundaryProduct t r ∈ q := by
    apply hIq
    rw [hideal]
    exact Ideal.mem_span_singleton_self _
  obtain ⟨i, hi, hq⟩ :=
    exists_activeBranch_eq_of_heightOnePrime_mem_boundaryProduct
      hprime q hqheight hprod
  subst q
  obtain ⟨P, hPprime, _hPminimal, hbranchP, hPheight, heP⟩ :=
    exists_heightTwo_prime_of_nonunit_natCast_mod_prime
      (t i) (hprime i hi) e he he_nonunit
  exact ⟨P, hPprime, hbranchP, hPheight, heP⟩

/-- A positive residue characteristic reached from a height-one branch
produces a height-two specialization of that branch.  Noninvertibility of
the characteristic is derived from the residue-field map. -/
theorem IsStrictNormalCrossingsAt.exists_heightTwoPrime_of_branch_residueCharacteristic
    (hI : I.IsStrictNormalCrossingsAt x)
    (q : Ideal (X.presheaf.stalk x)) [q.IsPrime]
    (hqheight : q.height = 1)
    (hIq : I.stalkIdeal x ≤ q)
    {k : Type uk} [CommRing k] [Nontrivial k]
    (phi : (X.presheaf.stalk x ⧸ q) →+* k)
    (p : ℕ) [CharZero (X.presheaf.stalk x ⧸ q)]
    [CharP k p] (hp : p.Prime) :
    ∃ (P : Ideal (X.presheaf.stalk x)) (_ : P.IsPrime),
      q < P ∧ P.height = 2 ∧
        ¬ IsUnit
          (algebraMap (X.presheaf.stalk x) (Localization.AtPrime P)
            (p : X.presheaf.stalk x)) := by
  have hp_nonunit :
      ¬ IsUnit (p : X.presheaf.stalk x ⧸ q) := by
    intro hp_unit
    have hp_image : IsUnit (phi (p : X.presheaf.stalk x ⧸ q)) :=
      hp_unit.map phi
    exact not_isUnit_zero (M₀ := k) (by
      simpa only [map_natCast, CharP.cast_eq_zero] using hp_image)
  exact hI.exists_heightTwoPrime_of_branch_nonunit_natCast
    q hqheight hIq p hp.pos hp_nonunit

/-- Global strict normal crossings supplies the pointwise height-two
specialization above any height-one branch containing the boundary stalk
ideal.  Membership of the point in the boundary support is derived from
that containment. -/
theorem IsStrictNormalCrossings.exists_heightTwoPrime_of_branch_residueCharacteristic
    (hI : I.IsStrictNormalCrossings)
    (q : Ideal (X.presheaf.stalk x)) [q.IsPrime]
    (hqheight : q.height = 1)
    (hIq : I.stalkIdeal x ≤ q)
    {k : Type uk} [CommRing k] [Nontrivial k]
    (phi : (X.presheaf.stalk x ⧸ q) →+* k)
    (p : ℕ) [CharZero (X.presheaf.stalk x ⧸ q)]
    [CharP k p] (hp : p.Prime) :
    ∃ (P : Ideal (X.presheaf.stalk x)) (_ : P.IsPrime),
      q < P ∧ P.height = 2 ∧
        ¬ IsUnit
          (algebraMap (X.presheaf.stalk x) (Localization.AtPrime P)
            (p : X.presheaf.stalk x)) := by
  have hxI : x ∈ I.support := by
    rw [← X.fromSpecStalk_closedPoint (x := x)]
    apply I.mem_support_fromSpecStalk_of_stalkIdeal_le
    exact hIq.trans
      (IsLocalRing.le_maximalIdeal (inferInstance : q.IsPrime).ne_top)
  exact (hI x hxI).exists_heightTwoPrime_of_branch_residueCharacteristic
    q hqheight hIq phi p hp

end AlgebraicGeometry.Scheme.IdealSheafData

end
