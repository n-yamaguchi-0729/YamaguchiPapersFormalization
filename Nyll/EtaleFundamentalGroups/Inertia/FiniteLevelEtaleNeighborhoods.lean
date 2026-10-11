/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Inertia.FiniteGaloisInvariantNeighborhood
import Nyll.SchemeTheory.RingTheory.Ramification.FiniteLevelInertiaLocalization
import Nyll.SchemeTheory.RingTheory.Localization.AwayAlgebra
import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.Algebra.Algebra.Tower
import Mathlib.Algebra.Group.Submonoid.Membership
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.CategoryTheory.Filtered.Basic
import Mathlib.FieldTheory.Galois.GaloisClosure
import Mathlib.RingTheory.Etale.Basic
import Mathlib.RingTheory.Ideal.Prime
import Mathlib.RingTheory.IntegralClosure.IntegralRestrict
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Localization.Basic


/-!
# Actual finite-level principal étale neighborhoods

The finite-Galois normalization theorem supplies an étale denominator at
each actual invariant stage. Multiplying it by any prescribed denominator
outside the contracted prime gives a further étale neighborhood. These
neighborhoods form a nonempty directed preorder: at a common finite Galois
level, multiply an étale denominator by the two transported denominators.

The transition condition uses divisibility of the literal transported
denominator. It therefore supplies the unit needed by the native Away map.
This file constructs the actual index and its filteredness; the diagram and
its colimit are separate declarations.
-/

noncomputable section

open CategoryTheory SchemeTheory

namespace EtaleFundamentalGroups.Inertia

universe u v w

/- The sparse transport helpers apply native localization owners with the
literal carriers exposed. They do not install another scalar action. -/
private def awayEquiv {A : Type u} {R : Type v} {S : Type w}
    [CommRing A] [CommRing R] [CommRing S] [Algebra A R] [Algebra A S]
    (e : R ≃ₐ[A] S) (f : R) :
    localizationAwayCommAlgCat A R f ≃ₐ[A] localizationAwayCommAlgCat A S (e f) := by
  change Localization.Away f ≃ₐ[A] Localization.Away (e f)
  exact IsLocalization.algEquivOfAlgEquiv (Localization.Away f)
    (Localization.Away (e f)) e (Submonoid.map_powers e f)

private theorem etale_away_mul {A : Type u} {R : Type w}
    [CommRing A] [CommRing R] [Algebra A R] (f d : R)
    [Algebra.Etale A (localizationAwayCommAlgCat A R f)] :
    Algebra.Etale A (localizationAwayCommAlgCat A R (f * d)) := by
  change Algebra.Etale A (Localization.Away (f * d))
  have : Algebra.Etale A (Localization.Away f) :=
    inferInstanceAs (Algebra.Etale A (localizationAwayCommAlgCat A R f))
  let T := Localization.Away (algebraMap R (Localization.Away f) d)
  have : Algebra.Etale A T := inferInstance
  exact Algebra.Etale.of_equiv
    ((IsLocalization.algEquiv (Submonoid.powers (f * d)) T
      (Localization.Away (f * d))).restrictScalars A)

attribute [local instance] normalizationInertiaImageAction normalizationInertiaImageTower
  normalizationInertiaCoefficientCommClass inertiaInvariantPrime_isPrime
  finiteLevelInertiaPrime_isPrime

variable (A : Type u) (K : Type v) (L : Type w)
    [CommRing A] [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K]
    [Algebra K L] [Algebra A L] [IsScalarTower A K L] [IsGalois K L]
    (Q : Ideal (integralClosure A L))

/-- An actual principal neighborhood at a finite invariant stage. Its
étaleness is part of the object property and is constructed below from the
finite-Galois normalization theorem. -/
structure FiniteLevelEtaleNeighborhood where
  /-- The actual finite Galois stage. -/
  level : FiniteGaloisIntermediateField K L
  /-- The element defining the principal open at this stage. -/
  denominator : finiteLevelInertiaSubalgebra A K L Q level
  /-- The principal open contains the contracted prime. -/
  not_mem : denominator ∉ finiteLevelInertiaPrime A K L Q level
  /-- The actual principal localization is etale over the original base. -/
  etale : Algebra.Etale A
    (localizationAwayCommAlgCat A
      (finiteLevelInertiaSubalgebra A K L Q level) denominator)

namespace FiniteLevelEtaleNeighborhood

/-- Literal finite-field inclusion together with denominator divisibility. -/
instance : LE (FiniteLevelEtaleNeighborhood A K L Q) where
  le X Y := ∃ h : X.level ≤ Y.level,
    finiteLevelInertiaSubalgebraMap A K L Q h X.denominator ∣ Y.denominator

instance : Preorder (FiniteLevelEtaleNeighborhood A K L Q) where
  le_refl X := ⟨le_refl X.level, dvd_refl X.denominator⟩
  le_trans X Y Z hXY hYZ := by
    obtain ⟨hEF, hXY⟩ := hXY
    obtain ⟨hFG, hYZ⟩ := hYZ
    refine ⟨hEF.trans hFG, ?_⟩
    exact (map_dvd (finiteLevelInertiaSubalgebraMap A K L Q hFG) hXY).trans hYZ

/-- Every transition makes the source denominator invertible in the target
principal localization, exactly as required by `Away.liftAlgHom`. -/
theorem denominator_isUnit {X Y : FiniteLevelEtaleNeighborhood A K L Q}
    (h : X ≤ Y) :
    ∃ hEF : X.level ≤ Y.level,
      IsUnit (algebraMap (finiteLevelInertiaSubalgebra A K L Q Y.level)
        (Localization.Away Y.denominator)
          (finiteLevelInertiaSubalgebraMap A K L Q hEF X.denominator)) := by
  obtain ⟨hEF, hd⟩ := h
  exact ⟨hEF, IsLocalization.Away.isUnit_of_dvd Y.denominator hd⟩

end FiniteLevelEtaleNeighborhood

variable [Q.IsPrime] [IsDomain A] [IsIntegrallyClosed A]

/-- The actual finite invariant stage has a principal neighborhood étale
over the original normal domain. The comparison with finite-level inertia
invariants is the proved equality of subalgebras. -/
theorem finiteLevelInertia_exists_etale_away (E : FiniteGaloisIntermediateField K L) :
    ∃ f : finiteLevelInertiaSubalgebra A K L Q E,
      f ∉ finiteLevelInertiaPrime A K L Q E ∧
        Algebra.Etale A
          (localizationAwayCommAlgCat A (finiteLevelInertiaSubalgebra A K L Q E) f) := by
  let qE : Ideal (integralClosure A E) :=
    Q.comap (IsScalarTower.toAlgHom A E L).mapIntegralClosure
  have : qE.IsPrime := Ideal.IsPrime.comap (IsScalarTower.toAlgHom A E L).mapIntegralClosure
  obtain ⟨f, hf, hEtale⟩ :=
    finiteGalois_integralClosure_inertia_exists_etale_away A K E qE
  let e : FixedPoints.subalgebra A (integralClosure A E) (qE.inertia Gal(E/K)) ≃ₐ[A]
      finiteLevelInertiaSubalgebra A K L Q E :=
    (Subalgebra.equivOfEq _ _ (finiteLevelInertiaSubalgebra_eq_fixedPoints A K L Q E)).symm
  have : Algebra.Etale A
      (localizationAwayCommAlgCat A (FixedPoints.subalgebra A (integralClosure A E)
        (qE.inertia Gal(E/K))) f) := hEtale
  have eLocal := awayEquiv
    (A := A)
    (R := FixedPoints.subalgebra A (integralClosure A E) (qE.inertia Gal(E/K)))
    (S := finiteLevelInertiaSubalgebra A K L Q E) e f
  have hlocal : Algebra.Etale A
      (localizationAwayCommAlgCat A (finiteLevelInertiaSubalgebra A K L Q E) (e f)) :=
    Algebra.Etale.of_equiv (R := A)
      (A := localizationAwayCommAlgCat A
        (FixedPoints.subalgebra A (integralClosure A E) (qE.inertia Gal(E/K))) f)
      (B := localizationAwayCommAlgCat A (finiteLevelInertiaSubalgebra A K L Q E) (e f)) eLocal
  exact ⟨e f, hf, hlocal⟩

/-- Any denominator outside the chosen prime can be inverted on a genuine
finite-level principal étale neighborhood. -/
theorem finiteLevelInertia_exists_etale_away_dvd
    (E : FiniteGaloisIntermediateField K L)
    (d : finiteLevelInertiaSubalgebra A K L Q E)
    (hd : d ∉ finiteLevelInertiaPrime A K L Q E) :
    ∃ f : finiteLevelInertiaSubalgebra A K L Q E,
      f ∉ finiteLevelInertiaPrime A K L Q E ∧
        Algebra.Etale A
          (localizationAwayCommAlgCat A (finiteLevelInertiaSubalgebra A K L Q E) f) ∧
            d ∣ f := by
  obtain ⟨g, hg, hEtale⟩ := finiteLevelInertia_exists_etale_away A K L Q E
  have : Algebra.Etale A
      (localizationAwayCommAlgCat A (finiteLevelInertiaSubalgebra A K L Q E) g) := hEtale
  have hp : (finiteLevelInertiaPrime A K L Q E).IsPrime := inferInstance
  exact ⟨g * d, hp.mul_notMem hg hd, etale_away_mul (A := A)
    (R := finiteLevelInertiaSubalgebra A K L Q E) g d, dvd_mul_left d g⟩

namespace FiniteLevelEtaleNeighborhood

instance : Nonempty (FiniteLevelEtaleNeighborhood A K L Q) := by
  obtain ⟨f, hf, hEtale⟩ :=
    finiteLevelInertia_exists_etale_away A K L Q (⊥ : FiniteGaloisIntermediateField K L)
  exact ⟨⟨⊥, f, hf, hEtale⟩⟩

/-- At a common finite Galois level, the product of the two transported
denominators still avoids the contracted prime. A further genuinely étale
denominator supplied above gives a common refinement. -/
instance : IsDirectedOrder (FiniteLevelEtaleNeighborhood A K L Q) where
  directed X Y := by
    let E : FiniteGaloisIntermediateField K L := X.level ⊔ Y.level
    let x : finiteLevelInertiaSubalgebra A K L Q E :=
      finiteLevelInertiaSubalgebraMap A K L Q le_sup_left X.denominator
    let y : finiteLevelInertiaSubalgebra A K L Q E :=
      finiteLevelInertiaSubalgebraMap A K L Q le_sup_right Y.denominator
    have hx : x ∉ finiteLevelInertiaPrime A K L Q E := X.not_mem
    have hy : y ∉ finiteLevelInertiaPrime A K L Q E := Y.not_mem
    have hp : (finiteLevelInertiaPrime A K L Q E).IsPrime := inferInstance
    have hxy : x * y ∉ finiteLevelInertiaPrime A K L Q E := hp.mul_notMem hx hy
    obtain ⟨f, hf, hEtale, hdiv⟩ :=
      finiteLevelInertia_exists_etale_away_dvd A K L Q E (x * y) hxy
    refine ⟨⟨E, f, hf, hEtale⟩, ?_, ?_⟩
    · exact ⟨le_sup_left, (dvd_mul_right x y).trans hdiv⟩
    · exact ⟨le_sup_right, (dvd_mul_left y x).trans hdiv⟩

end FiniteLevelEtaleNeighborhood

end EtaleFundamentalGroups.Inertia
