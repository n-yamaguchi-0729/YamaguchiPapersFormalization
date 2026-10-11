/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Inertia.FiniteLevelEtaleNeighborhoods
import SchemeTheory.RingTheory.Localization.AwayAlgebra
import SchemeTheory.RingTheory.Ramification.FiniteLevelInertiaLocalization
import Mathlib.Algebra.Algebra.Tower
import Mathlib.Algebra.Category.CommAlgCat.Basic
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.CategoryTheory.Limits.Cones
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Localization.Basic


/-!
# The actual diagram of finite-level principal étale neighborhoods

Every object is the native principal localization constructed in the
neighborhood index. Native localization lifts provide the transition maps
and the maps to the literal upper invariant prime localization. Their
generator formulas prove the functor and cocone laws by localization
extensionality. The stages retain the commutative algebra structures used
by their supplied étaleness proofs.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits SchemeTheory

namespace EtaleFundamentalGroups.Inertia

universe u v w

private def awayMap {A : Type*} [CommRing A]
    (R S : CommAlgCat A)
    (f : R →ₐ[A] S) (r : R) (s : S) (h : f r ∣ s) :
    localizationAwayCommAlgCat A R r →ₐ[A] localizationAwayCommAlgCat A S s := by
  change Localization.Away r →ₐ[A] Localization.Away s
  exact IsLocalization.Away.liftAlgHom r
    (f := (IsScalarTower.toAlgHom A S (Localization.Away s)).comp f)
    (IsLocalization.Away.isUnit_of_dvd s h)

private theorem awayMap_apply {A : Type*} [CommRing A]
    (R S : CommAlgCat A)
    (f : R →ₐ[A] S) (r : R) (s : S) (h : f r ∣ s) (x : R) :
    awayMap R S f r s h (algebraMap R (Localization.Away r) x) =
      algebraMap S (Localization.Away s) (f x) := by
  exact IsLocalization.Away.lift_eq (S := Localization.Away r) r
    (g := (algebraMap S (Localization.Away s)).comp f.toRingHom)
    (IsLocalization.Away.isUnit_of_dvd s h) x

private theorem awayHom_ext {A R B : Type*}
    [CommRing A] [CommRing R] [Semiring B] [Algebra A R] [Algebra A B]
    (r : R) (f g : localizationAwayCommAlgCat A R r →ₐ[A] B)
    (h : ∀ x : R, f (algebraMap R (Localization.Away r) x) =
      g (algebraMap R (Localization.Away r) x)) : f = g := by
  apply IsLocalization.algHom_ext (R := A) (A := R) (L := Localization.Away r)
    (B := B) (Submonoid.powers r)
  ext x
  exact h x

private def awayToPrime {A R S : Type*}
    [CommRing A] [CommRing R] [CommRing S] [Algebra A R] [Algebra A S]
    (f : R →ₐ[A] S) (r : R) (p : Ideal S) [p.IsPrime] (h : f r ∉ p) :
    localizationAwayCommAlgCat A R r →ₐ[A] Localization.AtPrime p := by
  change Localization.Away r →ₐ[A] Localization.AtPrime p
  exact IsLocalization.Away.liftAlgHom r
    (f := (IsScalarTower.toAlgHom A S (Localization.AtPrime p)).comp f)
    (IsLocalization.map_units (Localization.AtPrime p) (⟨f r, h⟩ : p.primeCompl))

private theorem awayToPrime_apply {A : Type*} [CommRing A]
    (R S : CommAlgCat A)
    (f : R →ₐ[A] S) (r : R) (p : Ideal S) [p.IsPrime] (h : f r ∉ p) (x : R) :
    awayToPrime (A := A) (R := R) (S := S) f r p h
      (algebraMap R (Localization.Away r) x) =
      algebraMap S (Localization.AtPrime p) (f x) := by
  exact IsLocalization.Away.lift_eq (S := Localization.Away r) r
    (g := (algebraMap S (Localization.AtPrime p)).comp f.toRingHom)
    (IsLocalization.map_units (Localization.AtPrime p) (⟨f r, h⟩ : p.primeCompl)) x

attribute [local instance] normalizationInertiaImageAction normalizationInertiaImageTower
  normalizationInertiaCoefficientCommClass inertiaInvariantPrime_isPrime
  finiteLevelInertiaPrime_isPrime

variable (A : Type u) (K : Type v) (L : Type w)
    [CommRing A] [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K]
    [Algebra K L] [Algebra A L] [IsScalarTower A K L] [IsGalois K L]
    (Q : Ideal (integralClosure A L))

local notation "N" => FiniteLevelEtaleNeighborhood A K L Q
local notation "C" => integralClosure A L
local notation "CI" => FixedPoints.subalgebra A C (Q.inertia Gal(L/K))

/- The field inclusion, divisor proof and coefficient algebra owners are
fixed before the native localization-map specialization. -/
/-- The native transition map of actual principal étale neighborhoods. -/
def finiteLevelEtaleNeighborhoodMap {X Y : N} (h : X ≤ Y) :
    localizationAwayCommAlgCat A (finiteLevelInertiaSubalgebra A K L Q X.level)
        X.denominator →ₐ[A]
      localizationAwayCommAlgCat A (finiteLevelInertiaSubalgebra A K L Q Y.level)
        Y.denominator := by
  have hex : ∃ hEF : X.level ≤ Y.level,
      finiteLevelInertiaSubalgebraMap A K L Q (E := X.level) (F := Y.level) hEF
        X.denominator ∣ Y.denominator := h
  let hEF : X.level ≤ Y.level := hex.choose
  have hd : finiteLevelInertiaSubalgebraMap A K L Q (E := X.level) (F := Y.level) hEF
      X.denominator ∣ Y.denominator :=
    hex.choose_spec
  let R : CommAlgCat.{w} A := CommAlgCat.of A (finiteLevelInertiaSubalgebra A K L Q X.level)
  let S : CommAlgCat.{w} A := CommAlgCat.of A (finiteLevelInertiaSubalgebra A K L Q Y.level)
  let f : R →ₐ[A] S :=
    finiteLevelInertiaSubalgebraMap A K L Q (E := X.level) (F := Y.level) hEF
  let result := awayMap (A := A) R S f X.denominator Y.denominator hd
  exact result

/-- The transition map is the literal finite normalization inclusion on coefficients. -/
theorem finiteLevelEtaleNeighborhoodMap_algebraMap {X Y : N} (h : X ≤ Y)
    (x : finiteLevelInertiaSubalgebra A K L Q X.level) :
    finiteLevelEtaleNeighborhoodMap A K L Q h
        (algebraMap (finiteLevelInertiaSubalgebra A K L Q X.level)
          (Localization.Away X.denominator) x) =
      algebraMap (finiteLevelInertiaSubalgebra A K L Q Y.level)
        (Localization.Away Y.denominator)
        (finiteLevelInertiaSubalgebraMap A K L Q (E := X.level) (F := Y.level) h.choose x) := by
  have hd : finiteLevelInertiaSubalgebraMap A K L Q (E := X.level) (F := Y.level) h.choose
      X.denominator ∣ Y.denominator :=
    h.choose_spec
  let R : CommAlgCat.{w} A := CommAlgCat.of A (finiteLevelInertiaSubalgebra A K L Q X.level)
  let S : CommAlgCat.{w} A := CommAlgCat.of A (finiteLevelInertiaSubalgebra A K L Q Y.level)
  let f : R →ₐ[A] S :=
    finiteLevelInertiaSubalgebraMap A K L Q (E := X.level) (F := Y.level) h.choose
  have hformula := awayMap_apply (A := A) R S f
    X.denominator Y.denominator hd x
  exact hformula

/-- The actual principal étale neighborhood diagram in commutative
algebras over the original base. -/
def finiteLevelEtaleDiagram : N ⥤ CommAlgCat.{w} A where
  obj X := localizationAwayCommAlgCat A
    (finiteLevelInertiaSubalgebra A K L Q X.level) X.denominator
  map h := CommAlgCat.ofHom (finiteLevelEtaleNeighborhoodMap A K L Q h.le)
  map_id X := by
    apply CommAlgCat.hom_ext
    apply awayHom_ext (A := A) (R := finiteLevelInertiaSubalgebra A K L Q X.level)
      X.denominator
    intro x
    change finiteLevelEtaleNeighborhoodMap A K L Q (le_refl X)
      (algebraMap _ (Localization.Away X.denominator) x) =
        algebraMap _ (Localization.Away X.denominator) x
    rw [finiteLevelEtaleNeighborhoodMap_algebraMap]
    rfl
  map_comp {X Y Z} h k := by
    apply CommAlgCat.hom_ext
    apply awayHom_ext (A := A) (R := finiteLevelInertiaSubalgebra A K L Q X.level)
      X.denominator
    intro x
    change finiteLevelEtaleNeighborhoodMap A K L Q (h.le.trans k.le)
        (algebraMap _ (Localization.Away X.denominator) x) =
      finiteLevelEtaleNeighborhoodMap A K L Q k.le
        (finiteLevelEtaleNeighborhoodMap A K L Q h.le
          (algebraMap _ (Localization.Away X.denominator) x))
    rw [finiteLevelEtaleNeighborhoodMap_algebraMap,
      finiteLevelEtaleNeighborhoodMap_algebraMap,
      finiteLevelEtaleNeighborhoodMap_algebraMap]
    rfl

variable [Q.IsPrime]

/- The upper map retains the literal accepted localization vertex. -/
/-- The native map to the literal upper invariant prime localization. -/
def finiteLevelEtaleNeighborhoodInclusion (X : N) :
    localizationAwayCommAlgCat A (finiteLevelInertiaSubalgebra A K L Q X.level)
        X.denominator →ₐ[A]
      (finiteLevelInertiaLocalizationCocone A K L Q).pt := by
  have hf : finiteLevelInertiaSubalgebraInclusion A K L Q X.level X.denominator ∉
      inertiaInvariantPrime A K L Q := X.not_mem
  let result := awayToPrime (A := A)
    (R := finiteLevelInertiaSubalgebra A K L Q X.level) (S := CI)
    (finiteLevelInertiaSubalgebraInclusion A K L Q X.level)
    X.denominator (inertiaInvariantPrime A K L Q) hf
  exact result

/-- The upper map is the literal normalization inclusion on coefficients. -/
theorem finiteLevelEtaleNeighborhoodInclusion_algebraMap (X : N)
    (x : finiteLevelInertiaSubalgebra A K L Q X.level) :
    finiteLevelEtaleNeighborhoodInclusion A K L Q X
        (algebraMap (finiteLevelInertiaSubalgebra A K L Q X.level)
          (Localization.Away X.denominator) x) =
      algebraMap CI (Localization.AtPrime (inertiaInvariantPrime A K L Q))
        (finiteLevelInertiaSubalgebraInclusion A K L Q X.level x) := by
  have hf : finiteLevelInertiaSubalgebraInclusion A K L Q X.level X.denominator ∉
      inertiaInvariantPrime A K L Q := X.not_mem
  let R : CommAlgCat.{w} A := CommAlgCat.of A (finiteLevelInertiaSubalgebra A K L Q X.level)
  let S : CommAlgCat.{w} A := CommAlgCat.of A CI
  let f : R →ₐ[A] S := finiteLevelInertiaSubalgebraInclusion A K L Q X.level
  have hformula := awayToPrime_apply (A := A) R S f
    X.denominator (inertiaInvariantPrime A K L Q) hf x
  exact hformula

/-- The actual étale stages form a cocone with the already constructed
upper invariant localization as vertex. -/
def finiteLevelEtaleCocone : Cocone
    (finiteLevelEtaleDiagram A K L Q ⋙ forget₂ (CommAlgCat.{w} A) (AlgCat.{w} A)) where
  pt := (finiteLevelInertiaLocalizationCocone A K L Q).pt
  ι.app X := AlgCat.ofHom (finiteLevelEtaleNeighborhoodInclusion A K L Q X)
  ι.naturality X Y h := by
    apply AlgCat.hom_ext
    apply awayHom_ext (A := A) (R := finiteLevelInertiaSubalgebra A K L Q X.level)
      X.denominator
    intro x
    change finiteLevelEtaleNeighborhoodInclusion A K L Q Y
        (finiteLevelEtaleNeighborhoodMap A K L Q h.le
          (algebraMap _ (Localization.Away X.denominator) x)) =
      finiteLevelEtaleNeighborhoodInclusion A K L Q X
        (algebraMap _ (Localization.Away X.denominator) x)
    rw [finiteLevelEtaleNeighborhoodMap_algebraMap,
      finiteLevelEtaleNeighborhoodInclusion_algebraMap,
      finiteLevelEtaleNeighborhoodInclusion_algebraMap]
    rfl

end EtaleFundamentalGroups.Inertia
