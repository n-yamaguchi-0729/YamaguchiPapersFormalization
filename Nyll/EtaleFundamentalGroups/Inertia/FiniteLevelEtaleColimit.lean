/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Inertia.FiniteLevelEtaleDiagram
import Nyll.EtaleFundamentalGroups.Inertia.FiniteLevelEtaleNeighborhoods
import Nyll.SchemeTheory.RingTheory.Localization.AwayAlgebra
import Nyll.SchemeTheory.RingTheory.Localization.CommAlgPrincipal
import Nyll.SchemeTheory.RingTheory.Ramification.FiniteLevelInertiaLocalization
import Mathlib.Algebra.Category.AlgCat.FilteredColimits
import Mathlib.Algebra.Category.CommAlgCat.Basic
import Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.Algebra.Group.Units.Basic
import Mathlib.CategoryTheory.ConcreteCategory.Basic
import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
import Mathlib.CategoryTheory.Limits.Types.Filtered
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Localization.Defs


/-!
# The étale filtered-colimit presentation in Stacks tag 0BSU

The already constructed localized finite-level colimit supplies an actual
finite-level representative. A denominator for this representative becomes
a unit on a genuine principal étale neighborhood. The two literal
coefficient squares and unit cancellation give its representative in the
étale diagram. Equality is detected by the actual inclusions into the upper
invariant localization.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits SchemeTheory

namespace EtaleFundamentalGroups.Inertia

universe u v w

private theorem away_injective_of_coeff_injective
    {A : Type*} [CommRing A] (R : CommAlgCat A) (r : R)
    {T : Type*} [CommSemiring T]
    (j : localizationAwayCommAlgCat A R r →+* T)
    (hj : Function.Injective fun x : R => j (algebraMap R (Localization.Away r) x)) :
    Function.Injective j := by
  exact SchemeTheory.principalLocalization_injective_of_coefficient_injective
    (R := R) (T := T) r j hj

/-- A denominator already made invertible supplies a preimage, using only
the two actual coefficient maps and the localization's fraction equation. -/
private theorem exists_preimage_of_unit_denominator
    {A : Type*} [CommRing A] (R : CommAlgCat A)
    (p : Ideal R) [p.IsPrime] (f n : R) (d : p.primeCompl)
    (z : Localization.AtPrime p)
    (hz : z * algebraMap R (Localization.AtPrime p) d =
      algebraMap R (Localization.AtPrime p) n)
    (hd : IsUnit (algebraMap R (Localization.Away f) d))
    {U : Type*} [Semiring U]
    (j : Localization.Away f →+* U) (k : Localization.AtPrime p →+* U)
    (hcoeff : ∀ a : R, j (algebraMap R (Localization.Away f) a) =
      k (algebraMap R (Localization.AtPrime p) a)) :
    ∃ x : Localization.Away f, j x = k z := by
  obtain ⟨b, hb⟩ := hd
  let x : Localization.Away f := algebraMap R (Localization.Away f) n * ↑(b⁻¹)
  have hx : x * algebraMap R (Localization.Away f) d =
      algebraMap R (Localization.Away f) n := by
    dsimp only [x]
    rw [← hb, mul_assoc, Units.inv_mul, mul_one]
  refine ⟨x, ?_⟩
  apply ((IsLocalization.map_units (Localization.AtPrime p) d).map k).mul_right_cancel
  calc
    j x * k (algebraMap R (Localization.AtPrime p) d) =
        j (x * algebraMap R (Localization.Away f) d) :=
      (congrArg (fun t : U => j x * t) (hcoeff d)).symm.trans
        (map_mul j x (algebraMap R (Localization.Away f) d)).symm
    _ = j (algebraMap R (Localization.Away f) n) := congrArg j hx
    _ = k (algebraMap R (Localization.AtPrime p) n) := hcoeff n
    _ = k z * k (algebraMap R (Localization.AtPrime p) d) := by
      rw [← hz, map_mul]

attribute [local instance] normalizationInertiaImageAction normalizationInertiaImageTower
  normalizationInertiaCoefficientCommClass inertiaInvariantPrime_isPrime
  finiteLevelInertiaPrime_isPrime

variable (A : Type u) (K : Type v) (L : Type w)
    [CommRing A] [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K]
    [Algebra K L] [Algebra A L] [IsScalarTower A K L] [IsGalois K L]
    (Q : Ideal (integralClosure A L)) [Q.IsPrime]

local notation "N" => FiniteLevelEtaleNeighborhood A K L Q
local notation "C" => integralClosure A L
local notation "CI" => FixedPoints.subalgebra A C (Q.inertia Gal(L/K))

/-- Each actual étale neighborhood embeds into the upper invariant
localization. The coefficient inclusion and the upper localization are
injective, and native localization extensionality supplies the result. -/
theorem finiteLevelEtaleNeighborhoodInclusion_injective (X : N) :
    Function.Injective (finiteLevelEtaleNeighborhoodInclusion A K L Q X) := by
  have hdom : IsDomain CI := inferInstance
  have hs := finiteLevelInertiaSubalgebraInclusion_injective A K L Q X.level
  have hu : Function.Injective
      (algebraMap CI (Localization.AtPrime (inertiaInvariantPrime A K L Q))) :=
    IsLocalization.injective
      (R := CI) (M := (inertiaInvariantPrime A K L Q).primeCompl)
      (Localization.AtPrime (inertiaInvariantPrime A K L Q))
      (inertiaInvariantPrime A K L Q).primeCompl_le_nonZeroDivisors
  let R : CommAlgCat.{w} A :=
    CommAlgCat.of A (finiteLevelInertiaSubalgebra A K L Q X.level)
  have hcoeff : Function.Injective fun a : R =>
      (finiteLevelEtaleNeighborhoodInclusion A K L Q X).toRingHom
        (algebraMap R (Localization.Away X.denominator) a) := by
    intro a b h
    change finiteLevelEtaleNeighborhoodInclusion A K L Q X
        (algebraMap R (Localization.Away X.denominator) a) =
      finiteLevelEtaleNeighborhoodInclusion A K L Q X
        (algebraMap R (Localization.Away X.denominator) b) at h
    rw [finiteLevelEtaleNeighborhoodInclusion_algebraMap,
      finiteLevelEtaleNeighborhoodInclusion_algebraMap] at h
    exact hs (hu h)
  let j : localizationAwayCommAlgCat A R X.denominator →+*
      Localization.AtPrime (inertiaInvariantPrime A K L Q) :=
    (finiteLevelEtaleNeighborhoodInclusion A K L Q X).toRingHom
  have hn := away_injective_of_coeff_injective
    (T := Localization.AtPrime (inertiaInvariantPrime A K L Q))
    R X.denominator j hcoeff
  exact hn

variable [IsDomain A] [IsIntegrallyClosed A]

/-- The accepted localized finite-level colimit supplies a representative;
the actual étale denominator-refinement theorem then places it on one of
the constructed étale neighborhoods. -/
private theorem finiteLevelEtale_exists_rep
    (z : (finiteLevelInertiaLocalizationCocone A K L Q).pt) :
    ∃ (X : N) (x : (finiteLevelEtaleDiagram A K L Q).obj X),
      finiteLevelEtaleNeighborhoodInclusion A K L Q X x = z := by
  obtain ⟨E, zE, hE⟩ := Concrete.isColimit_exists_rep
    (finiteLevelInertiaLocalizationDiagram A K L Q)
    (finiteLevelInertiaLocalizationCoconeIsColimit A K L Q) z
  let R : CommAlgCat.{w} A :=
    CommAlgCat.of A (finiteLevelInertiaSubalgebra A K L Q E)
  let p : Ideal R := finiteLevelInertiaPrime A K L Q E
  have : p.IsPrime := finiteLevelInertiaPrime_isPrime A K L Q E
  let z₀ : Localization.AtPrime p := zE
  obtain ⟨⟨n, d⟩, hz⟩ := IsLocalization.surj
    (R := R) (S := Localization.AtPrime p) p.primeCompl z₀
  obtain ⟨f, hf, hEtale, hdiv⟩ :=
    finiteLevelInertia_exists_etale_away_dvd A K L Q E (d : R) d.property
  let X : N := ⟨E, f, hf, hEtale⟩
  let j : Localization.Away f →+* (finiteLevelInertiaLocalizationCocone A K L Q).pt :=
    (finiteLevelEtaleNeighborhoodInclusion A K L Q X).toRingHom
  let k : Localization.AtPrime p →+* (finiteLevelInertiaLocalizationCocone A K L Q).pt :=
    (finiteLevelInertiaLocalizationInclusion A K L Q E).toRingHom
  have hcoeff : ∀ a : R, j (algebraMap R (Localization.Away f) a) =
      k (algebraMap R (Localization.AtPrime p) a) := by
    intro a
    change finiteLevelEtaleNeighborhoodInclusion A K L Q X
        (algebraMap R (Localization.Away f) a) =
      finiteLevelInertiaLocalizationInclusion A K L Q E
        (algebraMap R (Localization.AtPrime p) a)
    rw [finiteLevelEtaleNeighborhoodInclusion_algebraMap]
    have hcontract : finiteLevelInertiaPrime A K L Q E =
        (inertiaInvariantPrime A K L Q).comap
          (finiteLevelInertiaSubalgebraInclusion A K L Q E).toRingHom := rfl
    have hnative := Localization.localRingHom_to_map
      (R := finiteLevelInertiaSubalgebra A K L Q E) (P := CI)
      (finiteLevelInertiaPrime A K L Q E) (inertiaInvariantPrime A K L Q)
      (finiteLevelInertiaSubalgebraInclusion A K L Q E).toRingHom hcontract a
    exact hnative.symm
  have hd : IsUnit (algebraMap R (Localization.Away f) d) :=
    IsLocalization.Away.isUnit_of_dvd f hdiv
  obtain ⟨x, hx⟩ := exists_preimage_of_unit_denominator R p f n d z₀ hz hd j k hcoeff
  refine ⟨X, x, ?_⟩
  exact hx.trans hE

/-- The upper inertia-invariant prime localization is the filtered colimit
of the actual finite-level principal étale neighborhoods. There is no
finite-presentation assumption on the fraction field or the infinite
normalization, and the cocone vertex and its coefficient maps are literal. -/
def finiteLevelEtaleCoconeIsColimit : IsColimit (finiteLevelEtaleCocone A K L Q) := by
  apply isColimitOfReflects (forget₂ (AlgCat.{w} A) RingCat.{w})
  letI : ReflectsColimit
      ((finiteLevelEtaleDiagram A K L Q ⋙ forget₂ (CommAlgCat.{w} A) (AlgCat.{w} A)) ⋙
        forget₂ (AlgCat.{w} A) RingCat.{w}) (forget RingCat.{w}) :=
    reflectsColimit_of_reflectsIsomorphisms _ _
  apply isColimitOfReflects (forget RingCat.{w})
  apply Types.FilteredColimit.isColimitOf'
  · change ∀ z : (finiteLevelInertiaLocalizationCocone A K L Q).pt,
      ∃ (X : N) (x : (finiteLevelEtaleDiagram A K L Q).obj X),
        z = finiteLevelEtaleNeighborhoodInclusion A K L Q X x
    intro z
    obtain ⟨X, x, hx⟩ := finiteLevelEtale_exists_rep A K L Q z
    exact ⟨X, x, hx.symm⟩
  · intro X x y hxy
    refine ⟨X, 𝟙 X, ?_⟩
    have hxy' : x = y := finiteLevelEtaleNeighborhoodInclusion_injective A K L Q X hxy
    exact congrArg
      (ConcreteCategory.hom
        ((((finiteLevelEtaleDiagram A K L Q ⋙
          forget₂ (CommAlgCat.{w} A) (AlgCat.{w} A)) ⋙
          forget₂ (AlgCat.{w} A) RingCat.{w}) ⋙ forget RingCat.{w}).map (𝟙 X))) hxy'

end EtaleFundamentalGroups.Inertia
