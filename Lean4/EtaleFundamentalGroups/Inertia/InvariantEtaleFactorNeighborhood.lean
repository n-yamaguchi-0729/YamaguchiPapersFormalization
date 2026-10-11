/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Inertia.InvariantBaseChange
import EtaleFundamentalGroups.Inertia.InvariantFlatBaseChange
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.RingHomProperties
import Mathlib.RingTheory.Etale.Basic
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.RingHom.Etale
import Mathlib.RingTheory.RingHomProperties
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.RingTheory.Spectrum.Prime.RingHom
import Mathlib.RingTheory.Ideal.Maps


/-!
# The actual étale neighborhood map from an invariant tensor factor

The existing flat invariant equivalence identifies the base-changed original
fixed algebra with the fixed tensor algebra. Its composition with the right
tensor inclusion and a principal localization gives the actual neighborhood
map to the original fixed algebra. Étaleness follows from canonical base
change, the existing equivalence, and principal localization. The literal
square over the original base is retained.

For the finite transitive idempotent family, the previously constructed
coefficient-to-factor bijection additionally identifies this neighborhood
with the coefficient scheme. Source-local descent from its open image is a
separate step in Stacks tag 0BST.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct

namespace EtaleFundamentalGroups.Inertia

universe u w

private theorem tensorIncludeRight_etale
    (B A S : Type u) [CommRing B] [CommRing A] [CommRing S]
    [Algebra B A] [Algebra B S] [Algebra.Etale B A] :
    (Algebra.TensorProduct.includeRight (R := B) (A := A) (B := S)).toRingHom.Etale := by
  let : Algebra S (A ⊗[B] S) := Algebra.TensorProduct.rightAlgebra
  exact RingHom.Etale.isStableUnderBaseChange B A S (A ⊗[B] S)
    ((RingHom.etale_algebraMap).mpr inferInstance)

variable (B A R : Type u) (G : Type w)
  [CommRing B] [CommRing A] [CommRing R] [Algebra B A] [Algebra B R]
  [Group G] [Finite G] [MulSemiringAction G R] [SMulCommClass G B R]

local instance : MulSemiringAction G (A ⊗[B] R) := baseChangeAction B A R G
local instance : SMulCommClass G A (A ⊗[B] R) := baseChangeAction_smulCommClass B A R G

/-- The literal map from the original fixed algebra into a localized fixed
factor after flat base change. It uses the existing invariant equivalence. -/
def invariantFlatBaseChangeFactorMap [Module.Flat B A]
    (e : FixedPoints.subalgebra A (A ⊗[B] R) G) :
    FixedPoints.subalgebra B R G →+* Localization.Away e :=
  (algebraMap (FixedPoints.subalgebra A (A ⊗[B] R) G) (Localization.Away e)).comp
    ((invariantFlatBaseChangeEquiv B A R G).toRingHom.comp
      (Algebra.TensorProduct.includeRight
        (R := B) (A := A) (B := FixedPoints.subalgebra B R G)).toRingHom)

/-- An étale coefficient extension makes the actual selected-factor
neighborhood map étale, including finite presentation. -/
theorem invariantFlatBaseChangeFactorMap_etale [Algebra.Etale B A]
    (e : FixedPoints.subalgebra A (A ⊗[B] R) G) :
    RingHom.Etale (R := FixedPoints.subalgebra B R G) (S := Localization.Away e)
      (invariantFlatBaseChangeFactorMap B A R G e) := by
  apply RingHom.Etale.stableUnderComposition
  · apply RingHom.Etale.stableUnderComposition
    · exact tensorIncludeRight_etale B A (FixedPoints.subalgebra B R G)
    · exact RingHom.Etale.of_bijective (invariantFlatBaseChangeEquiv B A R G).bijective
  · exact (RingHom.etale_algebraMap).mpr (Algebra.Etale.of_isLocalizationAway e)

/-- The actual scheme map from the selected factor to the original fixed
algebra is an étale neighborhood map. -/
theorem invariantFactorNeighborhood_etale [Algebra.Etale B A]
    (e : FixedPoints.subalgebra A (A ⊗[B] R) G) :
    Etale (Spec.map (CommRingCat.ofHom (R := FixedPoints.subalgebra B R G)
      (S := Localization.Away e)
      (invariantFlatBaseChangeFactorMap B A R G e))) := by
  exact (HasRingHomProperty.Spec_iff (P := @Etale)).mpr
    (invariantFlatBaseChangeFactorMap_etale B A R G e)

/-- The neighborhood map preserves the literal original base map, through
the prescribed coefficient action on the localized factor. -/
theorem invariantFlatBaseChangeFactorMap_comp_algebraMap [Module.Flat B A]
    (e : FixedPoints.subalgebra A (A ⊗[B] R) G) :
    (invariantFlatBaseChangeFactorMap B A R G e).comp
        (algebraMap B (FixedPoints.subalgebra B R G)) =
      (algebraMap A (Localization.Away e)).comp (algebraMap B A) := by
  apply RingHom.ext
  intro b
  change algebraMap (FixedPoints.subalgebra A (A ⊗[B] R) G) (Localization.Away e)
      (invariantFlatBaseChangeEquiv B A R G
        (Algebra.TensorProduct.includeRight
          (R := B) (A := A) (B := FixedPoints.subalgebra B R G)
          (algebraMap B (FixedPoints.subalgebra B R G) b))) =
    algebraMap (FixedPoints.subalgebra A (A ⊗[B] R) G) (Localization.Away e)
      (algebraMap A (FixedPoints.subalgebra A (A ⊗[B] R) G) (algebraMap B A b))
  rw [(Algebra.TensorProduct.includeRight
      (R := B) (A := A) (B := FixedPoints.subalgebra B R G)).commutes,
    IsScalarTower.algebraMap_apply B A (A ⊗[B] FixedPoints.subalgebra B R G),
    (invariantFlatBaseChangeEquiv B A R G).commutes]

/-- The selected-factor neighborhood has its literal compatibility square
with the coefficient scheme and the original base scheme. -/
theorem invariantFactorNeighborhood_square [Module.Flat B A]
    (e : FixedPoints.subalgebra A (A ⊗[B] R) G) :
    Spec.map (CommRingCat.ofHom (R := FixedPoints.subalgebra B R G) (S := Localization.Away e)
      (invariantFlatBaseChangeFactorMap B A R G e)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap B (FixedPoints.subalgebra B R G))) =
      Spec.map (CommRingCat.ofHom (R := A) (S := Localization.Away e)
        (algebraMap A (Localization.Away e))) ≫
        Spec.map (CommRingCat.ofHom (algebraMap B A)) := by
  rw [← Spec.map_comp, ← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  exact invariantFlatBaseChangeFactorMap_comp_algebraMap B A R G e

/-- A prime of the tensor algebra outside the selected element supplies an
actual point of the localized invariant neighborhood. Its contraction is
exactly the contraction of the original ring prime to its invariant algebra. -/
theorem invariantFactorNeighborhood_exists_point [Module.Flat B A]
    (Q : PrimeSpectrum (A ⊗[B] R))
    (e : FixedPoints.subalgebra A (A ⊗[B] R) G) (he : (e : A ⊗[B] R) ∉ Q.asIdeal) :
    ∃ P : PrimeSpectrum (Localization.Away e),
      PrimeSpectrum.comap (R := FixedPoints.subalgebra B R G) (S := Localization.Away e)
          (invariantFlatBaseChangeFactorMap B A R G e) P =
        PrimeSpectrum.comap
          ((Algebra.TensorProduct.includeRight (R := B) (A := A) (B := R)).toRingHom.comp
            (FixedPoints.subalgebra B R G).val.toRingHom) Q := by
  let QJ : PrimeSpectrum (FixedPoints.subalgebra A (A ⊗[B] R) G) :=
    PrimeSpectrum.comap (FixedPoints.subalgebra A (A ⊗[B] R) G).val.toRingHom Q
  have hpoint : QJ ∈ Set.range (PrimeSpectrum.comap
      (R := FixedPoints.subalgebra A (A ⊗[B] R) G) (S := Localization.Away e)
      (algebraMap (FixedPoints.subalgebra A (A ⊗[B] R) G) (Localization.Away e))) := by
    rw [PrimeSpectrum.localization_away_comap_range (Localization.Away e) e]
    exact he
  obtain ⟨P, hP⟩ := hpoint
  have hPI : P.asIdeal.comap
      (algebraMap (FixedPoints.subalgebra A (A ⊗[B] R) G) (Localization.Away e)) =
        QJ.asIdeal := by
    change (PrimeSpectrum.comap
      (algebraMap (FixedPoints.subalgebra A (A ⊗[B] R) G) (Localization.Away e)) P).asIdeal =
        QJ.asIdeal
    exact congrArg PrimeSpectrum.asIdeal hP
  refine ⟨P, ?_⟩
  apply PrimeSpectrum.ext
  change P.asIdeal.comap
      ((algebraMap (FixedPoints.subalgebra A (A ⊗[B] R) G) (Localization.Away e)).comp
        ((invariantFlatBaseChangeEquiv B A R G).toRingHom.comp
          (Algebra.TensorProduct.includeRight
            (R := B) (A := A) (B := FixedPoints.subalgebra B R G)).toRingHom)) = _
  rw [← Ideal.comap_comap, hPI]
  change (Q.asIdeal.comap (FixedPoints.subalgebra A (A ⊗[B] R) G).val.toRingHom).comap
      ((invariantFlatBaseChangeEquiv B A R G).toRingHom.comp
        (Algebra.TensorProduct.includeRight
          (R := B) (A := A) (B := FixedPoints.subalgebra B R G)).toRingHom) = _
  rw [Ideal.comap_comap]
  have hmaps :
      (((FixedPoints.subalgebra A (A ⊗[B] R) G).val.comp
        (invariantFlatBaseChangeEquiv B A R G).toAlgHom).restrictScalars B).comp
          (Algebra.TensorProduct.includeRight
            (R := B) (A := A) (B := FixedPoints.subalgebra B R G)) =
        (Algebra.TensorProduct.includeRight (R := B) (A := A) (B := R)).comp
          (FixedPoints.subalgebra B R G).val :=
    (congrArg
      (fun f : (A ⊗[B] FixedPoints.subalgebra B R G) →ₐ[A] (A ⊗[B] R) =>
        (f.restrictScalars B).comp (Algebra.TensorProduct.includeRight
          (R := B) (A := A) (B := FixedPoints.subalgebra B R G)))
      (invariantFlatBaseChangeEquiv_val_comp B A R G)).trans
        (Algebra.TensorProduct.map_restrictScalars_comp_includeRight
          (AlgHom.id A A) (FixedPoints.subalgebra B R G).val)
  change Q.asIdeal.comap
      ((((FixedPoints.subalgebra A (A ⊗[B] R) G).val.comp
        (invariantFlatBaseChangeEquiv B A R G).toAlgHom).restrictScalars B).comp
          (Algebra.TensorProduct.includeRight
            (R := B) (A := A) (B := FixedPoints.subalgebra B R G))).toRingHom =
    Q.asIdeal.comap
      ((Algebra.TensorProduct.includeRight (R := B) (A := A) (B := R)).comp
        (FixedPoints.subalgebra B R G).val).toRingHom
  exact congrArg (fun f : FixedPoints.subalgebra B R G →ₐ[B] (A ⊗[B] R) =>
    Q.asIdeal.comap f.toRingHom) hmaps

end EtaleFundamentalGroups.Inertia
