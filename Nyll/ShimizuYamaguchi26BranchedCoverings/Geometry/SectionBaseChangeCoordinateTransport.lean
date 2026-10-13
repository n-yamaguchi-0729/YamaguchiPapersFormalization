/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.ProjectiveSpace.Basic
import Nyll.ShimizuYamaguchi26BranchedCoverings.Arithmetic.Determinant
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.IntegralCoordinateChange
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.IntegralSection
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.IntegralSectionCoordinateTransport
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.StandardAffineChart
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.TwoSectionComplement
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.Ring.Hom.Defs
import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.RingTheory.GradedAlgebra.RingHom
import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# Coordinate transport of the original section ideals after base change

Every Bézout coordinate change and its inverse commute with coefficient
extension. This follows from polynomial evaluation naturality, independently
of the specialized coordinate-swap proof in `SectionBaseChangeChart`.
Functoriality of ideal-sheaf pullback
therefore transports the existing integral pair identity to that ring, with
no new assertion about reducedness or an unrelated local equation ideal.

In particular, for the p-adic integers this identifies the pulled-back original
pair with the normalized pair used in the p-adic normal-crossing criterion of
Shimizu and Yamaguchi, Lemma 2.3, https://arxiv.org/abs/2608.15057v1.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

namespace ShimizuYamaguchi26BranchedCoverings

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Applying a ring homomorphism preserves the concrete Bézout identity
which supplies an invertible change of homogeneous coordinates. -/
theorem bezoutIdentity_map
    {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (u v a b : R) (hab : a * u + b * v = 1) :
    f a * f u + f b * f v = 1 := by
  rw [← map_mul, ← map_mul, ← map_add, hab, map_one]

private theorem bezoutCoordinateSubstitution_map
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] (u v a b : R) :
    (bezoutCoordinateSubstitution (algebraMap R S u) (algebraMap R S v)
      (algebraMap R S a) (algebraMap R S b)).comp (ProjSpace.mvMapGraded R S 1) =
      (ProjSpace.mvMapGraded R S 1).comp (bezoutCoordinateSubstitution u v a b) := by
  apply GradedRingHom.coe_ringHom_injective
  apply RingHom.ext
  intro P
  change MvPolynomial.eval₂ MvPolynomial.C (fun i : Fin 2 =>
      if i = 0 then
        MvPolynomial.C (algebraMap R S a) * MvPolynomial.X 0 +
          MvPolynomial.C (algebraMap R S b) * MvPolynomial.X 1
      else linearSectionEquation (algebraMap R S u) (algebraMap R S v))
        (MvPolynomial.map (algebraMap R S) P) =
    MvPolynomial.map (algebraMap R S)
      (MvPolynomial.eval₂ MvPolynomial.C (fun i : Fin 2 =>
        if i = 0 then MvPolynomial.C a * MvPolynomial.X 0 +
          MvPolynomial.C b * MvPolynomial.X 1
        else linearSectionEquation u v) P)
  rw [MvPolynomial.map_eval₂]
  apply congrArg (fun g : Fin 2 → MvPolynomial (Fin 2) S =>
    MvPolynomial.eval₂ MvPolynomial.C g (MvPolynomial.map (algebraMap R S) P))
  funext i
  dsimp only [Function.comp_apply]
  by_cases hi : i = 0
  · rw [ite_eq_left hi, ite_eq_left hi, map_add, map_mul, map_mul,
      MvPolynomial.map_C, MvPolynomial.map_C, MvPolynomial.map_X, MvPolynomial.map_X]
  · rw [ite_eq_right hi, ite_eq_right hi, linearSectionEquation, linearSectionEquation,
      map_sub, map_mul, map_mul, MvPolynomial.map_C, MvPolynomial.map_C,
      MvPolynomial.map_X, MvPolynomial.map_X]

/-- An actual Bézout projective coordinate change commutes with coefficient
extension. The target Bézout identity is obtained by applying the algebra map. -/
theorem integralCoordinateChange_comp_baseChange
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    (u v a b : R) (hab : a * u + b * v = 1) :
    (integralCoordinateChange (algebraMap R S u) (algebraMap R S v)
      (algebraMap R S a) (algebraMap R S b)
      (bezoutIdentity_map (algebraMap R S) u v a b hab)).hom ≫ ProjSpace.map R S 1 =
      ProjSpace.map R S 1 ≫ (integralCoordinateChange u v a b hab).hom := by
  change Proj.map (bezoutCoordinateSubstitution (algebraMap R S u) (algebraMap R S v)
      (algebraMap R S a) (algebraMap R S b)) _ ≫
      Proj.map (ProjSpace.mvMapGraded R S 1) _ =
    Proj.map (ProjSpace.mvMapGraded R S 1) _ ≫ Proj.map (bezoutCoordinateSubstitution u v a b) _
  rw [← Proj.map_comp, ← Proj.map_comp]
  simp only [bezoutCoordinateSubstitution_map]

/-- The inverse Bézout coordinate change also commutes with the actual
projective coefficient morphism. -/
theorem integralCoordinateChange_inv_comp_baseChange
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    (u v a b : R) (hab : a * u + b * v = 1) :
    (integralCoordinateChange (algebraMap R S u) (algebraMap R S v)
      (algebraMap R S a) (algebraMap R S b)
      (bezoutIdentity_map (algebraMap R S) u v a b hab)).inv ≫ ProjSpace.map R S 1 =
      ProjSpace.map R S 1 ≫ (integralCoordinateChange u v a b hab).inv := by
  let eR : ProjectiveLine R ≅ ProjectiveLine R := integralCoordinateChange u v a b hab
  let eS : ProjectiveLine S ≅ ProjectiveLine S :=
    integralCoordinateChange (algebraMap R S u) (algebraMap R S v)
      (algebraMap R S a) (algebraMap R S b)
      (bezoutIdentity_map (algebraMap R S) u v a b hab)
  have h : eS.hom ≫ ProjSpace.map R S 1 = ProjSpace.map R S 1 ≫ eR.hom :=
    integralCoordinateChange_comp_baseChange R S u v a b hab
  change eS.inv ≫ ProjSpace.map R S 1 = ProjSpace.map R S 1 ≫ eR.inv
  apply (cancel_mono eR.hom).mp
  rw [Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id,
    ← h, Iso.inv_hom_id_assoc]

/-- The original integer Bézout coefficients remain coefficients for the
same primitive coordinate pair in every commutative coefficient ring. -/
theorem intCast_bezoutIdentity
    (R : Type) [CommRing R] (u v a b : ℤ) (hab : a * u + b * v = 1) :
    (a : R) * (u : R) + (b : R) * (v : R) = 1 := by
  simpa only [Int.coe_castRingHom] using
    (bezoutIdentity_map (Int.castRingHom R) u v a b hab)

/-- The coefficient naturality of the inverse coordinate change, written
with the canonical integer casts used by the actual section constructions. -/
theorem integralCoordinateChange_intCast_inv_comp_baseChange
    (R : Type) [CommRing R] (u v a b : ℤ) (hab : a * u + b * v = 1) :
    (integralCoordinateChange (u : R) (v : R) (a : R) (b : R)
      (intCast_bezoutIdentity R u v a b hab)).inv ≫ ProjSpace.map ℤ R 1 =
      ProjSpace.map ℤ R 1 ≫ (integralCoordinateChange u v a b hab).inv := by
  simpa only [algebraMap_int_eq, Int.coe_castRingHom] using
    (integralCoordinateChange_inv_comp_baseChange ℤ R u v a b hab)

/-- The actual original pair, pulled back to any coefficient ring and then
normalized by its second section, equals the base change of the already
identified normalized integral pair. -/
theorem integralSectionPair_baseChange_ker_comap_coordinateChange_inv
    (R : Type) [CommRing R] (u v c d u' v' c' d' A B : ℤ)
    (hcd : c * u + d * v = 1) (hcd' : c' * u' + d' * v' = 1)
    (hAB : A * (-(c' * u + d' * v)) +
      B * coordinateDeterminant u' v' u v = 1) :
    (((integralSection u v c d hcd).ker *
      (integralSection u' v' c' d' hcd').ker).comap (ProjSpace.map ℤ R 1)).comap
        (integralCoordinateChange (u' : R) (v' : R) (c' : R) (d' : R)
          (intCast_bezoutIdentity R u' v' c' d' hcd')).inv =
      ((integralSection 1 0 1 0 (by decide)).ker *
        (integralSection (-(c' * u + d' * v))
          (coordinateDeterminant u' v' u v) A B hAB).ker).comap
            (ProjSpace.map ℤ R 1) := by
  rw [← Scheme.IdealSheafData.comap_comp,
    integralCoordinateChange_intCast_inv_comp_baseChange R u' v' c' d' hcd',
    Scheme.IdealSheafData.comap_comp,
    integralSectionPair_ker_comap_coordinateChange_inv
      u v c d u' v' c' d' A B hcd hcd' hAB]

/-- The original section, pulled back to a coefficient ring and then normalized
by its own Bezout coordinate change, is the actual pulled-back infinity section. -/
theorem integralSection_baseChange_ker_comap_coordinateChange_inv_self
    (R : Type) [CommRing R] (u v c d : ℤ) (hcd : c * u + d * v = 1) :
    ((integralSection u v c d hcd).ker.comap (ProjSpace.map ℤ R 1)).comap
      (integralCoordinateChange (u : R) (v : R) (c : R) (d : R)
        (intCast_bezoutIdentity R u v c d hcd)).inv =
      (integralSection 1 0 1 0 (by decide)).ker.comap (ProjSpace.map ℤ R 1) := by
  rw [← Scheme.IdealSheafData.comap_comp,
    integralCoordinateChange_intCast_inv_comp_baseChange R u v c d hcd,
    Scheme.IdealSheafData.comap_comp]
  exact congrArg (fun I : (ProjectiveLine ℤ).IdealSheafData => I.comap (ProjSpace.map ℤ R 1))
    (integralSection_ker_comap_coordinateChange_inv_self u v c d hcd)

/-- Coefficient extension preserves the actual single-section kernel identity
under an arbitrary integral Bezout coordinate change. -/
theorem integralSection_baseChange_ker_comap_coordinateChange_inv
    (R : Type) [CommRing R] (u v a b u' v' c d c' d' : ℤ)
    (hab : a * u + b * v = 1) (hcd : c * u' + d * v' = 1)
    (hcd' : c' * (-(a * u' + b * v')) +
      d' * coordinateDeterminant u v u' v' = 1) :
    ((integralSection u' v' c d hcd).ker.comap (ProjSpace.map ℤ R 1)).comap
        (integralCoordinateChange (u : R) (v : R) (a : R) (b : R)
          (intCast_bezoutIdentity R u v a b hab)).inv =
      (integralSection (-(a * u' + b * v'))
        (coordinateDeterminant u v u' v') c' d' hcd').ker.comap (ProjSpace.map ℤ R 1) := by
  rw [← Scheme.IdealSheafData.comap_comp,
    integralCoordinateChange_intCast_inv_comp_baseChange R u v a b hab,
    Scheme.IdealSheafData.comap_comp]
  exact congrArg (fun K : (ProjectiveLine ℤ).IdealSheafData =>
    K.comap (ProjSpace.map ℤ R 1))
    (integralSection_ker_comap_coordinateChange_inv
      u v a b u' v' c d c' d' hab hcd hcd')

end ShimizuYamaguchi26BranchedCoverings
