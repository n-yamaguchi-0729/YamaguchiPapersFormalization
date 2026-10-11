/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.StrictHenselian.GeometricStalk
import EtaleFundamentalGroups.StrictHenselian.GeometricStalkStructure
import EtaleFundamentalGroups.StrictHenselian.GeometricStalkAlgebraColimit
import EtaleFundamentalGroups.StrictHenselian.GeometricStalkFractionTensor
import EtaleFundamentalGroups.StrictHenselian.GeometricStalkFractionFieldMap
import EtaleFundamentalGroups.GenericTensor.FilteredColimit.CoconeLeg
import Mathlib.Algebra.Category.Ring.Under.Basic
import Mathlib.CategoryTheory.Limits.Cones
import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
import Mathlib.CategoryTheory.Limits.IsLimit
import Mathlib.CategoryTheory.Limits.Preserves.Basic
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.TensorProduct.Maps


/-!
# The actual strict generic field as a filtered colimit

Base-change the already constructed small pointed-neighborhood diagram from
R to its actual fraction field K. Its colimit is K ⊗[R] A, where A is the actual
geometric stalk. The existing fraction-tensor comparison identifies this ring
with Frac(A). Its K-scalar map is the existing geometricStalkFractionFieldMap:
fraction-ring extensionality reduces the comparison to the original map R → A.

Transporting the actual base-changed cocone along this K-algebra equivalence
gives a filtered colimit with vertex the actual strict generic field. The
literal cocone-leg formula retains both the fraction-field map and the actual
geometric-stalk germ maps.

This constructs the colimit required for finite-presentation descent over K,
without requiring finite presentation of K over R. It is a prerequisite for
StacksProjectChapter58.md:1092 / 0BSM, not the full exact-sequence result.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace EtaleFundamentalGroups.StrictHenselian

universe u

variable {R Ω : Type u} [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
  [IsLocalRing R] [Field Ω] (φ : R →+* Ω) [IsLocalHom φ]

/-- The generic tensor comparison respects the actual original fraction-field
map, rather than an independently chosen action on the strict generic field. -/
def geometricStalkGenericFieldEquiv :
    letI : Algebra R (geometricStalk (Spec.map (CommRingCat.ofHom φ))) :=
      (geometricStalkStructureMap φ).toAlgebra
    letI : Algebra (FractionRing R)
        (FractionRing (geometricStalk (Spec.map (CommRingCat.ofHom φ)))) :=
      (geometricStalkFractionFieldMap φ).toAlgebra
    (FractionRing R ⊗[R] geometricStalk (Spec.map (CommRingCat.ofHom φ))) ≃ₐ[FractionRing R]
      FractionRing (geometricStalk (Spec.map (CommRingCat.ofHom φ))) := by
  let A := geometricStalk (Spec.map (CommRingCat.ofHom φ))
  let K := FractionRing R
  let F := FractionRing A
  letI : Algebra R A := (geometricStalkStructureMap φ).toAlgebra
  letI : Algebra K F := (geometricStalkFractionFieldMap φ).toAlgebra
  let e : (A ⊗[R] K) ≃ₐ[A] F := geometricStalkFractionTensorEquiv φ
  have hmap : e.toRingHom.comp
      (Algebra.TensorProduct.includeRight : K →ₐ[R] (A ⊗[R] K)).toRingHom =
      geometricStalkFractionFieldMap φ := by
    apply IsFractionRing.ringHom_ext (A := R)
    intro r
    change e ((Algebra.TensorProduct.includeRight : K →ₐ[R] (A ⊗[R] K))
      (algebraMap R K r)) = geometricStalkFractionFieldMap φ (algebraMap R K r)
    rw [AlgHom.commutes]
    change e (algebraMap A (A ⊗[R] K) (geometricStalkStructureMap φ r)) = _
    rw [e.commutes]
    exact (geometricStalkFractionFieldMap_algebraMap φ r).symm
  refine
    { __ := (Algebra.TensorProduct.comm R K A).toRingEquiv.trans e.toRingEquiv
      commutes' := ?_ }
  intro k
  change e ((Algebra.TensorProduct.comm R K A) (k ⊗ₜ[R] (1 : A))) =
    geometricStalkFractionFieldMap φ k
  rw [Algebra.TensorProduct.comm_tmul]
  exact RingHom.congr_fun hmap k

/-- On stalk elements the generic comparison is the canonical inclusion in
the actual fraction field. -/
theorem geometricStalkGenericFieldEquiv_one_tmul
    (a : geometricStalk (Spec.map (CommRingCat.ofHom φ))) :
    let : Algebra R (geometricStalk (Spec.map (CommRingCat.ofHom φ))) :=
      (geometricStalkStructureMap φ).toAlgebra
    let : Algebra (FractionRing R)
        (FractionRing (geometricStalk (Spec.map (CommRingCat.ofHom φ)))) :=
      (geometricStalkFractionFieldMap φ).toAlgebra
    geometricStalkGenericFieldEquiv φ ((1 : FractionRing R) ⊗ₜ[R] a) =
      algebraMap (geometricStalk (Spec.map (CommRingCat.ofHom φ)))
        (FractionRing (geometricStalk (Spec.map (CommRingCat.ofHom φ)))) a := by
  let A := geometricStalk (Spec.map (CommRingCat.ofHom φ))
  let : Algebra R A := (geometricStalkStructureMap φ).toAlgebra
  let : Algebra (FractionRing R) (FractionRing A) :=
    (geometricStalkFractionFieldMap φ).toAlgebra
  change geometricStalkFractionTensorEquiv φ
    (algebraMap A (A ⊗[R] FractionRing R) a) = algebraMap A (FractionRing A) a
  exact (geometricStalkFractionTensorEquiv φ).commutes a

/-- The generic comparison retains both literal factor maps. -/
theorem geometricStalkGenericFieldEquiv_tmul (k : FractionRing R)
    (a : geometricStalk (Spec.map (CommRingCat.ofHom φ))) :
    let : Algebra R (geometricStalk (Spec.map (CommRingCat.ofHom φ))) :=
      (geometricStalkStructureMap φ).toAlgebra
    let : Algebra (FractionRing R)
        (FractionRing (geometricStalk (Spec.map (CommRingCat.ofHom φ)))) :=
      (geometricStalkFractionFieldMap φ).toAlgebra
    geometricStalkGenericFieldEquiv φ (k ⊗ₜ[R] a) =
      geometricStalkFractionFieldMap φ k *
        algebraMap (geometricStalk (Spec.map (CommRingCat.ofHom φ)))
          (FractionRing (geometricStalk (Spec.map (CommRingCat.ofHom φ)))) a := by
  let A := geometricStalk (Spec.map (CommRingCat.ofHom φ))
  let K := FractionRing R
  let : Algebra R A := (geometricStalkStructureMap φ).toAlgebra
  let : Algebra K (FractionRing A) := (geometricStalkFractionFieldMap φ).toAlgebra
  let e : (K ⊗[R] A) ≃ₐ[K] FractionRing A := geometricStalkGenericFieldEquiv φ
  calc
    e (k ⊗ₜ[R] a) = e ((k ⊗ₜ[R] (1 : A)) * ((1 : K) ⊗ₜ[R] a)) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    _ = e (k ⊗ₜ[R] (1 : A)) * e ((1 : K) ⊗ₜ[R] a) := map_mul e _ _
    _ = geometricStalkFractionFieldMap φ k * algebraMap A (FractionRing A) a := by
      change e (algebraMap K (K ⊗[R] A) k) * e ((1 : K) ⊗ₜ[R] a) = _
      rw [e.commutes]
      exact congrArg (fun z => geometricStalkFractionFieldMap φ k * z)
        (geometricStalkGenericFieldEquiv_one_tmul φ a)

variable [IsSepClosed Ω]

/-- Generic fibers of the actual small pointed étale-neighborhood diagram. -/
def geometricStalkSmallGenericAlgebraDiagram :
    GeometricStalkAlgebraIndex φ ⥤ Under (CommRingCat.of (FractionRing R)) :=
  geometricStalkSmallAlgebraDiagram φ ⋙
    CommRingCat.tensorProd (CommRingCat.of R) (CommRingCat.of (FractionRing R))

/-- Base change of the actual germ cocone, with its literal tensor vertex. -/
def geometricStalkGenericTensorCocone : Cocone (geometricStalkSmallGenericAlgebraDiagram φ) :=
  (CommRingCat.tensorProd (CommRingCat.of R) (CommRingCat.of (FractionRing R))).mapCocone
    (geometricStalkSmallAlgebraCocone φ)

/-- Tensor base change preserves the already constructed small colimit. -/
def geometricStalkGenericTensorCoconeIsColimit :
    IsColimit (geometricStalkGenericTensorCocone φ) := by
  let tK := CommRingCat.tensorProd (CommRingCat.of R) (CommRingCat.of (FractionRing R))
  have : PreservesColimit (geometricStalkSmallAlgebraDiagram φ) tK :=
    preservesColimit_of_natIso (geometricStalkSmallAlgebraDiagram φ)
      (CommRingCat.tensorProdIsoPushout (CommRingCat.of R)
        (CommRingCat.of (FractionRing R))).symm
  exact isColimitOfPreserves tK (geometricStalkSmallAlgebraCoconeIsColimit φ)

/-- The constructed comparison between the two actual vertices in `Under K`.
Its endpoints name the existing tensor cocone and the existing fraction-field
map explicitly, so later cocone transport reuses this single typed owner. -/
def geometricStalkGenericFieldVertexIso :
    (geometricStalkGenericTensorCocone φ).pt ≅
      Under.mk (CommRingCat.ofHom (geometricStalkFractionFieldMap φ)) := by
  let A := geometricStalk (Spec.map (CommRingCat.ofHom φ))
  letI : Algebra R A := (geometricStalkStructureMap φ).toAlgebra
  letI : Algebra (FractionRing R) (FractionRing A) :=
    (geometricStalkFractionFieldMap φ).toAlgebra
  exact (geometricStalkGenericFieldEquiv φ).toUnder

/-- The actual strict generic field is the vertex, with the actual induced
fraction-field scalar map. -/
def geometricStalkGenericFieldCocone : Cocone (geometricStalkSmallGenericAlgebraDiagram φ) :=
  (geometricStalkGenericTensorCocone φ).extend (geometricStalkGenericFieldVertexIso φ).hom

/-- The actual strict generic field cocone is colimiting; its vertex
comparison is constructed, not included as an input. -/
def geometricStalkGenericFieldCoconeIsColimit :
    IsColimit (geometricStalkGenericFieldCocone φ) :=
  IsColimit.extendIso (s := geometricStalkGenericTensorCocone φ)
    (geometricStalkGenericFieldVertexIso φ).hom
    (geometricStalkGenericTensorCoconeIsColimit φ)

/-- The actual generic cocone leg is the fraction-field scalar times the
fraction-field image of the original actual germ cocone leg. -/
theorem geometricStalkGenericFieldCocone_tmul (i : GeometricStalkAlgebraIndex φ)
    (k : FractionRing R) (z : (geometricStalkSmallAlgebraDiagram φ).obj i) :
    let : Algebra R ((geometricStalkSmallAlgebraDiagram φ).obj i).right :=
      ((geometricStalkSmallAlgebraDiagram φ).obj i).hom.hom.toAlgebra
    ((geometricStalkGenericFieldCocone φ).ι.app i).right (k ⊗ₜ[R] z) =
      geometricStalkFractionFieldMap φ k *
        algebraMap (geometricStalk (Spec.map (CommRingCat.ofHom φ)))
          (FractionRing (geometricStalk (Spec.map (CommRingCat.ofHom φ))))
          (((geometricStalkSmallAlgebraCocone φ).ι.app i).right z) := by
  let : Algebra R ((geometricStalkSmallAlgebraDiagram φ).obj i).right :=
    ((geometricStalkSmallAlgebraDiagram φ).obj i).hom.hom.toAlgebra
  let A := geometricStalk (Spec.map (CommRingCat.ofHom φ))
  let : Algebra R A := (geometricStalkStructureMap φ).toAlgebra
  let : Algebra (FractionRing R) (FractionRing A) :=
    (geometricStalkFractionFieldMap φ).toAlgebra
  change geometricStalkGenericFieldEquiv φ
    (filteredBaseChangeCoconeLegAlgHom (A := FractionRing R)
      (geometricStalkSmallAlgebraCocone φ) i (k ⊗ₜ[R] z)) = _
  rw [filteredBaseChangeCoconeLegAlgHom_tmul]
  exact geometricStalkGenericFieldEquiv_tmul φ k
    (CommRingCat.toAlgHom ((geometricStalkSmallAlgebraCocone φ).ι.app i) z)

end EtaleFundamentalGroups.StrictHenselian
