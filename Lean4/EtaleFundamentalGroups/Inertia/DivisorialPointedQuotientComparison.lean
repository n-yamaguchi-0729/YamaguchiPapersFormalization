/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.GaloisCovers.FieldCoverPointTransport
import EtaleFundamentalGroups.GaloisCovers.FieldCoverQuotient
import EtaleFundamentalGroups.GeometricFiber.Functoriality
import EtaleFundamentalGroups.Inertia.DivisorialStrictHenselian
import EtaleFundamentalGroups.Inertia.PointedQuotientTransport
import EtaleFundamentalGroups.Inertia.DivisorialQuotientFundamentalGroup

/-!
# Pointed finite-cover realization of divisorial inertia quotients

The pointed categorical quotient of the finite Galois field cover is the
usual restriction quotient.  Restricting that cover along the canonical
inertia-field morphism therefore realizes the canonical divisorial quotient,
with the base-point transport made explicit.
-/

noncomputable section


universe uA u

open CategoryTheory AlgebraicGeometry

namespace EtaleFundamentalGroups.Inertia

open AlgebraicGeometry.FiniteEtale

private theorem fieldComposite_isSepClosure
    (F E Omega : Type u)
    [Field F] [Field E] [Field Omega]
    [Algebra F E] [Algebra E Omega] [hFOmega : Algebra F Omega]
    [Algebra.IsSeparable F E] [IsSepClosure E Omega]
    (hcomp : algebraMap F Omega =
      (algebraMap E Omega).comp (algebraMap F E)) :
    IsSepClosure F Omega := by
  let : IsScalarTower F E Omega := IsScalarTower.of_algebraMap_eq' hcomp
  exact ⟨IsSepClosure.sep_closed E, Algebra.IsSeparable.trans F E Omega⟩

variable (K L : Type u) [Field K] [Field L] [Algebra K L]
variable [FiniteDimensional K L] [_root_.IsGalois K L]

/-- For the canonical point of the field cover `Spec L → Spec K`, the
categorical pointed quotient is the usual restriction homomorphism from the
chosen separable closure. -/
theorem fieldFiniteEtaleCoverQuotientHom_eq_restriction :
    let Omega := SeparableClosure L
    let : CommRing Omega := (inferInstance : Field Omega).toCommRing
    let : CommSemiring Omega := (inferInstance : Field Omega).toSemifield.toCommSemiring
    let : Algebra K Omega :=
      ((algebraMap L Omega).comp (algebraMap K L)).toAlgebra
    let : IsScalarTower K L Omega := IsScalarTower.of_algebraMap_eq' rfl
    let Y := FiniteEtale.mk (ξ K L)
    let hY := EtaleFundamentalGroups.fieldFiniteEtaleCover_isGalois K L
    let : CategoryTheory.PreGaloisCategory.IsGalois Y := hY
    let y := EtaleFundamentalGroups.fieldFiniteEtaleCoverCanonicalPoint K L Omega
    (EtaleFundamentalGroups.fieldGaloisToFiniteEtaleAutOpMulEquiv K L).symm.toMonoidHom.comp
        (EtaleFundamentalGroups.finiteEtaleGaloisCoverQuotientMonoidHom
          (ξ K Omega) Y hY y) =
      finiteGaloisSeparableClosureQuotientHom (K := K) (L := L) := by
  intro Omega hOmegaCommRing hOmegaCommSemiring hKOmega hKLOmega Y hY hYGalois y
  let : IsSepClosure K Omega := fieldComposite_isSepClosure K L Omega rfl
  apply MonoidHom.ext
  intro a
  let eK := absoluteGaloisToFiberAutMulEquiv K Omega inferInstance
  let sigma : Gal(Omega/K) := eK.symm a
  have hq := EtaleFundamentalGroups.fieldFiniteEtaleCoverQuotient_apply
    K L Omega sigma
  change
    (EtaleFundamentalGroups.fieldGaloisToFiniteEtaleAutOpMulEquiv K L).symm
        (EtaleFundamentalGroups.finiteEtaleGaloisCoverQuotientMonoidHom
          (ξ K Omega) Y hY y a) =
      AlgEquiv.restrictNormalHom (F := K) (K₁ := Omega) L (eK.symm a)
  simpa only [sigma, eK, MulEquiv.apply_symm_apply] using hq

end EtaleFundamentalGroups.Inertia

end
