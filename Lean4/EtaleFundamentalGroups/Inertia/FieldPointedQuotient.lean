/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.GaloisCovers.FieldCoverQuotient
import EtaleFundamentalGroups.GeometricFiber.FieldFundamentalGroupConjugacy
import EtaleFundamentalGroups.GeometricFiber.FieldFunctoriality
import EtaleFundamentalGroups.GeometricFiber.Functoriality
import EtaleFundamentalGroups.Inertia.DivisorialStrictHenselian
import EtaleFundamentalGroups.Inertia.PointedQuotientTransport

/-!
# Pointed finite quotients over abstract fields

The actual pointed quotient and its canonical restriction map are constructed
and compared before choosing an intermediate field or a separable closure.
Their geometric points therefore use the same field structures throughout.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.FiniteEtale

namespace EtaleFundamentalGroups.Inertia

section Restriction

variable (K L Omega : Type u) [Field K] [Field L] [Field Omega]
variable [Algebra K L] [Algebra K Omega] [Algebra L Omega]
variable [IsScalarTower K L Omega]
variable [FiniteDimensional K L] [_root_.IsGalois K L]
variable [IsSepClosed Omega] [IsSepClosure K Omega]

/-- Restriction from the chosen geometric-fiber fundamental group to a
finite Galois extension. -/
noncomputable def fieldFiniteGaloisRestrictionHom :
    Aut (fib K Omega) →* Gal(L/K) :=
  (AlgEquiv.restrictNormalHom (F := K) (K₁ := Omega) L).comp
    (absoluteGaloisToFiberAutMulEquiv K Omega inferInstance).symm.toMonoidHom

private theorem fieldCoverQuotient_eq_restriction :
    (EtaleFundamentalGroups.fieldGaloisToFiniteEtaleAutOpMulEquiv K L).symm.toMonoidHom.comp
      (EtaleFundamentalGroups.finiteEtaleGaloisCoverQuotientMonoidHom
        (ξ K Omega) (FiniteEtale.mk (ξ K L))
        (EtaleFundamentalGroups.fieldFiniteEtaleCover_isGalois K L)
        (EtaleFundamentalGroups.fieldFiniteEtaleCoverCanonicalPoint K L Omega)) =
      fieldFiniteGaloisRestrictionHom K L Omega := by
  apply MonoidHom.ext
  intro a
  let eK := absoluteGaloisToFiberAutMulEquiv K Omega inferInstance
  let sigma : Gal(Omega/K) := eK.symm a
  have h := EtaleFundamentalGroups.fieldFiniteEtaleCoverQuotient_apply
    K L Omega sigma
  change
    (EtaleFundamentalGroups.fieldGaloisToFiniteEtaleAutOpMulEquiv K L).symm
      (EtaleFundamentalGroups.finiteEtaleGaloisCoverQuotientMonoidHom
        (ξ K Omega) (FiniteEtale.mk (ξ K L))
        (EtaleFundamentalGroups.fieldFiniteEtaleCover_isGalois K L)
        (EtaleFundamentalGroups.fieldFiniteEtaleCoverCanonicalPoint K L Omega) a) =
      AlgEquiv.restrictNormalHom (F := K) (K₁ := Omega) L (eK.symm a)
  simpa only [sigma, eK, MulEquiv.apply_symm_apply] using h

end Restriction

section Pointed

variable (K F L Omega : Type u)
variable [Field K] [Field F] [Field L] [Field Omega]
variable [Algebra K L] [Algebra K F]
variable [Algebra K Omega] [Algebra F Omega] [Algebra L Omega]
variable [IsScalarTower K L Omega] [IsScalarTower K F Omega]
variable [FiniteDimensional K L] [_root_.IsGalois K L]
variable [IsSepClosed Omega] [IsSepClosure K Omega]

-- The nine data-bearing instances are the four fields and five algebras.
-- Each scalar target has one owner; the tower and closure witnesses are propositions.

/-- The actual pointed quotient of `Spec L → Spec K` along `Spec F → Spec K`,
transporting the point induced by `L → Omega` along `p`. The default is the
canonical comparison of the composite geometric point. -/
noncomputable def fieldPointedQuotientHom
    (p : fiber (ξ F Omega ≫ ξ K F) ≅ fib K Omega :=
      fieldBasePointFiberIso K F Omega) :
    Aut (fib F Omega) →* (Aut (FiniteEtale.mk (ξ K L)))ᵐᵒᵖ :=
  finiteEtaleGaloisCoverQuotientOfMorphism (ξ K F) (ξ F Omega)
    (FiniteEtale.mk (ξ K L))
    (EtaleFundamentalGroups.fieldFiniteEtaleCover_isGalois K L)
    (p.inv.app (FiniteEtale.mk (ξ K L))
      (EtaleFundamentalGroups.fieldFiniteEtaleCoverCanonicalPoint K L Omega))

/-- The fundamental-group map followed by restriction to the finite Galois
extension, with the composite geometric point transported along `p`. The
default comparison is the canonical one. -/
noncomputable def fieldCanonicalUnconjugatedHom
    (p : fiber (ξ F Omega ≫ ξ K F) ≅ fib K Omega :=
      fieldBasePointFiberIso K F Omega) :
    Aut (fib F Omega) →* Gal(L/K) :=
  (fieldFiniteGaloisRestrictionHom K L Omega).comp
    (p.conjAut.toMonoidHom.comp
      (fundamentalGroupHom (ξ K F) (ξ F Omega)).toMonoidHom)

/-- Transporting the deck group of the actual pointed quotient to the
finite Galois group gives the canonical unconjugated restriction map. -/
theorem fieldPointedQuotientHom_eq_canonicalUnconjugatedHom
    (p : fiber (ξ F Omega ≫ ξ K F) ≅ fib K Omega :=
      fieldBasePointFiberIso K F Omega) :
    (EtaleFundamentalGroups.fieldGaloisToFiniteEtaleAutOpMulEquiv K L).symm.toMonoidHom.comp
      (fieldPointedQuotientHom K F L Omega p) =
      fieldCanonicalUnconjugatedHom K F L Omega p := by
  let Y : FiniteEtale (Spec (.of K)) := FiniteEtale.mk (ξ K L)
  let hY : CategoryTheory.PreGaloisCategory.IsGalois Y :=
    EtaleFundamentalGroups.fieldFiniteEtaleCover_isGalois K L
  let : CategoryTheory.PreGaloisCategory.IsGalois Y := hY
  let y := EtaleFundamentalGroups.fieldFiniteEtaleCoverCanonicalPoint K L Omega
  let E := EtaleFundamentalGroups.fieldGaloisToFiniteEtaleAutOpMulEquiv K L
  let g : Aut (fib F Omega) →* Aut (fib K Omega) :=
    p.conjAut.toMonoidHom.comp
      (fundamentalGroupHom (ξ K F) (ξ F Omega)).toMonoidHom
  have ht := EtaleFundamentalGroups.finiteEtaleGaloisCoverQuotientOfMorphism_transport
    (ξ K F) (ξ F Omega) (ξ K Omega) p Y hY y
  have hr := fieldCoverQuotient_eq_restriction K L Omega
  calc
    E.symm.toMonoidHom.comp (fieldPointedQuotientHom K F L Omega p) =
      E.symm.toMonoidHom.comp
        ((EtaleFundamentalGroups.finiteEtaleGaloisCoverQuotientMonoidHom
          (ξ K Omega) Y hY y).comp g) :=
      congrArg (fun f : Aut (fib F Omega) →* (Aut Y)ᵐᵒᵖ ↦
        E.symm.toMonoidHom.comp f) ht
    _ = (E.symm.toMonoidHom.comp
        (EtaleFundamentalGroups.finiteEtaleGaloisCoverQuotientMonoidHom
          (ξ K Omega) Y hY y)).comp g := rfl
    _ = fieldCanonicalUnconjugatedHom K F L Omega p :=
      congrArg (fun f : Aut (fib K Omega) →* Gal(L/K) ↦ f.comp g) hr

end Pointed

end EtaleFundamentalGroups.Inertia

end
