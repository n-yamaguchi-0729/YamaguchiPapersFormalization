/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import SchemeTheory.RingTheory.Ramification.NativeAlgebraResidueCoefficient
import SchemeTheory.RingTheory.Ramification.NativeAlgebraResidueLocalization
import SchemeTheory.RingTheory.Ramification.NativeMaximalResidue
import SchemeTheory.RingTheory.Ramification.NativeAlgebraResidueEpi
import SchemeTheory.RingTheory.Ramification.StabilizerLocalizationAction
import SchemeTheory.CategoryTheory.CommAlgRingMap
import ValuedFieldTheory.Ramification.HilbertRamification.RootsOfUnityFieldEmbedding

import Mathlib.RingTheory.Ideal.Pointwise

/-!
# Native residue actions on roots

Constructs local residue-root group objects and maps induced by quotient automorphisms.
Identifies the native residue morphism with the localization roots action.
-/

noncomputable section

namespace EtaleFundamentalGroups.Inertia

open SchemeTheory RamificationTheory.HilbertRamification

open scoped Pointwise

universe u v

/-- Roots in the actual local residue field, with their native group object. -/
def commAlgResidueRootsGroup
    {A : Type u} [CommRing A] (R : CommAlgCat.{v} A)
    (Q : Ideal R) [Q.IsMaximal] (n : ℕ) : GrpCat.{v} :=
  rootsGroupObject Q.ResidueField n

/-- The given native quotient automorphism acts on roots through the fixed
canonical quotient-to-local-residue equivalence. -/
def commAlgResidueRootsMap
    {A : Type u} [CommRing A] (R : CommAlgCat.{v} A)
    (Q : Ideal R) [Q.IsMaximal] (n : ℕ)
    (ρ : nativeAlgebraResidueAutomorphisms R Q) :
    GrpCat.Hom (commAlgResidueRootsGroup R Q n) (commAlgResidueRootsGroup R Q n) :=
  rootsGroupMap
    (((maximalQuotientResidueEquiv Q).toRingHom.comp
      (nativeAlgebraResidueAutomorphismRingEquiv R Q ρ).toRingHom).comp
      (maximalQuotientResidueEquiv Q).symm.toRingHom) n

/-- The standard localization action on roots is induced by the SAME native
residue morphism. The equality uses its proved actual coefficient square. -/
theorem nativeAlgebraResidueMorphism_rootsMap
    {A : Type u} [CommRing A] (R : CommAlgCat.{v} A)
    (G : Type v) [Group G] [MulSemiringAction G R]
    (Q : Ideal R) [Q.IsMaximal]
    (hbase : ∀ g : G, (MulSemiringAction.toRingHom G R g).comp
      (commAlgCoefficientMap R) = commAlgCoefficientMap R)
    (n : ℕ) (d : nativeResidueStabilizer R G Q) :
    rootsGroupMap
        (MulSemiringAction.toRingHom (MulAction.stabilizer G Q) Q.ResidueField d) n =
      commAlgResidueRootsMap R Q n
        ((nativeAlgebraResidueMorphism R G Q hbase).hom'.toFun d) := by
  exact congrArg (fun f : Q.ResidueField →+* Q.ResidueField => rootsGroupMap f n)
    (nativeAlgebraResidueMorphism_localization_ringHom R G Q hbase d)

end EtaleFundamentalGroups.Inertia

end
