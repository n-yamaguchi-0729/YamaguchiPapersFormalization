/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Inertia.CommAlgCanonicalTameCharacter
import EtaleFundamentalGroups.Inertia.CommAlgIdealTameGroups
import EtaleFundamentalGroups.Inertia.CommAlgIdealInertiaConjugate
import EtaleFundamentalGroups.Inertia.CommAlgStabilizerResidueMorphism
import EtaleFundamentalGroups.Inertia.CommAlgResidueRootsMap
import EtaleFundamentalGroups.Inertia.FiniteIdealCanonicalTameConjugation
import ValuedFieldTheory.Ramification.HilbertRamification.RootsOfUnityFieldEmbedding
import Mathlib.RingTheory.Ideal.Pointwise

/-!
# Equivariance of intrinsic canonical tame characters

Constructs the native residue action on canonical tame roots and identifies it with the
localization action. Proves equivariance under stabilizer conjugation.
-/

noncomputable section

namespace EtaleFundamentalGroups.Inertia

open RamificationTheory.HilbertRamification
open scoped Pointwise

universe u v

/-- The same quotient residue automorphism acts on the full intrinsic tame
roots group through the fixed canonical quotient-residue equivalence. -/
def commAlgCanonicalResidueRootsMap
    (A : Type u) [CommRing A] (B : CommAlgCat.{v} A) [IsDedekindDomain B]
    (Q : Ideal B) [Q.IsMaximal] (hQ : Q ≠ ⊥)
    (ρ : nativeAlgebraResidueAutomorphisms B Q) :
    GrpCat.Hom (commAlgIdealTameRootsGroup A B Q hQ)
      (commAlgIdealTameRootsGroup A B Q hQ) :=
  commAlgResidueRootsMap B Q (commAlgIdealTameOrder A B Q hQ) ρ

/-- The actual intrinsic stabilizer acts through its existing native residue
morphism. No localized action is retained by this native map's interface. -/
def commAlgStabilizerCanonicalRootsMap
    (A : Type u) [CommRing A] (B : CommAlgCat.{v} A) [IsDedekindDomain B]
    (Q : Ideal B) [Q.IsMaximal] (hQ : Q ≠ ⊥)
    (d : nativeResidueStabilizer B (B ≃ₐ[A] B) Q) :
    GrpCat.Hom (commAlgIdealTameRootsGroup A B Q hQ)
      (commAlgIdealTameRootsGroup A B Q hQ) :=
  commAlgCanonicalResidueRootsMap A B Q hQ
    ((commAlgStabilizerResidueMorphism A B Q).hom'.toFun d)

/-- Its coefficient action is exactly the standard localization-residue
action, by the proved square for the same native residue morphism. -/
theorem commAlgStabilizerCanonicalRootsMap_eq_standard
    (A : Type u) [CommRing A] (B : CommAlgCat.{v} A) [IsDedekindDomain B]
    (Q : Ideal B) [Q.IsMaximal] (hQ : Q ≠ ⊥)
    (d : nativeResidueStabilizer B (B ≃ₐ[A] B) Q) :
    commAlgStabilizerCanonicalRootsMap A B Q hQ d =
      rootsGroupMap
        (MulSemiringAction.toRingHom (MulAction.stabilizer (B ≃ₐ[A] B) Q)
          Q.ResidueField d)
        (finiteIdealTameOrder B (B ≃ₐ[A] B) Q hQ) :=
  (nativeAlgebraResidueMorphism_rootsMap B (B ≃ₐ[A] B) Q
    (commAlgAutomorphism_comp_coefficient A B)
    (finiteIdealTameOrder B (B ≃ₐ[A] B) Q hQ) d).symm

/-- The existing canonical character intertwines actual intrinsic
conjugation with the same native stabilizer residue action on its roots. -/
theorem commAlgCanonicalTameCharacter_conjugate
    (A : Type u) [CommRing A] (B : CommAlgCat.{v} A)
    [IsDedekindDomain B] [Finite (B ≃ₐ[A] B)]
    (Q : Ideal B) [Q.IsMaximal] (hQ : Q ≠ ⊥)
    (d : nativeResidueStabilizer B (B ≃ₐ[A] B) Q)
    (σ : commAlgIdealInertiaGroup A B Q) :
    (commAlgCanonicalTameCharacter A B Q hQ).toFun
        (commAlgIdealInertiaConjugate A B Q d σ) =
      (commAlgStabilizerCanonicalRootsMap A B Q hQ d).hom'.toFun
        ((commAlgCanonicalTameCharacter A B Q hQ).toFun σ) := by
  have hconj := finiteIdealCanonicalTameCharacterGroupMap_conjugate
    A B (B ≃ₐ[A] B) Q hQ d σ
  exact hconj.trans
    (congrArg
      (fun f : GrpCat.Hom (commAlgIdealTameRootsGroup A B Q hQ)
          (commAlgIdealTameRootsGroup A B Q hQ) =>
        f.hom'.toFun ((commAlgCanonicalTameCharacter A B Q hQ).toFun σ))
      (commAlgStabilizerCanonicalRootsMap_eq_standard A B Q hQ d).symm)

end EtaleFundamentalGroups.Inertia
