/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Inertia.CommAlgCanonicalTameEquivariance
import Nyll.EtaleFundamentalGroups.Inertia.CommAlgStabilizerResidueCoefficients

/-!
# The actual finite canonical scalar action data

This data-only interface closes the native group and root carriers. It
stores actual functions and no propositions. Its sole factory uses the
existing canonical normalized character, conjugation and residue action;
equivariance is proved separately from the existing finite theorem.
-/

noncomputable section

namespace EtaleFundamentalGroups.Inertia

universe u v

/-- The carrier and scalar functions of an actual inertia action. No laws are fields. -/
structure ScalarInertiaActionData where
  /-- The actual inertia carrier. -/
  inertia : Type v
  /-- The actual decomposition carrier. -/
  decomposition : Type v
  /-- The actual residue coefficient carrier. -/
  residue : Type v
  /-- The scalar projection of the existing canonical character. -/
  character : inertia → residue
  /-- The existing decomposition conjugation on inertia. -/
  conjugate : decomposition → inertia → inertia
  /-- The scalar action of the existing residue automorphism. -/
  action : decomposition → residue → residue

/-- Store exactly the existing native canonical finite scalar maps. -/
def commAlgCanonicalTameScalarData
    (A : Type u) [CommRing A] (B : CommAlgCat.{v} A)
    [IsDedekindDomain B.carrier] [Finite (B.carrier ≃ₐ[A] B.carrier)]
    (Q : Ideal B.carrier) [Q.IsMaximal] (hQ : Q ≠ ⊥) :
    ScalarInertiaActionData.{v} where
  inertia := (commAlgIdealInertiaGroup A B Q).carrier
  decomposition := (commAlgIdealDecompositionGroup A B Q).carrier
  residue := Q.ResidueField
  character σ := ((commAlgCanonicalTameCharacter A B Q hQ).toFun σ).val.val
  conjugate := commAlgIdealInertiaConjugate A B Q
  action d := (commAlgDecompositionResidueRingHom A B Q d).toFun

/-- The actual stored maps satisfy canonical scalar equivariance. -/
theorem commAlgCanonicalTameScalarData_equivariant
    (A : Type u) [CommRing A] (B : CommAlgCat.{v} A)
    [IsDedekindDomain B.carrier] [Finite (B.carrier ≃ₐ[A] B.carrier)]
    (Q : Ideal B.carrier) [Q.IsMaximal] (hQ : Q ≠ ⊥)
    (d : (commAlgCanonicalTameScalarData A B Q hQ).decomposition)
    (σ : (commAlgCanonicalTameScalarData A B Q hQ).inertia) :
    (commAlgCanonicalTameScalarData A B Q hQ).character
        ((commAlgCanonicalTameScalarData A B Q hQ).conjugate d σ) =
      (commAlgCanonicalTameScalarData A B Q hQ).action d
        ((commAlgCanonicalTameScalarData A B Q hQ).character σ) :=
  congrArg (fun z : (commAlgIdealTameRootsGroup A B Q hQ).carrier => z.val.val)
    (commAlgCanonicalTameCharacter_conjugate A B Q hQ d σ)

end EtaleFundamentalGroups.Inertia

end
