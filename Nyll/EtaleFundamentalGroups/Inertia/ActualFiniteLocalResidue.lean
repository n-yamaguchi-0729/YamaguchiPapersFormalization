/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Inertia.AbsoluteFiniteNormalization
import Nyll.EtaleFundamentalGroups.Inertia.ActualFiniteNormalizationResidueMap
import Nyll.EtaleFundamentalGroups.Inertia.ActualFiniteNormalizationTower
import Nyll.EtaleFundamentalGroups.Inertia.ActualFiniteNormalizationLocalTower
import Nyll.SchemeTheory.Normalization.SubalgebraPreimage
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import Mathlib.RingTheory.Localization.AtPrime.Basic

/-!
# Local coefficient maps to the ambient residue field

Maps finite local normalizations into the original residue field. Identifies these maps with the
finite residue embeddings and proves their finite tower compatibility.
-/

noncomputable section

namespace EtaleFundamentalGroups.Inertia

open SchemeTheory

universe u v w

private theorem localRingHom_eq_of_eq
    (B C : Type w) [CommRing B] [CommRing C]
    (P : Ideal B) (R : Ideal C) [P.IsPrime] [R.IsPrime]
    (f g : B →+* C) (hf : P = R.comap f) (hg : P = R.comap g) (h : f = g) :
    Localization.localRingHom P R f hf = Localization.localRingHom P R g hg := by
  subst g
  rfl

variable (A : Type u) (K : Type v) (L : Type w)
  [CommRing A] [Field K] [Field L]
  [Algebra A K] [Algebra K L] [Algebra A L] [IsScalarTower A K L]
  (Q : Ideal (normalizationCommAlgCat A L)) [Q.IsPrime]

/-- The actual finite local normalization maps into the original residue
field by localizing its literal ambient inclusion and then taking residue. -/
def actualFiniteLocalResidueMap (E : FiniteGaloisIntermediateField K L) :
    letI := finiteAbsoluteNormalizationPrime_isPrime A K L Q E
    Localization.AtPrime (finiteAbsoluteNormalizationPrime A K L Q E) →+* Q.ResidueField := by
  letI := finiteAbsoluteNormalizationPrime_isPrime A K L Q E
  exact (IsLocalRing.residue (Localization.AtPrime Q)).comp
    (Localization.localRingHom (finiteAbsoluteNormalizationPrime A K L Q E) Q
      (finiteAbsoluteNormalizationRingMap A K L E) rfl)

/-- This local coefficient map induces precisely the residue embedding used
by the existing canonical tame coordinate. -/
theorem actualFiniteLocalResidueMap_eq_residueMap_comp
    [IsFractionRing A K] [IsGalois K L]
    (E : FiniteGaloisIntermediateField K L) :
    letI := finiteAbsoluteNormalizationPrime_isPrime A K L Q E
    actualFiniteLocalResidueMap A K L Q E =
      (actualFiniteNormalizationResidueMap A K L Q E).comp
        (IsLocalRing.residue
          (Localization.AtPrime (finiteAbsoluteNormalizationPrime A K L Q E))) := by
  let := finiteAbsoluteNormalizationPrime_isPrime A K L Q E
  let : IsLocalHom
      (Localization.localRingHom (finiteAbsoluteNormalizationPrime A K L Q E) Q
        (finiteAbsoluteNormalizationRingMap A K L E) rfl) :=
    Localization.isLocalHom_localRingHom
      (finiteAbsoluteNormalizationPrime A K L Q E) Q
      (finiteAbsoluteNormalizationRingMap A K L E) rfl
  exact (IsLocalRing.ResidueField.map_comp_residue
    (Localization.localRingHom (finiteAbsoluteNormalizationPrime A K L Q E) Q
      (finiteAbsoluteNormalizationRingMap A K L E) rfl)).symm

/-- The same literal local coefficient-to-residue maps form the actual
finite tower triangle. -/
theorem actualFiniteLocalResidueMap_tower
    (E F : FiniteGaloisIntermediateField K L) (h : E ≤ F) :
    letI := finiteAbsoluteNormalizationPrime_isPrime A K L Q E
    letI := finiteAbsoluteNormalizationPrime_isPrime A K L Q F
    (actualFiniteLocalResidueMap A K L Q F).comp
        (actualFiniteNormalizationTowerLocalRingMap A K L Q E F h) =
      actualFiniteLocalResidueMap A K L Q E := by
  let := finiteAbsoluteNormalizationPrime_isPrime A K L Q E
  let := finiteAbsoluteNormalizationPrime_isPrime A K L Q F
  have hlocal := Localization.localRingHom_comp
    (finiteAbsoluteNormalizationPrime A K L Q E)
    (finiteAbsoluteNormalizationPrime A K L Q F) Q
    (actualFiniteNormalizationTowerRingMap A K L E F h)
    (actualFiniteNormalizationPrime_tower A K L Q E F h)
    (finiteAbsoluteNormalizationRingMap A K L F) rfl
  have hlocal' := localRingHom_eq_of_eq
    (finiteAbsoluteNormalizationAlgebra A K L E) (normalizationCommAlgCat A L)
    (finiteAbsoluteNormalizationPrime A K L Q E) Q
    ((finiteAbsoluteNormalizationRingMap A K L F).comp
      (actualFiniteNormalizationTowerRingMap A K L E F h))
    (finiteAbsoluteNormalizationRingMap A K L E)
    (by
      rw [actualFiniteNormalizationTowerRingMap_comp]
      rfl) rfl
    (actualFiniteNormalizationTowerRingMap_comp A K L E F h)
  exact congrArg
    (fun f => (IsLocalRing.residue (Localization.AtPrime Q)).comp f)
    (hlocal.symm.trans hlocal')

end EtaleFundamentalGroups.Inertia

end
