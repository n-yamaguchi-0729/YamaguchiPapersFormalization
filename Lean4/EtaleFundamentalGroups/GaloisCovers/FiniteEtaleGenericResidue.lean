/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.FiniteEtale.FunctionField
import EtaleFundamentalGroups.GaloisCovers.FunctionFieldResidueNaturality

/-!
# Generic residue fields of finite-etale covers

Finiteness of a dense function-field extension transports to the residue
fields at the source generic point.  In particular, the generic residue-field
extension of a connected finite-etale cover is finite-dimensional.
-/

noncomputable section

open CategoryTheory TopologicalSpace
open CategoryTheory.PreGaloisCategory
open AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Hom

universe u

variable {S T : Scheme.{u}}

/-- A finite-dimensional function-field extension induced by a dense
morphism remains finite-dimensional after identifying both function fields
with generic-point residue fields. -/
theorem finiteDimensional_genericResidueField_of_functionField
    [IsIntegral S] [IsIntegral T]
    (q : T ⟶ S) (hq : DenseRange q) :
    letI : Algebra S.functionField T.functionField :=
      q.functionFieldAlgebraOfDenseRange hq
    FiniteDimensional S.functionField T.functionField →
    letI : Algebra (S.residueField (q (genericPoint T)))
        (T.residueField (genericPoint T)) :=
      (q.residueFieldMap (genericPoint T)).hom.toAlgebra
    FiniteDimensional (S.residueField (q (genericPoint T)))
      (T.residueField (genericPoint T)) := by
  let : Algebra S.functionField T.functionField :=
    q.functionFieldAlgebraOfDenseRange hq
  intro hfinite
  let : FiniteDimensional S.functionField T.functionField := hfinite
  let : Algebra (S.residueField (q (genericPoint T)))
      (T.residueField (genericPoint T)) :=
    (q.residueFieldMap (genericPoint T)).hom.toAlgebra
  let hη : genericPoint S = q (genericPoint T) :=
    (q.map_genericPoint_of_denseRange hq).symm
  let eS : S.functionField ≃+* S.residueField (q (genericPoint T)) :=
    (Scheme.functionFieldResidueFieldRingEquiv S).trans
      (S.residueFieldCongr hη).commRingCatIsoToRingEquiv
  let eT : T.functionField ≃+* T.residueField (genericPoint T) :=
    Scheme.functionFieldResidueFieldRingEquiv T
  apply Module.Finite.of_equiv_equiv eS eT
  change RingHom.comp (q.residueFieldMap (genericPoint T)).hom eS.toRingHom =
    RingHom.comp eT.toRingHom (q.functionFieldMap hq)
  have hnat := q.functionFieldResidueFieldRingEquiv_naturality hq
  have hnat' := congrArg CommRingCat.Hom.hom hnat
  simpa [eS, eT, hη, Category.assoc, RingHom.comp_assoc] using hnat'

end AlgebraicGeometry.Scheme.Hom

namespace EtaleFundamentalGroups

universe u

/-- The residue-field extension at the generic point of a connected
finite-etale cover is finite-dimensional over the residue field of its image
in the base. -/
theorem finiteDimensional_genericResidueField_of_finiteEtale_isConnected
    {X : Scheme.{u}} [IsIntegral X] [IsNormalIntegral X]
    [IsLocallyNoetherian X]
    (Y : FiniteEtale X) [IsConnected Y] :
    letI : IsIntegral Y.left :=
      isIntegral_left_of_isConnected_finiteEtale Y
    letI : Algebra (X.residueField (Y.hom (genericPoint Y.left)))
        (Y.left.residueField (genericPoint Y.left)) :=
      (Y.hom.residueFieldMap (genericPoint Y.left)).hom.toAlgebra
    FiniteDimensional (X.residueField (Y.hom (genericPoint Y.left)))
      (Y.left.residueField (genericPoint Y.left)) := by
  let : IsIntegral Y.left :=
    isIntegral_left_of_isConnected_finiteEtale Y
  let hY : DenseRange Y.hom :=
    finiteEtale_hom_denseRange_of_isConnected Y
  let : Algebra X.functionField Y.left.functionField :=
    finiteEtaleFunctionFieldAlgebra Y
  apply Scheme.Hom.finiteDimensional_genericResidueField_of_functionField
    (S := X) (T := Y.left) Y.hom hY
  exact finiteDimensional_functionField_of_finiteEtale_isConnected Y

end EtaleFundamentalGroups
