/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Inertia.NativeResidueRingAction
import Nyll.EtaleFundamentalGroups.Inertia.CommAlgStabilizerResidueMorphism
import Nyll.EtaleFundamentalGroups.Inertia.CommAlgDecompositionGroup
import Nyll.SchemeTheory.Normalization.NativeAutomorphismRingMaps

/-!
# Intrinsic stabilizer residue coefficients

The existing native intrinsic residue morphism has its actual algebra-
automorphism coefficient formula after canonical localization transport.
-/

namespace EtaleFundamentalGroups.Inertia

open SchemeTheory

universe u v

/-- The existing native decomposition carrier acts through its actual residue morphism. -/
noncomputable def commAlgDecompositionResidueRingHom
    (A : Type u) [CommRing A] (B : CommAlgCat.{v} A)
    (Q : Ideal B.carrier) [Q.IsMaximal]
    (d : (commAlgIdealDecompositionGroup A B Q).carrier) :
    Q.ResidueField →+* Q.ResidueField :=
  nativeAlgebraResidueRingHom B Q
    ((commAlgStabilizerResidueMorphism A B Q).hom'.toFun d)

theorem commAlgStabilizerResidueRingHom_coefficient
    (A : Type u) [CommRing A] (B : CommAlgCat.{v} A)
    (Q : Ideal B.carrier) [Q.IsMaximal]
    (d : (commAlgIdealDecompositionGroup A B Q).carrier)
    (b : B.carrier) :
    (commAlgDecompositionResidueRingHom A B Q d).toFun
        ((algebraMap B.carrier Q.ResidueField).toFun b) =
      (algebraMap B.carrier Q.ResidueField).toFun
        ((commAlgAutomorphismRingHom A B d.val).toFun b) :=
  nativeAlgebraResidueRingHom_coefficient B Q
    ((commAlgStabilizerResidueMorphism A B Q).hom'.toFun d) d.val.toRingHom
    (nativeAlgebraResidueMorphism_coefficientMap B (B.carrier ≃ₐ[A] B.carrier) Q
      (commAlgAutomorphism_comp_coefficient A B) d) b

end EtaleFundamentalGroups.Inertia
