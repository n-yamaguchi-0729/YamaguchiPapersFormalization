/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.RingTheory.FiniteLength
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.RingTheory.HopkinsLevitzki
import Mathlib.RingTheory.Ideal.Quotient.Basic
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.RingTheory.Noetherian.Basic

/-!
# Finite length of an Artinian socle

The submodule killed by the maximal ideal has its canonical residue-field
module structure.  An Artinian module over this field is finitely generated;
restriction of scalars then makes it finite over the original Noetherian ring.
-/

namespace EtaleFundamentalGroups.Purity

universe u v

variable {R : Type u} [CommRing R] [IsLocalRing R]

/-- An Artinian socle over a Noetherian local ring has finite length. -/
theorem isFiniteLength_torsionBySet_maximalIdeal_of_artinian
    [IsNoetherianRing R] (M : Type v) [AddCommGroup M] [Module R M]
    [IsArtinian R (Submodule.torsionBySet R M (IsLocalRing.maximalIdeal R))] :
    IsFiniteLength R (Submodule.torsionBySet R M (IsLocalRing.maximalIdeal R)) := by
  let S := Submodule.torsionBySet R M (IsLocalRing.maximalIdeal R)
  let : Field (R ⧸ IsLocalRing.maximalIdeal R) :=
    Ideal.Quotient.field (IsLocalRing.maximalIdeal R)
  let : IsArtinian (R ⧸ IsLocalRing.maximalIdeal R) S :=
    isArtinian_of_tower R (inferInstance : IsArtinian R S)
  let : IsNoetherian (R ⧸ IsLocalRing.maximalIdeal R) S :=
    IsSemiprimaryRing.isNoetherian_iff_isArtinian.mpr inferInstance
  let : Module.Finite R S :=
    Module.Finite.trans (R := R) (R ⧸ IsLocalRing.maximalIdeal R) S
  exact isFiniteLength_iff_isNoetherian_isArtinian.mpr ⟨inferInstance, inferInstance⟩

end EtaleFundamentalGroups.Purity
