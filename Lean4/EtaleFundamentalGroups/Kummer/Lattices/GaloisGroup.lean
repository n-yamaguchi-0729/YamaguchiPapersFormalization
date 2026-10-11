/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.Algebra.Algebra.Basic
import Mathlib.RingTheory.IsGaloisGroup.Defs
import EtaleFundamentalGroups.Kummer.Lattices.CharacterAction

/-!
# Galois group of a finite lattice cover

The character group of the finite quotient lattice acts diagonally on the
ambient lattice algebra.  This file packages that already constructed action
as a local `MulSemiringAction`, equips the lattice cover with its canonical
map-domain algebra structure, and proves that the character group is the
Galois group in the sense of `IsGaloisGroup`.

The action, algebra structure, and finiteness proof are named definitions, not
global instances.  This lets fraction-field consumers reuse exactly the same
action while keeping instance search local.
-/

namespace EtaleFundamentalGroups.Kummer

universe u v

noncomputable section

/-- The local semiring action induced by the diagonal character action. -/
@[reducible]
def latticeCharacterMulSemiringAction
    {k : Type u} {L : Type v} [CommRing k] [AddCommGroup L]
    (H : AddSubgroup L) :
    MulSemiringAction (Multiplicative (L ⧸ H) →* kˣ)
      (AddMonoidAlgebra k L) :=
  MulSemiringAction.compHom (AddMonoidAlgebra k L)
    (latticeCharacterAction H)

/-- The canonical algebra structure on a lattice cover, induced by the
map-domain homomorphism of the subgroup inclusion. -/
@[reducible]
def latticeMapDomainAlgebra
    {k : Type u} {L : Type v} [CommRing k] [AddCommGroup L]
    (H : AddSubgroup L) :
    Algebra (AddMonoidAlgebra k H) (AddMonoidAlgebra k L) :=
  (AddMonoidAlgebra.mapDomainAlgHom k k H.subtype).toRingHom.toAlgebra

/-- The map-domain algebra structure is faithful because the subgroup
inclusion, hence the induced map of lattice algebras, is injective. -/
theorem latticeMapDomainFaithfulSMul
    {k : Type u} {L : Type v} [CommRing k] [AddCommGroup L]
    (H : AddSubgroup L) :
    letI := latticeMapDomainAlgebra (k := k) H
    FaithfulSMul (AddMonoidAlgebra k H) (AddMonoidAlgebra k L) := by
  let := latticeMapDomainAlgebra (k := k) H
  rw [faithfulSMul_iff_algebraMap_injective]
  change Function.Injective (AddMonoidAlgebra.mapDomain H.subtype)
  exact AddMonoidAlgebra.mapDomain_injective H.subtype_injective

/-- Distinct quotient characters induce distinct diagonal automorphisms of
the ambient lattice algebra. -/
theorem latticeCharacterAction_injective
    {k : Type u} {L : Type v} [CommRing k] [AddCommGroup L]
    (H : AddSubgroup L) :
    Function.Injective (latticeCharacterAction (k := k) H) := by
  intro χ ψ hχψ
  ext l
  have hsingle := congrArg
    (fun f : AddMonoidAlgebra k L ≃ₐ[k] AddMonoidAlgebra k L =>
      (f (AddMonoidAlgebra.single l 1)).coeff l) hχψ
  simpa using hsingle

/-- The character group is finite.  This is kept as a named producer so it
can be installed only by fraction-field consumers of the Galois action. -/
theorem latticeCharacterGroupFinite
    {k : Type u} {L : Type v} [CommRing k] [AddCommGroup L]
    (H : AddSubgroup L) [Finite (L ⧸ H)]
    [HasEnoughRootsOfUnity k
      (Monoid.exponent (Multiplicative (L ⧸ H)))] :
    Finite (Multiplicative (L ⧸ H) →* kˣ) :=
  Finite.of_equiv (Multiplicative (L ⧸ H))
    (CommGroup.monoidHom_mulEquiv_of_hasEnoughRootsOfUnity
      (Multiplicative (L ⧸ H)) k).some.symm.toEquiv

/-- The diagonal quotient-character action makes the finite lattice cover a
Galois extension.  Both structures used by `IsGaloisGroup` are local and are
reproducible from the named action and map-domain algebra definitions above. -/
theorem latticeCharacter_isGaloisGroup
    {k : Type u} {L : Type v} [CommRing k] [IsDomain k]
    [AddCommGroup L]
    (H : AddSubgroup L) [Finite (L ⧸ H)]
    [HasEnoughRootsOfUnity k
      (Monoid.exponent (Multiplicative (L ⧸ H)))] :
    letI := latticeCharacterMulSemiringAction (k := k) H
    letI := latticeMapDomainAlgebra (k := k) H
    IsGaloisGroup (Multiplicative (L ⧸ H) →* kˣ)
      (AddMonoidAlgebra k H) (AddMonoidAlgebra k L) := by
  let := latticeCharacterMulSemiringAction (k := k) H
  let := latticeMapDomainAlgebra (k := k) H
  have hfixed :
      {x : AddMonoidAlgebra k L |
          ∀ χ : Multiplicative (L ⧸ H) →* kˣ,
            latticeCharacterAction H χ x = x} =
        ((AddMonoidAlgebra.mapDomainAlgHom k k H.subtype).range :
          Set (AddMonoidAlgebra k L)) :=
    fixedBy_latticeCharacterAction_eq_range (k := k) H
  refine
    { faithful := ?_
      commutes := ?_
      isInvariant := ?_ }
  · refine ⟨?_⟩
    intro χ ψ hχψ
    apply latticeCharacterAction_injective (k := k) H
    exact AlgEquiv.ext fun x => hχψ x
  · refine ⟨?_⟩
    intro χ a b
    have ha :
        latticeCharacterAction H χ
            (AddMonoidAlgebra.mapDomainAlgHom k k H.subtype a) =
          AddMonoidAlgebra.mapDomainAlgHom k k H.subtype a := by
      have haRange :
          AddMonoidAlgebra.mapDomainAlgHom k k H.subtype a ∈
            ((AddMonoidAlgebra.mapDomainAlgHom k k H.subtype).range :
              Set (AddMonoidAlgebra k L)) :=
        ⟨a, rfl⟩
      rw [← hfixed] at haRange
      exact haRange χ
    rw [Algebra.smul_def, Algebra.smul_def]
    change latticeCharacterAction H χ
        (AddMonoidAlgebra.mapDomainAlgHom k k H.subtype a * b) =
      AddMonoidAlgebra.mapDomainAlgHom k k H.subtype a *
        latticeCharacterAction H χ b
    rw [map_mul, ha]
  · refine ⟨?_⟩
    intro b hb
    have hbFixed :
        b ∈ {x : AddMonoidAlgebra k L |
          ∀ χ : Multiplicative (L ⧸ H) →* kˣ,
            latticeCharacterAction H χ x = x} := by
      intro χ
      exact hb χ
    rw [hfixed] at hbFixed
    obtain ⟨a, ha⟩ := hbFixed
    refine ⟨a, ?_⟩
    change AddMonoidAlgebra.mapDomainAlgHom k k H.subtype a = b
    exact ha

end

end EtaleFundamentalGroups.Kummer
