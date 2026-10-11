/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.GenericTensor.FilteredColimit.AlgEquivDescent
import EtaleFundamentalGroups.GenericTensor.FilteredColimit.CoconeLeg
import EtaleFundamentalGroups.GenericTensor.FilteredColimit.IdempotentDescent
import EtaleFundamentalGroups.Inertia.InvariantBaseChange
import Mathlib.Algebra.Category.Ring.Under.Basic
import Mathlib.RingTheory.Idempotents
import Mathlib.RingTheory.TensorProduct.Maps


/-!
# Finite equivariant idempotent families at one actual filtered stage

First descend the complete orthogonal family by the existing finite-product
algebra construction. All of its group-equivariance equations then descend
in one further transition, using a polynomial algebra with finitely many
variables. The tensor factor carrying the action remains arbitrary.

The permutation representation of the finite index is explicit. The action
on every tensor ring is the prescribed `baseChangeAction`, and the output
retains each literal cocone image. This supplies the finite action data for
the actual étale-neighborhood step of Stacks tag 0BST.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace EtaleFundamentalGroups.Inertia

universe u w

variable {R : CommRingCat.{u}} {B : Type u} [CommRing B] [Algebra R B]
  {G : Type w} [Group G] [Finite G] [MulSemiringAction G B] [SMulCommClass G R B]

local instance coefficientTensorAction (A : Under R) : MulSemiringAction G (A ⊗[R] B) :=
  baseChangeAction R A B G

private theorem exists_equivariant_refinement
    {J : Type u} [SmallCategory J] [IsFiltered J]
    (F : J ⥤ Under R) (c : Cocone F) (hc : IsColimit c) (k : J)
    {ι : Type u} [Fintype ι] (σ : G →* Equiv.Perm ι)
    (e : ι → (F.obj k ⊗[R] B)) (he : CompleteOrthogonalIdempotents e)
    (hσ : ∀ (g : G) (a : ι),
      filteredTensorToColimitAlgHom c k (g • e a) =
        filteredTensorToColimitAlgHom c k (e (σ g a))) :
    ∃ (l : J) (eₗ : ι → (F.obj l ⊗[R] B)),
      CompleteOrthogonalIdempotents eₗ ∧
        (∀ (g : G) (a : ι), g • eₗ a = eₗ (σ g a)) ∧
        ∀ a, filteredTensorToColimitAlgHom c l (eₗ a) =
          filteredTensorToColimitAlgHom c k (e a) := by
  obtain ⟨l, u, hu⟩ := exists_tensorProduct_family_eq_stage_of_filteredColimit F c hc k
    (fun p : G × ι => p.1 • e p.2) (fun p : G × ι => e (σ p.1 p.2))
    (fun p => hσ p.1 p.2)
  refine ⟨l,
    (fun a => Algebra.TensorProduct.map (CommRingCat.toAlgHom (F.map u)) (AlgHom.id R B) (e a)),
    he.map (Algebra.TensorProduct.map
      (CommRingCat.toAlgHom (F.map u)) (AlgHom.id R B)).toRingHom, ?_, ?_⟩
  · intro g a
    rw [← baseChangeAction_map R (F.obj k) B G (CommRingCat.toAlgHom (F.map u))]
    exact hu (g, a)
  · intro a
    apply (Algebra.TensorProduct.comm R c.pt B).injective
    rw [← filteredBaseChangeCoconeLegAlgHom_comm,
      ← filteredBaseChangeCoconeLegAlgHom_comm, Algebra.TensorProduct.comm_comp_map_apply]
    exact AlgHom.congr_fun (filteredBaseChangeCoconeLegAlgHom_naturality c u)
      (Algebra.TensorProduct.comm R (F.obj k) B (e a))

/-- A finite complete equivariant family after tensor passage to a filtered
colimit descends to one stage with all orthogonality, completeness, group
equations, and literal cocone images preserved. No finite presentation of
the acted-on algebra over the base is assumed. -/
theorem exists_equivariant_completeOrthogonalIdempotents_stage_of_filteredColimit
    {J : Type u} [SmallCategory J] [IsFiltered J]
    (F : J ⥤ Under R) (c : Cocone F) (hc : IsColimit c)
    {ι : Type u} [Fintype ι] (σ : G →* Equiv.Perm ι)
    (e : ι → (c.pt ⊗[R] B)) (he : CompleteOrthogonalIdempotents e)
    (hσ : ∀ (g : G) (a : ι), g • e a = e (σ g a)) :
    ∃ (k : J) (eₖ : ι → (F.obj k ⊗[R] B)),
      CompleteOrthogonalIdempotents eₖ ∧
        (∀ (g : G) (a : ι), g • eₖ a = eₖ (σ g a)) ∧
        ∀ a, filteredTensorToColimitAlgHom c k (eₖ a) = e a := by
  obtain ⟨k, eₖ, heₖ, hmap⟩ :=
    exists_completeOrthogonalIdempotents_stage_of_filteredColimit F c hc e he
  have hσk : ∀ (g : G) (a : ι),
      filteredTensorToColimitAlgHom c k (g • eₖ a) =
        filteredTensorToColimitAlgHom c k (eₖ (σ g a)) := by
    intro g a
    change Algebra.TensorProduct.map (CommRingCat.toAlgHom (c.ι.app k)) (AlgHom.id R B)
        (g • eₖ a) = filteredTensorToColimitAlgHom c k (eₖ (σ g a))
    rw [baseChangeAction_map R (F.obj k) B G (CommRingCat.toAlgHom (c.ι.app k))]
    change g • filteredTensorToColimitAlgHom c k (eₖ a) =
      filteredTensorToColimitAlgHom c k (eₖ (σ g a))
    rw [hmap, hmap, hσ]
  obtain ⟨l, eₗ, heₗ, hσl, hl⟩ := exists_equivariant_refinement F c hc k σ eₖ heₖ hσk
  exact ⟨l, eₗ, heₗ, hσl, fun a => (hl a).trans (hmap a)⟩

end EtaleFundamentalGroups.Inertia
