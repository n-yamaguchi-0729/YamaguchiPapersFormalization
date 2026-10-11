/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Purity.InjectiveModuleEnvelope
import Mathlib.Algebra.Category.ModuleCat.EnoughInjectives
import Mathlib.Algebra.Category.ModuleCat.Injective
import Mathlib.Algebra.Module.Submodule.Range

/-!
# Existence of injective hulls for modules

Start with Mathlib's injective presentation of a module and replace the
ambient injective module by an injective essential extension of the image.
The resulting embedding has essential image and the same universe as the
original module.  The proof constructs the hull from the preceding maximal
essential-extension argument; no hull existence is assumed.
-/

noncomputable section

open CategoryTheory

namespace EtaleFundamentalGroups.Purity

universe u

variable {R : Type u} [Ring R]

/-- Every module admits an embedding with essential image into an
injective module in the same universe. -/
theorem exists_module_injective_hull (M : ModuleCat.{u} R) :
    ∃ (E : ModuleCat.{u} R) (i : M →ₗ[R] E),
      Function.Injective i ∧ IsEssentialSubmodule (LinearMap.range i) ∧
        Module.Injective R E := by
  let A : ModuleCat.{u} R := Injective.under M
  let j : M →ₗ[R] A := (Injective.ι M).hom
  have hj : Function.Injective j :=
    (ModuleCat.mono_iff_injective (Injective.ι M)).mp inferInstance
  let : Module.Injective R A :=
    (Module.injective_iff_injective_object R A).mpr
      (inferInstance : CategoryTheory.Injective A)
  let N : Submodule R A := LinearMap.range j
  obtain ⟨E, hNE, hNess, hEinj⟩ := exists_injective_essential_extension N
  let i : M →ₗ[R] E := j.codRestrict E (fun m => hNE (LinearMap.mem_range_self j m))
  have hi : Function.Injective i := by
    intro a b hab
    apply hj
    exact congrArg Subtype.val hab
  have hrange : LinearMap.range i = N.comap E.subtype := by
    ext e
    constructor
    · rintro ⟨m, rfl⟩
      exact LinearMap.mem_range_self j m
    · intro he
      obtain ⟨m, hm⟩ := he
      exact ⟨m, Subtype.ext hm⟩
  refine ⟨ModuleCat.of R E, i, hi, ?_, hEinj⟩
  rw [hrange]
  exact hNess

end EtaleFundamentalGroups.Purity

end
