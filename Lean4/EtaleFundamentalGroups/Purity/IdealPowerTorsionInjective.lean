/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Purity.IdealPowerTorsionInjectivePresentation
import Mathlib.Algebra.Module.Injective
import Mathlib.Algebra.Module.Submodule.LinearMap
import Mathlib.Algebra.Module.Torsion.PrimaryComponent

/-!
# Injectivity of ideal-power torsion in an injective module

The primary component of an injective module embeds in an injective
power-torsion module.  Extending its inclusion into the original module
gives a map back whose image remains in the primary component.  This is
a retraction, so lifting maps into the injective power-torsion module and
composing with the retraction proves injectivity of the primary component.
-/

namespace EtaleFundamentalGroups.Purity

universe u

variable {R : Type u} [CommRing R] [IsNoetherianRing R]

/-- The ideal-primary component of an injective module over a Noetherian
ring is injective. -/
theorem moduleInjective_primaryComponent (I : Ideal R)
    (E : Type u) [AddCommGroup E] [Module R E] [Module.Injective R E] :
    Module.Injective R (Ideal.primaryComponent E I) := by
  let T : Submodule R E := Ideal.primaryComponent E I
  have hT : ∀ z : T, ∃ n : ℕ, ∀ a ∈ I ^ n, a • z = 0 := by
    intro z
    obtain ⟨n, hn⟩ := (Ideal.primaryComponent_mem (M := E) (I := I) (z : E)).mp z.property
    refine ⟨n, ?_⟩
    intro a ha
    apply Subtype.ext
    change a • (z : E) = (0 : E)
    exact (Submodule.mem_torsionBySet_iff (R := R) (M := E)
      ((I ^ n : Ideal R) : Set R) (z : E)).mp hn ⟨a, ha⟩
  obtain ⟨H, i, hi, hHinjective, hH, _hQ⟩ :=
    exists_idealPowerTorsion_injective_presentation I (ModuleCat.of R T) hT
  let : Module.Injective R H := hHinjective
  obtain ⟨g, hg⟩ :=
    Module.Injective.extension_property R E T H i hi T.subtype
  have hgmem (z : H) : g z ∈ T := by
    obtain ⟨n, hn⟩ := hH z
    apply (Ideal.primaryComponent_mem (M := E) (I := I) (g z)).mpr
    refine ⟨n, ?_⟩
    rw [Submodule.mem_torsionBySet_iff]
    intro a
    simpa only [map_smul, map_zero] using congrArg g (hn (a : R) a.property)
  let p : H →ₗ[R] T := g.codRestrict T hgmem
  have hpi (z : T) : p (i z) = z := by
    apply Subtype.ext
    exact LinearMap.congr_fun hg z
  refine ⟨?_⟩
  intro X Y _ _ _ _ f hf q
  obtain ⟨g', hg'⟩ :=
    Module.Injective.extension_property R H X Y f hf (i.comp q)
  refine ⟨p.comp g', ?_⟩
  intro x
  change p (g' (f x)) = q x
  calc
    p (g' (f x)) = p (i (q x)) := by
      apply congrArg p
      simpa only [LinearMap.comp_apply] using LinearMap.congr_fun hg' x
    _ = q x := hpi (q x)

end EtaleFundamentalGroups.Purity
