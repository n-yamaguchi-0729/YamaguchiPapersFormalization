/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Purity.IdealPowerTorsionFunctor
import Nyll.EtaleFundamentalGroups.Purity.IdealPowerTorsionQuotientLifting
import Nyll.EtaleFundamentalGroups.Purity.InjectiveLinearDualHomology
import Nyll.EtaleFundamentalGroups.Purity.TensorLinearDualComplex
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
import Mathlib.Algebra.Homology.Additive
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.CategoryTheory.Linear.Yoneda

/-!
# Degree-zero tensor vanishing and dual torsion lifting

Vanishing of degree-zero homology after tensoring with ideal quotients
makes every map from those quotients into the degree-zero dual lift to
degree one. Cofinality then gives surjectivity of the differential on
ideal-power torsion. This is the base of the injective-chain argument.
-/

namespace EtaleFundamentalGroups.Purity

universe u

open CategoryTheory Limits Opposite MonoidalCategory

variable {R : Type u} [CommRing R]

private theorem surjective_chain_d_zero_of_isZero_homology
    (K : ChainComplex (ModuleCat.{u} R) ℕ) (h : IsZero (K.homology 0)) :
    Function.Surjective (K.d 1 0) := by
  have hex : (K.sc' 1 0 0).Exact :=
    (K.exactAt_iff' 1 0 0 (ChainComplex.prev ℕ 0) ChainComplex.next_nat_zero).mp
      ((K.exactAt_iff_isZero_homology 0).mpr h)
  intro z
  apply (K.sc' 1 0 0).moduleCat_exact_iff.mp hex z
  change K.d 0 0 z = 0
  rw [K.shape 0 0 (by decide)]
  rfl

/-- Tensor vanishing over a cofinal ideal family supplies the degree-zero
surjectivity of the power-torsion dual complex. -/
theorem idealPowerTorsion_dual_d_surjective_of_tensor_zero
    (I : Ideal R) (J : ℕ → Ideal R)
    (hJI : ∀ n : ℕ, ∃ m : ℕ, J m ≤ I ^ n)
    (hIJ : ∀ m : ℕ, ∃ n : ℕ, I ^ n ≤ J m)
    (E : ModuleCat.{u} R) [Module.Injective R E]
    (C : CochainComplex (ModuleCat.{u} R) ℕ)
    (hzero : ∀ m : ℕ, IsZero
      ((((tensorLeft (ModuleCat.of R (R ⧸ J m))).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj C).homology 0)) :
    Function.Surjective
      ((idealPowerTorsionFunctor I).map ((linearDualComplex E C).d 1 0)) := by
  apply idealPowerTorsionFunctor_map_surjective_of_quotient_lifting I J hJI hIJ
  intro m
  let M : ModuleCat.{u} R := ModuleCat.of R (R ⧸ J m)
  let T := ((tensorLeft M).mapHomologicalComplex (ComplexShape.up ℕ)).obj C
  let D := linearDualComplex E C
  let H := (((linearCoyoneda R (ModuleCat.{u} R)).obj (op M)).mapHomologicalComplex
    (ComplexShape.down ℕ)).obj D
  let : Subsingleton (T.homology 0) := ModuleCat.isZero_iff_subsingleton.mp (hzero m)
  have hzLinear : IsZero (ModuleCat.of R (T.homology 0 →ₗ[R] E)) :=
    ModuleCat.isZero_iff_subsingleton.mpr inferInstance
  have hzDual : IsZero ((linearDualComplex E T).homology 0) :=
    hzLinear.of_iso (injectiveLinearDualComplexHomologyIso E T 0)
  have hzH : IsZero (H.homology 0) := hzDual.of_iso
    ((HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (ComplexShape.down ℕ) 0).mapIso
      (tensorLinearDualComplexIso M E C))
  have hsurj := surjective_chain_d_zero_of_isZero_homology H hzH
  intro g
  obtain ⟨f, hf⟩ := hsurj (ModuleCat.ofHom g)
  refine ⟨f.hom, ?_⟩
  exact congrArg (fun v : M ⟶ D.X 0 => v.hom) hf

end EtaleFundamentalGroups.Purity
