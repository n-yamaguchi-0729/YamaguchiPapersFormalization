/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Purity.PrincipalLocalizationComplex
import Mathlib.Algebra.Category.ModuleCat.Biproducts
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
import Mathlib.Algebra.Homology.Monoidal
import Mathlib.LinearAlgebra.DFinsupp

/-!
# The bounded flat Čech complex of a finite list

Tensoring the two-term principal localization complexes gives a complex
whose terms are flat and which ends in the degree given by the length of
the list. All signs, summands, and differentials are supplied by the
standard tensor product of homological complexes.
-/

noncomputable section

open CategoryTheory Limits MonoidalCategory
open scoped TensorProduct

namespace EtaleFundamentalGroups.Purity

universe u

variable {R : Type u} [CommRing R]

private instance cochainNatTensorSigns : (ComplexShape.up ℕ).TensorSigns where
  ε' := MonoidHom.mk' (fun n : ℕ => (-1 : ℤˣ) ^ n) (pow_add (-1 : ℤˣ))
  rel_add p q r hpq := by
    change p + 1 = q at hpq
    change (p + r) + 1 = q + r
    omega
  add_rel p q r hpq := by
    change p + 1 = q at hpq
    change (r + p) + 1 = r + q
    omega
  ε'_succ := by
    intro p q hpq
    change p + 1 = q at hpq
    subst q
    change (-1 : ℤˣ) ^ (p + 1) = -((-1 : ℤˣ) ^ p)
    rw [pow_succ, mul_neg, mul_one]

/-- The augmented Čech complex associated to a finite list of ring
elements, constructed by tensoring the actual principal localization maps. -/
def cechLocalizationComplex : List R → CochainComplex (ModuleCat.{u} R) ℕ
  | [] => HomologicalComplex.tensorUnit (ModuleCat.{u} R) (ComplexShape.up ℕ)
  | x :: xs => HomologicalComplex.tensorObj
      (principalLocalizationComplex x (ModuleCat.of R R)) (cechLocalizationComplex xs)

/-- A finite Čech complex has no terms above the length of its list. -/
theorem cechLocalizationComplex_isZero_X (xs : List R) (n : ℕ)
    (hn : xs.length < n) : IsZero ((cechLocalizationComplex xs).X n) := by
  induction xs generalizing n with
  | nil =>
    exact HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℕ)
      0 (𝟙_ (ModuleCat.{u} R)) n (by simpa only [List.length_nil] using hn.ne')
  | cons x xs ih =>
    apply (IsZero.iff_id_eq_zero _).mpr
    apply HomologicalComplex₂.total.hom_ext
    intro i j hij
    have hij' : i + j = n := hij
    have hz : IsZero ((principalLocalizationComplex x (ModuleCat.of R R)).X i ⊗
        (cechLocalizationComplex xs).X j) := by
      by_cases hi : 1 < i
      · exact (tensorRight ((cechLocalizationComplex xs).X j)).map_isZero
          (principalLocalizationComplex_isZero_X x (ModuleCat.of R R) i hi)
      · exact (tensorLeft ((principalLocalizationComplex x (ModuleCat.of R R)).X i)).map_isZero
          (ih j (by simp only [List.length_cons] at hn; omega))
    exact hz.eq_of_src _ _

private theorem flat_finite_coproduct {ι : Type} [Finite ι]
    (M : ι → ModuleCat.{u} R) (hM : ∀ i, Module.Flat R (M i)) :
    Module.Flat R (∐ M : ModuleCat.{u} R) := by
  let : Fintype ι := Fintype.ofFinite ι
  let : ∀ i, Module.Flat R (M i) := hM
  let e : (∐ M : ModuleCat.{u} R) ≅ ModuleCat.of R (∀ i, M i) :=
    (biproduct.isoCoproduct M).symm ≪≫ ModuleCat.biproductIsoPi M
  let : Module.Flat R (∀ i, M i) :=
    Module.Flat.of_linearEquiv (DFinsupp.linearEquivFunOnFintype (R := R) (M := fun i => M i)).symm
  exact Module.Flat.of_linearEquiv e.toLinearEquiv

/-- Every term of a finite Čech complex is flat over the original ring. -/
theorem cechLocalizationComplex_flat_X (xs : List R) (n : ℕ) :
    Module.Flat R ((cechLocalizationComplex xs).X n) := by
  induction xs generalizing n with
  | nil =>
    by_cases hn : n = 0
    · subst n
      exact Module.Flat.of_linearEquiv
        (HomologicalComplex.singleObjXIsoOfEq (ComplexShape.up ℕ)
          0 (𝟙_ (ModuleCat.{u} R)) 0 rfl).toLinearEquiv
    · have hz := cechLocalizationComplex_isZero_X ([] : List R) n (by
        simp only [List.length_nil]
        exact Nat.pos_of_ne_zero hn)
      let : Subsingleton ((cechLocalizationComplex ([] : List R)).X n) :=
        ModuleCat.subsingleton_of_isZero hz
      infer_instance
  | cons x xs ih =>
    let A := (principalLocalizationComplex x (ModuleCat.of R R)).X
    let B := (cechLocalizationComplex xs).X
    let J := {p : ℕ × ℕ // p.1 + p.2 = n}
    let f : J → Fin (n + 1) × Fin (n + 1) := fun p =>
      (⟨p.1.1, by have hp := p.2; omega⟩, ⟨p.1.2, by have hp := p.2; omega⟩)
    have hf : Function.Injective f := by
      intro p q hpq
      apply Subtype.ext
      exact Prod.ext (congrArg (fun z => z.1.val) hpq) (congrArg (fun z => z.2.val) hpq)
    let : Finite J := Finite.of_injective f hf
    change Module.Flat R (∐ (fun p : J => A p.1.1 ⊗ B p.1.2) : ModuleCat.{u} R)
    apply flat_finite_coproduct
    intro p
    let : Module.Flat R (A p.1.1) :=
      principalLocalizationComplex_flat_X x (ModuleCat.of R R) p.1.1
    let : Module.Flat R (B p.1.2) := ih p.1.2
    change Module.Flat R ((A p.1.1) ⊗[R] (B p.1.2))
    infer_instance

end EtaleFundamentalGroups.Purity
