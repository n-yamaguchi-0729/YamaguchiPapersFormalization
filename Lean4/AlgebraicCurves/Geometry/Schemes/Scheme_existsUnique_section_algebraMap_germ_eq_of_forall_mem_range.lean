/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_Scheme_existsUnique_section_algebraMap_germ_eq_of_forall_mem_range.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.Algebra.Algebra.Defs
import Mathlib.Algebra.Category.Ring.Basic
import Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Algebra.Group.Monoid
import Mathlib.Algebra.Group.Units.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Subring.Basic
import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.Tactic.Choose
import Mathlib.Tactic.Push
import Mathlib.Topology.Inseparable
import Mathlib.Topology.Sets.Opens
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
import Mathlib.Topology.Sheaves.Stalks
import Mathlib.Topology.Sober

/-!
# Scheme exists Unique section algebra Map germ eq of forall mem range
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Schemes.Proofs
namespace Scheme_existsUnique_section_algebraMap_germ_eq_of_forall_mem_range

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

namespace KLiftAux

variable {X : Scheme.{u}} [IsIntegral X]

theorem algebraMap_germ (W : X.Opens) (t : Γ(X, W)) (x : X) (hx : x ∈ W) :
    algebraMap (X.presheaf.stalk x) X.functionField (X.presheaf.germ W x hx t) =
      X.presheaf.germ W (genericPoint X)
        (((genericPoint_spec X).specializes (Set.mem_univ x)).mem_open W.isOpen hx) t := by
  change (X.presheaf.germ W x hx ≫ X.presheaf.stalkSpecializes
      ((genericPoint_spec X).specializes (Set.mem_univ x))) t = _
  rw [TopCat.Presheaf.germ_stalkSpecializes]

theorem algebraMap_germ_eq (W : X.Opens) (t : Γ(X, W)) (x y : X) (hx : x ∈ W) (hy : y ∈ W) :
    algebraMap (X.presheaf.stalk x) X.functionField (X.presheaf.germ W x hx t) =
      algebraMap (X.presheaf.stalk y) X.functionField (X.presheaf.germ W y hy t) := by
  rw [algebraMap_germ, algebraMap_germ]

theorem section_eq_of_algebraMap_germ_eq (W : X.Opens) (t t' : Γ(X, W)) (x : X) (hx : x ∈ W)
    (h : algebraMap (X.presheaf.stalk x) X.functionField (X.presheaf.germ W x hx t) =
      algebraMap (X.presheaf.stalk x) X.functionField (X.presheaf.germ W x hx t')) : t = t' := by
  let _ : Nonempty W := ⟨⟨x, hx⟩⟩
  apply X.germToFunctionField_injective W
  rw [algebraMap_germ, algebraMap_germ] at h
  exact h
omit [IsIntegral X] in
theorem section_eq_of_isEmpty (W : X.Opens) (hW : ∀ x : X, x ∉ W) (t t' : Γ(X, W)) : t = t' :=
  X.sheaf.eq_of_locally_eq' (fun _ : PEmpty.{u + 1} => (⊥ : X.Opens)) W (fun i => i.elim)
    (fun x hx => (hW x hx).elim) t t' (fun i => i.elim)

theorem exists_section_algebraMap_germ_eq (W : X.Opens) (s : X.functionField)
    (hs : ∀ x ∈ W, s ∈ (algebraMap (X.presheaf.stalk x) X.functionField).range) :
    ∃ u : Γ(X, W), ∀ (x : X) (hx : x ∈ W),
      algebraMap (X.presheaf.stalk x) X.functionField (X.presheaf.germ W x hx u) = s := by
  classical
  have loc : ∀ x : W, ∃ (V : X.Opens) (hxV : (x : X) ∈ V) (_ : V ≤ W) (t : Γ(X, V)),
      algebraMap (X.presheaf.stalk (x : X)) X.functionField (X.presheaf.germ V x hxV t) = s := by
    intro x
    obtain ⟨sx, hsx⟩ := hs x.1 x.2
    obtain ⟨V, hxV, t, ht⟩ := X.presheaf.exists_germ_eq sx
    have hxVW : (x : X) ∈ V ⊓ W := ⟨hxV, x.2⟩
    let t' : Γ(X, V) := t
    have ht' : X.presheaf.germ V (x : X) hxV t' = sx := ht
    refine ⟨V ⊓ W, hxVW, inf_le_right, X.presheaf.map (homOfLE inf_le_left).op t', ?_⟩
    have hg : X.presheaf.map (homOfLE (inf_le_left : V ⊓ W ≤ V)).op ≫
        X.presheaf.germ (V ⊓ W) (x : X) hxVW = X.presheaf.germ V (x : X) hxV :=
      X.presheaf.germ_res (homOfLE (inf_le_left : V ⊓ W ≤ V)) (x : X) hxVW
    exact (congrArg (algebraMap (X.presheaf.stalk (x : X)) X.functionField)
      ((congrArg (fun k : Γ(X, V) ⟶ X.presheaf.stalk (x : X) => k t') hg).trans ht')).trans hsx
  choose V hxV hVW t ht using loc
  have hcompat : TopCat.Presheaf.IsCompatible X.presheaf V t := by
    intro i j
    by_cases hne : ∃ z : X, z ∈ V i ⊓ V j
    · obtain ⟨z, hz⟩ := hne
      apply section_eq_of_algebraMap_germ_eq (V i ⊓ V j) _ _ z hz
      rw [TopCat.Presheaf.germ_res_apply, TopCat.Presheaf.germ_res_apply,
        algebraMap_germ_eq (V i) (t i) z i hz.1 (hxV i), ht i,
        algebraMap_germ_eq (V j) (t j) z j hz.2 (hxV j), ht j]
    · push Not at hne
      exact section_eq_of_isEmpty _ (fun z hz => hne z hz) _ _
  obtain ⟨uW, huW, -⟩ := X.sheaf.existsUnique_gluing' V W (fun i => homOfLE (hVW i))
    (fun x hx => Opens.mem_iSup.mpr ⟨⟨x, hx⟩, hxV ⟨x, hx⟩⟩) t hcompat
  let u : Γ(X, W) := uW
  have hu (i : W) : X.presheaf.map (homOfLE (hVW i)).op u = t i := huW i
  refine ⟨u, fun x hx => ?_⟩
  let i : W := ⟨x, hx⟩
  have hg : X.presheaf.map (homOfLE (hVW i)).op ≫ X.presheaf.germ (V i) x (hxV i) =
      X.presheaf.germ W x hx := X.presheaf.germ_res (homOfLE (hVW i)) x (hxV i)
  have hlocal : algebraMap (X.presheaf.stalk x) X.functionField
      (X.presheaf.germ (V i) x (hxV i) (X.presheaf.map (homOfLE (hVW i)).op u)) = s :=
    (congrArg (fun z : Γ(X, V i) => algebraMap (X.presheaf.stalk x) X.functionField
      (X.presheaf.germ (V i) x (hxV i) z)) (hu i)).trans (ht i)
  exact (congrArg (algebraMap (X.presheaf.stalk x) X.functionField)
    (congrArg (fun k : Γ(X, W) ⟶ X.presheaf.stalk x => k u) hg)).symm.trans hlocal

theorem exists_unit_section_algebraMap_germ_eq (W : X.Opens) (s : X.functionField) (hs0 : s ≠ 0)
    (hs : ∀ x ∈ W, s ∈ (algebraMap (X.presheaf.stalk x) X.functionField).range)
    (hs' : ∀ x ∈ W, s⁻¹ ∈ (algebraMap (X.presheaf.stalk x) X.functionField).range) :
    ∃ u : Γ(X, W), (∀ (x : X) (hx : x ∈ W),
      algebraMap (X.presheaf.stalk x) X.functionField (X.presheaf.germ W x hx u) = s) ∧ IsUnit u :=
        by
  obtain ⟨u, hu⟩ := exists_section_algebraMap_germ_eq W s hs
  obtain ⟨u', hu'⟩ := exists_section_algebraMap_germ_eq W s⁻¹ hs'
  refine ⟨u, hu, ?_⟩
  by_cases hne : ∃ x : X, x ∈ W
  · obtain ⟨x, hx⟩ := hne
    refine IsUnit.of_mul_eq_one u' ?_
    apply section_eq_of_algebraMap_germ_eq W _ _ x hx
    rw [map_mul, map_mul, hu x hx, hu' x hx, map_one, map_one, mul_inv_cancel₀ hs0]
  · push Not at hne
    rw [section_eq_of_isEmpty W hne u 1]
    exact isUnit_one

end KLiftAux

theorem _root_.AlgebraicGeometry.Scheme.existsUnique_section_algebraMap_germ_eq_of_forall_mem_range
    {X : Scheme.{u}} [IsIntegral X] (W : X.Opens) (s : X.functionField)
    (hs : ∀ x ∈ W, s ∈ (algebraMap (X.presheaf.stalk x) X.functionField).range) :
    ∃! u : Γ(X, W), ∀ (x : X) (hx : x ∈ W),
      algebraMap (X.presheaf.stalk x) X.functionField (X.presheaf.germ W x hx u) = s := by
  obtain ⟨u, hu⟩ := KLiftAux.exists_section_algebraMap_germ_eq W s hs
  refine ⟨u, hu, fun u' hu' => ?_⟩
  by_cases hne : ∃ x : X, x ∈ W
  · obtain ⟨x, hx⟩ := hne
    exact KLiftAux.section_eq_of_algebraMap_germ_eq W u' u x hx (by rw [hu x hx, hu' x hx])
  · push Not at hne
    exact KLiftAux.section_eq_of_isEmpty W hne u' u
end Scheme_existsUnique_section_algebraMap_germ_eq_of_forall_mem_range
end AlgebraicCurves.Geometry.Schemes.Proofs
end ProofImplementation
