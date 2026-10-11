/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_OModulePresheaf_flat_cochain_ofModules_of_locallyTrivial.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.AlgebraicGeometry.Morphisms.Separated
import SchemeTheory.Cohomology.Cech.OrderedAffineCoverCech
import AlgebraicCurves.Cohomology.Sheaves.OModulePresheafOfModules
import AlgebraicCurves.Geometry.Schemes.Scheme_TwoAffineOpenCover_flat_sections_of_flat
import AlgebraicCurves.Geometry.Projective.Scheme_Modules_projective_sections_of_locallyTrivial

/-!
# OModule Presheaf flat cochain of Modules of locally Trivial
-/

section ProofImplementation

namespace AlgebraicCurves.Cohomology.Sheaves.Proofs.FlatCochains

universe u

section cechflat
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

namespace CechFlatSol

theorem isAffineOpen_inter {V : Scheme.{u}} [V.IsSeparated] (K : V.OrderedAffineCover) :
    ∀ (n : ℕ) (s : K.Idx n), IsAffineOpen (K.inter s) := by
  intro n
  induction n with
  | zero =>
    intro s
    have : K.inter s = K.U (s.1 0) := by
      apply le_antisymm (K.inter_le s 0)
      exact le_iInf fun j => by rw [Subsingleton.elim (α := Fin 1) j 0]
    rw [this]
    exact K.isAffineOpen _
  | succ n ih =>
    intro s
    have : K.inter s = K.U (s.1 0) ⊓ K.inter (K.face s 0) := by
      apply le_antisymm
      · exact le_inf (K.inter_le s 0) (K.inter_le_inter_face s 0)
      · refine le_iInf fun j => ?_
        refine Fin.cases ?_ (fun k => ?_) j
        · exact inf_le_left
        · exact inf_le_right.trans (by
            have := K.inter_le (K.face s 0) k
            rw [K.face_val] at this
            simpa [Fin.succAbove_zero] using this)
    rw [this]
    exact (K.isAffineOpen _).inf (ih _)

end CechFlatSol

theorem _root_.AlgebraicGeometry.OModulePresheaf.flat_cochain_ofModules_of_locallyTrivial
    {R : Type u} [CommRing R] {V : Scheme.{u}} (π : V ⟶ Spec (.of R)) [Flat π] [IsSeparated π] (M
      : V.Modules)
    (htriv : ∀ x : V, ∃ (U : V.Opens), x ∈ U ∧
      Nonempty ((Scheme.Modules.pullback U.ι).obj M ≅ SheafOfModules.unit U.toScheme.ringCatSheaf))
    (K : V.OrderedAffineCover) (i : ℕ) :
    Module.Flat R ((OModulePresheaf.ofModules π M).cochain K i) := by
  classical
  have : V.IsSeparated := by
    constructor
    rw [show terminal.from V = π ≫ terminal.from _ from terminal.hom_ext _ _]
    infer_instance
  have : ∀ s : K.Idx i, Module.Flat R ((OModulePresheaf.ofModules π M).obj (K.inter s)) := fun s
    => by
    have haff : IsAffineOpen (K.inter s) := CechFlatSol.isAffineOpen_inter K i s
    let := Scheme.TwoAffineOpenCover.algebraOfHom π (K.inter s)
    have : Module.Flat R Γ(V, K.inter s) := Scheme.TwoAffineOpenCover.flat_sections_of_flat π _ haff
    have : Module.Projective Γ(V, K.inter s) ((OModulePresheaf.ofModules π M).obj (K.inter s)) :=
      Scheme.Modules.projective_sections_of_locallyTrivial M htriv ⟨K.inter s, haff⟩
    have : Module.Flat Γ(V, K.inter s) ((OModulePresheaf.ofModules π M).obj (K.inter s)) :=
      Module.Flat.of_projective
    exact Module.Flat.trans R Γ(V, K.inter s) ((OModulePresheaf.ofModules π M).obj (K.inter s))
  exact Module.Flat.of_linearEquiv
    (DirectSum.linearEquivFunOnFintype R (K.Idx i) fun s => (OModulePresheaf.ofModules π M).obj
      (K.inter s)).symm

end cechflat
end AlgebraicCurves.Cohomology.Sheaves.Proofs.FlatCochains
end ProofImplementation
