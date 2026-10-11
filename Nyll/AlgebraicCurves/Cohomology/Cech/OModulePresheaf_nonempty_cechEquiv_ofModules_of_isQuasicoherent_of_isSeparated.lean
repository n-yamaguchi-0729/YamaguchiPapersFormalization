/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_OModulePresheaf_nonempty_cechEquiv_ofModules_of_isQuasicoherent_of_isSeparated.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.SchemeTheory.Cohomology.Cech.OrderedAffineCoverCech
import Nyll.AlgebraicCurves.Cohomology.Sheaves.OModulePresheafOfModules
import Nyll.AlgebraicCurves.Cohomology.Cech.OModulePresheaf_nonempty_cechEquiv_ofModules_of_orderEmbedding_of_forall_lt
import Nyll.AlgebraicCurves.Cohomology.Cech.OModulePresheaf_nonempty_cechEquiv_of_orderIso
import Nyll.AlgebraicCurves.Cohomology.Cech.OModulePresheaf_nonempty_cechEquiv_of_orderIso_orderDual

/-!
# OModule Presheaf nonempty cech Equiv of Modules of is Quasicoherent of is Separated
-/

section ProofImplementation

namespace AlgebraicCurves.Cohomology.Cech.Proofs.SheafCechEquivOfModules
attribute [-instance] AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx
attribute [-simp] AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq
  AlgebraicGeometry.OModulePresheaf.Hom.id_app
  AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply
  AlgebraicGeometry.OModulePresheaf.AffHom.comp_app
  AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec
  AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe
  AlgebraicGeometry.OModulePresheaf.AffHom.id_app
  AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec
  AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app
  AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec
  AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec
  AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq
  AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq
  AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply
  AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq
  AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq
  AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry OrderDual

namespace P2mCoverIndep

variable {R : Type u} [CommRing R] {V : Scheme.{u}}

namespace Cover

variable (W : V.OrderedAffineCover)

/-- The ordered subcover selected by a predicate, with its coverage equality. -/
def sub (p : W.ι → Prop) (hcov : ⨆ j : {j // p j}, W.U j.1 = ⊤) : V.OrderedAffineCover := by
  classical
  exact
    { ι := {j // p j}
      U j := W.U j.1
      isAffineOpen j := W.isAffineOpen j.1
      iSup_eq_top := hcov }

theorem sub_U (p : W.ι → Prop) (hcov : ⨆ j : {j // p j}, W.U j.1 = ⊤) (j : {j // p j}) :
    (sub W p hcov).U j = W.U j.1 := rfl

/-- The same affine charts indexed in the reverse order. -/
def dual : V.OrderedAffineCover where
  ι := (W.ι)ᵒᵈ
  U j := W.U (ofDual j)
  isAffineOpen j := W.isAffineOpen (ofDual j)
  iSup_eq_top := by
    rw [← W.iSup_eq_top]
    exact le_antisymm (iSup_le fun j => le_iSup W.U (ofDual j)) (iSup_le fun i => le_iSup (fun j =>
      W.U (ofDual j)) (toDual i))

theorem dual_U (j : (W.ι)ᵒᵈ) : (dual W).U j = W.U (ofDual j) := rfl

end Cover

/-- The ordered affine cover formed by placing the charts of the first cover before those of the
second. -/
def sumCover (K K' : V.OrderedAffineCover) : V.OrderedAffineCover where
  ι := K.ι ⊕ₗ K'.ι
  U j := Sum.elim K.U K'.U (ofLex j)
  isAffineOpen j := by
    rcases h : ofLex j with i | i'
    · exact K.isAffineOpen i
    · exact K'.isAffineOpen i'
  iSup_eq_top := by
    apply le_antisymm le_top
    rw [← K.iSup_eq_top]
    exact iSup_le fun i => le_iSup (fun j : K.ι ⊕ₗ K'.ι => Sum.elim K.U K'.U (ofLex j)) (toLex
      (Sum.inl i))

theorem sumCover_U_inl (K K' : V.OrderedAffineCover) (i : K.ι) :
    (sumCover K K').U (toLex (Sum.inl i)) = K.U i := rfl

theorem sumCover_U_inr (K K' : V.OrderedAffineCover) (i' : K'.ι) :
    (sumCover K K').U (toLex (Sum.inr i')) = K'.U i' := rfl

section Induction

variable (π : V ⟶ Spec (.of R)) [IsSeparated π] (M : V.Modules)
  (hq : (OModulePresheaf.ofModules π M).IsQuasicoherent)

/-- Linear equivalences between degree zero and all positive Cech cohomology groups of two
covers. -/
def Same (K W : V.OrderedAffineCover) : Prop :=
  Nonempty ((OModulePresheaf.ofModules π M).H0 K ≃ₗ[R] (OModulePresheaf.ofModules π M).H0 W) ∧
    ∀ i : ℕ, Nonempty ((OModulePresheaf.ofModules π M).HSucc K i ≃ₗ[R] (OModulePresheaf.ofModules π
      M).HSucc W i)

omit [IsSeparated π] in
theorem Same.symm {K W : V.OrderedAffineCover} (h : Same π M K W) : Same π M W K :=
  ⟨⟨h.1.some.symm⟩, fun i => ⟨(h.2 i).some.symm⟩⟩

omit [IsSeparated π] in
theorem Same.trans {K W W' : V.OrderedAffineCover} (h : Same π M K W) (h' : Same π M W W') : Same π
  M K W' :=
  ⟨⟨h.1.some.trans h'.1.some⟩, fun i => ⟨(h.2 i).some.trans (h'.2 i).some⟩⟩

variable {π M}
variable (K W : V.OrderedAffineCover) (e : K.ι ↪o W.ι) (hU : ∀ i, W.U (e i) = K.U i)

/-- The indices from the embedded cover together with the finite set of additional charts. -/
def pT (T : Finset W.ι) (j : W.ι) : Prop := j ∈ Set.range e ∨ j ∈ T

include hU in
theorem cov_pT (T : Finset W.ι) : ⨆ j : {j // pT K W e T j}, W.U j.1 = ⊤ := by
  apply le_antisymm le_top
  rw [← K.iSup_eq_top]
  exact iSup_le fun i => by
    rw [← hU i]
    exact le_iSup (fun j : {j // pT K W e T j} => W.U j.1) ⟨e i, Or.inl ⟨i, rfl⟩⟩

/-- The ordered subcover consisting of the embedded cover and the selected additional charts. -/
def WT (T : Finset W.ι) : V.OrderedAffineCover := Cover.sub W (pT K W e T) (cov_pT K W e hU T)

omit [IsSeparated π] in
theorem same_WT_empty : Same π M K (WT K W e hU ∅) := by
  let f : K.ι → (WT K W e hU ∅).ι := fun i => ⟨e i, Or.inl ⟨i, rfl⟩⟩
  have hf : StrictMono f := fun a b h => e.strictMono h
  have hsurj : Function.Surjective f := by
    rintro ⟨j, hj⟩
    rcases hj with ⟨i, rfl⟩ | h
    · exact ⟨i, rfl⟩
    · exact absurd h (Finset.notMem_empty j)
  let eo : K.ι ≃o (WT K W e hU ∅).ι := hf.orderIsoOfSurjective f hsurj
  exact OModulePresheaf.nonempty_cechEquiv_of_orderIso (OModulePresheaf.ofModules π M) K (WT K W e
    hU ∅) eo
    (fun i => hU i)

include hq in
theorem same_WT_insert (T : Finset W.ι) (a : W.ι) (hmax : ∀ x ∈ T, x < a) (htop : ∀ i, e i < a) :
    Same π M (WT K W e hU (insert a T)) (WT K W e hU T) := by
  let incl : (WT K W e hU T).ι → (WT K W e hU (insert a T)).ι := fun j => ⟨j.1, j.2.imp id
    (Finset.mem_insert_of_mem)⟩
  let ε : (WT K W e hU T).ι ↪o (WT K W e hU (insert a T)).ι :=
    OrderEmbedding.ofMapLEIff incl (fun _ _ => Iff.rfl)
  refine OModulePresheaf.nonempty_cechEquiv_ofModules_of_orderEmbedding_of_forall_lt π M hq
    (WT K W e hU T) (WT K W e hU (insert a T)) ε (fun _ => rfl) ⟨a, Or.inr (Finset.mem_insert_self
      a T)⟩ ?_ ?_
  · rintro ⟨j, hj⟩
    by_cases hja : j = a
    · left; exact Subtype.ext hja
    · right
      have hj' : pT K W e T j := hj.imp id (fun h => (Finset.mem_insert.mp h).resolve_left hja)
      exact ⟨⟨j, hj'⟩, rfl⟩
  · rintro ⟨j, hj⟩
    change j < a
    rcases hj with ⟨i, rfl⟩ | h
    · exact htop i
    · exact hmax j h

include hq hU in
theorem same_of_forall_lt (hext : ∀ j, j ∉ Set.range e → ∀ i, e i < j) : Same π M K W := by
  classical
  let X : Finset W.ι := Finset.univ.filter fun j => j ∉ Set.range e
  have key : ∀ T : Finset W.ι, T ⊆ X → Same π M K (WT K W e hU T) := by
    intro T
    induction T using Finset.induction_on_max with
    | empty => exact fun _ => same_WT_empty K W e hU
    | insert a s hmax ih =>
      intro hsub
      have ha : a ∉ Set.range e := (Finset.mem_filter.mp (hsub (Finset.mem_insert_self a s))).2
      have hs : s ⊆ X := (Finset.subset_insert a s).trans hsub
      exact (ih hs).trans π M ((same_WT_insert hq K W e hU s a hmax (hext a ha)).symm π M)
  have hall : ∀ j : W.ι, pT K W e X j := fun j => by
    by_cases h : j ∈ Set.range e
    · exact Or.inl h
    · exact Or.inr (Finset.mem_filter.mpr ⟨Finset.mem_univ j, h⟩)
  let g : (WT K W e hU X).ι → W.ι := Subtype.val
  have hg : StrictMono g := Subtype.strictMono_coe _
  have hgs : Function.Surjective g := fun j => ⟨⟨j, hall j⟩, rfl⟩
  let eo : (WT K W e hU X).ι ≃o W.ι := hg.orderIsoOfSurjective g hgs
  have hlast : Same π M (WT K W e hU X) W :=
    OModulePresheaf.nonempty_cechEquiv_of_orderIso (OModulePresheaf.ofModules π M) (WT K W e hU X)
      W eo
      (fun j => rfl)
  exact (key X subset_rfl).trans π M hlast

end Induction

section Main

variable (π : V ⟶ Spec (.of R)) [IsSeparated π] (M : V.Modules)
  (hq : (OModulePresheaf.ofModules π M).IsQuasicoherent) (K K' : V.OrderedAffineCover)

include hq in
theorem same_left : Same π M K (sumCover K K') := by
  refine same_of_forall_lt hq K (sumCover K K')
    (OrderEmbedding.ofStrictMono (toLex ∘ Sum.inl) Sum.Lex.inl_strictMono) (fun i => rfl) ?_
  intro j hj i
  obtain ⟨x, rfl⟩ := toLex.surjective j
  rcases x with a | b
  · exact absurd ⟨a, rfl⟩ hj
  · exact Sum.Lex.inl_lt_inr i b

include hq in
theorem same_right : Same π M K' (sumCover K K') := by
  have h1 : Same π M K' (Cover.dual K') :=
    OModulePresheaf.nonempty_cechEquiv_of_orderIso_orderDual (OModulePresheaf.ofModules π M) K'
      (Cover.dual K')
      (OrderIso.dualDual K'.ι) (fun i => rfl)
  have h2 : Same π M (sumCover K K') (Cover.dual (sumCover K K')) :=
    OModulePresheaf.nonempty_cechEquiv_of_orderIso_orderDual (OModulePresheaf.ofModules π M)
      (sumCover K K')
      (Cover.dual (sumCover K K')) (OrderIso.dualDual (sumCover K K').ι) (fun i => rfl)
  let f : (K'.ι)ᵒᵈ → (K.ι ⊕ₗ K'.ι)ᵒᵈ := fun j => toDual (toLex (Sum.inr (ofDual j)))
  have hf : StrictMono f := fun j₁ j₂ h =>
    toDual_lt_toDual.mpr (Sum.Lex.inr_strictMono (ofDual_lt_ofDual.mpr h))
  let e : (Cover.dual K').ι ↪o (Cover.dual (sumCover K K')).ι := OrderEmbedding.ofStrictMono f hf
  have h3 : Same π M (Cover.dual K') (Cover.dual (sumCover K K')) := by
    refine same_of_forall_lt hq (Cover.dual K') (Cover.dual (sumCover K K')) e (fun i => rfl) ?_
    intro j hj i
    obtain ⟨x, hx⟩ := toLex.surjective (ofDual j)
    have hj' : j = toDual (toLex x) :=
      (congrArg (toDual : (K.ι ⊕ₗ K'.ι) → (K.ι ⊕ₗ K'.ι)ᵒᵈ) hx).symm
    rcases x with a | b
    · have h : f i < toDual (toLex (Sum.inl a)) :=
        toDual_lt_toDual.mpr (Sum.Lex.inl_lt_inr (α := K.ι) (β := K'.ι) a (ofDual i))
      rw [hj']
      exact h
    · exact absurd ⟨toDual b, by rw [hj']; rfl⟩ hj
  exact (h1.trans π M h3).trans π M (h2.symm π M)

include hq in
theorem main :
    Nonempty ((OModulePresheaf.ofModules π M).H0 K ≃ₗ[R] (OModulePresheaf.ofModules π M).H0 K') ∧
      ∀ i : ℕ, Nonempty ((OModulePresheaf.ofModules π M).HSucc K i ≃ₗ[R]
        (OModulePresheaf.ofModules π M).HSucc K' i) :=
  (same_left π M hq K K').trans π M ((same_right π M hq K K').symm π M)

end Main

end P2mCoverIndep

end
end AlgebraicCurves.Cohomology.Cech.Proofs.SheafCechEquivOfModules

section PublicStatement

universe u
open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.OrderDual
open _root_.AlgebraicCurves.Cohomology.Cech.Proofs.SheafCechEquivOfModules

namespace AlgebraicGeometry.OModulePresheaf

theorem nonempty_cechEquiv_ofModules_of_isQuasicoherent_of_isSeparated
    {R : Type u} [CommRing R] {V : Scheme.{u}} (π : V ⟶ Spec (.of R)) [IsSeparated π]
    (M : V.Modules) (hq : (OModulePresheaf.ofModules π M).IsQuasicoherent)
    (K K' : V.OrderedAffineCover) :
    Nonempty ((OModulePresheaf.ofModules π M).H0 K ≃ₗ[R] (OModulePresheaf.ofModules π M).H0 K') ∧
      ∀ i : ℕ, Nonempty ((OModulePresheaf.ofModules π M).HSucc K i ≃ₗ[R]
        (OModulePresheaf.ofModules π M).HSucc K' i) := by
  classical
  exact   P2mCoverIndep.main π M hq K K'

end AlgebraicGeometry.OModulePresheaf

end PublicStatement
end ProofImplementation
