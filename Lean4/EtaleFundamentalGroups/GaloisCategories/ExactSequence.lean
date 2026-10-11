/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/


import EtaleFundamentalGroups.ContinuousActions.ClosedNormalClosure
import EtaleFundamentalGroups.ContinuousActions.RestrictionEssentialImage
import EtaleFundamentalGroups.GaloisCategories.Surjectivity
import EtaleFundamentalGroups.GaloisCategories.TrivialComposite
import Mathlib.Data.List.TFAE

/-!
# Exact sequences of Galois categories

For two composable functors of Galois categories, exactness of the induced
sequence of profinite automorphism groups is equivalent to the two standard
categorical essential-image criteria.
-/

universe u₁ u₂ v₁ v₂ x₁ x₂ w

noncomputable section

open CategoryTheory Limits
open scoped FintypeCatDiscrete

namespace CategoryTheory.PreGaloisCategory

variable {C : Type u₁} [Category.{u₂} C] [GaloisCategory C]
variable {C' : Type v₁} [Category.{v₂} C'] [GaloisCategory C']
variable {C'' : Type x₁} [Category.{x₂} C''] [GaloisCategory C'']
variable {F : C ⥤ FintypeCat.{w}} [FiberFunctor F]
variable {F' : C' ⥤ FintypeCat.{w}} [FiberFunctor F']
variable {F'' : C'' ⥤ FintypeCat.{w}} [FiberFunctor F'']

private theorem essImage_of_res_essImage
    (H : C ⥤ C') (t : H ⋙ F' ≅ F) (X' : C')
    (ha : (ContAction.res FintypeCat (autHomOfCompIso H t)).essImage
      ((functorToContAction F').obj X')) :
    H.essImage X' := by
  let E := functorToContAction F
  let E' := functorToContAction F'
  let R := ContAction.res FintypeCat (autHomOfCompIso H t)
  obtain ⟨Y, ⟨eY⟩⟩ := ha
  let X : C := E.objPreimage Y
  let eX : E.obj X ≅ Y := E.objObjPreimageIso Y
  let s : E'.obj (H.obj X) ≅ R.obj (E.obj X) :=
    (functorToContActionCompIso H t).app X
  let e : E'.obj (H.obj X) ≅ E'.obj X' :=
    s ≪≫ R.mapIso eX ≪≫ eY
  exact
    ⟨X, ⟨(Functor.FullyFaithful.ofFullyFaithful E').preimageIso e⟩⟩

private theorem res_essImage_of_essImage
    (H : C ⥤ C') (t : H ⋙ F' ≅ F) (X' : C')
    (hX' : H.essImage X') :
    (ContAction.res FintypeCat (autHomOfCompIso H t)).essImage
      ((functorToContAction F').obj X') := by
  let E := functorToContAction F
  let E' := functorToContAction F'
  obtain ⟨X, ⟨e⟩⟩ := hX'
  exact
    ⟨E.obj X,
      ⟨((functorToContActionCompIso H t).app X).symm ≪≫
        E'.mapIso e⟩⟩

private theorem source_fixed_iff_induced_fixed
    (H' : C' ⥤ C'') (t' : H' ⋙ F'' ≅ F') (X' : C') :
    (∀ (a : Aut F'') (x : F''.obj (H'.obj X')), a • x = x) ↔
      ∀ (a : Aut F'') (y : F'.obj X'),
        autHomOfCompIso H' t' a • y = y := by
  let s := (functorToContActionCompIso H' t').app X'
  constructor
  · intro hfixed a y
    let x : F''.obj (H'.obj X') := (t'.app X').inv y
    have heq := ConcreteCategory.congr_hom (s.hom.hom.comm a) x
    change (t'.app X').hom (a • x) =
      autHomOfCompIso H' t' a • (t'.app X').hom x at heq
    rw [hfixed a x] at heq
    have hxy : (t'.app X').hom x = y := by
      dsimp [x]
      exact FintypeCat.inv_hom_id_apply (t'.app X') y
    rw [hxy] at heq
    exact heq.symm
  · intro hfixed a x
    apply
      (ConcreteCategory.bijective_of_isIso
        (t'.app X').hom).injective
    have heq := ConcreteCategory.congr_hom (s.hom.hom.comm a) x
    change (t'.app X').hom (a • x) =
      autHomOfCompIso H' t' a • (t'.app X').hom x at heq
    rw [hfixed a ((t'.app X').hom x)] at heq
    exact heq

private theorem kernel_fixed_functor_obj
    (H : C ⥤ C') (t : H ⋙ F' ≅ F) (X : C)
    (a : Aut F') (ha : autHomOfCompIso H t a = 1)
    (x : F'.obj (H.obj X)) :
    a • x = x := by
  let s := (functorToContActionCompIso H t).app X
  apply
    (ConcreteCategory.bijective_of_isIso
      (t.app X).hom).injective
  have heq := ConcreteCategory.congr_hom (s.hom.hom.comm a) x
  change (t.app X).hom (a • x) =
    autHomOfCompIso H t a • (t.app X).hom x at heq
  rw [ha, one_smul] at heq
  exact heq

private theorem kernel_fixed_of_epi
    (H : C ⥤ C') (t : H ⋙ F' ≅ F) (X : C) (X' : C')
    (q : H.obj X ⟶ X') [Epi q]
    (a : Aut F') (ha : autHomOfCompIso H t a = 1)
    (y : F'.obj X') :
    a • y = y := by
  obtain ⟨x, hx⟩ := surjective_on_fiber_of_epi F' q y
  calc
    a • y = a • F'.map q x := congrArg (a • ·) hx.symm
    _ = F'.map q (a • x) := mulAction_naturality F' a q x
    _ = F'.map q x :=
      congrArg (F'.map q) (kernel_fixed_functor_obj H t X a ha x)
    _ = y := hx

private theorem essImage_of_epi
    (H : C ⥤ C') (t : H ⋙ F' ≅ F)
    (hs : Function.Surjective (autHomOfCompIso H t))
    (X : C) (X' : C') (q : H.obj X ⟶ X') [Epi q] :
    H.essImage X' := by
  apply essImage_of_res_essImage H t X'
  apply
    (ContAction.essImage_res_iff_ker_le_ker_ρAut
      (autHomOfCompIso H t) hs
      ((functorToContAction F').obj X')).2
  intro a ha
  apply MonoidHom.mem_ker.mpr
  apply Iso.ext
  apply FintypeCat.hom_ext
  intro y
  change a • y = y
  exact
    kernel_fixed_of_epi H t X X' q a
      (MonoidHom.mem_ker.mp ha) y

/--
The exactness criterion for two composable functors of Galois categories:
exactness of the induced sequence of automorphism groups, the
essential-image characterization, and the epimorphic-cover characterization
are equivalent.
-/
@[stacks 0BS9]
theorem autHomOfCompIso_exact_sequence_tfae
    (H : C ⥤ C') (H' : C' ⥤ C'')
    [PreservesLimitsOfShape (Discrete PEmpty.{1}) H]
    (t : H ⋙ F' ≅ F) (t' : H' ⋙ F'' ≅ F') :
    List.TFAE [
      Function.Surjective (autHomOfCompIso H t) ∧
        (autHomOfCompIso H t).comp
            (autHomOfCompIso H' t') = 1 ∧
        (autHomOfCompIso H t).toMonoidHom.ker =
          ProCGroups.Presentations.Subgroup.closedNormalClosure
            (Set.range (autHomOfCompIso H' t')),
      Nonempty H.FullyFaithful ∧
        ∀ X' : C', H.essImage X' ↔
          ∃ (ι : Type) (_ : Finite ι),
            Nonempty ((∐ fun _ : ι => ⊤_ C'') ≅ H'.obj X'),
      Nonempty H.FullyFaithful ∧
        (∀ X : C, ∃ (ι : Type) (_ : Finite ι),
          Nonempty
            ((∐ fun _ : ι => ⊤_ C'') ≅ (H ⋙ H').obj X)) ∧
        ∀ X' : C',
          (∃ (ι : Type) (_ : Finite ι),
            Nonempty ((∐ fun _ : ι => ⊤_ C'') ≅ H'.obj X')) →
          ∃ (X : C) (q : H.obj X ⟶ X'), Epi q] := by
  let h := autHomOfCompIso H t
  let h' := autHomOfCompIso H' t'
  change List.TFAE [
    Function.Surjective h ∧ h.comp h' = 1 ∧
      h.toMonoidHom.ker =
        ProCGroups.Presentations.Subgroup.closedNormalClosure
          (Set.range h'),
    Nonempty H.FullyFaithful ∧
      ∀ X' : C', H.essImage X' ↔
        ∃ (ι : Type) (_ : Finite ι),
          Nonempty ((∐ fun _ : ι => ⊤_ C'') ≅ H'.obj X'),
    Nonempty H.FullyFaithful ∧
      (∀ X : C, ∃ (ι : Type) (_ : Finite ι),
        Nonempty
          ((∐ fun _ : ι => ⊤_ C'') ≅ (H ⋙ H').obj X)) ∧
      ∀ X' : C',
        (∃ (ι : Type) (_ : Finite ι),
          Nonempty ((∐ fun _ : ι => ⊤_ C'') ≅ H'.obj X')) →
        ∃ (X : C) (q : H.obj X ⟶ X'), Epi q]
  tfae_have 1 → 2 := by
    rintro ⟨hs, hcomp, hker⟩
    have hff : Nonempty H.FullyFaithful :=
      ((autHomOfCompIso_surjective_tfae F F' H t).out 1 2).mp hs
    refine ⟨hff, ?_⟩
    intro X'
    constructor
    · rintro ⟨X, ⟨e⟩⟩
      obtain ⟨ι, hfin, ⟨d⟩⟩ :=
        (autHomOfCompIso_comp_eq_one_iff H H' t t').1
          hcomp X
      exact ⟨ι, hfin, ⟨d ≪≫ H'.mapIso e⟩⟩
    · intro hdec
      have hsource :
          ∀ (a : Aut F'') (x : F''.obj (H'.obj X')),
            a • x = x :=
        (exists_iso_finite_coproduct_terminal_iff_fixed
          (F'' := F'') (H'.obj X')).1 hdec
      have hR :
          ∀ r ∈ Set.range h', ∀ y : F'.obj X', r • y = y := by
        rintro r ⟨a, rfl⟩ y
        exact
          (source_fixed_iff_induced_fixed H' t' X').1
            hsource a y
      apply essImage_of_res_essImage H t X'
      apply
        (ContAction.essImage_res_iff_ker_le_ker_ρAut
          h hs ((functorToContAction F').obj X')).2
      intro g hg
      apply MonoidHom.mem_ker.mpr
      apply Iso.ext
      apply FintypeCat.hom_ext
      intro y
      change g • y = y
      have hgclosure :
          g ∈ ProCGroups.Presentations.Subgroup.closedNormalClosure
            (Set.range h') := by
        rw [← hker]
        exact hg
      exact
        (open _root_.ProCGroups.Presentations.Subgroup in
          (mem_closedNormalClosure_iff_fixedBy_finite_continuous_actions
            (Set.range h') g).1 hgclosure
            ((functorToContAction F').obj X') hR y)
  tfae_have 2 → 1 := by
    rintro ⟨hff, hchar⟩
    have hs : Function.Surjective h :=
      ((autHomOfCompIso_surjective_tfae F F' H t).out 2 1).mp hff
    have hdecomp :
        ∀ X : C, ∃ (ι : Type) (_ : Finite ι),
          Nonempty
            ((∐ fun _ : ι => ⊤_ C'') ≅ (H ⋙ H').obj X) := by
      intro X
      exact (hchar (H.obj X)).1 (H.obj_mem_essImage X)
    have hcomp : h.comp h' = 1 :=
      (autHomOfCompIso_comp_eq_one_iff H H' t t').2 hdecomp
    refine ⟨hs, hcomp, le_antisymm ?_ ?_⟩
    · intro g hg
      apply
        (open _root_.ProCGroups.Presentations.Subgroup in
          (mem_closedNormalClosure_iff_fixedBy_finite_continuous_actions
            (Set.range h') g).2)
      intro Y hR y
      let E' := functorToContAction F'
      let X' : C' := E'.objPreimage Y
      let e : E'.obj X' ≅ Y := E'.objObjPreimageIso Y
      have hinduced :
          ∀ (a : Aut F'') (z : F'.obj X'), h' a • z = z := by
        intro a z
        apply
          (ConcreteCategory.bijective_of_isIso e.hom).injective
        have heq :=
          ConcreteCategory.congr_hom (e.hom.hom.comm (h' a)) z
        change e.hom (h' a • z) = h' a • e.hom z at heq
        rw [hR (h' a) ⟨a, rfl⟩ (e.hom z)] at heq
        exact heq
      have hsource :
          ∀ (a : Aut F'') (z : F''.obj (H'.obj X')),
            a • z = z :=
        (source_fixed_iff_induced_fixed H' t' X').2 hinduced
      have hdec :
          ∃ (ι : Type) (_ : Finite ι),
            Nonempty
              ((∐ fun _ : ι => ⊤_ C'') ≅ H'.obj X') :=
        (exists_iso_finite_coproduct_terminal_iff_fixed
          (F'' := F'') (H'.obj X')).2 hsource
      have hHX : H.essImage X' := (hchar X').2 hdec
      have hresX :
          (ContAction.res FintypeCat h).essImage (E'.obj X') :=
        res_essImage_of_essImage H t X' hHX
      have hresY : (ContAction.res FintypeCat h).essImage Y :=
        Functor.essImage.ofIso e hresX
      have hkerY :=
        (ContAction.essImage_res_iff_ker_le_ker_ρAut
          h hs Y).1 hresY
      have hgy : g ∈ (Action.ρAut Y.obj).ker := hkerY hg
      change Action.ρAut Y.obj g = 1 at hgy
      have hgy' := congrArg Iso.hom hgy
      exact ConcreteCategory.congr_hom hgy' y
    · apply
        ProCGroups.Presentations.closedNormalClosure_le_closed_normal
          (ProCGroups.ContinuousMonoidHom.isClosed_ker h)
      rintro _ ⟨a, rfl⟩
      apply MonoidHom.mem_ker.mpr
      have ha :=
        congrArg (fun k : Aut F'' →ₜ* Aut F => k a) hcomp
      simpa using ha
  tfae_have 2 → 3 := by
    rintro ⟨hff, hchar⟩
    refine ⟨hff, ?_, ?_⟩
    · intro X
      exact (hchar (H.obj X)).1 (H.obj_mem_essImage X)
    · intro X' hdec
      let hX' := (hchar X').2 hdec
      exact ⟨hX'.witness, hX'.getIso.hom, inferInstance⟩
  tfae_have 3 → 2 := by
    rintro ⟨hff, hdecomp, hepi⟩
    have hs : Function.Surjective h :=
      ((autHomOfCompIso_surjective_tfae F F' H t).out 2 1).mp hff
    refine ⟨hff, ?_⟩
    intro X'
    constructor
    · rintro ⟨X, ⟨e⟩⟩
      obtain ⟨ι, hfin, ⟨d⟩⟩ := hdecomp X
      exact ⟨ι, hfin, ⟨d ≪≫ H'.mapIso e⟩⟩
    · intro hdec
      obtain ⟨X, q, hq⟩ := hepi X' hdec
      let : Epi q := hq
      exact essImage_of_epi H t hs X X' q
  tfae_finish

end CategoryTheory.PreGaloisCategory
