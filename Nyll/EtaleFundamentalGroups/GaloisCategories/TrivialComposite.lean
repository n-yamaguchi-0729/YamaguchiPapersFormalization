/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.CategoryTheory.Galois.Decomposition
public import Nyll.EtaleFundamentalGroups.GaloisCategories.Functoriality

/-!
# Trivial composites of functors of Galois categories

The composite homomorphism on automorphism groups induced by two composable
functors is trivial exactly when every object in the image of the composite
functor is a finite coproduct of terminal objects.
-/

@[expose] public section

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
variable (H : C ⥤ C') (H' : C' ⥤ C'')

private theorem composite_smul_transport
    (t : H ⋙ F' ≅ F) (t' : H' ⋙ F'' ≅ F')
    (X : C) (a : Aut F'')
    (x : F''.obj ((H ⋙ H').obj X)) :
    (t.app X).hom ((t'.app (H.obj X)).hom (a • x)) =
      (autHomOfCompIso H t (autHomOfCompIso H' t' a)) •
        (t.app X).hom ((t'.app (H.obj X)).hom x) := by
  let s' := (functorToContActionCompIso H' t').app (H.obj X)
  let s := (functorToContActionCompIso H t).app X
  have ha' := ConcreteCategory.congr_hom (s'.hom.hom.comm a) x
  change (t'.app (H.obj X)).hom (a • x) =
      (autHomOfCompIso H' t' a) • (t'.app (H.obj X)).hom x at ha'
  have ha := ConcreteCategory.congr_hom
    (s.hom.hom.comm (autHomOfCompIso H' t' a))
      ((t'.app (H.obj X)).hom x)
  change (t.app X).hom
      ((autHomOfCompIso H' t' a) • (t'.app (H.obj X)).hom x) =
      (autHomOfCompIso H t (autHomOfCompIso H' t' a)) •
        (t.app X).hom ((t'.app (H.obj X)).hom x) at ha
  exact (congrArg (t.app X).hom ha').trans ha

private theorem composite_trivial_smul
    (t : H ⋙ F' ≅ F) (t' : H' ⋙ F'' ≅ F')
    (hcomp :
      (autHomOfCompIso H t).comp (autHomOfCompIso H' t') = 1)
    (X : C) (a : Aut F'') (x : F''.obj ((H ⋙ H').obj X)) :
    a • x = x := by
  apply
    (ConcreteCategory.bijective_of_isIso
      (t'.app (H.obj X)).hom).injective
  apply (ConcreteCategory.bijective_of_isIso (t.app X).hom).injective
  rw [composite_smul_transport H H' t t' X a x]
  have ha := congrArg (fun k : Aut F'' →ₜ* Aut F => k a) hcomp
  change autHomOfCompIso H t (autHomOfCompIso H' t' a) = 1 at ha
  rw [ha, one_smul]

private theorem fixed_smul_decomposition
    (Z : C'')
    (hfixed : ∀ (a : Aut F'') (x : F''.obj Z), a • x = x) :
    ∃ (ι : Type) (_ : Finite ι),
      Nonempty ((∐ fun _ : ι => ⊤_ C'') ≅ Z) := by
  obtain ⟨ι, hfin, f, e, hf⟩ :=
    has_decomp_connected_components' Z
  have hterm (i : ι) : IsTerminal (f i) := by
    letI : IsConnected (f i) := hf i
    let q : f i ⟶ Z := Sigma.ι f i ≫ e.hom
    haveI : Mono q := mono_comp _ _
    haveI : Mono (F''.map q) := F''.map_mono q
    have hqinj : Function.Injective (F''.map q) :=
      (ConcreteCategory.mono_iff_injective_of_preservesPullback
        (F''.map q)).mp inferInstance
    have hsub : Subsingleton (F''.obj (f i)) := ⟨by
      intro y z
      obtain ⟨a, ha⟩ :=
        (inferInstance :
          MulAction.IsPretransitive (Aut F'') (F''.obj (f i))).exists_smul_eq
            y z
      apply hqinj
      rw [← ha, ← mulAction_naturality F'' a q y]
      exact (hfixed a (F''.map q y)).symm⟩
    have hnon : Nonempty (F''.obj (f i)) := inferInstance
    have hFterm : IsTerminal (F''.obj (f i)) := by
      refine IsTerminal.ofUniqueHom
        (fun Y => FintypeCat.homMk (fun _ => hnon.some)) ?_
      intro Y m
      ext y
      exact hsub.elim _ _
    exact hFterm.isTerminalOfObj F'' (f i)
  exact ⟨ι, hfin,
    ⟨Sigma.mapIso
      (fun i => terminalIsTerminal.uniqueUpToIso (hterm i)) ≪≫ e⟩⟩

private theorem fiber_coproduct_terminal_exists_rep
    {ι : Type} [Finite ι]
    (x : F''.obj (∐ fun _ : ι => ⊤_ C'')) :
    ∃ (i : ι) (y : F''.obj (⊤_ C'')),
      F''.map (Sigma.ι (fun _ : ι => ⊤_ C'') i) y = x := by
  let f : ι → C'' := fun _ => ⊤_ C''
  let c : Cofan f := Cofan.mk (∐ f) (Sigma.ι f)
  have hc : IsColimit c := colimit.isColimit (Discrete.functor f)
  let s : Cocone (Discrete.functor f ⋙ F'') := F''.mapCocone c
  have hs : IsColimit s := isColimitOfPreserves F'' hc
  obtain ⟨⟨i⟩, y, hy⟩ := Concrete.isColimit_exists_rep _ hs x
  exact ⟨i, y, hy⟩

private theorem coproduct_terminal_smul_eq
    {ι : Type} [Finite ι]
    (a : Aut F'') (x : F''.obj (∐ fun _ : ι => ⊤_ C'')) :
    a • x = x := by
  obtain ⟨i, y, rfl⟩ :=
    fiber_coproduct_terminal_exists_rep (F'' := F'') x
  rw [mulAction_naturality]
  congr 1
  have hterm : IsTerminal (F''.obj (⊤_ C'')) :=
    terminalIsTerminal.isTerminalObj F'' (⊤_ C'')
  let : Unique (F''.obj (⊤_ C'')) :=
    Concrete.uniqueOfTerminalOfPreserves (F''.obj (⊤_ C'')) hterm
  exact Subsingleton.elim _ _

private theorem terminal_coproduct_iso_smul_eq
    {Z : C''}
    (hZ : ∃ (ι : Type) (_ : Finite ι),
      Nonempty ((∐ fun _ : ι => ⊤_ C'') ≅ Z))
    (a : Aut F'') (x : F''.obj Z) :
    a • x = x := by
  obtain ⟨ι, hfin, ⟨e⟩⟩ := hZ
  let y : F''.obj (∐ fun _ : ι => ⊤_ C'') := (F''.mapIso e).inv x
  have hy : a • y = y :=
    coproduct_terminal_smul_eq (F'' := F'') a y
  have hmap : F''.map e.hom y = x :=
    FintypeCat.inv_hom_id_apply (F''.mapIso e) x
  calc
    a • x = a • F''.map e.hom y := congrArg (a • ·) hmap.symm
    _ = F''.map e.hom (a • y) := mulAction_naturality F'' a e.hom y
    _ = F''.map e.hom y := congrArg (F''.map e.hom) hy
    _ = x := hmap

/--
An object of a Galois category is a finite coproduct of terminal objects
exactly when every automorphism of a fiber functor fixes every point of its
fiber.
-/
theorem exists_iso_finite_coproduct_terminal_iff_fixed
    (Z : C'') :
    (∃ (ι : Type) (_ : Finite ι),
      Nonempty ((∐ fun _ : ι => ⊤_ C'') ≅ Z)) ↔
      ∀ (a : Aut F'') (x : F''.obj Z), a • x = x :=
  ⟨fun hZ ↦ terminal_coproduct_iso_smul_eq (F'' := F'') hZ,
    fixed_smul_decomposition (F'' := F'') Z⟩

private theorem composite_trivial_decomposition
    (t : H ⋙ F' ≅ F) (t' : H' ⋙ F'' ≅ F')
    (hcomp :
      (autHomOfCompIso H t).comp (autHomOfCompIso H' t') = 1) :
    ∀ X : C, ∃ (ι : Type) (_ : Finite ι),
      Nonempty ((∐ fun _ : ι => ⊤_ C'') ≅ (H ⋙ H').obj X) := by
  intro X
  exact
    (exists_iso_finite_coproduct_terminal_iff_fixed
      (F'' := F'') ((H ⋙ H').obj X)).2
      (composite_trivial_smul H H' t t' hcomp X)

private theorem terminal_decomposition_composite_trivial
    (t : H ⋙ F' ≅ F) (t' : H' ⋙ F'' ≅ F')
    (hdecomp : ∀ X : C, ∃ (ι : Type) (_ : Finite ι),
      Nonempty ((∐ fun _ : ι => ⊤_ C'') ≅ (H ⋙ H').obj X)) :
    (autHomOfCompIso H t).comp (autHomOfCompIso H' t') = 1 := by
  apply ContinuousMonoidHom.ext
  intro a
  apply Aut.ext
  ext X x
  change autHomOfCompIso H t (autHomOfCompIso H' t' a) • x = x
  let y : F''.obj ((H ⋙ H').obj X) :=
    (t'.app (H.obj X)).inv ((t.app X).inv x)
  have hy : a • y = y :=
    terminal_coproduct_iso_smul_eq (F'' := F'') (hdecomp X) a y
  have htransport := composite_smul_transport H H' t t' X a y
  rw [hy] at htransport
  have hto : (t.app X).hom ((t'.app (H.obj X)).hom y) = x := by
    change (t.app X).hom ((t'.app (H.obj X)).hom
      ((t'.app (H.obj X)).inv ((t.app X).inv x))) = x
    rw [FintypeCat.inv_hom_id_apply, FintypeCat.inv_hom_id_apply]
  rw [hto] at htransport
  exact htransport.symm

/--
The composite homomorphism on automorphism groups is trivial exactly when
every object in the image of the composite functor is a finite coproduct of
terminal objects.
-/
@[stacks 0BS8]
theorem autHomOfCompIso_comp_eq_one_iff
    (t : H ⋙ F' ≅ F) (t' : H' ⋙ F'' ≅ F') :
    (autHomOfCompIso H t).comp (autHomOfCompIso H' t') = 1 ↔
      ∀ X : C, ∃ (ι : Type) (_ : Finite ι),
        Nonempty ((∐ fun _ : ι => ⊤_ C'') ≅ (H ⋙ H').obj X) :=
  ⟨composite_trivial_decomposition H H' t t',
    terminal_decomposition_composite_trivial H H' t t'⟩

end CategoryTheory.PreGaloisCategory
