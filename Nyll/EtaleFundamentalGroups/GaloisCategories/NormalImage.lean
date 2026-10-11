/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/


import Nyll.EtaleFundamentalGroups.ContinuousActions.NormalRange
import Nyll.EtaleFundamentalGroups.GaloisCategories.ConnectedActions
import Nyll.EtaleFundamentalGroups.GaloisCategories.TrivialComposite

/-!
# Normal images for functors of Galois categories

The image of the homomorphism induced by a functor of Galois categories is
normal exactly when the connected objects having a point after applying the
functor become finite coproducts of terminal objects, as in
[Stacks Project, Tag 0BTS](https://stacks.math.columbia.edu/tag/0BTS).
-/

noncomputable section

universe u₁ u₂ v₁ v₂ w

open CategoryTheory Limits
open scoped FintypeCatDiscrete

namespace CategoryTheory.PreGaloisCategory

variable {C : Type u₁} [Category.{u₂} C] [GaloisCategory C]
variable {C' : Type v₁} [Category.{v₂} C'] [GaloisCategory C']
variable {F : C ⥤ FintypeCat.{w}} [FiberFunctor F]
variable {F' : C' ⥤ FintypeCat.{w}} [FiberFunctor F']

private theorem nonempty_terminal_hom_iff_exists_range_fixed
    (H : C ⥤ C') (t : H ⋙ F' ≅ F) (X : C) :
    Nonempty (⊤_ C' ⟶ H.obj X) ↔
      ∃ x : F.obj X,
        ∀ a : Aut F', autHomOfCompIso H t a • x = x := by
  constructor
  · rintro ⟨q⟩
    let z : (⊤_ FintypeCat.{w}).obj :=
      (terminalIsTerminal.from (FintypeCat.of PUnit.{w + 1})) PUnit.unit
    let z' : F'.obj (⊤_ C') := (PreservesTerminal.iso F').inv z
    let y : F'.obj (H.obj X) := F'.map q z'
    let x : F.obj X := (t.app X).hom y
    refine ⟨x, ?_⟩
    intro a
    have hz : a • z' = z' := by
      have hterm : IsTerminal (F'.obj (⊤_ C')) :=
        terminalIsTerminal.isTerminalObj F' (⊤_ C')
      let : Unique (F'.obj (⊤_ C')) :=
        Concrete.uniqueOfTerminalOfPreserves (F'.obj (⊤_ C')) hterm
      exact Subsingleton.elim _ _
    have hy : a • y = y := by
      have hn := mulAction_naturality F' a q z'
      simpa only [y, hz] using hn
    let s := (functorToContActionCompIso H t).app X
    have hs := ConcreteCategory.congr_hom (s.hom.hom.comm a) y
    change (t.app X).hom (a • y) =
      autHomOfCompIso H t a • (t.app X).hom y at hs
    simpa only [x, hy] using hs.symm
  · rintro ⟨x, hx⟩
    let y : F'.obj (H.obj X) := (t.app X).inv x
    have hxy : (t.app X).hom y = x :=
      FintypeCat.inv_hom_id_apply (t.app X) x
    have hy (a : Aut F') : a • y = y := by
      apply (ConcreteCategory.bijective_of_isIso (t.app X).hom).injective
      let s := (functorToContActionCompIso H t).app X
      have hs := ConcreteCategory.congr_hom (s.hom.hom.comm a) y
      change (t.app X).hom (a • y) =
        autHomOfCompIso H t a • (t.app X).hom y at hs
      calc
        (t.app X).hom (a • y) =
            autHomOfCompIso H t a • (t.app X).hom y := hs
        _ = autHomOfCompIso H t a • x := congrArg _ hxy
        _ = x := hx a
        _ = (t.app X).hom y := hxy.symm
    let E' := functorToContAction F'
    let f : E'.obj (⊤_ C') ⟶ E'.obj (H.obj X) :=
      ObjectProperty.homMk (Action.Hom.mk
        (FintypeCat.homMk (fun _ => y)) (by
          intro a
          apply FintypeCat.hom_ext
          intro z
          exact (hy a).symm))
    exact
      ⟨(Functor.FullyFaithful.ofFullyFaithful E').preimage f⟩

private theorem terminal_decomposition_of_range_trivial
    (H : C ⥤ C') (t : H ⋙ F' ≅ F) (X : C)
    (htriv : ∀ (a : Aut F') (x : F.obj X),
      autHomOfCompIso H t a • x = x) :
    ∃ (ι : Type) (_ : Finite ι),
      Nonempty ((∐ fun _ : ι => ⊤_ C') ≅ H.obj X) := by
  apply
    (exists_iso_finite_coproduct_terminal_iff_fixed
      (F'' := F') (H.obj X)).2
  intro a y
  apply (ConcreteCategory.bijective_of_isIso (t.app X).hom).injective
  let s := (functorToContActionCompIso H t).app X
  have hs := ConcreteCategory.congr_hom (s.hom.hom.comm a) y
  change (t.app X).hom (a • y) =
    autHomOfCompIso H t a • (t.app X).hom y at hs
  calc
    (t.app X).hom (a • y) =
        autHomOfCompIso H t a • (t.app X).hom y := hs
    _ = (t.app X).hom y := htriv a ((t.app X).hom y)

private theorem range_trivial_of_terminal_decomposition
    (H : C ⥤ C') (t : H ⋙ F' ≅ F) (X : C)
    (hdecomp : ∃ (ι : Type) (_ : Finite ι),
      Nonempty ((∐ fun _ : ι => ⊤_ C') ≅ H.obj X)) :
    ∀ (a : Aut F') (x : F.obj X),
      autHomOfCompIso H t a • x = x := by
  intro a x
  let y : F'.obj (H.obj X) := (t.app X).inv x
  have hxy : (t.app X).hom y = x :=
    FintypeCat.inv_hom_id_apply (t.app X) x
  have hy : a • y = y :=
    (exists_iso_finite_coproduct_terminal_iff_fixed
      (F'' := F') (H.obj X)).1 hdecomp a y
  let s := (functorToContActionCompIso H t).app X
  have hs := ConcreteCategory.congr_hom (s.hom.hom.comm a) y
  change (t.app X).hom (a • y) =
    autHomOfCompIso H t a • (t.app X).hom y at hs
  calc
    autHomOfCompIso H t a • x =
        autHomOfCompIso H t a • (t.app X).hom y := congrArg _ hxy.symm
    _ = (t.app X).hom (a • y) := hs.symm
    _ = (t.app X).hom y := congrArg _ hy
    _ = x := hxy

/--
The image of the homomorphism induced by `H` and `t` is normal exactly when
every connected object that acquires a point after applying `H` becomes a
finite coproduct of terminal objects.
-/
@[stacks 0BTS]
theorem autHomOfCompIso_range_normal_iff_terminal_decomposition
    (H : C ⥤ C') (t : H ⋙ F' ≅ F) :
    (autHomOfCompIso H t).toMonoidHom.range.Normal ↔
      ∀ X : C, IsConnected X →
        Nonempty (⊤_ C' ⟶ H.obj X) →
        ∃ (ι : Type) (_ : Finite ι),
          Nonempty ((∐ fun _ : ι => ⊤_ C') ≅ H.obj X) := by
  constructor
  · intro hnormal X hconn hpoint
    let : IsConnected X := hconn
    let E := functorToContAction F
    have htrans :
        MulAction.IsPretransitive (Aut F) (E.obj X).obj.V := by
      change MulAction.IsPretransitive (Aut F) (F.obj X)
      infer_instance
    have hfixed :
        ∃ x : (E.obj X).obj.V,
          ∀ a : Aut F', autHomOfCompIso H t a • x = x :=
      (nonempty_terminal_hom_iff_exists_range_fixed H t X).1 hpoint
    have htriv :
        ∀ (a : Aut F') (x : (E.obj X).obj.V),
          autHomOfCompIso H t a • x = x :=
      (ContAction.range_normal_iff_fixed_point_implies_trivial
        (autHomOfCompIso H t)).1 hnormal (E.obj X) htrans hfixed
    exact terminal_decomposition_of_range_trivial H t X htriv
  · intro hdecomp
    apply
      (ContAction.range_normal_iff_fixed_point_implies_trivial
        (autHomOfCompIso H t)).2
    intro Z htrans hfixed
    let : MulAction (Aut F) Z.obj.V := Action.instMulAction Z.obj
    let E := functorToContAction F
    let X : C := E.objPreimage Z
    let eZ : E.obj X ≅ Z := E.objObjPreimageIso Z
    let ef :=
      (forget₂ (ContAction FintypeCat (Aut F)) FintypeCat).mapIso eZ
    let z : Z.obj.V := hfixed.choose
    let x : F.obj X := ef.inv z
    have hxz : ef.hom x = z :=
      FintypeCat.inv_hom_id_apply ef z
    let : Nonempty (F.obj X) := ⟨x⟩
    let : MulAction.IsPretransitive (Aut F) (F.obj X) := by
      constructor
      intro x₁ x₂
      let z₁ : Z.obj.V := ef.hom x₁
      let z₂ : Z.obj.V := ef.hom x₂
      obtain ⟨a, ha⟩ := htrans.exists_smul_eq z₁ z₂
      refine ⟨a, ?_⟩
      apply (ConcreteCategory.bijective_of_isIso ef.hom).injective
      have hc := ConcreteCategory.congr_hom (eZ.hom.hom.comm a) x₁
      change ef.hom (a • x₁) = a • z₁ at hc
      exact hc.trans ha
    let : IsConnected X :=
      FiberFunctor.isConnected_of_isPretransitive F X
    have hfixedX :
        ∃ x : F.obj X,
          ∀ a : Aut F', autHomOfCompIso H t a • x = x := by
      refine ⟨x, ?_⟩
      intro a
      apply (ConcreteCategory.bijective_of_isIso ef.hom).injective
      have hc := ConcreteCategory.congr_hom
        (eZ.hom.hom.comm (autHomOfCompIso H t a)) x
      change ef.hom (autHomOfCompIso H t a • x) =
        (Z.obj.ρ (autHomOfCompIso H t a)).hom (ef.hom x) at hc
      have hz := hfixed.choose_spec a
      change (Z.obj.ρ (autHomOfCompIso H t a)).hom z = z at hz
      exact hc.trans <|
        (congrArg
          (fun y : Z.obj.V =>
            (Z.obj.ρ (autHomOfCompIso H t a)).hom y) hxz).trans <|
        hz.trans hxz.symm
    have hpoint : Nonempty (⊤_ C' ⟶ H.obj X) :=
      (nonempty_terminal_hom_iff_exists_range_fixed H t X).2 hfixedX
    have htrivX :
        ∀ (a : Aut F') (x : F.obj X),
          autHomOfCompIso H t a • x = x :=
      range_trivial_of_terminal_decomposition H t X
        (hdecomp X inferInstance hpoint)
    intro a z'
    let x' : F.obj X := ef.inv z'
    have hxz' : ef.hom x' = z' :=
      FintypeCat.inv_hom_id_apply ef z'
    have hc := ConcreteCategory.congr_hom
      (eZ.hom.hom.comm (autHomOfCompIso H t a)) x'
    change ef.hom (autHomOfCompIso H t a • x') =
      (Z.obj.ρ (autHomOfCompIso H t a)).hom (ef.hom x') at hc
    change
      (Z.obj.ρ (autHomOfCompIso H t a)).hom z' = z'
    exact
      (congrArg
        (fun y : Z.obj.V =>
          (Z.obj.ρ (autHomOfCompIso H t a)).hom y) hxz'.symm).trans <|
      hc.symm.trans <|
      (congrArg (fun y : F.obj X => ef.hom y) (htrivX a x')).trans hxz'

end CategoryTheory.PreGaloisCategory
