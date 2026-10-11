/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.GeometricFiber.PointedComposition

/-!
# Strict composition with the canonical geometric-point identifications

The pullback pentagon identifies the composite fiber comparison with the
canonical one.  Consequently the original fundamental-group homomorphisms
compose after transport along the specified equality of geometric points.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Functor CategoryTheory.PreGaloisCategory

namespace AlgebraicGeometry.FiniteEtale

universe u

attribute [local instance] finiteEtaleOverCategoryCoherence
  finiteEtaleHasPullbacksAlongCoherence finiteEtaleStableUnderBaseChangeAlongCoherence

variable {X Y Z : Scheme.{u}} {Ω : Type u} [Field Ω]

/-- A fiber comparison transported to an equal point is the inverse of the
actual pullback-composition comparison with that specified composite. -/
theorem pullbackFiberIso_transport_hom_app
    (f : X ⟶ Y) (point : Spec (.of Ω) ⟶ X) (eta : Spec (.of Ω) ⟶ Y)
    (heta : point ≫ f = eta) (A : FiniteEtale Y) :
    (pullbackFiberIso f point ≪≫ eqToIso (congrArg fiber heta)).hom.app A =
      (forgetScheme Ω).map
        ((MorphismProperty.Over.pullbackComp
          (P := @IsFiniteEtale) (Q := ⊤) point f eta heta.symm).inv.app A) := by
  subst eta
  let v : (forgetScheme Ω).obj ((pullback point).obj ((pullback f).obj A)) ⟶
      (forgetScheme Ω).obj ((pullback (point ≫ f)).obj A) :=
    (forgetScheme Ω).map ((MorphismProperty.Over.pullbackComp
      (P := @IsFiniteEtale) (Q := ⊤) point f).inv.app A)
  change (𝟙 _ ≫ v) ≫ 𝟙 _ = v
  rw [Category.id_comp, Category.comp_id]

/-- The composite canonical comparison is the canonical comparison for the
composite scheme map, with its prescribed equality of target points. -/
theorem pullbackCompositeFiberIsoOfEq_eq_pullbackFiberIso
    (f : X ⟶ Y) (g : Y ⟶ Z) (m : X ⟶ Z) (hm : m = f ≫ g)
    (point : Spec (.of Ω) ⟶ X) (hpoint : (point ≫ f) ≫ g = point ≫ m) :
    pullbackCompositeFiberIsoOfEq f g m hm point (point ≫ m) hpoint = pullbackFiberIso m point := by
  subst m
  apply Iso.ext
  apply NatTrans.ext
  funext A
  have hlast := pullbackFiberIso_transport_hom_app g (point ≫ f) (point ≫ f ≫ g) hpoint A
  let A₀ : FiniteEtale (Spec (.of Ω)) :=
    (pullback point).obj ((pullback (f ≫ g)).obj A)
  let A₁ : FiniteEtale (Spec (.of Ω)) :=
    (pullback point).obj ((pullback f).obj ((pullback g).obj A))
  let A₂ : FiniteEtale (Spec (.of Ω)) :=
    (pullback (point ≫ f)).obj ((pullback g).obj A)
  let A₃ : FiniteEtale (Spec (.of Ω)) := (pullback (point ≫ f ≫ g)).obj A
  let a : A₀ ⟶ A₁ := (pullback point).map ((MorphismProperty.Over.pullbackComp
    (P := @IsFiniteEtale) (Q := ⊤) f g).hom.app A)
  let b : A₁ ⟶ A₂ := (MorphismProperty.Over.pullbackComp
    (P := @IsFiniteEtale) (Q := ⊤) point f).inv.app ((pullback g).obj A)
  let c : A₂ ⟶ A₃ := (MorphismProperty.Over.pullbackComp
    (P := @IsFiniteEtale) (Q := ⊤) (point ≫ f) g (point ≫ f ≫ g)
    (Category.assoc point f g).symm).inv.app A
  let d : A₀ ⟶ A₃ := (MorphismProperty.Over.pullbackComp
    (P := @IsFiniteEtale) (Q := ⊤) point (f ≫ g)).inv.app A
  have hcollapse : a ≫ b ≫ c = d :=
    pullbackComp_collapse_app point f g (point ≫ f ≫ g) rfl A
  have hmapped : (forgetScheme Ω).map a ≫ (forgetScheme Ω).map b ≫
      (forgetScheme Ω).map c = (forgetScheme Ω).map d := by
    calc
      (forgetScheme Ω).map a ≫ (forgetScheme Ω).map b ≫ (forgetScheme Ω).map c =
          (forgetScheme Ω).map a ≫ (forgetScheme Ω).map (b ≫ c) :=
        congrArg (fun q ↦ (forgetScheme Ω).map a ≫ q)
          ((forgetScheme Ω).map_comp b c).symm
      _ = (forgetScheme Ω).map (a ≫ b ≫ c) :=
        ((forgetScheme Ω).map_comp a (b ≫ c)).symm
      _ = (forgetScheme Ω).map d := congrArg (forgetScheme Ω).map hcollapse
  have hfirst := pullbackFiberIso_transport_hom_app (f ≫ g) point (point ≫ f ≫ g) rfl A
  have hmiddle := pullbackFiberIso_transport_hom_app f point (point ≫ f) rfl
    ((pullback g).obj A)
  simp only [eqToIso_refl, Iso.trans_refl] at hfirst hmiddle
  change (fiber point).map
      ((MorphismProperty.Over.pullbackComp
        (P := @IsFiniteEtale) (Q := ⊤) f g).hom.app A) ≫
      (𝟙 _ ≫ (pullbackFiberIso f point).hom.app ((pullback g).obj A) ≫
        (pullbackFiberIso g (point ≫ f)).hom.app A ≫
          (eqToIso (congrArg fiber hpoint)).hom.app A) =
    (pullbackFiberIso (f ≫ g) point).hom.app A
  rw [Category.id_comp]
  change (fiber point).map
      ((MorphismProperty.Over.pullbackComp
        (P := @IsFiniteEtale) (Q := ⊤) f g).hom.app A) ≫
      ((pullbackFiberIso f point).hom.app ((pullback g).obj A) ≫
        (pullbackFiberIso g (point ≫ f) ≪≫ eqToIso (congrArg fiber hpoint)).hom.app A) =
    (pullbackFiberIso (f ≫ g) point).hom.app A
  rw [hlast, hmiddle, hfirst]
  exact hmapped

/-- The original fundamental-group maps compose strictly after the prescribed
transport of the target geometric point. -/
theorem fundamentalGroupHom_comp_of_eq
    (f : X ⟶ Y) (g : Y ⟶ Z) (m : X ⟶ Z) (hm : m = f ≫ g)
    (point : Spec (.of Ω) ⟶ X) (hpoint : (point ≫ f) ≫ g = point ≫ m)
    (a : π₁ᵉᵗ(point)) :
    hpoint ▸ fundamentalGroupHom g (point ≫ f) (fundamentalGroupHom f point a) =
      fundamentalGroupHom m point a := by
  rw [fundamentalGroupHom_comp_transport_eq_autHomOfCompIso
    f g m hm point (point ≫ m) hpoint,
    pullbackCompositeFiberIsoOfEq_eq_pullbackFiberIso]
  rfl

end AlgebraicGeometry.FiniteEtale
