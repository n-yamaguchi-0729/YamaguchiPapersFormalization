/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.GeometricFiber.FundamentalGroup
import Nyll.EtaleFundamentalGroups.GeometricFiber.Functoriality

/-!
# Composition of maps on geometric fundamental groups

The canonical pullback comparisons for two successive scheme morphisms give
the same map on fundamental groups as the corresponding composite pullback
comparison.  Two factorizations of one scheme morphism therefore induce maps
which differ by an explicit inner automorphism.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.PreGaloisCategory

namespace AlgebraicGeometry.FiniteEtale

universe u

local instance finiteEtaleOverCategoryComposition (S : Scheme.{u}) :
    Category (MorphismProperty.Over
      (@IsFiniteEtale : MorphismProperty Scheme.{u}) ⊤ S) :=
  instCategory S

local instance finiteEtaleHasPullbacksAlongComposition
    {S T : Scheme.{u}} (f : S ⟶ T) :
    MorphismProperty.HasPullbacksAlong
      (@IsFiniteEtale : MorphismProperty Scheme.{u}) f :=
  ⟨fun _ _ ↦ inferInstance⟩

local instance finiteEtaleStableUnderBaseChangeAlongComposition
    {S T : Scheme.{u}} (f : S ⟶ T) :
    MorphismProperty.IsStableUnderBaseChangeAlong
      (@IsFiniteEtale : MorphismProperty Scheme.{u}) f :=
  ⟨fun h hf ↦ MorphismProperty.of_isPullback
    (P := (@IsFiniteEtale : MorphismProperty Scheme.{u})) h hf⟩

variable {X Y Z : Scheme.{u}}
variable {Omega : Type u} [Field Omega]

/-- The fiber comparison obtained by composing the two canonical pullback
comparisons and the canonical comparison of iterated pullbacks. -/
noncomputable def pullbackCompositeFiberIso
    (f : X ⟶ Y) (g : Y ⟶ Z) (xi : Spec (.of Omega) ⟶ X) :
    pullback (f ≫ g) ⋙ fiber xi ≅ fiber ((xi ≫ f) ≫ g) :=
  Functor.isoWhiskerRight
      (MorphismProperty.Over.pullbackComp
        (P := @IsFiniteEtale) (Q := ⊤) f g)
      (fiber xi) ≪≫
    Functor.associator (pullback g) (pullback f) (fiber xi) ≪≫
    Functor.isoWhiskerLeft (pullback g) (pullbackFiberIso f xi) ≪≫
    pullbackFiberIso g (xi ≫ f)


private theorem pullbackComp_conjAut
    (f : X ⟶ Y) (g : Y ⟶ Z) (xi : Spec (.of Omega) ⟶ X)
    (a : π₁ᵉᵗ(xi)) :
      (Functor.isoWhiskerRight
        (MorphismProperty.Over.pullbackComp (P := @IsFiniteEtale) (Q := ⊤) f g)
        (fiber xi)).conjAut
          (((Functor.whiskeringLeft _ _ FintypeCat).obj (pullback (f ≫ g))).mapAut
            (fiber xi) a) =
        (((Functor.whiskeringLeft _ _ FintypeCat).obj
          (pullback g ⋙ pullback f)).mapAut (fiber xi) a) := by
  let pc := MorphismProperty.Over.pullbackComp
    (P := @IsFiniteEtale) (Q := ⊤) f g
  apply Aut.ext
  ext C c
  apply ConcreteCategory.congr_hom
  change (fiber xi).map (pc.inv.app C) ≫ a.hom.app _ ≫
      (fiber xi).map (pc.hom.app C) = a.hom.app _
  rw [← a.hom.naturality (pc.hom.app C)]
  have hcancel : (fiber xi).map (pc.inv.app C) ≫
      (fiber xi).map (pc.hom.app C) = 𝟙 _ := by
    calc
      _ = (fiber xi).map (pc.inv.app C ≫ pc.hom.app C) :=
        ((fiber xi).map_comp _ _).symm
      _ = (fiber xi).map (𝟙 _) :=
        congrArg ((fiber xi).map) (pc.inv_hom_id_app C)
      _ = 𝟙 _ := (fiber xi).map_id _
  simp only [← Category.assoc, hcancel, Category.id_comp]

private theorem pullbackCompositeFiberIso_conjAut
    (f : X ⟶ Y) (g : Y ⟶ Z) (xi : Spec (.of Omega) ⟶ X)
    (b : Aut (pullback (f ≫ g) ⋙ fiber xi)) :
    (pullbackCompositeFiberIso f g xi).conjAut b =
      (pullbackFiberIso g (xi ≫ f)).conjAut
        ((Functor.isoWhiskerLeft (pullback g) (pullbackFiberIso f xi)).conjAut
          ((Functor.associator (pullback g) (pullback f) (fiber xi)).conjAut
            ((Functor.isoWhiskerRight
              (MorphismProperty.Over.pullbackComp (P := @IsFiniteEtale) (Q := ⊤) f g)
              (fiber xi)).conjAut b))) := by
  let e₁ := Functor.isoWhiskerRight
    (MorphismProperty.Over.pullbackComp (P := @IsFiniteEtale) (Q := ⊤) f g) (fiber xi)
  let e₂ := Functor.associator (pullback g) (pullback f) (fiber xi)
  let e₃ := Functor.isoWhiskerLeft (pullback g) (pullbackFiberIso f xi)
  let e₄ := pullbackFiberIso g (xi ≫ f)
  exact (e₁.trans_conjAut (e₂ ≪≫ e₃ ≪≫ e₄) b).trans
    ((e₂.trans_conjAut (e₃ ≪≫ e₄) (e₁.conjAut b)).trans
      (e₃.trans_conjAut e₄ (e₂.conjAut (e₁.conjAut b))))

/-- Successive fundamental-group maps are the map induced by the composite
pullback comparison. -/
theorem fundamentalGroupHom_comp_eq_autHomOfCompIso
    (f : X ⟶ Y) (g : Y ⟶ Z) (xi : Spec (.of Omega) ⟶ X)
    (a : π₁ᵉᵗ(xi)) :
    fundamentalGroupHom g (xi ≫ f) (fundamentalGroupHom f xi a) =
      CategoryTheory.PreGaloisCategory.autHomOfCompIso
        (pullback (f ≫ g)) (pullbackCompositeFiberIso f g xi) a := by
  have hpc := pullbackComp_conjAut f g xi a
  let b : Aut (pullback f ⋙ fiber xi) :=
    (((Functor.whiskeringLeft _ _ FintypeCat).obj (pullback f)).mapAut
      (fiber xi) a)
  have hassoc :
      (Functor.associator (pullback g) (pullback f) (fiber xi)).conjAut
          (((Functor.whiskeringLeft _ _ FintypeCat).obj
            (pullback g ⋙ pullback f)).mapAut (fiber xi) a) =
        (((Functor.whiskeringLeft _ _ FintypeCat).obj (pullback g)).mapAut
          (pullback f ⋙ fiber xi) b) := by
    apply Aut.ext
    ext C c
    rfl
  have hwhisker :
      (Functor.isoWhiskerLeft (pullback g) (pullbackFiberIso f xi)).conjAut
          (((Functor.whiskeringLeft _ _ FintypeCat).obj (pullback g)).mapAut
            (pullback f ⋙ fiber xi) b) =
        (((Functor.whiskeringLeft _ _ FintypeCat).obj (pullback g)).mapAut
          (fiber (xi ≫ f)) ((pullbackFiberIso f xi).conjAut b)) := by
    apply Aut.ext
    ext C c
    simp only [Iso.conjAut_hom, Iso.conj_apply, NatTrans.comp_app]
    rfl
  unfold fundamentalGroupHom
  simp only [CategoryTheory.PreGaloisCategory.autHomOfCompIso_apply]
  rw [pullbackCompositeFiberIso_conjAut f g xi]
  rw [(pullbackFiberIso g (xi ≫ f)).conjAut.apply_eq_iff_eq]
  have hchain0 := congrArg
    (Functor.associator (pullback g) (pullback f) (fiber xi)).conjAut hpc
  have hchain1 := hchain0.trans hassoc
  have hchain2 := congrArg
    (Functor.isoWhiskerLeft (pullback g) (pullbackFiberIso f xi)).conjAut hchain1
  have hchain3 := hchain2.trans hwhisker
  change (((Functor.whiskeringLeft _ _ FintypeCat).obj (pullback g)).mapAut
      (fiber (xi ≫ f)) ((pullbackFiberIso f xi).conjAut b)) = _
  exact hchain3.symm

/-- The composite pullback comparison transported to specified equal composite
morphisms and equal target geometric points. -/
noncomputable def pullbackCompositeFiberIsoOfEq
    (f : X ⟶ Y) (g : Y ⟶ Z) (m : X ⟶ Z) (hm : m = f ≫ g)
    (xi : Spec (.of Omega) ⟶ X) (eta : Spec (.of Omega) ⟶ Z)
    (heta : (xi ≫ f) ≫ g = eta) :
    pullback m ⋙ fiber xi ≅ fiber eta :=
  Functor.isoWhiskerRight
      (MorphismProperty.Over.pullbackComp
        (P := @IsFiniteEtale) (Q := ⊤) f g m hm)
      (fiber xi) ≪≫
    Functor.associator (pullback g) (pullback f) (fiber xi) ≪≫
    Functor.isoWhiskerLeft (pullback g) (pullbackFiberIso f xi) ≪≫
    pullbackFiberIso g (xi ≫ f) ≪≫
    eqToIso (congrArg fiber heta)

/-- Transporting the target point in a successive fundamental-group map gives
the map induced by the transported composite pullback comparison. -/
theorem fundamentalGroupHom_comp_transport_eq_autHomOfCompIso
    (f : X ⟶ Y) (g : Y ⟶ Z) (m : X ⟶ Z) (hm : m = f ≫ g)
    (xi : Spec (.of Omega) ⟶ X) (eta : Spec (.of Omega) ⟶ Z)
    (heta : (xi ≫ f) ≫ g = eta) (a : π₁ᵉᵗ(xi)) :
    heta ▸ fundamentalGroupHom g (xi ≫ f) (fundamentalGroupHom f xi a) =
      CategoryTheory.PreGaloisCategory.autHomOfCompIso
        (pullback m) (pullbackCompositeFiberIsoOfEq f g m hm xi eta heta) a := by
  subst m
  subst eta
  simpa [pullbackCompositeFiberIsoOfEq, pullbackCompositeFiberIso] using
    fundamentalGroupHom_comp_eq_autHomOfCompIso f g xi a

variable {Y' : Scheme.{u}}

/-- The explicit inner automorphism comparing the fundamental-group maps
obtained from two factorizations of one scheme morphism. -/
noncomputable def fundamentalGroupFactorizationConjugator
    (f₁ : X ⟶ Y) (g₁ : Y ⟶ Z) (f₂ : X ⟶ Y') (g₂ : Y' ⟶ Z)
    (m : X ⟶ Z) (hm₁ : m = f₁ ≫ g₁) (hm₂ : m = f₂ ≫ g₂)
    (xi : Spec (.of Omega) ⟶ X) (eta : Spec (.of Omega) ⟶ Z)
    (heta₁ : (xi ≫ f₁) ≫ g₁ = eta)
    (heta₂ : (xi ≫ f₂) ≫ g₂ = eta) : π₁ᵉᵗ(eta) :=
  (pullbackCompositeFiberIsoOfEq f₂ g₂ m hm₂ xi eta heta₂).symm ≪≫
    pullbackCompositeFiberIsoOfEq f₁ g₁ m hm₁ xi eta heta₁

/-- The maps on fundamental groups associated to two factorizations of one
scheme morphism agree up to the explicit inner automorphism above. -/
theorem fundamentalGroupHom_comp_conj_of_common_composite
    (f₁ : X ⟶ Y) (g₁ : Y ⟶ Z) (f₂ : X ⟶ Y') (g₂ : Y' ⟶ Z)
    (m : X ⟶ Z) (hm₁ : m = f₁ ≫ g₁) (hm₂ : m = f₂ ≫ g₂)
    (xi : Spec (.of Omega) ⟶ X) (eta : Spec (.of Omega) ⟶ Z)
    (heta₁ : (xi ≫ f₁) ≫ g₁ = eta)
    (heta₂ : (xi ≫ f₂) ≫ g₂ = eta) (a : π₁ᵉᵗ(xi)) :
    heta₁ ▸ fundamentalGroupHom g₁ (xi ≫ f₁)
        (fundamentalGroupHom f₁ xi a) =
      MulAut.conj
        (fundamentalGroupFactorizationConjugator
          f₁ g₁ f₂ g₂ m hm₁ hm₂ xi eta heta₁ heta₂)
        (heta₂ ▸ fundamentalGroupHom g₂ (xi ≫ f₂)
          (fundamentalGroupHom f₂ xi a)) := by
  rw [fundamentalGroupHom_comp_transport_eq_autHomOfCompIso
    f₁ g₁ m hm₁ xi eta heta₁]
  rw [fundamentalGroupHom_comp_transport_eq_autHomOfCompIso
    f₂ g₂ m hm₂ xi eta heta₂]
  exact CategoryTheory.PreGaloisCategory.autHomOfCompIso_eq_conj
    (pullback m)
    (pullbackCompositeFiberIsoOfEq f₂ g₂ m hm₂ xi eta heta₂)
    (pullbackCompositeFiberIsoOfEq f₁ g₁ m hm₁ xi eta heta₁) a

end AlgebraicGeometry.FiniteEtale
