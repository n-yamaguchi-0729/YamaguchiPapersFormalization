/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.FiniteEtale.Connected
import EtaleFundamentalGroups.GeometricFiber.FundamentalGroup

/-! # Actual Galois covers over intermediate finite étale schemes

The relative deck transformations are constructed from the original ones.
Their transitivity on each actual geometric fiber proves the Galois property.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.PreGaloisCategory AlgebraicGeometry

namespace AlgebraicGeometry.FiniteEtale

/-- A connected finite étale Galois cover is Galois over every connected
intermediate finite étale scheme. -/
theorem isGalois_over_intermediate
    {S : Scheme.{u}} [ConnectedSpace S]
    (A B : FiniteEtale S) [IsGalois A] [ConnectedSpace B.left]
    (f : A ⟶ B) {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (geom : Spec (.of Ω) ⟶ A.left) :
    IsGalois (C := FiniteEtale B.left) (FiniteEtale.mk f.left) := by
  have : ConnectedSpace A.left := connectedSpace_left_of_isConnected A
  let W : FiniteEtale B.left := FiniteEtale.mk f.left
  have : ConnectedSpace W.left := inferInstanceAs (ConnectedSpace A.left)
  have : IsConnected W := isConnected_of_connectedSpace_left W
  let geomIntermediate : Spec (.of Ω) ⟶ B.left := geom ≫ f.left
  let geomBase : Spec (.of Ω) ⟶ S := geom ≫ A.hom
  apply (isGalois_iff_pretransitive (fiber geomIntermediate) W).2
  constructor
  intro a b
  let za := fiberObjEquivHom geomIntermediate W a
  let zb := fiberObjEquivHom geomIntermediate W b
  have hbase (z : Over.mk geomIntermediate ⟶ W.toComma) : z.left ≫ A.hom = geomBase := by
    calc
      z.left ≫ A.hom = z.left ≫ (f.left ≫ B.hom) :=
        congrArg (z.left ≫ ·) (MorphismProperty.Over.w f).symm
      _ = (z.left ≫ f.left) ≫ B.hom := (Category.assoc _ _ _).symm
      _ = geomIntermediate ≫ B.hom := congrArg (· ≫ B.hom) z.w
      _ = geomBase := (Category.assoc _ _ _).trans
        (congrArg (geom ≫ ·) (MorphismProperty.Over.w f))
  let qa : Over.mk geomBase ⟶ A.toComma := Over.homMk za.left (hbase za)
  let qb : Over.mk geomBase ⟶ A.toComma := Over.homMk zb.left (hbase zb)
  let xa := (fiberObjEquivHom geomBase A).symm qa
  let xb := (fiberObjEquivHom geomBase A).symm qb
  have : MulAction.IsPretransitive (Aut A) ((fiber geomBase).obj A) :=
    (isGalois_iff_pretransitive (fiber geomBase) A).1 inferInstance
  obtain ⟨σ, hσ⟩ := MulAction.exists_smul_eq (Aut A) xa xb
  change (fiber geomBase).map σ.hom xa = xb at hσ
  have hfab : (fiber geomBase).map f xa = (fiber geomBase).map f xb := by
    change (fiber geomBase).map f ((fiberObjEquivHom geomBase A).symm qa) =
      (fiber geomBase).map f ((fiberObjEquivHom geomBase A).symm qb)
    rw [fiberObjEquivHom_symm_naturality, fiberObjEquivHom_symm_naturality]
    apply congrArg (fiberObjEquivHom geomBase B).symm
    apply Over.OverMorphism.ext
    exact za.w.trans zb.w.symm
  have hf : σ.hom ≫ f = f := by
    apply evaluation_injective_of_isConnected (fiber geomBase) A B xa
    change (fiber geomBase).map (σ.hom ≫ f) xa = (fiber geomBase).map f xa
    rw [Functor.map_comp, FintypeCat.comp_apply, hσ]
    exact hfab.symm
  let eσ : A.left ≅ A.left :=
    (FiniteEtale.forget S ⋙ Over.forget S).mapIso σ
  have hσd : eσ.hom ≫ f.left = f.left :=
    congrArg (fun k : A ⟶ B => k.left) hf
  let τ : Aut W := MorphismProperty.Over.isoMk eσ hσd
  refine ⟨τ, ?_⟩
  change (fiber geomIntermediate).map τ.hom a = b
  apply (fiberObjEquivHom geomIntermediate W).injective
  refine (fiberObjEquivHom_naturality geomIntermediate τ.hom a).symm.trans ?_
  apply Over.OverMorphism.ext
  have hσ' : (fiberObjEquivHom geomBase A).symm (qa ≫ σ.hom.hom) =
      (fiberObjEquivHom geomBase A).symm qb := by
    exact (fiberObjEquivHom_symm_naturality geomBase σ.hom qa).symm.trans hσ
  have hpoints := congrArg
    (fun q : Over.mk geomBase ⟶ A.toComma => q.left)
    ((fiberObjEquivHom geomBase A).symm.injective hσ')
  exact hpoints

end AlgebraicGeometry.FiniteEtale
