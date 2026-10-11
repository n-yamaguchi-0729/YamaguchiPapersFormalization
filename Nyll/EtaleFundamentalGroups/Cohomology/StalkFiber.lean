/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Category.Grp.EpiMono
import Mathlib.Algebra.Homology.ShortComplex.Ab
import Mathlib.Algebra.Torsor.Basic
import Mathlib.AlgebraicGeometry.Sites.EtalePoint
import Mathlib.AlgebraicGeometry.Sites.AffineEtale
import Mathlib.CategoryTheory.Sites.Point.Skyscraper

/-!
# Translation torsors in geometric stalks of extensions

A fiber of a short exact sequence of abelian groups is a torsor for its
actual kernel. Applying the exact geometric stalk functor gives this structure
for extensions of étale abelian sheaves. No splitting of the extension is
assumed: a point of each fiber is obtained from the surjective quotient map.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace EtaleFundamentalGroups.Cohomology

variable (S : ShortComplex AddCommGrpCat.{u}) (hS : S.ShortExact) (z : S.X₃)

/-- The fiber of the actual quotient homomorphism in an abelian extension. -/
abbrev abelianExtensionFiber := {e : S.X₂ // S.g e = z}

private def fiberTranslate (a : S.X₁) (e : abelianExtensionFiber S z) :
    abelianExtensionFiber S z :=
  ⟨S.f a + e.val, by rw [map_add, S.ab_zero_apply, zero_add, e.property]⟩

private theorem exists_fiberDifference (hS : S.ShortExact)
    (e f : abelianExtensionFiber S z) :
    ∃ a : S.X₁, S.f a = e.val - f.val := by
  apply (ShortComplex.ab_exact_iff S).mp hS.exact
  rw [map_sub, e.property, f.property, sub_self]

private def fiberDifference (e f : abelianExtensionFiber S z) : S.X₁ :=
  (exists_fiberDifference S z hS e f).choose

private theorem fiberDifference_spec (hS : S.ShortExact)
    (e f : abelianExtensionFiber S z) :
    S.f (fiberDifference S hS z e f) = e.val - f.val :=
  (exists_fiberDifference S z hS e f).choose_spec

/-- Translation and the unique kernel difference make every quotient fiber a
torsor. Both existence and uniqueness use the given short exact sequence. -/
@[instance_reducible]
def abelianExtensionFiberTorsor : AddTorsor S.X₁ (abelianExtensionFiber S z) where
  vadd := fiberTranslate S z
  zero_vadd e := Subtype.ext (by
    change S.f 0 + e.val = e.val
    rw [map_zero, zero_add])
  add_vadd a b e := Subtype.ext (by
    change S.f (a + b) + e.val = S.f a + (S.f b + e.val)
    rw [map_add, add_assoc])
  vsub := fiberDifference S hS z
  nonempty := by
    obtain ⟨e, he⟩ := (AddCommGrpCat.epi_iff_surjective S.g).mp hS.epi_g z
    exact ⟨⟨e, he⟩⟩
  vsub_vadd' e f := Subtype.ext (by
    change S.f (fiberDifference S hS z e f) + f.val = e.val
    rw [fiberDifference_spec S z hS, sub_add_cancel])
  vadd_vsub' a e := by
    apply (AddCommGrpCat.mono_iff_injective S.f).mp hS.mono_f
    exact (fiberDifference_spec S z hS (fiberTranslate S z a e) e).trans
      (add_sub_cancel_right (S.f a) e.val)

/-- The torsor action is the original inclusion followed by addition. -/
theorem abelianExtensionFiberTorsor_vadd (a : S.X₁) (e : abelianExtensionFiber S z) :
    let := abelianExtensionFiberTorsor S hS z
    (a +ᵥ e).val = S.f a + e.val := rfl

/-- Geometric stalks preserve the short exact sequence itself. -/
theorem shortExact_geometricStalk {X : Scheme.{u}} {Ω : Type u}
    [Field Ω] [IsSepClosed Ω] (ξ : Spec (.of Ω) ⟶ X)
    (E : ShortComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}))
    (hE : E.ShortExact) :
    (E.map (Scheme.pointSmallEtale ξ).sheafFiber).ShortExact :=
  hE.map_of_exact (Scheme.pointSmallEtale ξ).sheafFiber

/-- A quotient fiber in the actual geometric stalk is a torsor for the actual
kernel stalk; the required exactness is proved by the stalk functor. -/
@[instance_reducible]
def geometricStalkFiberTorsor {X : Scheme.{u}} {Ω : Type u}
    [Field Ω] [IsSepClosed Ω] (ξ : Spec (.of Ω) ⟶ X)
    (E : ShortComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}))
    (hE : E.ShortExact)
    (z : (Scheme.pointSmallEtale ξ).sheafFiber (A := AddCommGrpCat.{u}) |>.obj E.X₃) :
    AddTorsor ((Scheme.pointSmallEtale ξ).sheafFiber (A := AddCommGrpCat.{u}) |>.obj E.X₁)
      (abelianExtensionFiber (E.map (Scheme.pointSmallEtale ξ).sheafFiber) z) :=
  abelianExtensionFiberTorsor _ (shortExact_geometricStalk ξ E hE) z

/-- Transfer the actual kernel translations along specified coefficient and
fiber isomorphisms. The multiplicative tag permits a group action to commute
with these additive translations without changing the coefficient group. -/
@[instance_reducible]
def extensionFiberTransportTorsor (A : AddCommGrpCat.{u}) (eA : A ≅ S.X₁)
    {P : Type u} (eP : P ≃ abelianExtensionFiber S z) :
    Torsor (Multiplicative A) P := by
  let T := abelianExtensionFiberTorsor S hS z
  exact
    { smul := fun a p => eP.symm (eA.hom a.toAdd +ᵥ eP p)
      one_smul := fun p => eP.injective (by
        change eP (eP.symm (eA.hom 0 +ᵥ eP p)) = eP p
        rw [eP.apply_symm_apply, map_zero, zero_vadd])
      mul_smul := fun a b p => eP.injective (by
        change eP (eP.symm (eA.hom (a.toAdd + b.toAdd) +ᵥ eP p)) =
          eP (eP.symm (eA.hom a.toAdd +ᵥ
            eP (eP.symm (eA.hom b.toAdd +ᵥ eP p))))
        rw [eP.apply_symm_apply, eP.apply_symm_apply, eP.apply_symm_apply,
          map_add, add_vadd])
      sdiv := fun p q => Multiplicative.ofAdd (eA.inv (eP p -ᵥ eP q))
      nonempty := by
        obtain ⟨p⟩ := T.nonempty
        exact ⟨eP.symm p⟩
      sdiv_smul' := fun p q => eP.injective (by
        change eP (eP.symm (eA.hom (eA.inv (eP p -ᵥ eP q)) +ᵥ eP q)) = eP p
        rw [eP.apply_symm_apply, eA.inv_hom_id_apply, vsub_vadd])
      smul_sdiv' := fun a p => by
        change Multiplicative.ofAdd
          (eA.inv (eP (eP.symm (eA.hom a.toAdd +ᵥ eP p)) -ᵥ eP p)) = a
        rw [eP.apply_symm_apply, vadd_vsub, eA.hom_inv_id_apply]
        rfl }

/-- The transferred action still translates by the same original inclusion. -/
theorem extensionFiberTransportTorsor_smul (A : AddCommGrpCat.{u}) (eA : A ≅ S.X₁)
    {P : Type u} (eP : P ≃ abelianExtensionFiber S z) (a : Multiplicative A) (p : P) :
    let := extensionFiberTransportTorsor S hS z A eA eP
    (eP (a • p)).val = S.f (eA.hom a.toAdd) + (eP p).val := by
  change (eP (eP.symm (fiberTranslate S z (eA.hom a.toAdd) (eP p)))).val = _
  rw [eP.apply_symm_apply]
  rfl

end EtaleFundamentalGroups.Cohomology
