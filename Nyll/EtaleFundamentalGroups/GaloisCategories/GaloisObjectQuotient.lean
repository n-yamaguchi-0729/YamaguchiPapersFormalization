/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.Pi1.GaloisCategories.FundamentalGroup
public import Mathlib.CategoryTheory.Galois.GaloisObjects
public import Mathlib.CategoryTheory.Galois.Decomposition
public import Mathlib.CategoryTheory.Conj

/-!
# Finite quotients represented by Galois objects

A pointed Galois object identifies its fiber with its categorical
automorphism group.  Since categorical automorphisms act on the right of the
fiber while the fundamental group acts on the left, the resulting quotient
has target the opposite automorphism group.
-/

@[expose] public section

noncomputable section

open CategoryTheory

namespace CategoryTheory.PreGaloisCategory

universe u₁ u₂ w v

variable {C : Type u₁} [Category.{u₂} C]
variable (F : CategoryTheory.Functor C FintypeCat.{w})
  [GaloisCategory C] [FiberFunctor F]
variable (G : Type v) [Group G]
variable [∀ X, MulAction G (F.obj X)] [hNatural : IsNaturalSMul F G]

/-- The quotient represented by a pointed Galois object.  The opposite on
the target records the contravariance of categorical automorphism
multiplication relative to the left fundamental-group action. -/
noncomputable def galoisObjectQuotientMonoidHom
    (A : C) [IsGalois A] (a : F.obj A) : G →* (Aut A)ᵐᵒᵖ := by
  let e := evaluationEquivOfIsGalois F A a
  refine
    { toFun := fun g ↦ MulOpposite.op (e.symm (g • a))
      map_one' := ?_
      map_mul' := ?_ }
  · apply MulOpposite.unop_injective
    apply e.injective
    simp [e]
  · intro g h
    apply MulOpposite.unop_injective
    apply e.injective
    calc
      F.map ((e.symm ((g * h) • a)).asIso.hom) a =
          (g * h) • a :=
        evaluationEquivOfIsGalois_symm_fiber F A a ((g * h) • a)
      _ = g • (h • a) := mul_smul g h a
      _ = g • F.map ((e.symm (h • a)).asIso.hom) a := by
        rw [evaluationEquivOfIsGalois_symm_fiber]
      _ = F.map ((e.symm (h • a)).asIso.hom) (g • a) :=
        (IsNaturalSMul.naturality g (e.symm (h • a)).asIso.hom a).symm
      _ = F.map ((e.symm (g • a)).asIso.hom ≫
          (e.symm (h • a)).asIso.hom) a := by
        rw [F.map_comp, FintypeCat.comp_apply,
          evaluationEquivOfIsGalois_symm_fiber]
      _ = F.map ((e.symm (h • a) * e.symm (g • a)).asIso.hom) a := rfl

include hNatural in
/-- The opposite deck quotient selects the automorphism with the specified value at the point. -/
@[simp]
theorem galoisObjectQuotientMonoidHom_unop_apply
    (A : C) [IsGalois A] (a : F.obj A) (g : G) :
    (galoisObjectQuotientMonoidHom F G A a g).unop =
      (evaluationEquivOfIsGalois F A a).symm (g • a) :=
  rfl

include hNatural in
/-- Evaluating the cover automorphism selected by the quotient recovers the
fundamental-group action on the chosen point. -/
@[simp]
theorem galoisObjectQuotientMonoidHom_evaluation
    (A : C) [IsGalois A] (a : F.obj A) (g : G) :
    F.map ((galoisObjectQuotientMonoidHom F G A a g).unop.asIso.hom) a = g • a := by
  exact evaluationEquivOfIsGalois_symm_fiber F A a (g • a)

/-- The kernel of the finite quotient represented by a pointed Galois object
is exactly the stabilizer of the chosen fiber point. -/
theorem galoisObjectQuotientMonoidHom_ker
    (A : C) [IsGalois A] (a : F.obj A) :
    (galoisObjectQuotientMonoidHom F G A a).ker =
      MulAction.stabilizer G a := by
  ext g
  rw [MonoidHom.mem_ker, MulAction.mem_stabilizer_iff]
  constructor
  · intro hg
    have h := galoisObjectQuotientMonoidHom_evaluation F G A a g
    rw [hg] at h
    simpa using h.symm
  · intro hg
    apply MulOpposite.unop_injective
    apply (evaluationEquivOfIsGalois F A a).injective
    rw [galoisObjectQuotientMonoidHom_unop_apply, hg, Equiv.apply_symm_apply]
    change a = F.map (𝟙 A) a
    simp only [Functor.map_id, FintypeCat.id_apply]

/-- A transitive fundamental-group action makes the quotient represented by
a Galois object surjective. -/
theorem galoisObjectQuotientMonoidHom_surjective
    (A : C) [IsGalois A] (a : F.obj A)
    [MulAction.IsPretransitive G (F.obj A)] :
    Function.Surjective (galoisObjectQuotientMonoidHom F G A a) := by
  intro sigma
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G
    a (F.map sigma.unop.asIso.hom a)
  refine ⟨g, ?_⟩
  apply MulOpposite.unop_injective
  apply (evaluationEquivOfIsGalois F A a).injective
  rw [galoisObjectQuotientMonoidHom_unop_apply, hg, Equiv.apply_symm_apply]
  exact (evaluationEquivOfIsGalois_apply F A a sigma.unop).symm

/-- Pointed finite Galois quotients separate the automorphisms of a fiber
functor. A natural automorphism fixing the fiber of every Galois object fixes
every fiber, since every fiber point is the image of a pointed Galois object. -/
theorem iInf_galoisObjectQuotientMonoidHom_ker :
    (⨅ (A : C) (hA : IsGalois A) (a : F.obj A),
      (let _ : IsGalois A := hA
       galoisObjectQuotientMonoidHom F (Aut F) A a).ker) = ⊥ := by
  apply le_antisymm ?_ bot_le
  intro g hg
  rw [Subgroup.mem_bot]
  apply Aut.ext
  apply Iso.ext
  apply natTrans_ext_of_isGalois F
  intro A hA
  apply FintypeCat.hom_ext
  intro a
  have hfix := (Subgroup.mem_iInf.mp
    (Subgroup.mem_iInf.mp (Subgroup.mem_iInf.mp hg A) hA) a)
  rw [galoisObjectQuotientMonoidHom_ker,
    MulAction.mem_stabilizer_iff] at hfix
  change g • a = a
  exact hfix

include hNatural in
/-- An actual pointed morphism between Galois objects commutes with the
actual deck transformations selected by the same original group element.
The square is proved by evaluation at the source point; deck compatibility
is not an extra premise on the morphism. -/
theorem galoisObjectQuotientMonoidHom_hom_naturality
    (A B : C) [IsGalois A] [IsGalois B] (f : A ⟶ B) (x : F.obj A) (g : G) :
    (galoisObjectQuotientMonoidHom F G A x g).unop.asIso.hom ≫ f =
      f ≫ (galoisObjectQuotientMonoidHom F G B (F.map f x) g).unop.asIso.hom := by
  apply evaluation_injective_of_isConnected F A B x
  simp only [Functor.map_comp, FintypeCat.comp_apply,
    galoisObjectQuotientMonoidHom_evaluation]
  exact IsNaturalSMul.naturality g f x

include hNatural in
/-- Map an actual intertwining point down a Galois domination. Both deck
actions are the quotients represented by the displayed original points;
their compatibility follows from the actual morphism. -/
theorem galoisObjectIntertwiningPoint_map
    {I : Type*} (α β : I → G)
    (A B : C) [IsGalois A] [IsGalois B] (f : A ⟶ B) (x y : F.obj A)
    (hy : ∀ i, β i • y = F.map
      ((galoisObjectQuotientMonoidHom F G A x (α i)).unop.asIso.hom) y) :
    ∀ i, β i • F.map f y = F.map
      ((galoisObjectQuotientMonoidHom F G B (F.map f x) (α i)).unop.asIso.hom)
      (F.map f y) := by
  intro i
  calc
    β i • F.map f y = F.map f (β i • y) := (IsNaturalSMul.naturality (β i) f y).symm
    _ = F.map f (F.map
        ((galoisObjectQuotientMonoidHom F G A x (α i)).unop.asIso.hom) y) :=
      congrArg (F.map f) (hy i)
    _ = F.map
        ((galoisObjectQuotientMonoidHom F G B (F.map f x) (α i)).unop.asIso.hom)
        (F.map f y) := by
      change (F.map ((galoisObjectQuotientMonoidHom F G A x (α i)).unop.asIso.hom) ≫
        F.map f) y = (F.map f ≫
          F.map ((galoisObjectQuotientMonoidHom F G B (F.map f x) (α i)).unop.asIso.hom)) y
      rw [← F.map_comp, ← F.map_comp, galoisObjectQuotientMonoidHom_hom_naturality]

include hNatural in
/-- Point descent preserves membership in the orbit of the same specified
subgroup. Thus the geometric-orbit condition is retained when it was proved
upstairs; an unrestricted orbit is not silently replaced by a geometric one. -/
theorem galoisObjectIntertwiningPoint_map_mem_orbit
    {I : Type*} (α β : I → G) (H : Subgroup G)
    (A B : C) [IsGalois A] [IsGalois B] (f : A ⟶ B) (x y : F.obj A)
    (horbit : y ∈ MulAction.orbit H x)
    (hy : ∀ i, β i • y = F.map
      ((galoisObjectQuotientMonoidHom F G A x (α i)).unop.asIso.hom) y) :
    F.map f y ∈ MulAction.orbit H (F.map f x) ∧
      ∀ i, β i • F.map f y = F.map
        ((galoisObjectQuotientMonoidHom F G B (F.map f x) (α i)).unop.asIso.hom)
        (F.map f y) := by
  refine ⟨?_, galoisObjectIntertwiningPoint_map F G α β A B f x y hy⟩
  obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.mp horbit
  refine MulAction.mem_orbit_iff.mpr ⟨g, ?_⟩
  exact (IsNaturalSMul.naturality g.val f x).symm.trans (congrArg (F.map f) hg)

/-- Changing the actual fiber functor transports both the chosen point and
its original group action, without changing the selected deck automorphism. -/
theorem galoisObjectQuotientMonoidHom_fiberIso
    (F' : C ⥤ FintypeCat.{w}) [FiberFunctor F'] (s : F ≅ F')
    (A : C) [IsGalois A] (x : F.obj A) (g : Aut F) :
    galoisObjectQuotientMonoidHom F' (Aut F') A (s.hom.app A x) (s.conjAut g) =
      galoisObjectQuotientMonoidHom F (Aut F) A x g := by
  apply MulOpposite.unop_injective
  apply (evaluationEquivOfIsGalois F' A (s.hom.app A x)).injective
  change F'.map
      ((galoisObjectQuotientMonoidHom F' (Aut F') A (s.hom.app A x)
        (s.conjAut g)).unop.asIso.hom) (s.hom.app A x) = _
  rw [galoisObjectQuotientMonoidHom_evaluation]
  let d := (galoisObjectQuotientMonoidHom F (Aut F) A x g).unop
  calc
    s.conjAut g • s.hom.app A x = s.hom.app A (g • x) := by
      change s.hom.app A (g.asIso.hom.app A (s.inv.app A (s.hom.app A x))) = _
      have hx : s.inv.app A (s.hom.app A x) = x :=
        ConcreteCategory.congr_hom (s.hom_inv_id_app A) x
      rw [hx]
      rfl
    _ = s.hom.app A (F.map d.asIso.hom x) :=
      congrArg (s.hom.app A) (galoisObjectQuotientMonoidHom_evaluation F (Aut F) A x g).symm
    _ = F'.map d.asIso.hom (s.hom.app A x) := NatTrans.naturality_apply s.hom d.asIso.hom x

end CategoryTheory.PreGaloisCategory
