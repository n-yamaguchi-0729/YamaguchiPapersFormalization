/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.FieldTheory.IsSepClosed
import Mathlib.FieldTheory.PurelyInseparable.Basic

/-!
# Automorphisms of a normal extension and its relative separable closure

Restriction is surjective by normality. It is injective because a purely
inseparable extension admits at most one extension of a field embedding.
For an algebraic closure this is the residue-automorphism identification in
Stacks Project, Tag 0BUB.

Reference: https://stacks.math.columbia.edu/tag/0BUB
-/

noncomputable section

namespace EtaleFundamentalGroups.Inertia

universe u v w

/-- Equality over a purely inseparable subfield is checked on the actual
underlying field maps. The lower automorphism base is independent of that
subfield, so this owner needs no scalar tower through it. -/
private theorem algEquiv_eq_of_agree_on_purelyInseparable_base
    {k : Type u} {E : Type v} (F : Type w)
    [Field k] [Field E] [Field F] [Algebra k E] [Algebra F E]
    [IsPurelyInseparable F E]
    (σ τ : Gal(E/k))
    (h : ∀ x : F, σ (algebraMap F E x) = τ (algebraMap F E x)) : σ = τ := by
  have hcomp : σ.toRingHom.comp (algebraMap F E) =
      τ.toRingHom.comp (algebraMap F E) := RingHom.ext h
  have heq : σ.toRingHom = τ.toRingHom :=
    IsPurelyInseparable.injective_comp_algebraMap F E E hcomp
  exact AlgEquiv.ext (fun x : E => DFunLike.congr_fun heq x)

/-- Restriction to the actual relative separable closure retains the
ambient coefficient. This field-only computation owns the scalar tower. -/
theorem separableClosure_restrictNormal_coefficient
    (k : Type u) (E : Type v) [Field k] [Field E] [Algebra k E] [Normal k E]
    (σ : E ≃ₐ[k] E) (z : separableClosure k E) :
    ((σ.restrictNormal (separableClosure k E)).toRingHom.toFun z).val =
      σ.toRingHom.toFun z.val :=
  AlgEquiv.restrictNormal_commutes σ (separableClosure k E) z

/-- Restriction to the relative separable closure is injective, including
in positive characteristic and without a perfectness hypothesis. -/
theorem separableClosure_restrictNormalHom_injective
    (k : Type u) (E : Type v) [Field k] [Field E] [Algebra k E] [Normal k E] :
    Function.Injective (AlgEquiv.restrictNormalHom (separableClosure k E) :
      Gal(E/k) →* Gal(separableClosure k E/k)) := by
  intro σ τ h
  apply algEquiv_eq_of_agree_on_purelyInseparable_base (separableClosure k E) σ τ
  intro x
  rw [← AlgEquiv.restrictNormal_commutes σ (separableClosure k E) x,
    ← AlgEquiv.restrictNormal_commutes τ (separableClosure k E) x]
  exact congrArg (algebraMap (separableClosure k E) E) (DFunLike.congr_fun h x)

/-- The canonical restriction isomorphism used to replace automorphisms
of the algebraic residue closure by its separable Galois group. -/
def separableClosureAutEquiv
    (k : Type u) (E : Type v) [Field k] [Field E] [Algebra k E] [Normal k E] :
    Gal(E/k) ≃* Gal(separableClosure k E/k) :=
  MulEquiv.ofBijective (AlgEquiv.restrictNormalHom (separableClosure k E))
    ⟨separableClosure_restrictNormalHom_injective k E,
      AlgEquiv.restrictNormalHom_surjective (F := k) (K₁ := separableClosure k E) E⟩

end EtaleFundamentalGroups.Inertia

end
