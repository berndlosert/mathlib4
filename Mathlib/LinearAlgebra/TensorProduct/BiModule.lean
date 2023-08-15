/-
Copyright (c) 2023 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/

import Mathlib.LinearAlgebra.TensorProduct
import Mathlib.RingTheory.TensorProduct

/-! # Structure of A ⊗[R] B module on a tensor product -/


section General

variable {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]
  {M : Type*} [AddCommMonoid M] [Module R M]

def moduleOfRingHom (f : A →+* (M →ₗ[R] M)) : Module A M := {
  smul := fun a x ↦ f a x
  one_smul := fun x ↦ by
    change f 1 x = x
    simp only [map_one, LinearMap.one_apply]
  mul_smul := fun a a' x ↦ by
    change f (a * a') x = f a (f a' x)
    simp only [map_mul, LinearMap.mul_apply]
  smul_zero := fun a ↦ by
    change f a 0 = 0
    simp only [LinearMap.map_zero]
  smul_add := fun a x y ↦ by
    change f a (x + y) = f a x + f a y
    simp only [map_add]
  add_smul := fun a a' x ↦ by
    change f (a + a') x = f a x + f a' x
    simp only [map_add, LinearMap.add_apply]
  zero_smul := fun x ↦ by
    change f 0 x = 0
    simp only [map_zero, LinearMap.zero_apply] }


section TensorProduct
variable {R A B : Type*} [CommSemiring R] [Ring A] [Ring B]
  [Algebra R A] [Algebra R B]
  {M N : Type*} [AddCommMonoid M] [AddCommMonoid N]
  [Module R M] [Module A M] [IsScalarTower R A M]
  [Module R N] [Module B N] [IsScalarTower R B N]

open scoped TensorProduct

def toFun_aux (a : A) (b : B) : M ⊗[R] N →ₗ[R] M ⊗[R] N := by
  apply TensorProduct.lift
  apply LinearMap.mk₂ R (fun m n ↦ (a • m) ⊗ₜ[R] (b • n))
  · intro m m' n
    simp only [smul_add, TensorProduct.add_tmul]
  · intro r m n
    rw [TensorProduct.smul_tmul', smul_algebra_smul_comm]
  · intro m n n'
    simp only [smul_add, TensorProduct.tmul_add]
  · intro r m n
    rw [← TensorProduct.tmul_smul r, smul_algebra_smul_comm]

@[simp]
def toFun_aux_apply (a : A) (b: B) (m : M) (n : N) :
    toFun_aux a b (m ⊗ₜ[R] n) = (a • m) ⊗ₜ[R] (b • n) := rfl

def TensorProduct.moduleMap' : (A ⊗[R] B) →ₗ[R] (M ⊗[R] N) →ₗ[R] (M ⊗[R] N) := by
  apply TensorProduct.lift
  apply LinearMap.mk₂ R toFun_aux
  · intro a a' b
    apply TensorProduct.ext'
    intro m n
    simp only [toFun_aux_apply, LinearMap.add_apply, add_smul, TensorProduct.add_tmul]
  · intro r a b
    apply TensorProduct.ext'
    intro m n
    simp only [toFun_aux_apply, smul_assoc, LinearMap.smul_apply, TensorProduct.smul_tmul']
  · intro a b b'
    apply TensorProduct.ext'
    intro m n
    simp only [toFun_aux_apply, LinearMap.add_apply, add_smul, TensorProduct.tmul_add]
  · intro r a b
    apply TensorProduct.ext'
    intro m n
    simp only [toFun_aux_apply, smul_assoc, TensorProduct.tmul_smul, LinearMap.smul_apply]

def Algebra.TensorProduct.moduleMap : (A ⊗[R] B) →ₐ[R] (M ⊗[R] N) →ₗ[R] (M ⊗[R] N) := by
  apply Algebra.TensorProduct.algHomOfLinearMapTensorProduct
    (TensorProduct.moduleMap') -- (TensorProduct.moduleMap' R A B M N)
  · intro a a' b b'
    simp only [TensorProduct.moduleMap', TensorProduct.lift.tmul, LinearMap.mk₂_apply]
    apply _root_.TensorProduct.ext'
    intro m n
    simp only [toFun_aux_apply, LinearMap.mul_apply, mul_smul]
  · intro r
    simp only [TensorProduct.moduleMap', TensorProduct.lift.tmul, LinearMap.mk₂_apply]
    apply _root_.TensorProduct.ext'
    intro m n
    simp only [toFun_aux_apply, algebraMap_smul, one_smul, Module.algebraMap_end_apply]
    exact rfl

def Algebra.TensorProduct.module : Module (A ⊗[R] B) (M ⊗[R] N) :=
  moduleOfRingHom (Algebra.TensorProduct.moduleMap.toRingHom)

lemma TensorProduct.lift_mk₂ (R : Type*) [CommSemiring R]
    {M Nₗ Pₗ : Type*} [AddCommMonoid M] [AddCommMonoid Nₗ] [AddCommMonoid Pₗ]
    [Module R M] [Module R Nₗ] [Module R Pₗ]
    (f : M → Nₗ → Pₗ)
    (H1 : ∀ (m₁ m₂ : M) (n : Nₗ), f (m₁ + m₂) n = f m₁ n + f m₂ n)
    (H2 : ∀ (c : R) (m : M) (n : Nₗ), f (c • m) n = c • f m n)
    (H3 : ∀ (m : M) (n₁ n₂ : Nₗ), f m (n₁ + n₂) = f m n₁ + f m n₂)
    (H4 : ∀ (c : R) (m : M) (n : Nₗ), f m (c • n) = c • f m n)
    (m : M) (n : Nₗ) :
    TensorProduct.lift (LinearMap.mk₂ R f H1 H2 H3 H4) (m ⊗ₜ[R] n) = f m n := rfl

section

variable {P : Type*} [AddCommMonoid P] [Module R P]

local instance : Module (A ⊗[R] B) (M ⊗[R] N) := Algebra.TensorProduct.module

lemma Algebra.TensorProduct.moduleMap_smul_eq (c : A ⊗[R] B) (z : M ⊗[R] N) :
  c • z = Algebra.TensorProduct.moduleMap (R := R) (A := A) (B := B) (M := M) (N := N) c z := rfl

lemma Algebra.TensorProduct.moduleMap_smul_tmul (a : A) (b : B) (m : M) (n : N) :
    (a ⊗ₜ[R] b) • (m ⊗ₜ[R] n) = (a • m) ⊗ₜ[R] (b • n) := rfl

lemma isLinearMapHomothety (a : A) : IsLinearMap R (fun (z : M ⊗[R] N) ↦ a • z) := by
  apply IsLinearMap.mk
  · intro x y
    simp only [smul_add]
  · intro r x
    exact smul_algebra_smul_comm r a x

lemma isLinearMapHomothety₂ (c : A ⊗[R] B) :
    IsLinearMap R (fun (z : M ⊗[R] N) ↦ c • z) := by
  apply IsLinearMap.mk
  · intro x y
    simp only [smul_add]
  · intro r z
    rw [Algebra.TensorProduct.moduleMap_smul_eq]
    rw [map_smul]
    rfl




lemma Algebra.TensorProduct.isScalarTowerModule :
  IsScalarTower A (A ⊗[R] B) (M ⊗[R] N) := by
  apply IsScalarTower.mk
  intro a c z
  suffices : a • c = a ⊗ₜ[R] 1 * c
  rw [this, mul_smul]
  generalize c • z = y
  simp only [Algebra.TensorProduct.moduleMap_smul_eq]
  conv_rhs => rw [← IsLinearMap.mk'_apply (isLinearMapHomothety a)]
  revert y
  rw [← LinearMap.ext_iff]
  dsimp only
  ext m n
  dsimp
  rw [← Algebra.TensorProduct.moduleMap_smul_eq,  Algebra.TensorProduct.moduleMap_smul_tmul]
  simp only [one_smul]
  rfl
  · induction c using TensorProduct.induction_on with
    | zero =>
        simp only [smul_zero, mul_zero]
    | tmul x y =>
        simp only [tmul_mul_tmul, one_mul]
        rfl
    | add x y hx hy =>
        simp only [smul_add, mul_add, hx, hy]

lemma Algebra.TensorProduct.isScalarTowerModule' :
  IsScalarTower R (A ⊗[R] B) (M ⊗[R] N) := by
  apply IsScalarTower.mk
  intro r c z
  suffices : r • c = (r • (1: A)) • c
  rw [this]
  rw [Algebra.TensorProduct.isScalarTowerModule.smul_assoc]
  simp only [smul_assoc, one_smul]
  simp only [smul_assoc, one_smul]


end
