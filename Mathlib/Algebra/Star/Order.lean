/-
Copyright (c) 2023 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.Algebra.Star.Basic
import Mathlib.GroupTheory.Submonoid.Basic

#align_import algebra.star.order from "leanprover-community/mathlib"@"31c24aa72e7b3e5ed97a8412470e904f82b81004"

/-! # Star ordered rings

We define the class `StarOrderedRing R`, which says that the order on `R` respects the
star operation, i.e. an element `r` is nonnegative iff it is in the `AddSubmonoid` generated by
elements of the form `star s * s`. In many cases, including all C⋆-algebras, this can be reduced to
`0 ≤ r ↔ ∃ s, r = star s * s`. However, this generality is slightly more convenient (e.g., it
allows us to register a `StarOrderedRing` instance for `ℚ`), and more closely resembles the
literature (see the seminal paper [*The positive cone in Banach algebras*][kelleyVaught1953])

In order to accommodate `NonUnitalSemiring R`, we actually don't characterize nonnegativity, but
rather the entire `≤` relation with `StarOrderedRing.le_iff`. However, notice that when `R` is a
`NonUnitalRing`, these are equivalent (see `StarOrderedRing.nonneg_iff` and
`StarOrderedRing.ofNonnegIff`).

It is important to note that while a `StarOrderedRing` is an `OrderedAddCommMonoid` it is often
*not* an `OrderedSemiring`.

## TODO

* In a Banach star algebra without a well-defined square root, the natural ordering is given by the
positive cone which is the _closure_ of the sums of elements `star r * r`. A weaker version of
`StarOrderedRing` could be defined for this case (again, see
[*The positive cone in Banach algebras*][kelleyVaught1953]). Note that the current definition has
the advantage of not requiring a topology.
-/

universe u

variable {R : Type u}

/-- An ordered `*`-ring is a `*`ring with a partial order such that the nonnegative elements
constitute precisely the `AddSubmonoid` generated by elements of the form `star s * s`.

If you are working with a `NonUnitalRing` and not a `NonUnitalSemiring`, it may be more
convenient to declare instances using `StarOrderedRing.ofNonnegIff'`.

Porting note: dropped an unneeded assumption
`add_le_add_left : ∀ {x y}, x ≤ y → ∀ z, z + x ≤ z + y` -/
class StarOrderedRing (R : Type u) [NonUnitalSemiring R] [PartialOrder R] extends StarRing R where
  /-- characterization of the order in terms of the `StarRing` structure. -/
  le_iff :
    ∀ x y : R, x ≤ y ↔ ∃ p, p ∈ AddSubmonoid.closure (Set.range fun s => star s * s) ∧ y = x + p
#align star_ordered_ring StarOrderedRing
attribute [instance 200] StarOrderedRing.toStarRing

namespace StarOrderedRing

-- see note [lower instance priority]
instance (priority := 100) toOrderedAddCommMonoid [NonUnitalSemiring R] [PartialOrder R]
    [StarOrderedRing R] : OrderedAddCommMonoid R where
  add_le_add_left := fun x y hle z ↦ by
    rw [StarOrderedRing.le_iff] at hle ⊢
    refine hle.imp fun s hs ↦ ?_
    rw [hs.2, add_assoc]
    exact ⟨hs.1, rfl⟩
#align star_ordered_ring.to_ordered_add_comm_monoid StarOrderedRing.toOrderedAddCommMonoid

-- see note [lower instance priority]
instance (priority := 100) toExistsAddOfLE [NonUnitalSemiring R] [PartialOrder R]
    [StarOrderedRing R] : ExistsAddOfLE R where
  exists_add_of_le h :=
    match (le_iff _ _).mp h with
    | ⟨p, _, hp⟩ => ⟨p, hp⟩
#align star_ordered_ring.to_has_exists_add_of_le StarOrderedRing.toExistsAddOfLE

-- see note [lower instance priority]
instance (priority := 100) toOrderedAddCommGroup [NonUnitalRing R] [PartialOrder R]
    [StarOrderedRing R] : OrderedAddCommGroup R where
  add_le_add_left := @add_le_add_left _ _ _ _

#align star_ordered_ring.to_ordered_add_comm_group StarOrderedRing.toOrderedAddCommGroup

-- set note [reducible non-instances]
/-- To construct a `StarOrderedRing` instance it suffices to show that `x ≤ y` if and only if
`y = x + star s * s` for some `s : R`.

This is provided for convenience because it holds in some common scenarios (e.g.,`ℝ≥0`, `C(X, ℝ≥0)`)
and obviates the hassle of `AddSubmonoid.closure_induction` when creating those instances.

If you are working with a `NonUnitalRing` and not a `NonUnitalSemiring`, see
`StarOrderedRing.ofNonnegIff` for a more convenient version.
 -/
@[reducible]
def ofLeIff [NonUnitalSemiring R] [PartialOrder R] [StarRing R]
    (h_le_iff : ∀ x y : R, x ≤ y ↔ ∃ s, y = x + star s * s) : StarOrderedRing R where
  le_iff := fun x y => by
    refine' ⟨fun h => _, _⟩
    · obtain ⟨p, hp⟩ := (h_le_iff x y).mp h
      exact ⟨star p * p, AddSubmonoid.subset_closure ⟨p, rfl⟩, hp⟩
    · rintro ⟨p, hp, hpxy⟩
      revert x y hpxy
      refine' AddSubmonoid.closure_induction hp _ (fun x y h => add_zero x ▸ h.ge) _
      · rintro _ ⟨s, rfl⟩ x y rfl
        exact (h_le_iff _ _).mpr ⟨s, rfl⟩
      · rintro a b ha hb x y rfl
        rw [← add_assoc]
        exact (ha _ _ rfl).trans (hb _ _ rfl)
#align star_ordered_ring.of_le_iff StarOrderedRing.ofLeIffₓ

-- set note [reducible non-instances]
/-- When `R` is a non-unital ring, to construct a `StarOrderedRing` instance it suffices to
show that the nonnegative elements are precisely those elements in the `AddSubmonoid` generated
by `star s * s` for `s : R`. -/
@[reducible]
def ofNonnegIff [NonUnitalRing R] [PartialOrder R] [StarRing R]
    (h_add : ∀ {x y : R}, x ≤ y → ∀ z, z + x ≤ z + y)
    (h_nonneg_iff : ∀ x : R, 0 ≤ x ↔ x ∈ AddSubmonoid.closure (Set.range fun s : R => star s * s)) :
    StarOrderedRing R where
  le_iff := fun x y => by
    haveI : CovariantClass R R (· + ·) (· ≤ ·) := ⟨fun _ _ _ h => h_add h _⟩
    simpa only [← sub_eq_iff_eq_add', sub_nonneg, exists_eq_right'] using h_nonneg_iff (y - x)
#align star_ordered_ring.of_nonneg_iff StarOrderedRing.ofNonnegIff

-- set note [reducible non-instances]
/-- When `R` is a non-unital ring, to construct a `StarOrderedRing` instance it suffices to
show that the nonnegative elements are precisely those elements of the form `star s * s`
for `s : R`.

This is provided for convenience because it holds in many common scenarios (e.g.,`ℝ`, `ℂ`, or
any C⋆-algebra), and obviates the hassle of `AddSubmonoid.closure_induction` when creating those
instances. -/
@[reducible]
def ofNonnegIff' [NonUnitalRing R] [PartialOrder R] [StarRing R]
    (h_add : ∀ {x y : R}, x ≤ y → ∀ z, z + x ≤ z + y)
    (h_nonneg_iff : ∀ x : R, 0 ≤ x ↔ ∃ s, x = star s * s) : StarOrderedRing R :=
  ofLeIff <| by
    haveI : CovariantClass R R (· + ·) (· ≤ ·) := ⟨fun _ _ _ h => h_add h _⟩
    simpa [sub_eq_iff_eq_add', sub_nonneg] using fun x y => h_nonneg_iff (y - x)
#align star_ordered_ring.of_nonneg_iff' StarOrderedRing.ofNonnegIff'

theorem nonneg_iff [NonUnitalSemiring R] [PartialOrder R] [StarOrderedRing R] {x : R} :
    0 ≤ x ↔ x ∈ AddSubmonoid.closure (Set.range fun s : R => star s * s) := by
  simp only [le_iff, zero_add, exists_eq_right']
#align star_ordered_ring.nonneg_iff StarOrderedRing.nonneg_iff

end StarOrderedRing

section NonUnitalSemiring

variable [NonUnitalSemiring R] [PartialOrder R] [StarOrderedRing R]

theorem star_mul_self_nonneg (r : R) : 0 ≤ star r * r :=
  StarOrderedRing.nonneg_iff.mpr <| AddSubmonoid.subset_closure ⟨r, rfl⟩
#align star_mul_self_nonneg star_mul_self_nonneg

theorem star_mul_self_nonneg' (r : R) : 0 ≤ r * star r := by
  simpa only [star_star] using star_mul_self_nonneg (star r)
#align star_mul_self_nonneg' star_mul_self_nonneg'

theorem conjugate_nonneg {a : R} (ha : 0 ≤ a) (c : R) : 0 ≤ star c * a * c := by
  rw [StarOrderedRing.nonneg_iff] at ha
  refine' AddSubmonoid.closure_induction ha (fun x hx => _)
    (by rw [MulZeroClass.mul_zero, MulZeroClass.zero_mul]) fun x y hx hy => _
  · obtain ⟨x, rfl⟩ := hx
    convert star_mul_self_nonneg (x * c) using 1
    rw [star_mul, ← mul_assoc, mul_assoc _ _ c]
  · calc
      0 ≤ star c * x * c + 0 := by rw [add_zero]; exact hx
      _ ≤ star c * x * c + star c * y * c := add_le_add_left hy _
      _ ≤ _ := by rw [mul_add, add_mul]
#align conjugate_nonneg conjugate_nonneg

theorem conjugate_nonneg' {a : R} (ha : 0 ≤ a) (c : R) : 0 ≤ c * a * star c := by
  simpa only [star_star] using conjugate_nonneg ha (star c)
#align conjugate_nonneg' conjugate_nonneg'

theorem conjugate_le_conjugate {a b : R} (hab : a ≤ b) (c : R) :
    star c * a * c ≤ star c * b * c := by
  rw [StarOrderedRing.le_iff] at hab ⊢
  obtain ⟨p, hp, rfl⟩ := hab
  simp_rw [← StarOrderedRing.nonneg_iff] at hp ⊢
  exact ⟨star c * p * c, conjugate_nonneg hp c, by simp only [add_mul, mul_add]⟩
#align conjugate_le_conjugate conjugate_le_conjugate

theorem conjugate_le_conjugate' {a b : R} (hab : a ≤ b) (c : R) : c * a * star c ≤ c * b * star c :=
  by simpa only [star_star] using conjugate_le_conjugate hab (star c)
#align conjugate_le_conjugate' conjugate_le_conjugate'

end NonUnitalSemiring
