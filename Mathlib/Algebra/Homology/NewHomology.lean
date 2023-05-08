import Mathlib.Algebra.Homology.ShortComplex.Homology
import Mathlib.Algebra.Homology.HomologicalComplex

open CategoryTheory Category Limits

variable (C : Type _) [Category C] [HasZeroMorphisms C] {ι : Type _} (c : ComplexShape ι)

namespace HomologicalComplex

@[simps]
def shortComplexFunctor' (i j k : ι) : HomologicalComplex C c ⥤ ShortComplex C where
  obj K := ShortComplex.mk (K.d i j) (K.d j k) (K.d_comp_d i j k)
  map f :=
    { τ₁ := f.f i
      τ₂ := f.f j
      τ₃ := f.f k }

@[simps!]
noncomputable def shortComplexFunctor (i : ι) :=
  shortComplexFunctor' C c (c.prev i) i (c.next i)

variable {C c}
variable (K L M : HomologicalComplex C c) (φ : K ⟶ L) (ψ : L ⟶ M)

abbrev sc' (i j k : ι) := (shortComplexFunctor' C c i j k).obj K
noncomputable abbrev sc (i : ι) := (shortComplexFunctor C c i).obj K

abbrev HasHomology (i : ι) := (K.sc i).HasHomology

section

variable (i : ι) [K.HasHomology i] [L.HasHomology i] [M.HasHomology i]

noncomputable def newHomology := (K.sc i).homology
noncomputable def newCycles := (K.sc i).cycles
noncomputable def homologyπ : K.newCycles i ⟶ K.newHomology i := (K.sc i).homologyπ
noncomputable def iCycles : K.newCycles i ⟶ K.X i := (K.sc i).iCycles

variable {i}

noncomputable def liftCycles {A : C} (k : A ⟶ K.X i) (j : ι) (hj : c.next i = j)
    (hk : k ≫ K.d i j = 0) : A ⟶ K.newCycles i :=
  (K.sc i).liftCycles k (by subst hj ; exact hk)

@[reducible]
noncomputable def liftCycles' {A : C} (k : A ⟶ K.X i) (j : ι) (hj : c.Rel i j)
    (hk : k ≫ K.d i j = 0) : A ⟶ K.newCycles i :=
  K.liftCycles k j (c.next_eq' hj) hk

@[reassoc (attr := simp)]
lemma liftCycles_i {A : C} (k : A ⟶ K.X i) (j : ι) (hj : c.next i = j)
    (hk : k ≫ K.d i j = 0) : K.liftCycles k j hj hk ≫ K.iCycles i = k := by
  dsimp [liftCycles, iCycles]
  simp

noncomputable def toCycles (i j : ι) [K.HasHomology j] :
  K.X i ⟶ K.newCycles j :=
  K.liftCycles (K.d i j) (c.next j) rfl (K.d_comp_d _ _ _)

variable (i)

@[reassoc (attr := simp)]
lemma iCycles_d (j : ι) : K.iCycles i ≫ K.d i j = 0 := by
  by_cases hij : c.Rel i j
  . obtain rfl := c.next_eq' hij
    exact (K.sc i).iCycles_g
  . rw [K.shape _ _ hij, comp_zero]

@[reassoc (attr := simp)]
lemma toCycles_i (i j : ι) [K.HasHomology j] :
    K.toCycles i j ≫ K.iCycles j = K.d i j :=
  liftCycles_i _ _ _ _ _

instance [K.HasHomology i] : Mono (K.iCycles i) := by
  dsimp only [iCycles]
  infer_instance

instance [K.HasHomology i] : Epi (K.homologyπ i) := by
  dsimp only [homologyπ]
  infer_instance

variable {i}

@[reassoc]
lemma liftCycles_homologyπ_eq_zero_of_boundary {A : C} (k : A ⟶ K.X i) (j : ι)
    (hj : c.next i = j) {i' : ι} (x : A ⟶ K.X i') (hx : k = x ≫ K.d i' i) :
    K.liftCycles k j hj (by rw [hx, assoc, K.d_comp_d, comp_zero]) ≫ K.homologyπ i = 0 := by
  by_cases c.Rel i' i
  . obtain rfl := c.prev_eq' h
    exact (K.sc i).liftCycles_homologyπ_eq_zero_of_boundary _ x hx
  . have : liftCycles K k j hj (by rw [hx, assoc, K.d_comp_d, comp_zero]) = 0 := by
      rw [K.shape _ _ h, comp_zero] at hx
      rw [← cancel_mono (K.iCycles i), zero_comp, liftCycles_i, hx]
    rw [this, zero_comp]

@[reassoc (attr := simp)]
lemma toCycles_comp_homology_π (i j : ι) [K.HasHomology j]:
    K.toCycles i j ≫ K.homologyπ j = 0 :=
  K.liftCycles_homologyπ_eq_zero_of_boundary (K.d i j) (c.next j) rfl (𝟙 _) (by simp)

variable {K L M} (i)

noncomputable def homologyMap : K.newHomology i ⟶ L.newHomology i :=
  ShortComplex.homologyMap ((shortComplexFunctor C c i).map φ)

variable (K)

@[simp]
lemma homologyMap_id : homologyMap (𝟙 K) i = 𝟙 _ :=
  ShortComplex.homologyMap_id _

@[reassoc (attr := simp)]
lemma homologyMap_comp : homologyMap (φ ≫ ψ) i = homologyMap φ i ≫ homologyMap ψ i := by
  dsimp [homologyMap]
  rw [Functor.map_comp, ShortComplex.homologyMap_comp]

variable (C c)

@[simps]
noncomputable def newHomologyFunctor [CategoryWithHomology C] : HomologicalComplex C c ⥤ C where
  obj K := K.newHomology i
  map f := homologyMap f i

/- TODO : adapt more of the homology of ShortComplex API to this situation, including the
dual versions cyclesCo, etc... -/

end

end HomologicalComplex
