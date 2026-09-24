import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Cohomology.EulerCharacteristic.TopComplexFiberEulerChar

/-! # From a cochain complex to a top-down indexed complex

Let `A` be a commutative ring, `K^•` a cochain complex of `A`-modules (indexed by `ℤ`) and
`n ∈ ℕ`. The part of `K` in degrees `≤ n−1` is rewritten as the elementary "top-down indexed"
complex `T := TopCx.ofCochainComplex K n` (`T.X j = K^{n−1−j}`, `T.d j = d^{n−2−j}`). If `K^n = 0`,
then for `i = n−1−j`:
1. the `j`-th (non-base-changed) homology of `T` is finite iff the categorical cohomology `H^i(K)`
   is a finite `A`-module;
2. for every prime `p`, the `j`-th homology of `T ⊗ κ(p)` (`TopCx.hfin`, `TopCx.hdim`, written with
   `LinearMap.baseChange` and quotients `ker/range`) is finite-dimensional iff the categorical
   cohomology `H^i((extendScalars (A → κ(p))).mapHomologicalComplex K)` is, with equal dimensions.

Proof sketch:
1. `HomologicalComplex.homologyIsoSc'`: `H^i(K) ≅ (K.sc' (i−1) i (i+1)).homology`.
2. `ShortComplex.moduleCatHomologyIso`: the homology of a short complex `S` in `ModuleCat` is
   `ker S.g / range S.moduleCatToCycles`, and `range (moduleCatToCycles) = (range S.f).submoduleOf (ker S.g)`,
   so the homology is `LinearMap.midHomology S.f.hom S.g.hom`; finiteness and `finrank` are
   transported along linear isomorphisms.
3. For `j = 0` (`i = n−1`): `K^n = 0` gives `ker (d^{n−1}) = ⊤`, and `midHomology ≃ X_0 / range d_0`.
4. For (2) one also needs the natural isomorphism `e_M : (extendScalars φ).obj M ≃ₗ[κ] κ ⊗[A] M`
   (`φ = algebraMap`; the underlying types agree, but the `A`-module structure of `extendScalars`
   comes from `restrictScalars φ` and is only propositionally equal to `Algebra.toModule`); `e` is
   the identity on pure tensors and `e_N ∘ (extendScalars φ).map f = f.baseChange κ ∘ e_M`;
   `midHomology` is invariant under isomorphisms of three-term diagrams.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits TensorProduct

noncomputable section

/-- The categorical homology of a short complex in `ModuleCat` and the quotient `ker/range` have the
same finiteness and the same dimension. -/
theorem ShortComplex.moduleCat_homology_midHomology {R : Type u} [CommRing R]
    (S : ShortComplex (ModuleCat.{u} R)) :
    (Module.Finite R S.homology ↔ Module.Finite R (LinearMap.midHomology S.f.hom S.g.hom)) ∧
    Module.finrank R S.homology = Module.finrank R (LinearMap.midHomology S.f.hom S.g.hom) := by
  have heq : LinearMap.range S.moduleCatToCycles
      = (LinearMap.range S.f.hom).submoduleOf (LinearMap.ker S.g.hom) := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩; exact ⟨y, rfl⟩
    · rintro ⟨y, hy⟩; exact ⟨y, Subtype.ext hy⟩
  let e : S.homology ≃ₗ[R]
      (LinearMap.ker S.g.hom ⧸ LinearMap.range S.moduleCatToCycles) :=
    S.moduleCatHomologyIso.toLinearEquiv
  unfold LinearMap.midHomology
  rw [← heq]
  exact ⟨⟨fun _ => Module.Finite.equiv e, fun _ => Module.Finite.equiv e.symm⟩, e.finrank_eq⟩

/-- When the outgoing map has full kernel, the middle homology is the cokernel. -/
theorem LinearMap.midHomology_of_ker_eq_top {R : Type u} [CommRing R] {U V W : Type u}
    [AddCommGroup U] [AddCommGroup V] [AddCommGroup W] [Module R U] [Module R V] [Module R W]
    (f : U →ₗ[R] V) (g : V →ₗ[R] W) (hg : LinearMap.ker g = ⊤) :
    (Module.Finite R (LinearMap.midHomology f g) ↔ Module.Finite R (V ⧸ LinearMap.range f)) ∧
    Module.finrank R (LinearMap.midHomology f g) = Module.finrank R (V ⧸ LinearMap.range f) := by
  let e : LinearMap.midHomology f g ≃ₗ[R] (V ⧸ LinearMap.range f) :=
    Submodule.Quotient.equiv _ _ (LinearEquiv.ofTop (LinearMap.ker g) hg) (by
      ext x
      simp only [Submodule.mem_map, Submodule.submoduleOf, Submodule.mem_comap,
        Submodule.subtype_apply]
      constructor
      · rintro ⟨y, hy, rfl⟩; exact hy
      · intro hx; exact ⟨⟨x, by rw [hg]; trivial⟩, hx, rfl⟩)
  exact ⟨⟨fun _ => Module.Finite.equiv e, fun _ => Module.Finite.equiv e.symm⟩, e.finrank_eq⟩

/-- Transport of a three-term diagram along linear isomorphisms: finiteness and dimension of the
middle homology are unchanged. -/
theorem LinearMap.midHomology_of_equiv {R : Type u} [CommRing R] {U V W U' V' W' : Type u}
    [AddCommGroup U] [AddCommGroup V] [AddCommGroup W] [Module R U] [Module R V] [Module R W]
    [AddCommGroup U'] [AddCommGroup V'] [AddCommGroup W'] [Module R U'] [Module R V'] [Module R W']
    (f : U →ₗ[R] V) (g : V →ₗ[R] W) (f' : U' →ₗ[R] V') (g' : V' →ₗ[R] W')
    (eU : U ≃ₗ[R] U') (eV : V ≃ₗ[R] V') (eW : W ≃ₗ[R] W')
    (h1 : ∀ x, eV (f x) = f' (eU x)) (h2 : ∀ x, eW (g x) = g' (eV x)) :
    (Module.Finite R (LinearMap.midHomology f g) ↔ Module.Finite R (LinearMap.midHomology f' g')) ∧
    Module.finrank R (LinearMap.midHomology f g) = Module.finrank R (LinearMap.midHomology f' g') := by
  have hker : (LinearMap.ker g).map (eV : V →ₗ[R] V') = LinearMap.ker g' := by
    ext y
    simp only [Submodule.mem_map, LinearMap.mem_ker, LinearEquiv.coe_coe]
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [← h2, hx, map_zero]
    · intro hy
      refine ⟨eV.symm y, ?_, eV.apply_symm_apply y⟩
      apply eW.injective
      rw [h2, eV.apply_symm_apply, hy, map_zero]
  let eK : LinearMap.ker g ≃ₗ[R] LinearMap.ker g' := eV.ofSubmodules _ _ hker
  have hmap : ((LinearMap.range f).submoduleOf (LinearMap.ker g)).map (eK : _ →ₗ[R] _)
      = (LinearMap.range f').submoduleOf (LinearMap.ker g') := by
    ext y
    simp only [Submodule.mem_map, Submodule.submoduleOf, Submodule.mem_comap,
      Submodule.subtype_apply, LinearEquiv.coe_coe, LinearMap.mem_range]
    constructor
    · rintro ⟨x, ⟨u, hu⟩, rfl⟩
      refine ⟨eU u, ?_⟩
      rw [← h1, hu]; rfl
    · rintro ⟨u', hu'⟩
      refine ⟨eK.symm y, ⟨eU.symm u', ?_⟩, eK.apply_symm_apply y⟩
      apply eV.injective
      rw [h1, eU.apply_symm_apply, hu']
      exact (congrArg Subtype.val (eK.apply_symm_apply y)).symm
  let e : LinearMap.midHomology f g ≃ₗ[R] LinearMap.midHomology f' g' :=
    Submodule.Quotient.equiv _ _ eK hmap
  exact ⟨⟨fun _ => Module.Finite.equiv e, fun _ => Module.Finite.equiv e.symm⟩, e.finrank_eq⟩

/-- Cokernel version of `LinearMap.midHomology_of_equiv`. -/
theorem LinearMap.cokernel_of_equiv {R : Type u} [CommRing R] {U V U' V' : Type u}
    [AddCommGroup U] [AddCommGroup V] [Module R U] [Module R V]
    [AddCommGroup U'] [AddCommGroup V'] [Module R U'] [Module R V']
    (f : U →ₗ[R] V) (f' : U' →ₗ[R] V') (eU : U ≃ₗ[R] U') (eV : V ≃ₗ[R] V')
    (h1 : ∀ x, eV (f x) = f' (eU x)) :
    (Module.Finite R (V ⧸ LinearMap.range f) ↔ Module.Finite R (V' ⧸ LinearMap.range f')) ∧
    Module.finrank R (V ⧸ LinearMap.range f) = Module.finrank R (V' ⧸ LinearMap.range f') := by
  have hmap : (LinearMap.range f).map (eV : V →ₗ[R] V') = LinearMap.range f' := by
    ext y
    simp only [Submodule.mem_map, LinearMap.mem_range, LinearEquiv.coe_coe]
    constructor
    · rintro ⟨_, ⟨u, rfl⟩, rfl⟩; exact ⟨eU u, (h1 u).symm⟩
    · rintro ⟨u', rfl⟩
      exact ⟨f (eU.symm u'), ⟨_, rfl⟩, by rw [h1, eU.apply_symm_apply]⟩
  let e : (V ⧸ LinearMap.range f) ≃ₗ[R] (V' ⧸ LinearMap.range f') :=
    Submodule.Quotient.equiv _ _ eV hmap
  exact ⟨⟨fun _ => Module.Finite.equiv e, fun _ => Module.Finite.equiv e.symm⟩, e.finrank_eq⟩

section ExtendScalarsEquiv

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]

/-- The identity, as an `R`-linear isomorphism between `S` with scalars restricted along
`algebraMap` and `S` with the module structure `Algebra.toModule`. -/
def ModuleCat.restrictScalarsSelfEquiv :
    ((ModuleCat.restrictScalars (algebraMap R S)).obj (ModuleCat.of S S)) ≃ₗ[R] S where
  toFun x := x
  invFun x := x
  map_add' _ _ := rfl
  map_smul' r x := (Algebra.smul_def r (show S from x)).symm
  left_inv _ := rfl
  right_inv _ := rfl

/-- The underlying `R`-linear isomorphism (the identity on pure tensors). -/
def ModuleCat.extendScalarsEquivAux (M : ModuleCat.{u} R) :
    (TensorProduct R ((ModuleCat.restrictScalars (algebraMap R S)).obj (ModuleCat.of S S)) M)
      ≃ₗ[R] S ⊗[R] M :=
  TensorProduct.congr ModuleCat.restrictScalarsSelfEquiv (LinearEquiv.refl R M)

/-- (extendScalars (algebraMap R S)).obj M ≃ₗ[S] S ⊗[R] M -/
def ModuleCat.extendScalarsEquiv (M : ModuleCat.{u} R) :
    ((ModuleCat.extendScalars (algebraMap R S)).obj M) ≃ₗ[S] S ⊗[R] M where
  toFun x := ModuleCat.extendScalarsEquivAux M x
  invFun y := (ModuleCat.extendScalarsEquivAux M).symm y
  map_add' x y := (ModuleCat.extendScalarsEquivAux M).map_add x y
  map_smul' s x := by
    induction x using TensorProduct.induction_on with
    | zero =>
      exact (congrArg (ModuleCat.extendScalarsEquivAux M)
        (smul_zero (A := (ModuleCat.extendScalars (algebraMap R S)).obj M) s)).trans
        ((ModuleCat.extendScalarsEquivAux M).map_zero.trans ((smul_zero s).symm.trans
          (congrArg (s • ·) (ModuleCat.extendScalarsEquivAux M).map_zero.symm)))
    | tmul s' m => rfl
    | add x y hx hy =>
      exact (congrArg (ModuleCat.extendScalarsEquivAux M)
        (smul_add (A := (ModuleCat.extendScalars (algebraMap R S)).obj M) s x y)).trans
        (((ModuleCat.extendScalarsEquivAux M).map_add _ _).trans
          ((congrArg₂ (· + ·) hx hy).trans ((smul_add s _ _).symm.trans
            (congrArg (s • ·) ((ModuleCat.extendScalarsEquivAux M).map_add x y).symm))))
  left_inv x := (ModuleCat.extendScalarsEquivAux M).symm_apply_apply x
  right_inv y := (ModuleCat.extendScalarsEquivAux M).apply_symm_apply y

theorem ModuleCat.extendScalarsEquiv_naturality {M N : ModuleCat.{u} R} (g : M ⟶ N)
    (x : (ModuleCat.extendScalars (algebraMap R S)).obj M) :
    ModuleCat.extendScalarsEquiv N (((ModuleCat.extendScalars (algebraMap R S)).map g).hom x)
      = (g.hom.baseChange S) (ModuleCat.extendScalarsEquiv M x) := by
  induction x using TensorProduct.induction_on with
  | zero =>
    have h1 := map_zero ((ModuleCat.extendScalarsEquiv (S := S) N).toLinearMap ∘ₗ
      ((ModuleCat.extendScalars (algebraMap R S)).map g).hom)
    have h2 := map_zero ((g.hom.baseChange S) ∘ₗ (ModuleCat.extendScalarsEquiv (S := S) M).toLinearMap)
    exact h1.trans h2.symm
  | tmul s m => rfl
  | add x y hx hy =>
    have h1 := map_add ((ModuleCat.extendScalarsEquiv (S := S) N).toLinearMap ∘ₗ
      ((ModuleCat.extendScalars (algebraMap R S)).map g).hom)
      (x : (ModuleCat.extendScalars (algebraMap R S)).obj M) y
    have h2 := map_add ((g.hom.baseChange S) ∘ₗ (ModuleCat.extendScalarsEquiv (S := S) M).toLinearMap)
      (x : (ModuleCat.extendScalars (algebraMap R S)).obj M) y
    exact h1.trans ((congrArg₂ (· + ·) hx hy).trans h2.symm)

end ExtendScalarsEquiv

/-- The part of a cochain complex in degrees `≤ n−1`, indexed from the top down. -/
def TopCx.ofCochainComplex {A : CommRingCat.{u}} (K : CochainComplex (ModuleCat.{u} A) ℤ) (n : ℕ) :
    TopCx A where
  X j := K.X ((n : ℤ) - 1 - (j : ℤ))
  d j := (K.d ((n : ℤ) - 1 - ((j + 1 : ℕ) : ℤ)) ((n : ℤ) - 1 - (j : ℤ))).hom
  d_comp j := by
    ext x
    have := K.d_comp_d ((n : ℤ) - 1 - ((j + 1 + 1 : ℕ) : ℤ)) ((n : ℤ) - 1 - ((j + 1 : ℕ) : ℤ))
      ((n : ℤ) - 1 - (j : ℤ))
    exact congrArg (fun f => f.hom x) this

namespace TopCx

variable {A : CommRingCat.{u}} (K : CochainComplex (ModuleCat.{u} A) ℤ) (n : ℕ)

theorem ofCochainComplex_flat (hflat : ∀ i, Module.Flat A (K.X i)) (j : ℕ) :
    Module.Flat A ((ofCochainComplex K n).X j) := hflat _

theorem ofCochainComplex_subsingleton (hbdd : ∀ i : ℤ, (i < 0 ∨ (n : ℤ) ≤ i) → IsZero (K.X i))
    (j : ℕ) (hj : n < j) : Subsingleton ((ofCochainComplex K n).X j) :=
  ModuleCat.subsingleton_of_isZero (hbdd _ (Or.inl (by omega)))

/-- The homology of a `ℤ`-indexed cochain complex is the homology of the three-term short complex. -/
theorem homology_sc'_fin {R : Type u} [CommRing R] (L : CochainComplex (ModuleCat.{u} R) ℤ)
    (a b c : ℤ) (hab : a + 1 = b) (hbc : b + 1 = c) :
    (Module.Finite R (L.homology b) ↔
      Module.Finite R (LinearMap.midHomology (L.d a b).hom (L.d b c).hom)) ∧
    Module.finrank R (L.homology b) =
      Module.finrank R (LinearMap.midHomology (L.d a b).hom (L.d b c).hom) := by
  let e : L.homology b ≃ₗ[R] (L.sc' a b c).homology :=
    (L.homologyIsoSc' a b c (by simp; omega) (by simp; omega)).toLinearEquiv
  obtain ⟨h1, h2⟩ := ShortComplex.moduleCat_homology_midHomology (L.sc' a b c)
  exact ⟨⟨fun _ => h1.mp (Module.Finite.equiv e), fun h => by
    have := h1.mpr h; exact Module.Finite.equiv e.symm⟩, e.finrank_eq.trans h2⟩

/-- (1) Finiteness of the non-base-changed homology. -/
theorem ofCochainComplex_fin0 (hn : IsZero (K.X n)) (j : ℕ) :
    (ofCochainComplex K n).fin0 j ↔ Module.Finite A (K.homology ((n : ℤ) - 1 - (j : ℤ))) := by
  cases j with
  | zero =>
    have hc : IsZero (K.X ((n : ℤ) - 1 - ((0 : ℕ) : ℤ) + 1)) := by
      have : ((n : ℤ) - 1 - ((0 : ℕ) : ℤ) + 1) = n := by simp
      rw [this]; exact hn
    have := ModuleCat.subsingleton_of_isZero hc
    have hker : LinearMap.ker (K.d ((n : ℤ) - 1 - ((0 : ℕ) : ℤ))
        ((n : ℤ) - 1 - ((0 : ℕ) : ℤ) + 1)).hom = ⊤ := by
      ext x; simp [Subsingleton.elim _ (0 : K.X ((n : ℤ) - 1 - ((0 : ℕ) : ℤ) + 1))]
    rw [(homology_sc'_fin K ((n : ℤ) - 1 - ((0 + 1 : ℕ) : ℤ)) ((n : ℤ) - 1 - ((0 : ℕ) : ℤ))
      ((n : ℤ) - 1 - ((0 : ℕ) : ℤ) + 1) (by push_cast; ring) rfl).1,
      (LinearMap.midHomology_of_ker_eq_top _ _ hker).1]
    exact Iff.rfl
  | succ j =>
    rw [(homology_sc'_fin K ((n : ℤ) - 1 - ((j + 1 + 1 : ℕ) : ℤ)) ((n : ℤ) - 1 - ((j + 1 : ℕ) : ℤ))
      ((n : ℤ) - 1 - (j : ℤ)) (by push_cast; ring) (by push_cast; ring)).1]
    exact Iff.rfl

/-- (2) Homology after base change to `κ(p)`: finite-dimensionality and dimension. -/
theorem ofCochainComplex_hfin_hdim (hn : IsZero (K.X n)) (p : PrimeSpectrum A) (j : ℕ) :
    ((ofCochainComplex K n).hfin p.asIdeal.ResidueField j ↔
      Module.Finite p.asIdeal.ResidueField
        ((((ModuleCat.extendScalars (CommRingCat.ofHom
          (algebraMap A p.asIdeal.ResidueField)).hom).mapHomologicalComplex _).obj K).homology
            ((n : ℤ) - 1 - (j : ℤ)))) ∧
    (ofCochainComplex K n).hdim p.asIdeal.ResidueField j =
      Module.finrank p.asIdeal.ResidueField
        ((((ModuleCat.extendScalars (CommRingCat.ofHom
          (algebraMap A p.asIdeal.ResidueField)).hom).mapHomologicalComplex _).obj K).homology
            ((n : ℤ) - 1 - (j : ℤ))) := by
  let κ := p.asIdeal.ResidueField
  let L := ((ModuleCat.extendScalars (CommRingCat.ofHom
    (algebraMap A κ)).hom).mapHomologicalComplex (ComplexShape.up ℤ)).obj K
  let e := fun M : ModuleCat.{u} A => ModuleCat.extendScalarsEquiv (R := A) (S := κ) M
  have hnat : ∀ {M N : ModuleCat.{u} A} (g : M ⟶ N) (x),
      e N (((ModuleCat.extendScalars (algebraMap A κ)).map g).hom x)
        = (g.hom.baseChange κ) (e M x) := fun g x => ModuleCat.extendScalarsEquiv_naturality g x
  cases j with
  | zero =>
    have hc : IsZero (L.X ((n : ℤ) - 1 - ((0 : ℕ) : ℤ) + 1)) := by
      have : ((n : ℤ) - 1 - ((0 : ℕ) : ℤ) + 1) = n := by simp
      rw [this]
      exact (ModuleCat.extendScalars _).map_isZero hn
    have := ModuleCat.subsingleton_of_isZero hc
    have hker : LinearMap.ker (L.d ((n : ℤ) - 1 - ((0 : ℕ) : ℤ))
        ((n : ℤ) - 1 - ((0 : ℕ) : ℤ) + 1)).hom = ⊤ := by
      ext x; simp [Subsingleton.elim _ (0 : L.X ((n : ℤ) - 1 - ((0 : ℕ) : ℤ) + 1))]
    obtain ⟨f1, f2⟩ := homology_sc'_fin L ((n : ℤ) - 1 - ((0 + 1 : ℕ) : ℤ))
      ((n : ℤ) - 1 - ((0 : ℕ) : ℤ)) ((n : ℤ) - 1 - ((0 : ℕ) : ℤ) + 1) (by push_cast; ring) rfl
    obtain ⟨g1, g2⟩ := LinearMap.midHomology_of_ker_eq_top
      (L.d ((n : ℤ) - 1 - ((0 + 1 : ℕ) : ℤ)) ((n : ℤ) - 1 - ((0 : ℕ) : ℤ))).hom _ hker
    obtain ⟨k1, k2⟩ := LinearMap.cokernel_of_equiv
      (L.d ((n : ℤ) - 1 - ((0 + 1 : ℕ) : ℤ)) ((n : ℤ) - 1 - ((0 : ℕ) : ℤ))).hom
      ((K.d ((n : ℤ) - 1 - ((0 + 1 : ℕ) : ℤ)) ((n : ℤ) - 1 - ((0 : ℕ) : ℤ))).hom.baseChange κ)
      (e _) (e _) (fun x => hnat _ x)
    exact ⟨(f1.trans (g1.trans k1)).symm, (f2.trans (g2.trans k2)).symm⟩
  | succ j =>
    obtain ⟨f1, f2⟩ := homology_sc'_fin L ((n : ℤ) - 1 - ((j + 1 + 1 : ℕ) : ℤ))
      ((n : ℤ) - 1 - ((j + 1 : ℕ) : ℤ)) ((n : ℤ) - 1 - (j : ℤ))
      (by push_cast; ring) (by push_cast; ring)
    obtain ⟨k1, k2⟩ := LinearMap.midHomology_of_equiv
      (L.d ((n : ℤ) - 1 - ((j + 1 + 1 : ℕ) : ℤ)) ((n : ℤ) - 1 - ((j + 1 : ℕ) : ℤ))).hom
      (L.d ((n : ℤ) - 1 - ((j + 1 : ℕ) : ℤ)) ((n : ℤ) - 1 - (j : ℤ))).hom
      ((K.d ((n : ℤ) - 1 - ((j + 1 + 1 : ℕ) : ℤ)) ((n : ℤ) - 1 - ((j + 1 : ℕ) : ℤ))).hom.baseChange κ)
      ((K.d ((n : ℤ) - 1 - ((j + 1 : ℕ) : ℤ)) ((n : ℤ) - 1 - (j : ℤ))).hom.baseChange κ)
      (e _) (e _) (e _) (fun x => hnat _ x) (fun x => hnat _ x)
    exact ⟨(f1.trans k1).symm, (f2.trans k2).symm⟩

end TopCx

end
