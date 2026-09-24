import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.IdealSheaf.IdealSheafStalkIdeal
import MiyaokaMori.AlgebraicGeometry.Modules.IdealSheaf.IdealSheafStalkIdealBasic
import MiyaokaMori.AlgebraicGeometry.Modules.IdealSheaf.IdealSheafStalkIdealEqMapGerm

/-! # Global sections of `O_X/J` without quotient sheaves

For an ideal sheaf `J` on a scheme `X` we package the **compatible families**
`(s_U)_U`, `s_U ∈ Γ(X, U)/J(U)`, indexed by *all* affine opens `U` and compatible under
restriction, as a `Γ(X, ⊤)`-module `J.quotFamilies`. For a quasi-coherent `J` this is
`Γ(X, O_X/J)` (sheaf condition on the basis of affine opens), but we never need that: every
statement about `quotFamilies` is checked on affine opens and stalks directly.

Also: the germ `quotFamilies J → O_{X,x}/J_x` (independent of the affine open used), the
submodule `J.subFamilies K` of families with `s_U ∈ K(U)/J(U)` ("sections of `K/J`"), and the
stalk pieces `J.stalkPiece K x = K_x/J_x ⊆ O_{X,x}/J_x` together with the `Γ(X, ⊤)`-linear germ
map `J.subFamiliesGerm K T : subFamilies → Π_{x ∈ T} K_x/J_x`.

Used in the length inequality of Stacks 0AGT: there `J = I·O_X`, `K = E^d` and `Γ(X, ⊤)` acts
through `A → Γ(X, O_X)`.

The `Γ(X, ⊤)`-algebra structures on `Γ(X, U)` and on the stalks are **scoped instances**
(`open scoped AlgebraicGeometry.Scheme.IdealSheafData.QuotFamilies0agt`), not global ones.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X : AlgebraicGeometry.Scheme.{u}}

namespace QuotFamilies0agt

/-- `Γ(X, U)` as a `Γ(X, ⊤)`-algebra through restriction (scoped instance). -/
scoped instance algebraTopSections (U : X.Opens) : Algebra Γ(X, ⊤) Γ(X, U) :=
  (X.presheaf.map (homOfLE le_top).op).hom.toAlgebra

/-- `O_{X,x}` as a `Γ(X, ⊤)`-algebra through the germ at `x` (scoped instance). -/
scoped instance algebraTopStalk (x : X) : Algebra Γ(X, ⊤) (X.presheaf.stalk x) :=
  (X.presheaf.germ ⊤ x trivial).hom.toAlgebra

end QuotFamilies0agt

open scoped QuotFamilies0agt

theorem algebraMap_topSections_apply (U : X.Opens) (r : Γ(X, ⊤)) :
    algebraMap Γ(X, ⊤) Γ(X, U) r = X.presheaf.map (homOfLE le_top).op r := rfl

theorem algebraMap_topStalk_apply (x : X) (r : Γ(X, ⊤)) :
    algebraMap Γ(X, ⊤) (X.presheaf.stalk x) r = X.presheaf.germ ⊤ x trivial r := rfl

/-- Restriction `Γ(X, V) → Γ(X, U)` (`U ≤ V`) as a `Γ(X, ⊤)`-algebra map. -/
def resAlgHom {U V : X.Opens} (h : U ≤ V) : Γ(X, V) →ₐ[Γ(X, ⊤)] Γ(X, U) where
  toRingHom := (X.presheaf.map (homOfLE h).op).hom
  commutes' r := by
    show X.presheaf.map (homOfLE h).op (X.presheaf.map (homOfLE le_top).op r) =
      X.presheaf.map (homOfLE le_top).op r
    rw [← CommRingCat.comp_apply, ← Functor.map_comp, ← op_comp, homOfLE_comp]

theorem resAlgHom_apply {U V : X.Opens} (h : U ≤ V) (t : Γ(X, V)) :
    resAlgHom h t = X.presheaf.map (homOfLE h).op t := rfl

/-- The germ `Γ(X, U) → O_{X,x}` as a `Γ(X, ⊤)`-algebra map. -/
def germAlgHom (U : X.Opens) (x : X) (hx : x ∈ U) : Γ(X, U) →ₐ[Γ(X, ⊤)] X.presheaf.stalk x where
  toRingHom := (X.presheaf.germ U x hx).hom
  commutes' r := by
    show X.presheaf.germ U x hx (X.presheaf.map (homOfLE le_top).op r) =
      X.presheaf.germ ⊤ x trivial r
    rw [← CommRingCat.comp_apply, X.presheaf.germ_res]

theorem germAlgHom_apply (U : X.Opens) (x : X) (hx : x ∈ U) (t : Γ(X, U)) :
    germAlgHom U x hx t = X.presheaf.germ U x hx t := rfl

variable (J : X.IdealSheafData)

/-- Restriction `Γ(X, V)/J(V) → Γ(X, U)/J(U)` for affine opens `U ≤ V`. -/
def quotRes {U V : X.affineOpens} (h : U ≤ V) :
    Γ(X, V) ⧸ J.ideal V →ₐ[Γ(X, ⊤)] Γ(X, U) ⧸ J.ideal U :=
  Ideal.quotientMapₐ (J.ideal U) (resAlgHom (X := X) (U := U.1) (V := V.1) h)
    (J.ideal_le_comap_ideal h)

theorem quotRes_mk {U V : X.affineOpens} (h : U ≤ V) (t : Γ(X, V)) :
    J.quotRes h (Ideal.Quotient.mk (J.ideal V) t) =
      Ideal.Quotient.mk (J.ideal U) (X.presheaf.map (homOfLE h).op t) := rfl

theorem quotRes_quotRes {U V W : X.affineOpens} (h₁ : U ≤ V) (h₂ : V ≤ W)
    (s : Γ(X, W) ⧸ J.ideal W) :
    J.quotRes h₁ (J.quotRes h₂ s) = J.quotRes (h₁.trans h₂) s := by
  obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective s
  rw [quotRes_mk, quotRes_mk, quotRes_mk]
  congr 1
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

/-- **Compatible families** `(s_U)_U`, `s_U ∈ Γ(X, U)/J(U)` over all affine opens `U`, as a
`Γ(X, ⊤)`-submodule of the product. For quasi-coherent `J` this is `Γ(X, O_X/J)`. -/
def quotFamilies : Submodule Γ(X, ⊤) (∀ U : X.affineOpens, Γ(X, U) ⧸ J.ideal U) where
  carrier := {s | ∀ (U V : X.affineOpens) (h : U ≤ V), J.quotRes h (s V) = s U}
  zero_mem' := fun U V h => by simp
  add_mem' := fun {s t} hs ht U V h => by
    show J.quotRes h (s V + t V) = s U + t U
    rw [map_add, hs U V h, ht U V h]
  smul_mem' := fun r {s} hs U V h => by
    simp only [Pi.smul_apply, map_smul, hs U V h]

theorem quotFamilies_compat (s : J.quotFamilies) {U V : X.affineOpens} (h : U ≤ V) :
    J.quotRes h (s.1 V) = s.1 U := s.2 U V h

/-- `Γ(X, ⊤) → quotFamilies J`, `r ↦ (r|_U mod J(U))_U`. -/
def toQuotFamilies : Γ(X, ⊤) →ₗ[Γ(X, ⊤)] J.quotFamilies where
  toFun r := ⟨fun U => algebraMap Γ(X, ⊤) (Γ(X, U) ⧸ J.ideal U) r,
    fun U V h => (J.quotRes h).commutes r⟩
  map_add' r r' := Subtype.ext (funext fun U => by simp only [map_add]; rfl)
  map_smul' r r' := Subtype.ext (funext fun U => by
    simp only [smul_eq_mul, map_mul, RingHom.id_apply, Submodule.coe_smul, Pi.smul_apply,
      Algebra.smul_def])

theorem toQuotFamilies_apply_coe (r : Γ(X, ⊤)) (U : X.affineOpens) :
    (J.toQuotFamilies r).1 U = Ideal.Quotient.mk (J.ideal U) (X.presheaf.map (homOfLE le_top).op r) :=
  rfl

/-! ### Germs -/

theorem ideal_le_comap_stalkIdeal (U : X.affineOpens) {x : X} (hx : x ∈ U.1) :
    J.ideal U ≤ (J.stalkIdeal x).comap (X.presheaf.germ U.1 x hx).hom := by
  rw [J.stalkIdeal_eq_map_germ x U hx]
  exact Ideal.le_comap_map

/-- The germ `Γ(X, U)/J(U) → O_{X,x}/J_x` at `x ∈ U`. -/
def quotGerm (U : X.affineOpens) {x : X} (hx : x ∈ U.1) :
    Γ(X, U) ⧸ J.ideal U →ₐ[Γ(X, ⊤)] X.presheaf.stalk x ⧸ J.stalkIdeal x :=
  Ideal.quotientMapₐ (J.stalkIdeal x) (germAlgHom (X := X) U.1 x hx) (J.ideal_le_comap_stalkIdeal U hx)

theorem quotGerm_mk (U : X.affineOpens) {x : X} (hx : x ∈ U.1) (t : Γ(X, U)) :
    J.quotGerm U hx (Ideal.Quotient.mk (J.ideal U) t) =
      Ideal.Quotient.mk (J.stalkIdeal x) (X.presheaf.germ U.1 x hx t) := rfl

theorem quotGerm_quotRes {U V : X.affineOpens} (h : U ≤ V) {x : X} (hx : x ∈ U.1)
    (s : Γ(X, V) ⧸ J.ideal V) :
    J.quotGerm U hx (J.quotRes h s) = J.quotGerm V (h hx) s := by
  obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective s
  rw [quotRes_mk, quotGerm_mk, quotGerm_mk]
  congr 1
  exact X.presheaf.germ_res_apply (homOfLE h) x hx t

/-- An affine open containing `x` (chosen once and for all). -/
def affineOpenOf (x : X) : X.affineOpens := (X.exists_affineOpens_mem x).choose

theorem mem_affineOpenOf (x : X) : x ∈ (affineOpenOf x).1 := (X.exists_affineOpens_mem x).choose_spec

/-- The germ of a compatible family at `x`, as a `Γ(X, ⊤)`-linear map to `O_{X,x}/J_x`. -/
def germ (x : X) : J.quotFamilies →ₗ[Γ(X, ⊤)] X.presheaf.stalk x ⧸ J.stalkIdeal x :=
  (J.quotGerm (affineOpenOf x) (mem_affineOpenOf x)).toLinearMap ∘ₗ
    (LinearMap.proj (affineOpenOf x) ∘ₗ J.quotFamilies.subtype)

/-- The germ can be computed on any affine open containing `x`. -/
theorem germ_eq (s : J.quotFamilies) {x : X} (U : X.affineOpens) (hx : x ∈ U.1) :
    J.germ x s = J.quotGerm U hx (s.1 U) := by
  -- an affine open `W ∋ x` inside `U ⊓ affineOpenOf x`
  obtain ⟨_, ⟨W, hW, rfl⟩, hxW, hWle⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
    (show x ∈ (U.1 ⊓ (affineOpenOf x).1 : X.Opens) from ⟨hx, mem_affineOpenOf x⟩)
    (U.1 ⊓ (affineOpenOf x).1).isOpen
  have hWU : (⟨W, hW⟩ : X.affineOpens) ≤ U := fun y hy => (hWle hy).1
  have hWU₀ : (⟨W, hW⟩ : X.affineOpens) ≤ affineOpenOf x := fun y hy => (hWle hy).2
  show J.quotGerm (affineOpenOf x) (mem_affineOpenOf x) (s.1 (affineOpenOf x)) = J.quotGerm U hx (s.1 U)
  rw [← J.quotGerm_quotRes hWU₀ hxW, J.quotFamilies_compat s hWU₀,
    ← J.quotGerm_quotRes hWU hxW, J.quotFamilies_compat s hWU]

theorem germ_toQuotFamilies (r : Γ(X, ⊤)) (x : X) :
    J.germ x (J.toQuotFamilies r) = algebraMap Γ(X, ⊤) (X.presheaf.stalk x ⧸ J.stalkIdeal x) r := by
  rw [germ_eq J _ (affineOpenOf x) (mem_affineOpenOf x), toQuotFamilies_apply_coe]
  exact (J.quotGerm (affineOpenOf x) (mem_affineOpenOf x)).commutes r

/-! ### Sections of `K/J` inside `O_X/J` -/

variable (K : X.IdealSheafData)

/-- Families with `s_U ∈ K(U)/J(U)` for every affine `U`: "global sections of `K/J`". -/
def subFamilies : Submodule Γ(X, ⊤) J.quotFamilies where
  carrier := {s | ∀ U : X.affineOpens, s.1 U ∈ Submodule.map (J.ideal U).mkQ (K.ideal U)}
  zero_mem' := fun U => by simp
  add_mem' := fun {s t} hs ht U => by
    simpa only [Submodule.coe_add, Pi.add_apply] using Submodule.add_mem _ (hs U) (ht U)
  smul_mem' := fun r {s} hs U => by
    show r • s.1 U ∈ _
    rw [← algebraMap_smul Γ(X, U) r]
    exact Submodule.smul_mem _ _ (hs U)

theorem mem_subFamilies {s : J.quotFamilies} :
    s ∈ J.subFamilies K ↔ ∀ U : X.affineOpens, s.1 U ∈ Submodule.map (J.ideal U).mkQ (K.ideal U) := Iff.rfl

/-- The stalk piece `K_x/J_x ⊆ O_{X,x}/J_x`. -/
def stalkPiece (x : X) : Submodule (X.presheaf.stalk x) (X.presheaf.stalk x ⧸ J.stalkIdeal x) :=
  Submodule.map (J.stalkIdeal x).mkQ (K.stalkIdeal x)

theorem germ_mem_stalkPiece {s : J.quotFamilies} (hs : s ∈ J.subFamilies K) (x : X) :
    J.germ x s ∈ J.stalkPiece K x := by
  rw [J.germ_eq s (affineOpenOf x) (mem_affineOpenOf x)]
  obtain ⟨k, hk, hks⟩ := (Submodule.mem_map).1 (hs (affineOpenOf x))
  rw [← hks]
  show J.quotGerm _ _ (Ideal.Quotient.mk _ k) ∈ _
  rw [quotGerm_mk]
  refine Submodule.mem_map_of_mem ?_
  rw [K.stalkIdeal_eq_map_germ x (affineOpenOf x) (mem_affineOpenOf x)]
  exact Ideal.mem_map_of_mem _ hk

/-- The `Γ(X, ⊤)`-linear germ map `subFamilies J K → Π_{x ∈ T} K_x/J_x`. -/
def subFamiliesGerm (T : Finset X) :
    J.subFamilies K →ₗ[Γ(X, ⊤)] ∀ x : T, ((J.stalkPiece K x.1).restrictScalars Γ(X, ⊤)) :=
  LinearMap.pi fun x => LinearMap.codRestrict ((J.stalkPiece K x.1).restrictScalars Γ(X, ⊤))
    (J.germ x.1 ∘ₗ (J.subFamilies K).subtype) fun s => J.germ_mem_stalkPiece K s.2 x.1

theorem subFamiliesGerm_apply_coe (T : Finset X) (s : J.subFamilies K) (x : T) :
    ((J.subFamiliesGerm K T s x : (J.stalkPiece K x.1).restrictScalars Γ(X, ⊤)) :
      X.presheaf.stalk x.1 ⧸ J.stalkIdeal x.1) = J.germ x.1 s.1 := rfl

/-- Length comparison: the length of a stalk piece over `O_{X,x}` is at most its length over
`Γ(X, ⊤)` (every `O_{X,x}`-submodule is a `Γ(X, ⊤)`-submodule). -/
theorem length_stalkPiece_le_length_restrictScalars (x : X) :
    Module.length (X.presheaf.stalk x) (J.stalkPiece K x) ≤
      Module.length Γ(X, ⊤) ((J.stalkPiece K x).restrictScalars Γ(X, ⊤)) :=
  Submodule.length_le_length_restrictScalars Γ(X, ⊤) (J.stalkPiece K x)

end AlgebraicGeometry.Scheme.IdealSheafData

end
