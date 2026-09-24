import MiyaokaMori.Prelude

/-! # Charts `D₊(a)` under `Proj.fromOfGlobalSections`

**Absolute-Proj facts** (Stacks 01O4 (2), 01MN; Mathlib `AlgebraicGeometry/ProjectiveSpectrum/Basic.lean`) used for
the immersion of a relative Proj into a projective bundle (Stacks 07RM, paragraph 5). Throughout, `A` is a graded ring with
grading `𝒜`, `Y` a scheme, `Φ : A →+* Γ(Y, ⊤)` a ring map whose image of the irrelevant ideal generates the unit
ideal, and `φ := Proj.fromOfGlobalSections 𝒜 Φ hΦ : Y ⟶ Proj 𝒜` (Stacks 01O4: the morphism "`y ↦ [Φ(-)(y)]`").
`j : Proj 𝒜 ⟶ P` is an arbitrary open immersion (in the application, the chart `π⁻¹V ≅ Proj A(V) ↪ Proj_S 𝒮`).

* `preimage_image_basicOpen`: `(φ ≫ j)⁻¹(j(D₊(a))) = Y.basicOpen (Φ a)` for `a` homogeneous of positive
  degree — Mathlib `fromOfGlobalSections_preimage_basicOpen` and `j⁻¹(j(U)) = U`.
* `isAffineOpen_image_basicOpen`: `j(D₊(a))` is affine (Mathlib `Proj.isAffineOpen_basicOpen`, image of an
  affine open under an open immersion).
* `comp_appLE_image_appIso_inv`: the ring map of `φ ≫ j` on the chart `j(D₊(a))` is the ring map of `φ` on
  `D₊(a)`, once a section of `P` over `j(D₊(a))` is read through `j.appIso` as a section of `Proj 𝒜` over `D₊(a)`.
* `fromOfGlobalSections_appLE_awayToSection_mk_mul`:
  the ring map `Γ(D₊(a), O) = A_{(a)} → Γ(O, O_Y)` of `φ` (for `O ≤ φ⁻¹D₊(a) = Y.basicOpen (Φ a)`) sends the
  degree-zero fraction `b / a^k` (`b ∈ 𝒜 (k·d)`, `a ∈ 𝒜 d`) to the element `g` with `g · Φ(a)^k = Φ(b)` in `Γ(O, O_Y)`
  — this pins `g` down because `Φ(a)` is a unit on `Y.basicOpen (Φ a)`. Proof: through the ring map
  `θ : Γ(Y,⊤)[1/Φa] → Γ(Y, Y.basicOpen (Φ a))` induced by the first three factors of Mathlib's
  `toBasicOpenOfGlobalSections` (`awayToBasicOpenSections`, with `θ(r/1) = r|`), `φ.appLE` on `D₊(a)` is
  `θ ∘ IsLocalization.map Φ ∘ val` (`fromOfGlobalSections_appLE_awayToSection`), and `mk' x y · (y/1) = x/1`. -/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.Proj

variable {A : Type u} [CommRing A] {σ : Type u} [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜]
  {Y P : AlgebraicGeometry.Scheme.{u}} (Φ : A →+* Γ(Y, ⊤))
  (hΦ : (HomogeneousIdeal.irrelevant 𝒜).toIdeal.map Φ = ⊤)

/-- `(φ ≫ j)⁻¹(j(D₊(a))) = Y.basicOpen (Φ a)` for `a ∈ 𝒜 n`, `0 < n`, `j` an open immersion. -/
theorem fromOfGlobalSections_comp_preimage_image_basicOpen (j : AlgebraicGeometry.Proj 𝒜 ⟶ P)
    [AlgebraicGeometry.IsOpenImmersion j] {a : A} {n : ℕ} (hn : 0 < n) (ha : a ∈ 𝒜 n) :
    (AlgebraicGeometry.Proj.fromOfGlobalSections 𝒜 Φ hΦ ≫ j) ⁻¹ᵁ (j ''ᵁ AlgebraicGeometry.Proj.basicOpen 𝒜 a) =
      Y.basicOpen (Φ a) := by
  have h : (AlgebraicGeometry.Proj.fromOfGlobalSections 𝒜 Φ hΦ ≫ j) ⁻¹ᵁ
      (j ''ᵁ AlgebraicGeometry.Proj.basicOpen 𝒜 a) =
      AlgebraicGeometry.Proj.fromOfGlobalSections 𝒜 Φ hΦ ⁻¹ᵁ
        (j ⁻¹ᵁ (j ''ᵁ AlgebraicGeometry.Proj.basicOpen 𝒜 a)) := rfl
  rw [h, j.preimage_image_eq, AlgebraicGeometry.Proj.fromOfGlobalSections_preimage_basicOpen 𝒜 Φ hΦ hn ha]

/-- `j(D₊(a))` is an affine open of `P` (`a ∈ 𝒜 n`, `0 < n`). -/
theorem isAffineOpen_image_basicOpen (j : AlgebraicGeometry.Proj 𝒜 ⟶ P) [AlgebraicGeometry.IsOpenImmersion j]
    {a : A} {n : ℕ} (hn : 0 < n) (ha : a ∈ 𝒜 n) :
    AlgebraicGeometry.IsAffineOpen (j ''ᵁ AlgebraicGeometry.Proj.basicOpen 𝒜 a) :=
  (AlgebraicGeometry.Proj.isAffineOpen_basicOpen 𝒜 a ha hn).image_of_isOpenImmersion j

/-- `appLE` along an equality of opens of the target (`eqToHom` transport). -/
theorem _root_.AlgebraicGeometry.Scheme.Hom.appLE_map_eqToHom {Y P : AlgebraicGeometry.Scheme.{u}} (g : Y ⟶ P)
    {U U' : P.Opens} (h : U = U') {O : Y.Opens} (e : O ≤ g ⁻¹ᵁ U') (e' : O ≤ g ⁻¹ᵁ U) (u : Γ(P, U')) :
    g.appLE U O e' (P.presheaf.map (eqToHom h).op u) = g.appLE U' O e u := by
  subst h
  rw [eqToHom_refl, op_id, P.presheaf.map_id]
  rfl

/-- **The ring map of `φ ≫ j` on the chart `j(U)`** is the ring map of `φ` on `U`, on sections read through
`j.appIso U : Γ(P, j(U)) ≅ Γ(Proj 𝒜, U)` (`comp_appLE` + `appIso_inv_app`). -/
theorem _root_.AlgebraicGeometry.Scheme.Hom.comp_appLE_image_appIso_inv {Y Q P : AlgebraicGeometry.Scheme.{u}}
    (φ : Y ⟶ Q) (j : Q ⟶ P) [AlgebraicGeometry.IsOpenImmersion j] (U : Q.Opens) {O : Y.Opens}
    (e : O ≤ (φ ≫ j) ⁻¹ᵁ (j ''ᵁ U)) (e' : O ≤ φ ⁻¹ᵁ U) (u : Γ(Q, U)) :
    (φ ≫ j).appLE (j ''ᵁ U) O e ((j.appIso U).inv u) = φ.appLE U O e' u := by
  rw [AlgebraicGeometry.Scheme.Hom.comp_appLE, CommRingCat.comp_apply,
    AlgebraicGeometry.Scheme.Hom.appIso_inv_app_apply]
  exact φ.appLE_map_eqToHom (j.preimage_image_eq U) e' _ u

/-! ## The fraction formula: auxiliary ring map `θ : Γ(Y, ⊤)[1/Φ a] → Γ(Y, Y.basicOpen (Φ a))` -/

section FractionAux

variable (x : Γ(Y, ⊤))

/-- `Y.basicOpen x ≅ (Spec Γ(Y,⊤))_x ≅ Spec Γ(Y,⊤)[1/x]` — the first three factors of Mathlib's
`toBasicOpenOfGlobalSections`. -/
def basicOpenToSpecAway : (Y.basicOpen x).toScheme ⟶ AlgebraicGeometry.Spec (.of <| Localization.Away x) :=
  (Y.isoOfEq (Y.toSpecΓ_preimage_basicOpen x)).inv ≫ Y.toSpecΓ ∣_ (PrimeSpectrum.basicOpen x) ≫
    (AlgebraicGeometry.basicOpenIsoSpecAway x).hom

/-- The ring map `θ : Γ(Y,⊤)[1/x] → Γ(Y, Y.basicOpen x)` induced by `basicOpenToSpecAway` on global sections. -/
def awayToBasicOpenSections : Localization.Away x →+* Γ(Y, Y.basicOpen x) :=
  ((Y.basicOpen x).topIso.hom.hom.comp (AlgebraicGeometry.Proj.basicOpenToSpecAway x).appTop.hom).comp
    (AlgebraicGeometry.Scheme.ΓSpecIso (.of <| Localization.Away x)).inv.hom

set_option backward.isDefEq.respectTransparency false in
/-- `basicOpenToSpecAway x ≫ Spec (algebraMap) = ι ≫ toSpecΓ` (`basicOpenIsoSpecAway_hom_SpecMap`,
`morphismRestrict_ι`, `isoOfEq_inv_ι`). -/
theorem basicOpenToSpecAway_comp_SpecMap_algebraMap :
    AlgebraicGeometry.Proj.basicOpenToSpecAway x ≫
        AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap Γ(Y, ⊤) (Localization.Away x))) =
      (Y.basicOpen x).ι ≫ Y.toSpecΓ := by
  unfold AlgebraicGeometry.Proj.basicOpenToSpecAway
  rw [Category.assoc, Category.assoc, AlgebraicGeometry.basicOpenIsoSpecAway_hom_SpecMap,
    AlgebraicGeometry.morphismRestrict_ι, ← Category.assoc, AlgebraicGeometry.Scheme.isoOfEq_inv_ι]

set_option backward.isDefEq.respectTransparency false in
/-- `θ (r/1) = r|_{Y_x}`. -/
theorem awayToBasicOpenSections_algebraMap (r : Γ(Y, ⊤)) :
    AlgebraicGeometry.Proj.awayToBasicOpenSections x (algebraMap Γ(Y, ⊤) (Localization.Away x) r) =
      Y.presheaf.map (homOfLE (Y.basicOpen_le x)).op r := by
  have h1 : (AlgebraicGeometry.Scheme.ΓSpecIso (.of <| Localization.Away x)).inv
        (algebraMap Γ(Y, ⊤) (Localization.Away x) r) =
      (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap Γ(Y, ⊤) (Localization.Away x)))).appTop
        ((AlgebraicGeometry.Scheme.ΓSpecIso Γ(Y, ⊤)).inv r) := by
    have := ConcreteCategory.congr_hom (AlgebraicGeometry.Scheme.ΓSpecIso_inv_naturality
      (CommRingCat.ofHom (algebraMap Γ(Y, ⊤) (Localization.Away x)))) r
    rw [CommRingCat.comp_apply, CommRingCat.comp_apply] at this
    exact this
  have h2 : (AlgebraicGeometry.Proj.basicOpenToSpecAway x).appTop
        ((AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap Γ(Y, ⊤) (Localization.Away x)))).appTop
          ((AlgebraicGeometry.Scheme.ΓSpecIso Γ(Y, ⊤)).inv r)) =
      ((Y.basicOpen x).ι ≫ Y.toSpecΓ).appTop ((AlgebraicGeometry.Scheme.ΓSpecIso Γ(Y, ⊤)).inv r) := by
    rw [← AlgebraicGeometry.Proj.basicOpenToSpecAway_comp_SpecMap_algebraMap]
    rfl
  show (Y.basicOpen x).topIso.hom ((AlgebraicGeometry.Proj.basicOpenToSpecAway x).appTop
    ((AlgebraicGeometry.Scheme.ΓSpecIso (.of <| Localization.Away x)).inv
      (algebraMap Γ(Y, ⊤) (Localization.Away x) r))) = _
  rw [h1, h2, AlgebraicGeometry.Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
    AlgebraicGeometry.Scheme.toSpecΓ_appTop, CategoryTheory.Iso.inv_hom_id_apply,
    AlgebraicGeometry.Scheme.Opens.ι_appTop]
  unfold AlgebraicGeometry.Scheme.Opens.topIso
  rw [Functor.mapIso_hom, ← CommRingCat.comp_apply, ← Y.presheaf.map_comp]
  exact congrArg (fun i => Y.presheaf.map i r) (Subsingleton.elim _ _)

end FractionAux

set_option backward.isDefEq.respectTransparency false in
/-- **`φ.appLE` on `D₊(a)` through `θ`**: on `Y_{Φa} := Y.basicOpen (Φ a)`, the ring map of
`φ = fromOfGlobalSections 𝒜 Φ hΦ` on the chart `D₊(a)` sends `awayToSection 𝒜 a m` to
`θ (IsLocalization.map Φ (m.val))` (the four factors of Mathlib's `toBasicOpenOfGlobalSections` on global sections). -/
theorem fromOfGlobalSections_appLE_awayToSection {a : A} {d : ℕ} (ha : a ∈ 𝒜 d) (hd : 0 < d)
    (m : HomogeneousLocalization.Away 𝒜 a)
    (hy : Submonoid.powers a ≤ Submonoid.comap Φ (Submonoid.powers (Φ a))) :
    (AlgebraicGeometry.Proj.fromOfGlobalSections 𝒜 Φ hΦ).appLE (AlgebraicGeometry.Proj.basicOpen 𝒜 a)
        (Y.basicOpen (Φ a)) (AlgebraicGeometry.Proj.fromOfGlobalSections_preimage_basicOpen 𝒜 Φ hΦ hd ha).ge
        (AlgebraicGeometry.Proj.awayToSection 𝒜 a m) =
      AlgebraicGeometry.Proj.awayToBasicOpenSections (Φ a)
        (IsLocalization.map (Localization.Away (Φ a)) Φ hy m.val) := by
  -- the piece of `toBasicOpenOfGlobalSections`, factored through `basicOpenToSpecAway`
  have hmor : AlgebraicGeometry.Proj.toBasicOpenOfGlobalSections 𝒜 Φ rfl hd ha =
      AlgebraicGeometry.Proj.basicOpenToSpecAway (Φ a) ≫
        AlgebraicGeometry.Spec.map (CommRingCat.ofHom (RingHom.comp
          (IsLocalization.map (Localization.Away (Φ a)) Φ hy)
          (algebraMap (HomogeneousLocalization.Away 𝒜 a) (Localization.Away a)))) ≫
        (AlgebraicGeometry.Proj.basicOpenIsoSpec 𝒜 a ha hd).inv := by
    unfold AlgebraicGeometry.Proj.toBasicOpenOfGlobalSections AlgebraicGeometry.Proj.basicOpenToSpecAway
    simp only [Category.assoc]
  -- `appLE = topIso.hom ∘ (resLE).app ⊤ ∘ topIso.inv`
  have h1 : (AlgebraicGeometry.Proj.fromOfGlobalSections 𝒜 Φ hΦ).appLE (AlgebraicGeometry.Proj.basicOpen 𝒜 a)
      (Y.basicOpen (Φ a)) (AlgebraicGeometry.Proj.fromOfGlobalSections_preimage_basicOpen 𝒜 Φ hΦ hd ha).ge
      (AlgebraicGeometry.Proj.awayToSection 𝒜 a m) =
      (Y.basicOpen (Φ a)).topIso.hom
        (((AlgebraicGeometry.Proj.fromOfGlobalSections 𝒜 Φ hΦ).resLE (AlgebraicGeometry.Proj.basicOpen 𝒜 a)
          (Y.basicOpen (Φ a)) (AlgebraicGeometry.Proj.fromOfGlobalSections_preimage_basicOpen 𝒜 Φ hΦ hd ha).ge).app ⊤
          ((AlgebraicGeometry.Proj.basicOpen 𝒜 a).topIso.inv (AlgebraicGeometry.Proj.awayToSection 𝒜 a m))) := by
    rw [AlgebraicGeometry.Scheme.Hom.resLE_app_top, CommRingCat.comp_apply, CommRingCat.comp_apply,
      CategoryTheory.Iso.inv_hom_id_apply]
    exact (CategoryTheory.Iso.inv_hom_id_apply (Y.basicOpen (Φ a)).topIso _).symm
  -- the last factor `basicOpenIsoSpec.inv` undoes `topIso.inv ∘ awayToSection` up to `ΓSpecIso.inv`
  have h2 : (AlgebraicGeometry.Proj.basicOpen 𝒜 a).topIso.inv (AlgebraicGeometry.Proj.awayToSection 𝒜 a m) =
      (AlgebraicGeometry.Proj.basicOpenIsoSpec 𝒜 a ha hd).hom.app ⊤
        ((AlgebraicGeometry.Scheme.ΓSpecIso (.of <| HomogeneousLocalization.Away 𝒜 a)).inv m) := by
    rw [AlgebraicGeometry.Proj.basicOpenIsoSpec_hom, AlgebraicGeometry.Proj.basicOpenToSpec_app_top,
      CommRingCat.comp_apply, CommRingCat.comp_apply, CategoryTheory.Iso.inv_hom_id_apply]
    rfl
  have hm2 : (AlgebraicGeometry.Proj.basicOpenToSpecAway (Φ a) ≫
        AlgebraicGeometry.Spec.map (CommRingCat.ofHom (RingHom.comp
          (IsLocalization.map (Localization.Away (Φ a)) Φ hy)
          (algebraMap (HomogeneousLocalization.Away 𝒜 a) (Localization.Away a)))) ≫
        (AlgebraicGeometry.Proj.basicOpenIsoSpec 𝒜 a ha hd).inv) ≫
        (AlgebraicGeometry.Proj.basicOpenIsoSpec 𝒜 a ha hd).hom =
      AlgebraicGeometry.Proj.basicOpenToSpecAway (Φ a) ≫
        AlgebraicGeometry.Spec.map (CommRingCat.ofHom (RingHom.comp
          (IsLocalization.map (Localization.Away (Φ a)) Φ hy)
          (algebraMap (HomogeneousLocalization.Away 𝒜 a) (Localization.Away a)))) := by
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have h3 : ∀ w, (AlgebraicGeometry.Proj.basicOpenToSpecAway (Φ a) ≫
        AlgebraicGeometry.Spec.map (CommRingCat.ofHom (RingHom.comp
          (IsLocalization.map (Localization.Away (Φ a)) Φ hy)
          (algebraMap (HomogeneousLocalization.Away 𝒜 a) (Localization.Away a)))) ≫
        (AlgebraicGeometry.Proj.basicOpenIsoSpec 𝒜 a ha hd).inv).app ⊤
        ((AlgebraicGeometry.Proj.basicOpenIsoSpec 𝒜 a ha hd).hom.app ⊤ w) =
      (AlgebraicGeometry.Proj.basicOpenToSpecAway (Φ a) ≫
        AlgebraicGeometry.Spec.map (CommRingCat.ofHom (RingHom.comp
          (IsLocalization.map (Localization.Away (Φ a)) Φ hy)
          (algebraMap (HomogeneousLocalization.Away 𝒜 a) (Localization.Away a))))).app ⊤ w := by
    intro w
    rw [← hm2]
    rfl
  -- `Spec.map g` on global sections is `g` through `ΓSpecIso`
  have h4 : (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (RingHom.comp
          (IsLocalization.map (Localization.Away (Φ a)) Φ hy)
          (algebraMap (HomogeneousLocalization.Away 𝒜 a) (Localization.Away a))))).appTop
        ((AlgebraicGeometry.Scheme.ΓSpecIso (.of <| HomogeneousLocalization.Away 𝒜 a)).inv m) =
      (AlgebraicGeometry.Scheme.ΓSpecIso (.of <| Localization.Away (Φ a))).inv
        (IsLocalization.map (Localization.Away (Φ a)) Φ hy m.val) := by
    have := ConcreteCategory.congr_hom (AlgebraicGeometry.Scheme.ΓSpecIso_inv_naturality
      (CommRingCat.ofHom (RingHom.comp (IsLocalization.map (Localization.Away (Φ a)) Φ hy)
        (algebraMap (HomogeneousLocalization.Away 𝒜 a) (Localization.Away a))))) m
    rw [CommRingCat.comp_apply, CommRingCat.comp_apply] at this
    exact this.symm
  rw [h1, AlgebraicGeometry.Proj.fromOfGlobalSections_resLE 𝒜 Φ hΦ hd ha, hmor, h2, h3]
  show (Y.basicOpen (Φ a)).topIso.hom ((AlgebraicGeometry.Proj.basicOpenToSpecAway (Φ a)).appTop
    ((AlgebraicGeometry.Spec.map (CommRingCat.ofHom (RingHom.comp
          (IsLocalization.map (Localization.Away (Φ a)) Φ hy)
          (algebraMap (HomogeneousLocalization.Away 𝒜 a) (Localization.Away a))))).appTop
        ((AlgebraicGeometry.Scheme.ΓSpecIso (.of <| HomogeneousLocalization.Away 𝒜 a)).inv m))) = _
  rw [h4]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- **The ring map of `φ = fromOfGlobalSections 𝒜 Φ hΦ` on the chart `D₊(a)`, on fractions** (Stacks 01O4 (2)):
for `O ≤ φ⁻¹D₊(a)` and the degree-zero fraction `b / a^k ∈ A_{(a)} = Γ(D₊(a), O)` (`a ∈ 𝒜 d`, `b ∈ 𝒜 (k·d)`,
`Proj.awayToSection`, `HomogeneousLocalization.Away.mk`), its image `g` under `φ.appLE (D₊(a)) O` satisfies
`g · Φ(a)|_O^k = Φ(b)|_O`.

**Proof (Mathlib `AlgebraicGeometry/ProjectiveSpectrum/Basic.lean`).**
1. Reduce to `O = Y.basicOpen (Φ a) = φ⁻¹D₊(a)` (`fromOfGlobalSections_preimage_basicOpen`, `appLE_map`; both sides
   are compatible with restriction).
2. On `Y_{Φa}`, `φ.appLE (D₊(a)) Y_{Φa} = topIso ∘ (φ.resLE …).appTop ∘ topIso⁻¹` (`resLE_app_top`), and
   `φ.resLE = toBasicOpenOfGlobalSections 𝒜 Φ rfl hd ha` (`fromOfGlobalSections_resLE`).
3. `toBasicOpenOfGlobalSections` is `Y_{Φa} ≅ (Spec Γ(Y,⊤))_{Φa} ≅ Spec Γ(Y,⊤)[1/Φa] → Spec A[1/a]_0 ≅ D₊(a)`; on
   global sections the last factor undoes `topIso⁻¹ ∘ awayToSection` up to `ΓSpecIso` (`basicOpenToSpec_app_top`),
   `Spec.map g` is `g` (`ΓSpecIso_inv_naturality`), and the first three factors give the ring map
   `θ : Γ(Y,⊤)[1/Φa] → Γ(Y, Y_{Φa})` with `θ(r/1) = r|` (`awayToBasicOpenSections_algebraMap`:
   `basicOpenIsoSpecAway_hom_SpecMap`, `morphismRestrict_ι`, `isoOfEq_inv_ι`, `toSpecΓ_appTop`, `ι_appTop`)
   (`fromOfGlobalSections_appLE_awayToSection`).
4. `b/a^k` (`Away.mk ha k b hb`, `.val = mk b ⟨a^k, _⟩`) goes to `Φ(b)/Φ(a)^k` under `IsLocalization.map Φ`
   (`IsLocalization.map_mk'`), and `mk' x y · (y/1) = x/1` (`IsLocalization.mk'_spec`); apply the ring map `θ`.

**Edge cases.** `k = 0`: the fraction is `b/1` with `b ∈ 𝒜 0`, the statement is `φ.appLE (b/1) = Φ(b)|_O`, i.e.
the degree-zero part (`fromOfGlobalSections_toSpecZero`). `O = ∅`: trivial. `a` nilpotent: `D₊(a) = ∅` and
`Y.basicOpen (Φ a) = ∅`, `O = ∅`. -/
theorem fromOfGlobalSections_appLE_awayToSection_mk_mul {a : A} {d : ℕ} (ha : a ∈ 𝒜 d) (hd : 0 < d)
    (k : ℕ) {b : A} (hb : b ∈ 𝒜 (k • d)) {O : Y.Opens}
    (hO : O ≤ AlgebraicGeometry.Proj.fromOfGlobalSections 𝒜 Φ hΦ ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen 𝒜 a) :
    (AlgebraicGeometry.Proj.fromOfGlobalSections 𝒜 Φ hΦ).appLE (AlgebraicGeometry.Proj.basicOpen 𝒜 a) O hO
        (AlgebraicGeometry.Proj.awayToSection 𝒜 a (HomogeneousLocalization.Away.mk 𝒜 ha k b hb)) *
      (Y.presheaf.map (homOfLE (le_top : O ≤ ⊤)).op (Φ a)) ^ k =
      Y.presheaf.map (homOfLE (le_top : O ≤ ⊤)).op (Φ b) := by
  have hO' : O ≤ Y.basicOpen (Φ a) := by
    rwa [AlgebraicGeometry.Proj.fromOfGlobalSections_preimage_basicOpen 𝒜 Φ hΦ hd ha] at hO
  have hy : Submonoid.powers a ≤ Submonoid.comap Φ (Submonoid.powers (Φ a)) := by
    rw [← Submonoid.map_le_iff_le_comap, Submonoid.map_powers]
  -- the identity on `Y_{Φa}`
  have key : (AlgebraicGeometry.Proj.fromOfGlobalSections 𝒜 Φ hΦ).appLE (AlgebraicGeometry.Proj.basicOpen 𝒜 a)
        (Y.basicOpen (Φ a)) (AlgebraicGeometry.Proj.fromOfGlobalSections_preimage_basicOpen 𝒜 Φ hΦ hd ha).ge
        (AlgebraicGeometry.Proj.awayToSection 𝒜 a (HomogeneousLocalization.Away.mk 𝒜 ha k b hb)) *
      (Y.presheaf.map (homOfLE (Y.basicOpen_le (Φ a))).op (Φ a)) ^ k =
      Y.presheaf.map (homOfLE (Y.basicOpen_le (Φ a))).op (Φ b) := by
    rw [AlgebraicGeometry.Proj.fromOfGlobalSections_appLE_awayToSection 𝒜 Φ hΦ ha hd _ hy,
      HomogeneousLocalization.Away.val_mk, Localization.mk_eq_mk'_apply,
      IsLocalization.map_mk' (M := Submonoid.powers a) (S := Localization.Away a)
        (T := Submonoid.powers (Φ a)) (Q := Localization.Away (Φ a)) (g := Φ) hy b ⟨a ^ k, ⟨k, rfl⟩⟩,
      ← AlgebraicGeometry.Proj.awayToBasicOpenSections_algebraMap (Φ a) (Φ b),
      ← AlgebraicGeometry.Proj.awayToBasicOpenSections_algebraMap (Φ a) (Φ a),
      ← map_pow (AlgebraicGeometry.Proj.awayToBasicOpenSections (Φ a)),
      ← map_pow (algebraMap Γ(Y, ⊤) (Localization.Away (Φ a))),
      ← map_mul (AlgebraicGeometry.Proj.awayToBasicOpenSections (Φ a)), ← map_pow Φ a k]
    exact congrArg (AlgebraicGeometry.Proj.awayToBasicOpenSections (Φ a)) (IsLocalization.mk'_spec _ _ _)
  -- restrict from `Y_{Φa}` to `O`
  have hA := ConcreteCategory.congr_hom (AlgebraicGeometry.Scheme.Hom.appLE_map
    (AlgebraicGeometry.Proj.fromOfGlobalSections 𝒜 Φ hΦ)
    (AlgebraicGeometry.Proj.fromOfGlobalSections_preimage_basicOpen 𝒜 Φ hΦ hd ha).ge (homOfLE hO').op)
    (AlgebraicGeometry.Proj.awayToSection 𝒜 a (HomogeneousLocalization.Away.mk 𝒜 ha k b hb))
  rw [CommRingCat.comp_apply] at hA
  have hB : ∀ z : Γ(Y, ⊤), Y.presheaf.map (homOfLE hO').op (Y.presheaf.map (homOfLE (Y.basicOpen_le (Φ a))).op z) =
      Y.presheaf.map (homOfLE (le_top : O ≤ ⊤)).op z := by
    intro z
    rw [← CommRingCat.comp_apply, ← Y.presheaf.map_comp]
    rfl
  have h := congrArg (Y.presheaf.map (homOfLE hO').op) key
  rw [map_mul, map_pow, hA, hB, hB] at h
  exact h

end AlgebraicGeometry.Proj

end
