import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.GradedQcAlgebraSectionsRing
import MiyaokaMori.AlgebraicGeometry.Modules.QuasiCoherent.QcSectionsBasicOpenLocalization
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.GradedAffineAlgebra
import MiyaokaMori.RingTheory.DirectSumLocalization
import MiyaokaMori.AlgebraicGeometry.Modules.QuasiCoherent.QcLocalizedModule

/-! # From graded quasi-coherent algebras in `X.Modules` to graded affine algebras

The bridge `Scheme.GradedQCAlgebra` (an `ℕ`-graded commutative monoid object of `X.Modules`) ↦
`Scheme.GradedAffineAlgebra`: `U ↦` the section ring `S.sectionsRing U = ⊕_m Γ(U, S_m)`, restriction
`sectionsRestrict`, structure map `sectionsUnit`, grading `sectionsGrading`. The data come from
`GradedQcAlgebraSectionsRing.lean`; functoriality is proved here; quasi-coherence (compatibility with
localization) is the theorem `GradedQCAlgebra.affineUnit_coequifibered`.

Graded algebras given by sheaf-theoretic constructions (`Sym`, weighted `Sym`, Rees algebras, pullbacks) are
produced in the `X.Modules` encoding and enter the relative Proj / twist through this conversion, so the
relative Proj side needs only one implementation.
-/

set_option autoImplicit false

universe u

open CategoryTheory Opposite

noncomputable section

namespace AlgebraicGeometry.Scheme.GradedQCAlgebra

variable {X : Scheme.{u}} (S : X.GradedQCAlgebra)

/-- The underlying ring homomorphism of restriction. -/
def sectionsRestrictHom {U V : X.Opens} (h : U ≤ V) : S.sectionsRing V →+* S.sectionsRing U :=
  ((S.sectionsRestrict h : S.sectionsGrading V →+*ᵍ S.sectionsGrading U) :
    S.sectionsRing V →+* S.sectionsRing U)

-- `sectionsRestrict` is `toRingHom := sectionsRestrictRingHom` (a `DirectSum.toSemiring`); the three proofs
-- below go through the characterizing lemma `sectionsRestrictRingHom_of` and direct sum induction rather
-- than any definitional equality with `DirectSum.map`.
/-- Restriction along `U ≤ U` is the identity. -/
theorem sectionsRestrictHom_refl {U : X.Opens} (h : U ≤ U) :
    S.sectionsRestrictHom h = RingHom.id _ := by
  have hpiece : ∀ (m : ℕ) (a : S.sectionsPiece U m),
      S.sectionsRestrictPiece h m a = a := by
    intro m a
    have h1 : homOfLE h = 𝟙 U := Subsingleton.elim _ _
    show ((S.part m).val.map (homOfLE h).op).hom a = a
    rw [h1, op_id, (S.part m).val.map_id]
    rfl
  refine DirectSum.ringHom_ext fun m a => ?_
  show S.sectionsRestrictRingHom h (DirectSum.of (S.sectionsPiece U) m a)
    = DirectSum.of (S.sectionsPiece U) m a
  rw [S.sectionsRestrictRingHom_of h m a, hpiece m a]

theorem sectionsRestrictHom_trans {U V W : X.Opens} (hUV : U ≤ V) (hVW : V ≤ W) (hUW : U ≤ W) :
    S.sectionsRestrictHom hUW = (S.sectionsRestrictHom hUV).comp (S.sectionsRestrictHom hVW) := by
  have h1 : homOfLE hUW = homOfLE hUV ≫ homOfLE hVW := Subsingleton.elim _ _
  have hpiece : ∀ (m : ℕ) (a : S.sectionsPiece W m),
      S.sectionsRestrictPiece hUW m a
        = S.sectionsRestrictPiece hUV m (S.sectionsRestrictPiece hVW m a) := by
    intro m a
    show ((S.part m).val.map (homOfLE hUW).op).hom a
      = ((S.part m).val.map (homOfLE hUV).op).hom (((S.part m).val.map (homOfLE hVW).op).hom a)
    exact (PresheafOfModules.congr_map_apply _ (congrArg Quiver.Hom.op h1) _).trans
      (PresheafOfModules.map_comp_apply _ _ _ _)
  refine DirectSum.ringHom_ext fun m a => ?_
  show S.sectionsRestrictRingHom hUW (DirectSum.of (S.sectionsPiece W) m a)
    = S.sectionsRestrictRingHom hUV (S.sectionsRestrictRingHom hVW
        (DirectSum.of (S.sectionsPiece W) m a))
  rw [S.sectionsRestrictRingHom_of hUW m a, S.sectionsRestrictRingHom_of hVW m a,
    S.sectionsRestrictRingHom_of hUV m _, hpiece m a]

/-- The presheaf of rings `U ↦ ⊕_m Γ(U, S_m)` on the affine site. -/
def affineRing : X.AffineZariskiSiteᵒᵖ ⥤ CommRingCat.{u} where
  obj U := CommRingCat.of (S.sectionsRing U.unop.toOpens)
  map f := CommRingCat.ofHom
    (S.sectionsRestrictHom (AffineZariskiSite.toOpens_mono f.unop.le))
  map_id U := by
    apply CommRingCat.hom_ext
    exact S.sectionsRestrictHom_refl _
  map_comp f g := by
    apply CommRingCat.hom_ext
    exact S.sectionsRestrictHom_trans _ _ _

/-- The underlying ring homomorphism `Γ(X,U) → ⊕_m Γ(U, S_m)` of the structure map (landing in degree `0`). -/
def sectionsUnitHom (U : X.Opens) : Γ(X, U) →+* S.sectionsRing U where
  toFun r := ((S.sectionsUnit U r : S.sectionsGrading U 0) : S.sectionsRing U)
  map_one' := congrArg Subtype.val (map_one (S.sectionsUnit U))
  map_mul' a b := congrArg Subtype.val (map_mul (S.sectionsUnit U) a b)
  map_zero' := congrArg Subtype.val (map_zero (S.sectionsUnit U))
  map_add' a b := congrArg Subtype.val (map_add (S.sectionsUnit U) a b)

/-- The structure map commutes with restriction (this is the naturality of `S.one`). -/
theorem sectionsUnitHom_naturality {U V : X.Opens} (h : U ≤ V) (r : Γ(X, V)) :
    S.sectionsRestrictHom h (S.sectionsUnitHom V r) =
      S.sectionsUnitHom U ((X.presheaf.map (homOfLE h).op).hom r) := by
  have h1 : ((MonoidalCategoryStruct.tensorUnit X.Modules).val.map (homOfLE h).op) r
      = (X.presheaf.map (homOfLE h).op).hom r := rfl
  have hone : S.sectionsRestrictPiece h 0 (S.one.app V r)
      = S.one.app U ((X.presheaf.map (homOfLE h).op).hom r) := by
    have hn := PresheafOfModules.naturality_apply S.one.val (homOfLE h).op r
    rw [h1] at hn
    exact hn.symm
  have hV : S.sectionsUnitHom V r = DirectSum.of (S.sectionsPiece V) 0 (S.one.app V r) := rfl
  have hU : S.sectionsUnitHom U ((X.presheaf.map (homOfLE h).op).hom r)
      = DirectSum.of (S.sectionsPiece U) 0
        (S.one.app U ((X.presheaf.map (homOfLE h).op).hom r)) := rfl
  rw [hV, hU]
  show S.sectionsRestrictRingHom h (DirectSum.of (S.sectionsPiece V) 0 (S.one.app V r))
    = DirectSum.of (S.sectionsPiece U) 0 _
  rw [S.sectionsRestrictRingHom_of h 0 (S.one.app V r)]
  exact congrArg _ hone

/-- The structure map on the affine site. -/
def affineUnit : (AffineZariskiSite.toOpensFunctor X).op ⋙ X.presheaf ⟶ S.affineRing where
  app U := CommRingCat.ofHom (S.sectionsUnitHom U.unop.toOpens)
  naturality U V f := by
    apply CommRingCat.hom_ext
    refine RingHom.ext fun r => ?_
    exact (S.sectionsUnitHom_naturality (AffineZariskiSite.toOpens_mono f.unop.le) r).symm

/-! ## Three ingredients for Stacks 01I8 -/

/-- The `Γ(X,U)`-module structure on `Γ(U, S_m)`. Mathlib's instance is on `Γ(S.part m, U)`
(`= (Scheme.Modules.presheaf _).obj _`, an object of `Ab`), while `S.sectionsPiece U m` unfolds to
`(S.part m).val.obj (op U)` (an object of `ModuleCat`) — definitionally equal but **syntactically
different**, and instance search does not see through `Scheme.Modules.presheaf` (a `def`). This registers
the same instance in the second spelling; otherwise `Module Γ(X,U)` cannot be synthesized on
`⨁ m, S.sectionsPiece U m`. The name carries a module suffix to avoid clashing with `local instance`s
elsewhere (`local` only affects the attribute; the name is still global). -/
local instance sectionsPieceModule_ofGradedQCAlgebra (U : X.Opens) (m : ℕ) :
    Module Γ(X, U) (S.sectionsPiece U m) :=
  inferInstanceAs (Module Γ(X, U) Γ(S.part m, U))

section Aux

/-- A purely ring-theoretic step (`S.sectionsRing U` is a `def`, on which `rw [add_mul]` / `ring` find no
instances; the step is isolated as a lemma and applied by `exact` through definitional equality). -/
private theorem mul_add_mul_aux {R : Type*} [CommRing R] (x y A B : R) :
    (x + y) * (A * B) = x * A * B + y * B * A := by ring

/-- Place a section of the `m`-th piece into the section ring. `S.sectionsRing U` is a `def` that typeclass
search does not see through; writing `DirectSum.of` directly gives the two sides of `*` the types
`S.sectionsRing U` and `⨁ m, S.sectionsPiece U m`, definitionally equal but syntactically different, and
`HMul` fails to synthesize; this definition only writes the result type as the former. -/
def ofPiece (U : X.Opens) (m : ℕ) (a : S.sectionsPiece U m) : S.sectionsRing U :=
  DirectSum.of (S.sectionsPiece U) m a

/-- **Graded version of the unit law**: multiplication by the structure map is the piecewise scalar action. -/
theorem sectionsUnitHom_mul_ofPiece (U : X.Opens) (r : Γ(X, U)) {m : ℕ}
    (a : S.sectionsPiece U m) :
    S.sectionsUnitHom U r * S.ofPiece U m a
      = S.ofPiece U m (@HSMul.hSMul Γ(X, U) Γ(S.part m, U) Γ(S.part m, U) _ r a) := by
  refine Eq.trans (DirectSum.of_mul_of (A := S.sectionsPiece U) (S.one.app U r) a)
    (DirectSum.of_eq_of_gradedMonoid_eq ?_)
  show (GradedMonoid.mk (0 + m) (S.sectionsGMul U (S.one.app U r) a) :
      GradedMonoid (S.sectionsPiece U)) = GradedMonoid.mk m _
  rw [S.sectionsGOne_app_sectionsGMul U r a]
  exact S.mk_eqToHom_app U (Nat.zero_add m).symm _

/-- The restriction ring homomorphism on generators: piecewise restriction. -/
theorem sectionsRestrictHom_ofPiece {U V : X.Opens} (h : U ≤ V) (m : ℕ)
    (a : S.sectionsPiece V m) :
    S.sectionsRestrictHom h (S.ofPiece V m a) = S.ofPiece U m (S.sectionsRestrictPiece h m a) :=
  S.sectionsRestrictRingHom_of h m a

/-- The restriction ring homomorphism, as an additive homomorphism, is `DirectSum.map` (piecewise
restriction). -/
theorem sectionsRestrictHom_toAddMonoidHom {U V : X.Opens} (h : U ≤ V) :
    (S.sectionsRestrictHom h).toAddMonoidHom
      = DirectSum.map (fun m => S.sectionsRestrictPiece h m) :=
  DirectSum.addHom_ext fun i a =>
    (S.sectionsRestrictHom_ofPiece h i a).trans (DirectSum.map_of _ i a).symm

/-- The `m`-th component of an element of the section ring (again to write the type as `S.sectionsRing U`). -/
def component (U : X.Opens) (m : ℕ) : S.sectionsRing U → S.sectionsPiece U m :=
  fun (x : DirectSum ℕ (S.sectionsPiece U)) => x m

/-- The support of an element of the section ring: the indices with nonzero component, a finite set. -/
def supp (U : X.Opens) : S.sectionsRing U → Finset ℕ :=
  letI : ∀ (i : ℕ) (a : S.sectionsPiece U i), Decidable (a ≠ 0) := fun _ _ => Classical.dec _
  fun (x : DirectSum ℕ (S.sectionsPiece U)) => x.support

/-- An element of the section ring is the finite sum of its components over its support. -/
theorem sum_supp (U : X.Opens) (x : S.sectionsRing U) :
    ∑ m ∈ S.supp U x, S.ofPiece U m (S.component U m x) = x := by
  let _ : ∀ (i : ℕ) (a : S.sectionsPiece U i), Decidable (a ≠ 0) := fun _ _ => Classical.dec _
  exact DirectSum.sum_support_of (β := S.sectionsPiece U) x

/-- The kernel of the restriction ring homomorphism: componentwise zero. -/
theorem sectionsRestrictHom_eq_zero_iff {U V : X.Opens} (h : U ≤ V) (x : S.sectionsRing V) :
    S.sectionsRestrictHom h x = 0 ↔ ∀ m, S.sectionsRestrictPiece h m (S.component V m x) = 0 := by
  have hx : (S.sectionsRestrictHom h).toAddMonoidHom x
      = DirectSum.map (fun m => S.sectionsRestrictPiece h m) x :=
    congrArg (fun φ => φ x) (S.sectionsRestrictHom_toAddMonoidHom h)
  constructor
  · intro h0 m
    have h1 : DirectSum.map (fun m => S.sectionsRestrictPiece h m) x = 0 := hx.symm.trans h0
    have h2 := congrArg (fun (y : DirectSum ℕ (S.sectionsPiece U)) => y m) h1
    exact (DirectSum.map_apply (fun m => S.sectionsRestrictPiece h m) m x).symm.trans h2
  · intro h0
    refine hx.trans (DirectSum.ext fun m => ?_)
    exact (DirectSum.map_apply (fun m => S.sectionsRestrictPiece h m) m x).trans
      ((h0 m).trans (DirectSum.zero_apply m).symm)

/-- The **piecewise** scalar action of `Γ(X,U)` on the section ring, as an additive homomorphism.
`S.sectionsRing U` is a `def`, and `HSMul` cannot be synthesized for `r • z` directly (the types are
definitionally equal but syntactically different); this definition only writes the type back as
`S.sectionsRing U`, and its body is `r • -`. -/
def pieceSmulHom (U : X.Opens) (r : Γ(X, U)) : S.sectionsRing U →+ S.sectionsRing U :=
  (DistribSMul.toAddMonoidHom (DirectSum ℕ (S.sectionsPiece U)) r :
    DirectSum ℕ (S.sectionsPiece U) →+ DirectSum ℕ (S.sectionsPiece U))

/-- **Piecewise scalar action = multiplication by the image of the structure map** (the global version of
the unit law). This is the only bridge between the module language on `⨁` and the ring language on the
section ring: the surjectivity and kernel steps of `affineUnit_coequifibered` each translate through it once. -/
theorem pieceSmulHom_eq (U : X.Opens) (r : Γ(X, U)) (z : S.sectionsRing U) :
    S.pieceSmulHom U r z = S.sectionsUnitHom U r * z := by
  induction z using DirectSum.induction_on with
  | zero =>
    exact (map_zero (S.pieceSmulHom U r)).trans (mul_zero (S.sectionsUnitHom U r)).symm
  | of m a =>
    refine Eq.trans ?_ (S.sectionsUnitHom_mul_ofPiece U r a).symm
    exact ((DirectSum.lof Γ(X, U) ℕ (S.sectionsPiece U) m).map_smul r a).symm
  | add x0 y0 hx hy =>
    obtain ⟨x, rfl⟩ : ∃ x : S.sectionsRing U, x = x0 := ⟨x0, rfl⟩
    obtain ⟨y, rfl⟩ : ∃ y : S.sectionsRing U, y = y0 := ⟨y0, rfl⟩
    have h3 : S.pieceSmulHom U r (x + y) = S.pieceSmulHom U r x + S.pieceSmulHom U r y :=
      map_add (S.pieceSmulHom U r) x y
    have h4 := congrArg₂ (fun a b : S.sectionsRing U => a + b) hx hy
    exact h3.trans (h4.trans (mul_add (S.sectionsUnitHom U r) x y).symm)

end Aux

/-- The affine-local characterization of quasi-coherence: `A(D(f)) = A(U)[1/f]` (Stacks 01I8).

Route (parallel to `QCAlgebra.unit_coequifibered`, with every step done piece by piece):
`coequifibered_iff_forall_isLocalizationAway` reduces the claim to "for every affine open `U` and
`f ∈ Γ(X,U)`, `A(D f)` is the localization of `A(U)` away from `sectionsUnitHom U f`", and three conditions
are checked:

* **invertibility**: `sectionsUnitHom_naturality` moves the image of `f` to `D f`, where `f|_{D f}` is
  invertible;
* **surjectivity**: for `z ∈ A(D f)`, induction on the direct sum. The generator step `of m a` is exactly the
  quasi-coherence of `S.part m` (`Modules.exists_pow_smul_eq_map_basicOpen`), with the scalar action turned
  into ring multiplication by `sectionsUnitHom_mul_ofPiece`; the addition step takes the sum of the two
  exponents (not the max, which would need extra monotonicity);
* **kernel**: `sectionsRestrictHom` is componentwise (`sectionsRestrictHom_eq_zero_iff`), so each component
  has an annihilating exponent (`Modules.exists_pow_smul_eq_zero_of_map_basicOpen_eq_zero`), and taking the
  supremum over the **finite support** gives a uniform exponent — the only extra content of the graded
  version over the ungraded one. -/
theorem affineUnit_coequifibered : S.affineUnit.Coequifibered := by
  rw [AffineZariskiSite.coequifibered_iff_forall_isLocalizationAway]
  intro U f
  have hV : X.basicOpen f ≤ U.toOpens := X.basicOpen_le f
  letI : Algebra (S.sectionsRing U.toOpens) (S.sectionsRing (X.basicOpen f)) :=
    (S.sectionsRestrictHom hV).toAlgebra
  show IsLocalization.Away (S.sectionsUnitHom U.toOpens f) (S.sectionsRing (X.basicOpen f))
  have halg : ∀ a : S.sectionsRing U.toOpens,
      algebraMap (S.sectionsRing U.toOpens) (S.sectionsRing (X.basicOpen f)) a
        = S.sectionsRestrictHom hV a := fun _ => rfl
  have hres : ∀ r : Γ(X, U.toOpens),
      S.sectionsRestrictHom hV (S.sectionsUnitHom U.toOpens r)
        = S.sectionsUnitHom (X.basicOpen f) ((X.presheaf.map (homOfLE hV).op).hom r) :=
    fun r => S.sectionsUnitHom_naturality hV r
  -- piecewise: view `Γ(D f, S_m)` as a `Γ(X,U)`-module through the restriction ring homomorphism; the
  -- restriction map is then `Γ(X,U)`-linear. The same instance is registered in **two spellings**:
  -- `Γ(S.part m, D f)` (used by the statement of `isLocalizedModule_basicOpen`) and `S.sectionsPiece (D f) m`
  -- (used to synthesize `Module` on `⨁`); definitionally equal, syntactically different.
  letI inst1 : ∀ m : ℕ, Module Γ(X, U.toOpens) Γ(S.part m, X.basicOpen f) := fun _ =>
    Module.compHom _ (X.presheaf.map (homOfLE hV).op).hom
  letI inst2 : ∀ m : ℕ, Module Γ(X, U.toOpens) (S.sectionsPiece (X.basicOpen f) m) := inst1
  have hsm : ∀ (m : ℕ) (r : Γ(X, U.toOpens)) (x : Γ(S.part m, X.basicOpen f)),
      r • x = (X.presheaf.map (homOfLE hV).op).hom r • x := fun _ _ _ => rfl
  let fm : ∀ m : ℕ, S.sectionsPiece U.toOpens m →ₗ[Γ(X, U.toOpens)]
      S.sectionsPiece (X.basicOpen f) m := fun m =>
    { toFun := S.sectionsRestrictPiece hV m
      map_add' := fun a b => map_add (S.sectionsRestrictPiece hV m) a b
      map_smul' := fun r a =>
        (Scheme.Modules.map_smul (S.part m) (homOfLE hV) r a).trans (hsm m r _).symm }
  -- each piece is a localization away from `f` (`S.part m` is quasi-coherent), hence so is the direct sum
  haveI : ∀ m : ℕ, IsLocalizedModule (Submonoid.powers f) (fm m) := fun m => by
    haveI := S.quasicoherent m
    exact Scheme.Modules.isLocalizedModule_basicOpen (S.part m) U.2 f (hsm m) (fm m)
      (fun _ => rfl)
  haveI hloc : IsLocalizedModule (Submonoid.powers f) (DirectSum.lmap fm) :=
    IsLocalizedModule.directSum (Submonoid.powers f) fm
  -- `DirectSum.lmap fm` is the restriction homomorphism of the section ring
  have hlmap : ∀ x : S.sectionsRing U.toOpens,
      DirectSum.lmap fm x = S.sectionsRestrictHom hV x := by
    intro x
    have h1 : (S.sectionsRestrictHom hV).toAddMonoidHom x
        = DirectSum.map (fun m => S.sectionsRestrictPiece hV m) x :=
      congrArg (fun φ => φ x) (S.sectionsRestrictHom_toAddMonoidHom hV)
    refine DirectSum.ext fun m => ?_
    have h2 := congrArg (fun (y : DirectSum ℕ (S.sectionsPiece (X.basicOpen f))) => y m) h1
    exact (h2.trans (DirectSum.map_apply (fun m => S.sectionsRestrictPiece hV m) m x)).symm
  refine (_root_.isLocalization_iff (Submonoid.powers _) _).mpr ⟨?_, ?_, ?_⟩
  · rintro ⟨-, n, rfl⟩
    rw [halg, map_pow, hres]
    exact IsUnit.pow n (RingHom.isUnit_map (S.sectionsUnitHom (X.basicOpen f))
      (X.toRingedSpace.isUnit_res_basicOpen f))
  · intro z
    obtain ⟨⟨x, ⟨-, n, rfl⟩⟩, hx⟩ :=
      IsLocalizedModule.surj (Submonoid.powers f) (DirectSum.lmap fm) z
    refine ⟨⟨x, ⟨_, n, rfl⟩⟩, ?_⟩
    have h1 : S.pieceSmulHom (X.basicOpen f)
        ((X.presheaf.map (homOfLE hV).op).hom (f ^ n)) z = S.sectionsRestrictHom hV x :=
      hx.trans (hlmap x)
    rw [S.pieceSmulHom_eq, ← hres, map_pow] at h1
    rw [halg, halg]
    exact (_root_.mul_comm z _).trans h1
  · intro x y hxy
    rw [halg, halg] at hxy
    have h1 : DirectSum.lmap fm x = DirectSum.lmap fm y :=
      (hlmap x).trans (hxy.trans (hlmap y).symm)
    obtain ⟨⟨-, n, rfl⟩, hc⟩ :=
      IsLocalizedModule.exists_of_eq (S := Submonoid.powers f) (f := DirectSum.lmap fm) h1
    refine ⟨⟨S.sectionsUnitHom U.toOpens f ^ n, ⟨n, rfl⟩⟩, ?_⟩
    have h2 : S.pieceSmulHom U.toOpens (f ^ n) x = S.pieceSmulHom U.toOpens (f ^ n) y := hc
    rw [S.pieceSmulHom_eq, S.pieceSmulHom_eq, map_pow] at h2
    exact h2


/-! ## Piecewise correspondence between `S.part m` and the `m`-th piece of the graded affine algebra

`S.sectionsGrading U m` is by definition the **image** of `DirectSum.of _ m`, so this bridge is the statement
that `DirectSum.of _ m` is an additive isomorphism onto its image, with inverse taking the `m`-th component
(constructive, no `Classical.choice`). Downstream uses (`locallyWeighted_part_isFiniteType`,
`GradedPieceLocallyFree`) need exactly this direction: transporting information about an atlas on the section
ring back to `Γ(U, S_m)`. -/

section Bridge

variable (U : X.Opens) (m : ℕ)

@[simp] theorem component_ofPiece (a : S.sectionsPiece U m) :
    S.component U m (S.ofPiece U m a) = a :=
  DirectSum.of_eq_same m a

theorem ofPiece_injective : Function.Injective (S.ofPiece U m) := fun a b hab => by
  have h := congrArg (S.component U m) hab
  rwa [S.component_ofPiece, S.component_ofPiece] at h

/-- Lying in the `m`-th piece ⟺ being recovered by "take the `m`-th component, then put it back". -/
theorem mem_sectionsGrading_iff (x : S.sectionsRing U) :
    x ∈ S.sectionsGrading U m ↔ S.ofPiece U m (S.component U m x) = x := by
  constructor
  · rintro ⟨a, rfl⟩
    exact congrArg (S.ofPiece U m) (S.component_ofPiece U m a)
  · intro hx
    exact ⟨S.component U m x, hx⟩

/-- **Piecewise correspondence**: `Γ(U, S_m) ≃+ (m-th piece of the section ring)`. -/
def sectionsPieceEquivGrading : S.sectionsPiece U m ≃+ S.sectionsGrading U m where
  toFun a := ⟨S.ofPiece U m a, ⟨a, rfl⟩⟩
  invFun x := S.component U m x.1
  left_inv a := S.component_ofPiece U m a
  right_inv x := Subtype.ext ((S.mem_sectionsGrading_iff U m x.1).mp x.2)
  map_add' a b := Subtype.ext (map_add (DirectSum.of (S.sectionsPiece U) m) a b)

@[simp] theorem coe_sectionsPieceEquivGrading (a : S.sectionsPiece U m) :
    ((S.sectionsPieceEquivGrading U m a : S.sectionsGrading U m) : S.sectionsRing U)
      = S.ofPiece U m a := rfl

@[simp] theorem sectionsPieceEquivGrading_symm_apply (x : S.sectionsGrading U m) :
    (S.sectionsPieceEquivGrading U m).symm x = S.component U m x.1 := rfl

/-- The piecewise correspondence is compatible with restriction. -/
theorem sectionsPieceEquivGrading_restrict {V : X.Opens} (h : U ≤ V) (a : S.sectionsPiece V m) :
    ((S.sectionsPieceEquivGrading U m (S.sectionsRestrictPiece h m a) :
        S.sectionsGrading U m) : S.sectionsRing U)
      = S.sectionsRestrictHom h
          ((S.sectionsPieceEquivGrading V m a : S.sectionsGrading V m) : S.sectionsRing V) :=
  (S.sectionsRestrictHom_ofPiece h m a).symm

/-- The piecewise correspondence is compatible with the structure map (scalar action): multiplication by
`sectionsUnitHom r` in the section ring corresponds to `r • -` on `Γ(U, S_m)`. -/
theorem sectionsPieceEquivGrading_smul (r : Γ(X, U)) (a : S.sectionsPiece U m) :
    S.sectionsUnitHom U r
        * ((S.sectionsPieceEquivGrading U m a : S.sectionsGrading U m) : S.sectionsRing U)
      = ((S.sectionsPieceEquivGrading U m
          (@HSMul.hSMul Γ(X, U) Γ(S.part m, U) Γ(S.part m, U) _ r a) :
            S.sectionsGrading U m) : S.sectionsRing U) :=
  S.sectionsUnitHom_mul_ofPiece U r a

end Bridge

/-- A graded monoid object of `X.Modules` ↦ a graded quasi-coherent algebra on the affine site. -/
def toGradedAffineAlgebra : X.GradedAffineAlgebra where
  ring := S.affineRing
  unit := S.affineUnit
  coequifibered := S.affineUnit_coequifibered
  grading U := S.sectionsGrading U.toOpens
  graded U := (inferInstance : GradedRing (S.sectionsGrading U.toOpens))
  restrict_mem {U V} h {_ _} ha :=
    (S.sectionsRestrict (AffineZariskiSite.toOpens_mono h)).map_mem ha
  unit_mem U r := (S.sectionsUnit U.toOpens r).2

/-- The `m`-th piece of `S.toGradedAffineAlgebra` on an affine open `U` is `S.sectionsGrading U m`; together
with `sectionsPieceEquivGrading` this gives `Γ(U, S_m) ≃+ (S.toGradedAffineAlgebra).grading U m`. -/
theorem toGradedAffineAlgebra_grading (U : X.AffineZariskiSite) (m : ℕ) :
    S.toGradedAffineAlgebra.grading U m = S.sectionsGrading U.toOpens m := rfl

/-- The **automatic coercion** from `X.GradedQCAlgebra` to `X.GradedAffineAlgebra`: `Scheme.relativeProj` /
`relativeProj.twist` take an `X.GradedAffineAlgebra`, and call sites `relativeProj S` with
`S : X.GradedQCAlgebra` get `↑S` inserted by this instance. -/
instance : CoeOut (X.GradedQCAlgebra) (X.GradedAffineAlgebra) :=
  ⟨fun S => S.toGradedAffineAlgebra⟩

end AlgebraicGeometry.Scheme.GradedQCAlgebra

end
