import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.GradedQcAlgebraSectionsRing
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.GradedQuasicoherentAlgebra
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.RelativeProjQC
import MiyaokaMori.RingTheory.GradedRing.VeroneseGradedRing
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.VeroneseSubalgebra
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.Stacks0b5j
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.RelativeProj

/-! # The Veronese algebra has the same relative Proj

`Proj_X S^{(m)} ≅ Proj_X S`: passing to a Veronese subalgebra does not change the relative Proj
(Lemma 2.2 of the paper; Stacks 0B5J).

The isomorphism is glued from chartwise isomorphisms indexed by `X.AffineZariskiSite`, natural in the chart and
compatible with the structure morphisms, via the gluing functor `GradedAffineAlgebra.projFunctor`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/- The intermediate data (the graded ring homomorphisms `ψ`, `φ` and the two directions of the chartwise
   isomorphism) and each proof obligation (membership and compatibility with the operations, the irrelevant-ideal
   conditions of the two `Proj.map`, mutual inverseness, naturality in `U`, compatibility with the structure
   morphisms) are stated separately; the definition of `relativeProj.veroneseIso` only refers to them. -/

/-- The underlying additive homomorphism of `ψ`: the `ℓ`-th piece is placed in the `ℓm`-th piece of `A(U)`. -/

noncomputable def AlgebraicGeometry.Scheme.relativeProj.veroneseIso.toVeroneseAdd {X : AlgebraicGeometry.Scheme.{u}}
    (S : X.GradedQCAlgebra) (m : ℕ) (U : X.Opens) :
    (S.veronese m).sectionsRing U →+ S.sectionsRing U :=
  DirectSum.toAddMonoid (β := (S.veronese m).sectionsPiece U)
    (fun ℓ => DirectSum.of (S.sectionsPiece U) (ℓ * m))

/-- The `i`-th component of the image is nonzero only for `i = ℓm` (the component formula of `DirectSum.of`), so it
vanishes when `m ∤ i`. -/
theorem AlgebraicGeometry.Scheme.relativeProj.veroneseIso.toVeroneseAdd_mem {X : AlgebraicGeometry.Scheme.{u}}
    (S : X.GradedQCAlgebra) (m : ℕ) (U : X.Opens) (x : (S.veronese m).sectionsRing U) :
    AlgebraicGeometry.Scheme.relativeProj.veroneseIso.toVeroneseAdd S m U x ∈ veroneseSubring (S.sectionsGrading U) m := by
  induction x using DirectSum.induction_on with
  | zero =>
      exact (veroneseSubring (S.sectionsGrading U) m).zero_mem
  | of ℓ a =>
      change (DirectSum.toAddMonoid
        (β := fun j : ℕ => (S.veronese m).sectionsPiece U j)
        (fun j : ℕ => DirectSum.of (S.sectionsPiece U) (j * m))
        ((DirectSum.of (fun j : ℕ => (S.veronese m).sectionsPiece U j) ℓ) a)) ∈
        veroneseSubring (S.sectionsGrading U) m
      have hmap := DirectSum.toAddMonoid_of
        (β := fun j : ℕ => (S.veronese m).sectionsPiece U j)
        (γ := DirectSum ℕ fun j => S.sectionsPiece U j)
        (fun j : ℕ => DirectSum.of (S.sectionsPiece U) (j * m)) ℓ a
      rw [hmap]
      apply veroneseSubring.mem_of_mem_graded
        (S.sectionsGrading U) m (dvd_mul_left m ℓ)
      exact ⟨a, rfl⟩
  | add x y hx hy =>
      change (DirectSum.toAddMonoid
        (β := fun j : ℕ => (S.veronese m).sectionsPiece U j)
        (fun j : ℕ => DirectSum.of (S.sectionsPiece U) (j * m)) (x + y)) ∈
        veroneseSubring (S.sectionsGrading U) m
      rw [map_add]
      exact (veroneseSubring (S.sectionsGrading U) m).add_mem hx hy

theorem AlgebraicGeometry.Scheme.relativeProj.veroneseIso.toVeronese_map_one {X : AlgebraicGeometry.Scheme.{u}}
    (S : X.GradedQCAlgebra) (m : ℕ) (U : X.Opens) :
    (⟨AlgebraicGeometry.Scheme.relativeProj.veroneseIso.toVeroneseAdd S m U 1, AlgebraicGeometry.Scheme.relativeProj.veroneseIso.toVeroneseAdd_mem S m U 1⟩ : veroneseSubring (S.sectionsGrading U) m) = 1 := by
  apply Subtype.ext
  change AlgebraicGeometry.Scheme.relativeProj.veroneseIso.toVeroneseAdd S m U 1 =
    (1 : S.sectionsRing U)
  change DirectSum.toAddMonoid
      (fun ℓ : ℕ => DirectSum.of (S.sectionsPiece U) (ℓ * m))
      (1 : DirectSum ℕ fun ℓ => (S.veronese m).sectionsPiece U ℓ) =
    (1 : DirectSum ℕ fun ℓ => S.sectionsPiece U ℓ)
  rw [DirectSum.one_def]
  change DirectSum.toAddMonoid
      (fun ℓ : ℕ => DirectSum.of (S.sectionsPiece U) (ℓ * m))
      (DirectSum.of (fun ℓ : ℕ => (S.veronese m).sectionsPiece U ℓ) 0
        (GradedMonoid.GOne.one : (S.veronese m).sectionsPiece U 0)) =
    (1 : DirectSum ℕ fun ℓ => S.sectionsPiece U ℓ)
  rw [DirectSum.one_def]
  have hmap := DirectSum.toAddMonoid_of
    (β := fun ℓ : ℕ => (S.veronese m).sectionsPiece U ℓ)
    (γ := DirectSum ℕ fun ℓ => S.sectionsPiece U ℓ)
    (fun ℓ : ℕ => DirectSum.of (S.sectionsPiece U) (ℓ * m)) 0
    (GradedMonoid.GOne.one : (S.veronese m).sectionsPiece U 0)
  apply hmap.trans
  apply DirectSum.of_eq_of_gradedMonoid_eq
  exact S.mk_eqToHom_app U (Nat.zero_mul m).symm (S.one.app U (1 : Γ(X, U)))


namespace AlgebraicGeometry.Scheme.relativeProj.veroneseIso

open scoped DirectSum

variable {X : AlgebraicGeometry.Scheme.{u}} (S : X.GradedQCAlgebra) (m : ℕ)

/-! ### Definitional bridge for components (`GradedQCAlgebra.component U i x` is `x i`) -/

theorem component_add (T : X.GradedQCAlgebra) (U : X.Opens) (i : ℕ) (x y : T.sectionsRing U) :
    T.component U i (x + y) = T.component U i x + T.component U i y :=
  DirectSum.add_apply _ _ _

theorem component_zero (T : X.GradedQCAlgebra) (U : X.Opens) (i : ℕ) :
    T.component U i (0 : T.sectionsRing U) = 0 := rfl

theorem component_of_same (T : X.GradedQCAlgebra) (U : X.Opens) (i : ℕ) (a : T.sectionsPiece U i) :
    T.component U i (DirectSum.of (T.sectionsPiece U) i a) = a :=
  DirectSum.of_eq_same i a

theorem component_of_ne (T : X.GradedQCAlgebra) (U : X.Opens) {i j : ℕ} (a : T.sectionsPiece U i)
    (h : j ≠ i) : T.component U j (DirectSum.of (T.sectionsPiece U) i a) = 0 :=
  DirectSum.of_eq_of_ne i j a h

theorem component_ext (T : X.GradedQCAlgebra) (U : X.Opens) {x y : T.sectionsRing U}
    (h : ∀ i, T.component U i x = T.component U i y) : x = y :=
  DirectSum.ext h

/-- The value of `ψ` on generators: `a` in the `ℓ`-th piece is placed in the `ℓm`-th piece of `A(U)`. -/
theorem toVeroneseAdd_of (U : X.Opens) (ℓ : ℕ) (a : (S.veronese m).sectionsPiece U ℓ) :
    toVeroneseAdd S m U (DirectSum.of ((S.veronese m).sectionsPiece U) ℓ a) =
      DirectSum.of (S.sectionsPiece U) (ℓ * m) a :=
  DirectSum.toAddMonoid_of _ ℓ a

/-- `ψ` preserves the unit (generator form): the graded unit of `S.veronese m`, placed in the piece `0 * m`, is the
`1` of `A(U)`. -/
theorem of_gone (U : X.Opens) :
    DirectSum.of (S.sectionsPiece U) (0 * m)
        (GradedMonoid.GOne.one : (S.veronese m).sectionsPiece U 0) = (1 : S.sectionsRing U) := by
  change _ = DirectSum.of (S.sectionsPiece U) 0 GradedMonoid.GOne.one
  apply DirectSum.of_eq_of_gradedMonoid_eq
  exact S.mk_eqToHom_app U (Nat.zero_mul m).symm (S.one.app U (1 : Γ(X, U)))

/-- `ψ` preserves the graded multiplication (generator form): the multiplication of `veronese` is `S.mul (ℓm) (ℓ'm)`
followed by the index transport `eqToHom ((ℓ+ℓ')m = ℓm + ℓ'm)`, and `mk_eqToHom_app` says the transport does not
change the `GradedMonoid` element. -/
theorem of_gmul (U : X.Opens) {i j : ℕ} (a : (S.veronese m).sectionsPiece U i)
    (b : (S.veronese m).sectionsPiece U j) :
    DirectSum.of (S.sectionsPiece U) ((i + j) * m) (GradedMonoid.GMul.mul a b) =
      DirectSum.of (S.sectionsPiece U) (i * m) a * DirectSum.of (S.sectionsPiece U) (j * m) b := by
  refine Eq.trans ?_
    (DirectSum.of_mul_of (A := S.sectionsPiece U) (i := i * m) (j := j * m) a b).symm
  exact DirectSum.of_eq_of_gradedMonoid_eq
    (S.mk_eqToHom_app U (add_mul i j m).symm (S.sectionsGMul U a b))

/-- `ψ` as a ring homomorphism (`DirectSum.toSemiring`; its underlying function is `toVeroneseAdd`). -/
noncomputable def toVeroneseSemiringHom (U : X.Opens) : (S.veronese m).sectionsRing U →+* S.sectionsRing U :=
  DirectSum.toSemiring (fun ℓ => DirectSum.of (S.sectionsPiece U) (ℓ * m)) (of_gone S m U)
    (of_gmul S m U)

theorem toVeroneseSemiringHom_apply (U : X.Opens) (x : (S.veronese m).sectionsRing U) :
    toVeroneseSemiringHom S m U x = toVeroneseAdd S m U x := rfl

/-- `ψ` preserves multiplication: the `map_mul` of `toVeroneseSemiringHom`. -/
theorem toVeronese_map_mul (U : X.Opens) (x y : (S.veronese m).sectionsRing U) :
    (⟨toVeroneseAdd S m U (x * y), toVeroneseAdd_mem S m U (x * y)⟩ :
        veroneseSubring (S.sectionsGrading U) m) =
      ⟨toVeroneseAdd S m U x, toVeroneseAdd_mem S m U x⟩ *
        ⟨toVeroneseAdd S m U y, toVeroneseAdd_mem S m U y⟩ := by
  apply Subtype.ext
  exact (toVeroneseSemiringHom S m U).map_mul x y

noncomputable def toVeroneseRingHom (U : X.Opens) :
    (S.veronese m).sectionsRing U →+* veroneseSubring (S.sectionsGrading U) m where
  toFun x := ⟨toVeroneseAdd S m U x, toVeroneseAdd_mem S m U x⟩
  map_one' := toVeronese_map_one S m U
  map_mul' := toVeronese_map_mul S m U
  map_zero' := Subtype.ext (map_zero (toVeroneseAdd S m U))
  map_add' x y := Subtype.ext (map_add (toVeroneseAdd S m U) x y)

/-- `ψ` preserves the grading (`m > 0`). **False for `m = 0`**: `ψ` sends every `of i a` to the `0`-th piece, while
`veroneseGrading 𝒜 0 i` (`i ≥ 1`) contains only `0`. -/
theorem toVeronese_map_mem (hm : 0 < m) (U : X.Opens) {i : ℕ} {x : (S.veronese m).sectionsRing U}
    (hx : x ∈ (S.veronese m).sectionsGrading U i) :
    toVeroneseRingHom S m U x ∈ veroneseGrading (S.sectionsGrading U) m i := by
  obtain ⟨a, rfl⟩ := hx
  refine ⟨?_, fun h0 => absurd h0 hm.ne'⟩
  show toVeroneseAdd S m U (DirectSum.of _ i a) ∈ S.sectionsGrading U (i * m)
  rw [toVeroneseAdd_of]
  exact ⟨a, rfl⟩

/-- `ψ : A^{(m)}(U) → A(U)^{(m)}` (a graded ring homomorphism). -/
noncomputable def toVeronese (hm : 0 < m) (U : X.Opens) :
    (S.veronese m).sectionsGrading U →+*ᵍ veroneseGrading (S.sectionsGrading U) m where
  toRingHom := toVeroneseRingHom S m U
  map_mem := toVeronese_map_mem S m hm U

/-- The underlying function of `φ`: take the `ℓm`-th component of an element of `A(U)^{(m)}`
(`DFinsupp.comapDomain`). -/
noncomputable def ofVeroneseFun (hm : 0 < m) (U : X.Opens) :
    veroneseSubring (S.sectionsGrading U) m → (S.veronese m).sectionsRing U :=
  fun y => (DFinsupp.comapDomain (β := S.sectionsPiece U) (fun ℓ : ℕ => ℓ * m)
    (fun _ _ h => Nat.eq_of_mul_eq_mul_right hm h)
    (show Π₀ j, S.sectionsPiece U j from ((y : veroneseSubring (S.sectionsGrading U) m) : S.sectionsRing U)) :
    (S.veronese m).sectionsRing U)

theorem ofVeroneseFun_apply (hm : 0 < m) (U : X.Opens) (y : veroneseSubring (S.sectionsGrading U) m)
    (ℓ : ℕ) :
    (S.veronese m).component U ℓ (ofVeroneseFun S m hm U y) =
      S.component U (ℓ * m) (y : S.sectionsRing U) :=
  DFinsupp.comapDomain_apply _ _ _ _

/-- The `ℓm`-th component of `ψ x` is the `ℓ`-th component of `x` (`m > 0`). -/
theorem toVeroneseAdd_apply_mul (hm : 0 < m) (U : X.Opens) (x : (S.veronese m).sectionsRing U)
    (ℓ : ℕ) :
    S.component U (ℓ * m) (toVeroneseAdd S m U x) = (S.veronese m).component U ℓ x := by
  induction x using DirectSum.induction_on with
  | zero =>
      exact (congrArg (S.component U (ℓ * m)) (map_zero (toVeroneseAdd S m U))).trans rfl
  | of j a =>
      rw [toVeroneseAdd_of]
      by_cases h : j = ℓ
      · subst h
        exact (component_of_same S U _ a).trans (component_of_same (S.veronese m) U _ a).symm
      · exact (component_of_ne S U a (fun e => h (Nat.eq_of_mul_eq_mul_right hm e).symm)).trans
          (component_of_ne (S.veronese m) U a (Ne.symm h)).symm
  | add x y hx hy =>
      exact ((congrArg (S.component U (ℓ * m)) (map_add (toVeroneseAdd S m U) x y)).trans
        (component_add S U _ _ _)).trans
        ((congrArg₂ (· + ·) hx hy).trans (component_add (S.veronese m) U ℓ x y).symm)

/-- The components of the image of `ψ` at non-multiples of `m` vanish. -/
theorem toVeroneseAdd_apply_of_not_dvd (U : X.Opens) (x : (S.veronese m).sectionsRing U) {i : ℕ}
    (hi : ¬ m ∣ i) : S.component U i (toVeroneseAdd S m U x) = 0 := by
  induction x using DirectSum.induction_on with
  | zero => exact (congrArg (S.component U i) (map_zero (toVeroneseAdd S m U))).trans rfl
  | of j a =>
      rw [toVeroneseAdd_of]
      exact component_of_ne S U a (fun e => hi (e ▸ dvd_mul_left m j))
  | add x y hx hy =>
      refine ((congrArg (S.component U i) (map_add (toVeroneseAdd S m U) x y)).trans
        (component_add S U _ _ _)).trans ?_
      exact (congrArg₂ (· + ·) hx hy).trans (add_zero 0)

/-- The components of an element of `A(U)^{(m)}` at non-multiples of `m` vanish: this is the definition of
`veroneseSubring` (`GradedRing.proj 𝒜 i y = 0`), and the decomposition of `A(U)` is the componentwise
`DirectSum.map`. -/
theorem component_eq_zero_of_mem_veroneseSubring (U : X.Opens)
    (y : veroneseSubring (S.sectionsGrading U) m) {i : ℕ} (hi : ¬ m ∣ i) :
    S.component U i (y : S.sectionsRing U) = 0 := by
  have h := y.2 i hi
  rw [GradedRing.proj_apply] at h
  have h' : DirectSum.of (S.sectionsPiece U) i (S.component U i (y : S.sectionsRing U)) = 0 := h
  exact DirectSum.of_injective i (h'.trans (map_zero _).symm)

/-- `ψ ∘ φ = id` (on `A(U)^{(m)}`). -/
theorem toVeroneseAdd_ofVeroneseFun (hm : 0 < m) (U : X.Opens)
    (y : veroneseSubring (S.sectionsGrading U) m) :
    toVeroneseAdd S m U (ofVeroneseFun S m hm U y) = (y : S.sectionsRing U) := by
  refine component_ext S U fun i => ?_
  by_cases hi : m ∣ i
  · obtain ⟨ℓ, hℓ⟩ := hi
    rw [mul_comm] at hℓ
    subst hℓ
    rw [toVeroneseAdd_apply_mul S m hm U]
    exact ofVeroneseFun_apply S m hm U y ℓ
  · rw [toVeroneseAdd_apply_of_not_dvd S m U _ hi,
      component_eq_zero_of_mem_veroneseSubring S m U y hi]

/-- `φ ∘ ψ = id` (on `A^{(m)}(U)`). -/
theorem ofVeroneseFun_toVeroneseAdd (hm : 0 < m) (U : X.Opens) (x : (S.veronese m).sectionsRing U) :
    ofVeroneseFun S m hm U ⟨toVeroneseAdd S m U x, toVeroneseAdd_mem S m U x⟩ = x := by
  refine component_ext (S.veronese m) U fun ℓ => ?_
  rw [ofVeroneseFun_apply]
  exact toVeroneseAdd_apply_mul S m hm U x ℓ

theorem ofVeronese_map_one (hm : 0 < m) (U : X.Opens) : ofVeroneseFun S m hm U 1 = 1 := by
  rw [← toVeronese_map_one S m U]
  exact ofVeroneseFun_toVeroneseAdd S m hm U 1

theorem ofVeronese_map_mul (hm : 0 < m) (U : X.Opens) (x y : veroneseSubring (S.sectionsGrading U) m) :
    ofVeroneseFun S m hm U (x * y) =
      ofVeroneseFun S m hm U x * ofVeroneseFun S m hm U y := by
  have hx : x = ⟨toVeroneseAdd S m U (ofVeroneseFun S m hm U x),
      toVeroneseAdd_mem S m U (ofVeroneseFun S m hm U x)⟩ :=
    Subtype.ext (toVeroneseAdd_ofVeroneseFun S m hm U x).symm
  have hy : y = ⟨toVeroneseAdd S m U (ofVeroneseFun S m hm U y),
      toVeroneseAdd_mem S m U (ofVeroneseFun S m hm U y)⟩ :=
    Subtype.ext (toVeroneseAdd_ofVeroneseFun S m hm U y).symm
  conv_lhs => rw [hx, hy]
  rw [← toVeronese_map_mul, ofVeroneseFun_toVeroneseAdd]

/-- By `DFinsupp.comapDomain_zero`. -/
theorem ofVeronese_map_zero (hm : 0 < m) (U : X.Opens) : ofVeroneseFun S m hm U 0 = 0 := by
  exact DFinsupp.comapDomain_zero _ _

/-- By `DFinsupp.comapDomain_add`. -/
theorem ofVeronese_map_add (hm : 0 < m) (U : X.Opens) (x y : veroneseSubring (S.sectionsGrading U) m) :
    ofVeroneseFun S m hm U (x + y) =
      ofVeroneseFun S m hm U x + ofVeroneseFun S m hm U y := by
  exact DFinsupp.comapDomain_add _ _ _ _

noncomputable def ofVeroneseRingHom (hm : 0 < m) (U : X.Opens) :
    veroneseSubring (S.sectionsGrading U) m →+* (S.veronese m).sectionsRing U where
  toFun := ofVeroneseFun S m hm U
  map_one' := ofVeronese_map_one S m hm U
  map_mul' := ofVeronese_map_mul S m hm U
  map_zero' := ofVeronese_map_zero S m hm U
  map_add' := ofVeronese_map_add S m hm U

/-- `φ` preserves the grading: `y ∈ A(U)_{im}` means `y = of (im) a`, and `comapDomain` turns it into `of i a`. -/
theorem ofVeronese_map_mem (hm : 0 < m) (U : X.Opens) {i : ℕ} {y : veroneseSubring (S.sectionsGrading U) m}
    (hy : y ∈ veroneseGrading (S.sectionsGrading U) m i) :
    ofVeroneseRingHom S m hm U y ∈ (S.veronese m).sectionsGrading U i := by
  obtain ⟨a, ha⟩ := hy.1
  refine ⟨a, ?_⟩
  show DirectSum.of ((S.veronese m).sectionsPiece U) i a =
    DFinsupp.comapDomain (β := S.sectionsPiece U) (fun ℓ : ℕ => ℓ * m)
      (fun _ _ h => Nat.eq_of_mul_eq_mul_right hm h) (y : S.sectionsRing U)
  rw [← ha]
  exact (DFinsupp.comapDomain_single (β := S.sectionsPiece U) (fun ℓ : ℕ => ℓ * m)
    (fun _ _ h => Nat.eq_of_mul_eq_mul_right hm h) i a).symm

/-- `φ : A(U)^{(m)} → A^{(m)}(U)` (a graded ring homomorphism). -/
noncomputable def ofVeronese (hm : 0 < m) (U : X.Opens) :
    veroneseGrading (S.sectionsGrading U) m →+*ᵍ (S.veronese m).sectionsGrading U where
  toRingHom := ofVeroneseRingHom S m hm U
  map_mem := ofVeronese_map_mem S m hm U

theorem ofVeronese_toVeronese (hm : 0 < m) (U : X.Opens) (x : (S.veronese m).sectionsRing U) :
    ofVeronese S m hm U (toVeronese S m hm U x) = x :=
  ofVeroneseFun_toVeroneseAdd S m hm U x

theorem toVeronese_ofVeronese (hm : 0 < m) (U : X.Opens) (y : veroneseSubring (S.sectionsGrading U) m) :
    toVeronese S m hm U (ofVeronese S m hm U y) = y :=
  Subtype.ext (toVeroneseAdd_ofVeroneseFun S m hm U y)

theorem ofVeronese_comp_toVeronese (hm : 0 < m) (U : X.Opens) :
    (ofVeronese S m hm U).comp (toVeronese S m hm U) =
      GradedRingHom.id ((S.veronese m).sectionsGrading U) :=
  GradedRingHom.ext fun x => ofVeronese_toVeronese S m hm U x

theorem toVeronese_comp_ofVeronese (hm : 0 < m) (U : X.Opens) :
    (toVeronese S m hm U).comp (ofVeronese S m hm U) =
      GradedRingHom.id (veroneseGrading (S.sectionsGrading U) m) :=
  GradedRingHom.ext fun y => toVeronese_ofVeronese S m hm U y

/-- The irrelevant-ideal condition for `Proj.map φ`: for `x ∈ A^{(m)}(U)_i` (`i > 0`), `x = φ(ψ x)`, and `ψ x` is
homogeneous of positive degree, hence in the irrelevant ideal. -/
theorem irrelevant_le_map_ofVeronese (hm : 0 < m) (U : X.Opens) :
    HomogeneousIdeal.irrelevant ((S.veronese m).sectionsGrading U) ≤
      HomogeneousIdeal.map (ofVeronese S m hm U)
        (HomogeneousIdeal.irrelevant (veroneseGrading (S.sectionsGrading U) m)) := by
  rw [HomogeneousIdeal.irrelevant_le]
  intro i hi x hx
  have hx' : x ∈ (S.veronese m).sectionsGrading U i := hx
  have hψ : toVeronese S m hm U x ∈
      HomogeneousIdeal.irrelevant (veroneseGrading (S.sectionsGrading U) m) :=
    HomogeneousIdeal.mem_irrelevant_of_mem _ hi (toVeronese_map_mem S m hm U hx')
  have h := Ideal.mem_map_of_mem (ofVeronese S m hm U) hψ
  rw [ofVeronese_toVeronese] at h
  exact h

/-- The irrelevant-ideal condition for `Proj.map ψ` (symmetric). -/
theorem irrelevant_le_map_toVeronese (hm : 0 < m) (U : X.Opens) :
    HomogeneousIdeal.irrelevant (veroneseGrading (S.sectionsGrading U) m) ≤
      HomogeneousIdeal.map (toVeronese S m hm U)
        (HomogeneousIdeal.irrelevant ((S.veronese m).sectionsGrading U)) := by
  rw [HomogeneousIdeal.irrelevant_le]
  intro i hi y hy
  have hy' : y ∈ veroneseGrading (S.sectionsGrading U) m i := hy
  have hφ : ofVeronese S m hm U y ∈
      HomogeneousIdeal.irrelevant ((S.veronese m).sectionsGrading U) :=
    HomogeneousIdeal.mem_irrelevant_of_mem _ hi (ofVeronese_map_mem S m hm U hy')
  have h := Ideal.mem_map_of_mem (toVeronese S m hm U) hφ
  rw [toVeronese_ofVeronese] at h
  exact h

/-- `Proj.map` depends only on the graded homomorphism, not on the proof of the irrelevant-ideal condition. -/
theorem proj_map_congr {A B σ τ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
    [CommRing B] [SetLike τ B] [AddSubgroupClass τ B]
    {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ]
    {f g : 𝒜 →+*ᵍ ℬ} (e : f = g)
    (hf : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map f)
    (hg : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map g) :
    AlgebraicGeometry.Proj.map f hf = AlgebraicGeometry.Proj.map g hg := by
  subst e; rfl

/-- By functoriality of `Proj.map` (`Proj.map_comp` / `Proj.map_id`) and `φ ∘ ψ = id`. -/
theorem map_ofVeronese_comp_map_toVeronese (hm : 0 < m) (U : X.Opens) :
    AlgebraicGeometry.Proj.map (ofVeronese S m hm U) (irrelevant_le_map_ofVeronese S m hm U) ≫
        AlgebraicGeometry.Proj.map (toVeronese S m hm U) (irrelevant_le_map_toVeronese S m hm U) =
      𝟙 _ := by
  rw [← AlgebraicGeometry.Proj.map_comp,
    proj_map_congr (ofVeronese_comp_toVeronese S m hm U) _ (by simp)]
  exact AlgebraicGeometry.Proj.map_id

theorem map_toVeronese_comp_map_ofVeronese (hm : 0 < m) (U : X.Opens) :
    AlgebraicGeometry.Proj.map (toVeronese S m hm U) (irrelevant_le_map_toVeronese S m hm U) ≫
        AlgebraicGeometry.Proj.map (ofVeronese S m hm U) (irrelevant_le_map_ofVeronese S m hm U) =
      𝟙 _ := by
  rw [← AlgebraicGeometry.Proj.map_comp,
    proj_map_congr (toVeronese_comp_ofVeronese S m hm U) _ (by simp)]
  exact AlgebraicGeometry.Proj.map_id

end AlgebraicGeometry.Scheme.relativeProj.veroneseIso


/-! ## Two general compatibilities on the Stacks 0B5J side

`Proj.veroneseHom` is natural in graded homomorphisms and compatible with `toSpecZero`. The proofs reduce, via
`hom_ext` along Mathlib's affine open covers `Proj.affineOpenCover` / `Proj.mapAffineOpenCover`, to a single chart
`D₊(f)`, then write `veroneseHom` as `Spec.map (veroneseAwayEquiv) ≫ awayι` using `awayι_comp_veroneseHom` /
`veroneseChart_eq` of `Stacks0b5j.lean`, and finish with a numerator/denominator computation in
`HomogeneousLocalization`. -/

namespace AlgebraicGeometry.Proj

attribute [local instance] AlgebraicGeometry.Proj.veroneseHom_isIso

theorem veroneseIso_hom {A σ : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
    (𝒜 : ℕ → σ) [GradedRing 𝒜] (d : ℕ) (hd : 0 < d) :
    (AlgebraicGeometry.Proj.veroneseIso 𝒜 d hd).hom = inv (AlgebraicGeometry.Proj.veroneseHom 𝒜 d hd) :=
  rfl

/-- Transport of `awayι` along an equality of elements `f = f'`: `Away 𝒜 f → Away 𝒜 f'` is
`HomogeneousLocalization.mapId`. -/
theorem awayι_congr_elem {A σ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
    (𝒜 : ℕ → σ) [GradedRing 𝒜] {f f' : A} (e : f = f') {i : ℕ} (hf : f ∈ 𝒜 i) (hf' : f' ∈ 𝒜 i)
    (hi : 0 < i) :
    AlgebraicGeometry.Proj.awayι 𝒜 f hf hi =
      AlgebraicGeometry.Spec.map (CommRingCat.ofHom
        (HomogeneousLocalization.mapId 𝒜 (le_of_eq (congrArg Submonoid.powers e.symm)))) ≫
        AlgebraicGeometry.Proj.awayι 𝒜 f' hf' hi := by
  subst e
  simp [HomogeneousLocalization.mapId]

/-- The value of `veroneseAwayEquiv` on `mk` (definitional). -/
theorem veroneseAwayEquiv_mk {A σ : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
    (𝒜 : ℕ → σ) [GradedRing 𝒜] (d : ℕ) (hd : 0 < d) {f : A} {i : ℕ} (hf : f ∈ 𝒜 i)
    (c : HomogeneousLocalization.NumDenSameDeg (veroneseGrading 𝒜 d)
      (Submonoid.powers (⟨f ^ d, (veronese_pow_mem 𝒜 d hd hf).1⟩ : veroneseSubring 𝒜 d))) :
    veroneseAwayEquiv 𝒜 d hd hf (HomogeneousLocalization.mk c) =
      HomogeneousLocalization.mk (veroneseAwayEquiv.toNumDen 𝒜 d hd hf c) := rfl

theorem veroneseAwayEquiv_toRingHom_mk {A σ : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
    (𝒜 : ℕ → σ) [GradedRing 𝒜] (d : ℕ) (hd : 0 < d) {f : A} {i : ℕ} (hf : f ∈ 𝒜 i)
    (c : HomogeneousLocalization.NumDenSameDeg (veroneseGrading 𝒜 d)
      (Submonoid.powers (⟨f ^ d, (veronese_pow_mem 𝒜 d hd hf).1⟩ : veroneseSubring 𝒜 d))) :
    (veroneseAwayEquiv 𝒜 d hd hf).toRingHom (HomogeneousLocalization.mk c) =
      HomogeneousLocalization.mk (veroneseAwayEquiv.toNumDen 𝒜 d hd hf c) := rfl

set_option backward.isDefEq.respectTransparency false in
/-- **`veroneseHom` is natural in graded ring homomorphisms** (the construction of Stacks 0B5J is functorial).
`g : 𝒜 →+*ᵍ 𝒜'` is arbitrary and `g'` is any graded homomorphism induced by `g` on the Veronese subrings (only
required to agree with `g` elementwise).
Proof: `hom_ext` along `Proj.mapAffineOpenCover g hg` (charts `D₊(g f)`, `f ∈ 𝒜` of positive degree); both sides
become `Spec.map (ring hom) ≫ awayι (S^{(d)}) ⟨f^d⟩`, and both ring homomorphisms send `mk ⟨n, a, (f^d)^k⟩` to
`mk ⟨nd, g a, g (f^d)^k⟩` (`NumDenSameDeg.ext`). -/
theorem veroneseHom_naturality {A A' σ σ' : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
    [CommRing A'] [SetLike σ' A'] [AddSubgroupClass σ' A']
    (𝒜 : ℕ → σ) (𝒜' : ℕ → σ') [GradedRing 𝒜] [GradedRing 𝒜'] (d : ℕ) (hd : 0 < d)
    (g : 𝒜 →+*ᵍ 𝒜') (hg : HomogeneousIdeal.irrelevant 𝒜' ≤ (HomogeneousIdeal.irrelevant 𝒜).map g)
    (g' : veroneseGrading 𝒜 d →+*ᵍ veroneseGrading 𝒜' d)
    (hg' : HomogeneousIdeal.irrelevant (veroneseGrading 𝒜' d) ≤
      (HomogeneousIdeal.irrelevant (veroneseGrading 𝒜 d)).map g')
    (hgg' : ∀ x : veroneseSubring 𝒜 d, ((g' x : veroneseSubring 𝒜' d) : A') = g x) :
    AlgebraicGeometry.Proj.map g hg ≫ AlgebraicGeometry.Proj.veroneseHom 𝒜 d hd =
      AlgebraicGeometry.Proj.veroneseHom 𝒜' d hd ≫ AlgebraicGeometry.Proj.map g' hg' := by
  refine (AlgebraicGeometry.Proj.mapAffineOpenCover g hg).openCover.hom_ext _ _ fun s => ?_
  have hL := AlgebraicGeometry.Proj.awayι_comp_veroneseHom 𝒜 d hd s
  have hR := AlgebraicGeometry.Proj.awayι_comp_veroneseHom_assoc 𝒜' d hd
    ⟨s.1, ⟨g s.2.1, g.2 s.2.2⟩⟩ (AlgebraicGeometry.Proj.map g' hg')
  simp only [AlgebraicGeometry.Scheme.AffineOpenCover.openCover_f,
    AlgebraicGeometry.Proj.affineOpenCover_f] at hL hR
  simp only [AlgebraicGeometry.Scheme.AffineOpenCover.openCover_f,
    AlgebraicGeometry.Proj.mapAffineOpenCover_f]
  rw [AlgebraicGeometry.Proj.awayι_comp_map_assoc g hg s.1.2 s.2.1 s.2.2, hL, hR,
    AlgebraicGeometry.Proj.veroneseChart_eq, AlgebraicGeometry.Proj.veroneseChart_eq]
  have e : (⟨g s.2.1 ^ d, (veronese_pow_mem 𝒜' d hd (g.2 s.2.2)).1⟩ : veroneseSubring 𝒜' d) =
      g' ⟨s.2.1 ^ d, (veronese_pow_mem 𝒜 d hd s.2.2).1⟩ :=
    Subtype.ext ((hgg' _).trans (map_pow g s.2.1 d)).symm
  rw [awayι_congr_elem (veroneseGrading 𝒜' d) e _ (g'.2 (veronese_pow_mem_grading 𝒜 d hd s.2.2)),
    Category.assoc, Category.assoc,
    AlgebraicGeometry.Proj.awayι_comp_map g' hg' s.1.2 _ (veronese_pow_mem_grading 𝒜 d hd s.2.2)]
  simp only [← Category.assoc, ← AlgebraicGeometry.Spec.map_comp]
  congr 2
  ext x
  obtain ⟨c, rfl⟩ := HomogeneousLocalization.mk_surjective x
  simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.coe_comp, Function.comp_apply]
  erw [veroneseAwayEquiv_toRingHom_mk, HomogeneousLocalization.map_mk,
    HomogeneousLocalization.map_mk, veroneseAwayEquiv_toRingHom_mk]
  exact congrArg HomogeneousLocalization.val (congrArg HomogeneousLocalization.mk
    (HomogeneousLocalization.NumDenSameDeg.ext _ rfl (hgg' c.num).symm (hgg' c.den).symm))

/-- The comparison of degree-`0` pieces `(S^{(d)})_0 → S_0` (`x ∈ 𝒜 (0·d) = 𝒜 0`). -/
def veroneseZeroToZero {A σ : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
    (𝒜 : ℕ → σ) [GradedRing 𝒜] (d : ℕ) : veroneseGrading 𝒜 d 0 →+* 𝒜 0 where
  toFun y := ⟨((y : veroneseSubring 𝒜 d) : A), by
    have h := y.2.1
    rwa [Nat.zero_mul] at h⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

/-- The other direction `S_0 → (S^{(d)})_0`. -/
def zeroToVeroneseZero {A σ : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
    (𝒜 : ℕ → σ) [GradedRing 𝒜] (d : ℕ) : 𝒜 0 →+* veroneseGrading 𝒜 d 0 where
  toFun x := ⟨⟨(x : A), veroneseSubring.mem_of_mem_graded 𝒜 d (dvd_zero d) x.2⟩,
    ⟨by rw [Nat.zero_mul]; exact x.2, fun _ => Or.inl rfl⟩⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

theorem zeroToVeroneseZero_comp_veroneseZeroToZero {A σ : Type*} [CommRing A] [SetLike σ A]
    [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜] (d : ℕ) :
    (zeroToVeroneseZero 𝒜 d).comp (veroneseZeroToZero 𝒜 d) = RingHom.id _ :=
  RingHom.ext fun _ => Subtype.ext (Subtype.ext rfl)

theorem veroneseZeroToZero_comp_zeroToVeroneseZero {A σ : Type*} [CommRing A] [SetLike σ A]
    [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜] (d : ℕ) :
    (veroneseZeroToZero 𝒜 d).comp (zeroToVeroneseZero 𝒜 d) = RingHom.id _ :=
  RingHom.ext fun _ => Subtype.ext rfl

set_option backward.isDefEq.respectTransparency false in
/-- **`veroneseHom` is compatible with the structure morphism `toSpecZero`**: the two maps to the Spec of the
degree-`0` piece differ only by `(S^{(d)})_0 = S_0`. -/
theorem veroneseHom_toSpecZero {A σ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
    (𝒜 : ℕ → σ) [GradedRing 𝒜] (d : ℕ) (hd : 0 < d) :
    AlgebraicGeometry.Proj.veroneseHom 𝒜 d hd ≫
        AlgebraicGeometry.Proj.toSpecZero (veroneseGrading 𝒜 d) =
      AlgebraicGeometry.Proj.toSpecZero 𝒜 ≫
        AlgebraicGeometry.Spec.map (CommRingCat.ofHom (veroneseZeroToZero 𝒜 d)) := by
  refine (AlgebraicGeometry.Proj.affineOpenCover 𝒜).openCover.hom_ext _ _ fun s => ?_
  have hL := AlgebraicGeometry.Proj.awayι_comp_veroneseHom 𝒜 d hd s
  simp only [AlgebraicGeometry.Scheme.AffineOpenCover.openCover_f,
    AlgebraicGeometry.Proj.affineOpenCover_f] at hL ⊢
  rw [← Category.assoc, hL, AlgebraicGeometry.Proj.veroneseChart_eq, Category.assoc,
    AlgebraicGeometry.Proj.awayι_toSpecZero, ← Category.assoc,
    AlgebraicGeometry.Proj.awayι_toSpecZero, ← AlgebraicGeometry.Spec.map_comp,
    ← AlgebraicGeometry.Spec.map_comp]
  congr 1
  refine CommRingCat.hom_ext (RingHom.ext fun a => HomogeneousLocalization.val_injective _ ?_)
  rfl

end AlgebraicGeometry.Proj

/-- The chartwise isomorphism `Proj A^{(m)}(U) ≅ Proj A(U)^{(m)} ≅ Proj A(U)` (the second part is
`Proj.veroneseIso` of Stacks 0B5J). -/

noncomputable def AlgebraicGeometry.Scheme.relativeProj.veroneseIso.chartIso {X : AlgebraicGeometry.Scheme.{u}}
    (S : X.GradedQCAlgebra) (m : ℕ) (hm : 0 < m) (U : X.AffineZariskiSite) :
    AlgebraicGeometry.Proj ((S.veronese m).sectionsGrading U.toOpens) ≅
      AlgebraicGeometry.Proj (S.sectionsGrading U.toOpens) :=
  { hom := AlgebraicGeometry.Proj.map (AlgebraicGeometry.Scheme.relativeProj.veroneseIso.ofVeronese S m hm U.toOpens)
      (AlgebraicGeometry.Scheme.relativeProj.veroneseIso.irrelevant_le_map_ofVeronese S m hm U.toOpens)
    inv := AlgebraicGeometry.Proj.map (AlgebraicGeometry.Scheme.relativeProj.veroneseIso.toVeronese S m hm U.toOpens)
      (AlgebraicGeometry.Scheme.relativeProj.veroneseIso.irrelevant_le_map_toVeronese S m hm U.toOpens)
    hom_inv_id := AlgebraicGeometry.Scheme.relativeProj.veroneseIso.map_ofVeronese_comp_map_toVeronese S m hm U.toOpens
    inv_hom_id := AlgebraicGeometry.Scheme.relativeProj.veroneseIso.map_toVeronese_comp_map_ofVeronese S m hm U.toOpens } ≪≫
  AlgebraicGeometry.Proj.veroneseIso (S.sectionsGrading U.toOpens) m hm

namespace AlgebraicGeometry.Scheme.relativeProj.veroneseIso

attribute [local instance] AlgebraicGeometry.Proj.veroneseHom_isIso

variable {X : AlgebraicGeometry.Scheme.{u}} (S : X.GradedQCAlgebra) (m : ℕ)

/-- The components of the restriction homomorphism: piecewise restriction (`sectionsRestrictHom_toAddMonoidHom` +
`DirectSum.map_apply`). -/
theorem component_restrict (T : X.GradedQCAlgebra) {U V : X.Opens} (h : U ≤ V) (i : ℕ)
    (y : T.sectionsRing V) :
    T.component U i (T.sectionsRestrictHom h y) = T.sectionsRestrictPiece h i (T.component V i y) := by
  have h1 : (T.sectionsRestrictHom h).toAddMonoidHom y =
      DirectSum.map (fun m => T.sectionsRestrictPiece h m) y :=
    congrArg (fun φ => φ y) (T.sectionsRestrictHom_toAddMonoidHom h)
  exact (congrArg (T.component U i) h1).trans (DirectSum.map_apply _ i y)

/-- The restriction `restrictGraded` is `sectionsRestrictHom` on the sections-ring encoding. -/
theorem restrictGraded_apply' (T : X.GradedQCAlgebra) {U V : X.AffineZariskiSite} (h : U ≤ V)
    (y : T.sectionsRing V.toOpens) :
    T.toGradedAffineAlgebra.restrictGraded h y =
      T.sectionsRestrictHom (AlgebraicGeometry.Scheme.AffineZariskiSite.toOpens_mono h) y := rfl

theorem ofVeronese_apply (hm : 0 < m) (U : X.Opens) (y : veroneseSubring (S.sectionsGrading U) m) :
    ofVeronese S m hm U y = ofVeroneseFun S m hm U y := rfl

theorem toVeronese_apply (hm : 0 < m) (U : X.Opens) (x : (S.veronese m).sectionsRing U) :
    ((toVeronese S m hm U x : veroneseSubring (S.sectionsGrading U) m) : S.sectionsRing U) =
      toVeroneseAdd S m U x := rfl

/-- `ψ_U ∘ res^{(m)} ∘ φ_V` is the restriction `A(V) → A(U)` on the underlying rings (componentwise comparison). -/
theorem toVeronese_restrict_ofVeronese (hm : 0 < m) {U V : X.AffineZariskiSite} (h : U ≤ V)
    (x : veroneseSubring (S.sectionsGrading V.toOpens) m) :
    ((toVeronese S m hm U.toOpens ((S.veronese m).toGradedAffineAlgebra.restrictGraded h
        (ofVeronese S m hm V.toOpens x)) : veroneseSubring (S.sectionsGrading U.toOpens) m) :
      S.sectionsRing U.toOpens) =
    S.toGradedAffineAlgebra.restrictGraded h (x : S.sectionsRing V.toOpens) := by
  rw [restrictGraded_apply', restrictGraded_apply', toVeronese_apply, ofVeronese_apply]
  refine component_ext S U.toOpens fun i => ?_
  rw [component_restrict]
  by_cases hi : m ∣ i
  · obtain ⟨ℓ, hℓ⟩ := hi
    rw [mul_comm] at hℓ
    subst hℓ
    rw [toVeroneseAdd_apply_mul S m hm, component_restrict, ofVeroneseFun_apply]
    rfl
  · rw [toVeroneseAdd_apply_of_not_dvd S m _ _ hi,
      component_eq_zero_of_mem_veroneseSubring S m _ x hi, map_zero]

/-- The chartwise isomorphisms are natural for `U ≤ V`: functoriality of `Proj.map` + naturality of `veroneseHom`
in graded homomorphisms (`Proj.veroneseHom_naturality` with `g' = ψ_U ∘ res^{(m)} ∘ φ_V`). -/
theorem chartIso_naturality (hm : 0 < m) {U V : X.AffineZariskiSite} (f : U ⟶ V) :
    (S.veronese m).toGradedAffineAlgebra.projFunctor.map f ≫ (chartIso S m hm V).hom =
      (chartIso S m hm U).hom ≫ S.toGradedAffineAlgebra.projFunctor.map f := by
  have h : U ≤ V := leOfHom f
  let resS : S.sectionsGrading V.toOpens →+*ᵍ S.sectionsGrading U.toOpens :=
    S.toGradedAffineAlgebra.restrictGraded h
  let resB : (S.veronese m).sectionsGrading V.toOpens →+*ᵍ (S.veronese m).sectionsGrading U.toOpens :=
    (S.veronese m).toGradedAffineAlgebra.restrictGraded h
  have hS : HomogeneousIdeal.irrelevant (S.sectionsGrading U.toOpens) ≤
      (HomogeneousIdeal.irrelevant (S.sectionsGrading V.toOpens)).map resS :=
    S.toGradedAffineAlgebra.restrict_irrelevant_le h
  have hB : HomogeneousIdeal.irrelevant ((S.veronese m).sectionsGrading U.toOpens) ≤
      (HomogeneousIdeal.irrelevant ((S.veronese m).sectionsGrading V.toOpens)).map resB :=
    (S.veronese m).toGradedAffineAlgebra.restrict_irrelevant_le h
  let ρ : veroneseGrading (S.sectionsGrading V.toOpens) m →+*ᵍ
      veroneseGrading (S.sectionsGrading U.toOpens) m :=
    ((toVeronese S m hm U.toOpens).comp resB).comp (ofVeronese S m hm V.toOpens)
  have hρ : HomogeneousIdeal.irrelevant (veroneseGrading (S.sectionsGrading U.toOpens) m) ≤
      (HomogeneousIdeal.irrelevant (veroneseGrading (S.sectionsGrading V.toOpens) m)).map ρ :=
    HomogeneousIdeal.irrelevant_le_map_comp (irrelevant_le_map_ofVeronese S m hm V.toOpens)
      (HomogeneousIdeal.irrelevant_le_map_comp hB (irrelevant_le_map_toVeronese S m hm U.toOpens))
  have key := AlgebraicGeometry.Proj.veroneseHom_naturality (S.sectionsGrading V.toOpens)
    (S.sectionsGrading U.toOpens) m hm resS hS ρ hρ
    (fun x => toVeronese_restrict_ofVeronese S m hm h x)
  have key' : inv (AlgebraicGeometry.Proj.veroneseHom (S.sectionsGrading U.toOpens) m hm) ≫
      AlgebraicGeometry.Proj.map resS hS =
      AlgebraicGeometry.Proj.map ρ hρ ≫
        inv (AlgebraicGeometry.Proj.veroneseHom (S.sectionsGrading V.toOpens) m hm) := by
    rw [IsIso.inv_comp_eq, ← Category.assoc, ← key, Category.assoc, IsIso.hom_inv_id,
      Category.comp_id]
  have e : resB.comp (ofVeronese S m hm V.toOpens) = (ofVeronese S m hm U.toOpens).comp ρ :=
    GradedRingHom.ext fun x => (ofVeronese_toVeronese S m hm U.toOpens _).symm
  show AlgebraicGeometry.Proj.map resB hB ≫
      (AlgebraicGeometry.Proj.map (ofVeronese S m hm V.toOpens)
        (irrelevant_le_map_ofVeronese S m hm V.toOpens) ≫
        inv (AlgebraicGeometry.Proj.veroneseHom (S.sectionsGrading V.toOpens) m hm)) =
    (AlgebraicGeometry.Proj.map (ofVeronese S m hm U.toOpens)
        (irrelevant_le_map_ofVeronese S m hm U.toOpens) ≫
        inv (AlgebraicGeometry.Proj.veroneseHom (S.sectionsGrading U.toOpens) m hm)) ≫
      AlgebraicGeometry.Proj.map resS hS
  rw [Category.assoc, key', ← Category.assoc, ← Category.assoc,
    ← AlgebraicGeometry.Proj.map_comp, ← AlgebraicGeometry.Proj.map_comp]
  exact congrArg (· ≫ inv (AlgebraicGeometry.Proj.veroneseHom (S.sectionsGrading V.toOpens) m hm))
    (proj_map_congr e _ _)

noncomputable def natIso (hm : 0 < m) :
    (S.veronese m).toGradedAffineAlgebra.projFunctor ≅ S.toGradedAffineAlgebra.projFunctor :=
  CategoryTheory.NatIso.ofComponents (fun U => chartIso S m hm U)
    (fun f => chartIso_naturality S m hm f)

/-- The colimit of the natural isomorphism of gluing functors gives the isomorphism of the underlying schemes. -/
noncomputable def leftIso (hm : 0 < m) :
    (AlgebraicGeometry.Scheme.relativeProj (S.veronese m)).left ≅
      (AlgebraicGeometry.Scheme.relativeProj S).left :=
  CategoryTheory.Limits.HasColimit.isoOfNatIso (natIso S m hm)

/-- `Spec.map (φ)_0 ≫ Spec.map ((S^{(m)})_0 → S_0) ≫ Spec.map (Γ(X,U) → A(U)_0) = Spec.map (Γ(X,U) → A^{(m)}(U)_0)`
at the level of ring homomorphisms: for `r ∈ Γ(X,U)`, `φ` sends `of 0 (S.one.app U r)` (regarded as a degree-`0`
element of the Veronese subring) to `of 0 ((S.veronese m).one.app U r)`; the two differ only by the `eqToHom`
transport of the index `0 * m = 0`, which follows from `φ ∘ ψ = id` and `mk_eqToHom_app`. -/
theorem ofVeronese_zero_unit (hm : 0 < m) (U : X.AffineZariskiSite) (r : Γ(X, U.toOpens)) :
    (ofVeronese S m hm U.toOpens).gradedZeroRingHom
        (AlgebraicGeometry.Proj.zeroToVeroneseZero (S.sectionsGrading U.toOpens) m
          (S.toGradedAffineAlgebra.unitZero U r)) =
      (S.veronese m).toGradedAffineAlgebra.unitZero U r := by
  apply Subtype.ext
  change ofVeroneseFun S m hm U.toOpens _ = DirectSum.of ((S.veronese m).sectionsPiece U.toOpens) 0
    ((S.veronese m).one.app U.toOpens r)
  have h1 : DirectSum.of (S.sectionsPiece U.toOpens) 0 (S.one.app U.toOpens r) =
      toVeroneseAdd S m U.toOpens (DirectSum.of ((S.veronese m).sectionsPiece U.toOpens) 0
        ((S.veronese m).one.app U.toOpens r)) :=
    (DirectSum.of_eq_of_gradedMonoid_eq
      (S.mk_eqToHom_app U.toOpens (Nat.zero_mul m).symm (S.one.app U.toOpens r)).symm).trans
      (toVeroneseAdd_of S m U.toOpens 0 ((S.veronese m).one.app U.toOpens r)).symm
  have h2 : (⟨DirectSum.of (S.sectionsPiece U.toOpens) 0 (S.one.app U.toOpens r),
      veroneseSubring.mem_of_mem_graded (S.sectionsGrading U.toOpens) m (dvd_zero m)
        ⟨_, rfl⟩⟩ : veroneseSubring (S.sectionsGrading U.toOpens) m) =
      ⟨toVeroneseAdd S m U.toOpens (DirectSum.of ((S.veronese m).sectionsPiece U.toOpens) 0
        ((S.veronese m).one.app U.toOpens r)), toVeroneseAdd_mem S m U.toOpens _⟩ :=
    Subtype.ext h1
  exact (congrArg (ofVeroneseFun S m hm U.toOpens) h2).trans
    (ofVeroneseFun_toVeroneseAdd S m hm U.toOpens _)

/-- The chartwise isomorphism is compatible with the structure morphism to the base `U`: `Proj.map φ` is compatible
with `toSpecZero` (`proj_map_toSpecZero`), `veroneseHom` is compatible with `toSpecZero`
(`Proj.veroneseHom_toSpecZero`), and then the unit maps on the degree-`0` pieces are compared. -/
theorem chartIso_hom_projToOpen (hm : 0 < m) (U : X.AffineZariskiSite) :
    (chartIso S m hm U).hom ≫ S.toGradedAffineAlgebra.projToOpen U =
      (S.veronese m).toGradedAffineAlgebra.projToOpen U := by
  have hvh : inv (AlgebraicGeometry.Proj.veroneseHom (S.sectionsGrading U.toOpens) m hm) ≫
      AlgebraicGeometry.Proj.toSpecZero (S.sectionsGrading U.toOpens) =
      AlgebraicGeometry.Proj.toSpecZero (veroneseGrading (S.sectionsGrading U.toOpens) m) ≫
        AlgebraicGeometry.Spec.map (CommRingCat.ofHom
          (AlgebraicGeometry.Proj.zeroToVeroneseZero (S.sectionsGrading U.toOpens) m)) := by
    rw [IsIso.inv_comp_eq, ← Category.assoc,
      AlgebraicGeometry.Proj.veroneseHom_toSpecZero, Category.assoc,
      ← AlgebraicGeometry.Spec.map_comp, ← CommRingCat.ofHom_comp,
      AlgebraicGeometry.Proj.veroneseZeroToZero_comp_zeroToVeroneseZero]
    simp
  have hφ := AlgebraicGeometry.Proj.proj_map_toSpecZero (ofVeronese S m hm U.toOpens)
    (irrelevant_le_map_ofVeronese S m hm U.toOpens)
  show (AlgebraicGeometry.Proj.map (ofVeronese S m hm U.toOpens)
        (irrelevant_le_map_ofVeronese S m hm U.toOpens) ≫
        inv (AlgebraicGeometry.Proj.veroneseHom (S.sectionsGrading U.toOpens) m hm)) ≫
      (AlgebraicGeometry.Proj.toSpecZero (S.sectionsGrading U.toOpens) ≫
        AlgebraicGeometry.Spec.map (CommRingCat.ofHom (S.toGradedAffineAlgebra.unitZero U)) ≫
        U.2.isoSpec.inv) =
    AlgebraicGeometry.Proj.toSpecZero ((S.veronese m).sectionsGrading U.toOpens) ≫
      AlgebraicGeometry.Spec.map (CommRingCat.ofHom ((S.veronese m).toGradedAffineAlgebra.unitZero U)) ≫
      U.2.isoSpec.inv
  rw [Category.assoc, reassoc_of% hvh, reassoc_of% hφ]
  simp only [Category.assoc, ← AlgebraicGeometry.Spec.map_comp_assoc]
  congr 3
  exact CommRingCat.hom_ext (RingHom.ext fun r => ofVeronese_zero_unit S m hm U r)

/-- Compatibility with the structure morphism to `X` (on every chart it is `Proj → Spec A(U)_0 → U`, with
`A^{(m)}(U)_0 = A(U)_0`). -/
theorem leftIso_hom_comp (hm : 0 < m) :
    (leftIso S m hm).hom ≫ (AlgebraicGeometry.Scheme.relativeProj S).hom =
      (AlgebraicGeometry.Scheme.relativeProj (S.veronese m)).hom := by
  refine CategoryTheory.Limits.colimit.hom_ext fun U => ?_
  have : CategoryTheory.Limits.HasColimit (S.veronese m).toGradedAffineAlgebra.projFunctor :=
    inferInstanceAs (CategoryTheory.Limits.HasColimit
      (S.veronese m).toGradedAffineAlgebra.projGluingData.functor)
  have : CategoryTheory.Limits.HasColimit S.toGradedAffineAlgebra.projFunctor :=
    inferInstanceAs (CategoryTheory.Limits.HasColimit S.toGradedAffineAlgebra.projGluingData.functor)
  have h0 : CategoryTheory.Limits.colimit.ι (S.veronese m).toGradedAffineAlgebra.projGluingData.functor U ≫
      (leftIso S m hm).hom = (chartIso S m hm U).hom ≫ S.toGradedAffineAlgebra.projChart U :=
    CategoryTheory.Limits.HasColimit.isoOfNatIso_ι_hom (natIso S m hm) U
  have h1 := S.toGradedAffineAlgebra.projChart_hom U
  have h2 := (S.veronese m).toGradedAffineAlgebra.projChart_hom U
  have h3 := chartIso_hom_projToOpen S m hm U
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (· ≫ S.toGradedAffineAlgebra.relativeProj.hom) h0).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg ((chartIso S m hm U).hom ≫ ·) h1).trans ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (· ≫ U.toOpens.ι) h3).trans ?_
  exact h2.symm

end AlgebraicGeometry.Scheme.relativeProj.veroneseIso

noncomputable def AlgebraicGeometry.Scheme.relativeProj.veroneseIso {X : AlgebraicGeometry.Scheme.{u}}
    (S : X.GradedQCAlgebra) (m : ℕ) (hm : 0 < m) :
    AlgebraicGeometry.Scheme.relativeProj (S.veronese m) ≅ AlgebraicGeometry.Scheme.relativeProj S :=
  CategoryTheory.Over.isoMk (AlgebraicGeometry.Scheme.relativeProj.veroneseIso.leftIso S m hm) (AlgebraicGeometry.Scheme.relativeProj.veroneseIso.leftIso_hom_comp S m hm)

end
