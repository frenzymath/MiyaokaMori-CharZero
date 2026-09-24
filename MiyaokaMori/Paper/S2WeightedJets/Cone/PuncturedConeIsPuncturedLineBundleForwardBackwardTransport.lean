import MiyaokaMori.Prelude
import MiyaokaMori.Paper.S2WeightedJets.Cone.PuncturedConeIsPuncturedLineBundleContract
import MiyaokaMori.AlgebraicGeometry.Modules.TotalSpace.TotalSpaceHomEquivCoordinates
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveBundle.HomogeneousEquationSectionAtTotalSpaceSectionCoordinate

/-! # Transport lemmas for the inverse identities `α ≫ β = 𝟙` and `β ≫ α = 𝟙`

Formal transport facts used to prove that the two characterised morphisms α : Z^× → Tot(L)^× and
β : Tot(L)^× → Z^× are mutually inverse (eq. (2.1) of the paper: "the two
constructions are inverse in local trivializations"). Everything here is stated at the level of variables
(schemes, morphisms, modules) so that the concrete proofs only combine these facts with `Eq.trans` /
`congrArg`.

Contents:
* `pullbackCongr` transport (`subst`-`rfl`), `pullbackComp` at the level of global sections, and the
  **associativity coherence** `pullbackComp_assoc_apply` derived from Mathlib's
  `Scheme.Modules.pseudofunctor_associativity`;
* the abstract core `coordinate_comp_eq_of_pullback_pullback_eq` of α ≫ β = 𝟙 (steps S1–S3): from the
  C ×ₖ X-level identity Φ_α(Φ_β(Ψ z)) = Ψ z deduce the C-level identity (α ≫ β)^*z = z;
The **section API** built on top of these lemmas lives in `…ForwardBackwardSectionAPI`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y Z W : AlgebraicGeometry.Scheme.{u}}

/-- Transport along `f = f'` preserves a pulled-back global section. -/
theorem pullbackCongr_apply_sectionPullbackAlong {f f' : X ⟶ Y} (h : f = f') (M : Y.Modules)
    (s : (M.val.obj (Opposite.op ⊤) : Type u)) :
    (((pullbackCongr h).hom.app M).val.app (Opposite.op ⊤)).hom (sectionPullbackAlong f s) =
      sectionPullbackAlong f' s := by
  subst h; rfl

/-- Two successive transports compose. -/
theorem pullbackCongr_apply_pullbackCongr_apply {f f' f'' : X ⟶ Y} (h : f = f') (h' : f' = f'')
    (M : Y.Modules) (x : (((pullback f).obj M).val.obj (Opposite.op ⊤) : Type u)) :
    (((pullbackCongr h').hom.app M).val.app (Opposite.op ⊤)).hom
        ((((pullbackCongr h).hom.app M).val.app (Opposite.op ⊤)).hom x) =
      (((pullbackCongr (h.trans h')).hom.app M).val.app (Opposite.op ⊤)).hom x := by
  subst h h'; rfl

/-- Transport along a proof of `f = f` is the identity (K-like reduction of `eqToHom`). -/
theorem pullbackCongr_apply_self {f : X ⟶ Y} (h : f = f) (M : Y.Modules)
    (x : (((pullback f).obj M).val.obj (Opposite.op ⊤) : Type u)) :
    (((pullbackCongr h).hom.app M).val.app (Opposite.op ⊤)).hom x = x := rfl

/-- Transport along `f = f'` commutes with `(pullbackComp f p).inv` (the first argument). -/
theorem pullbackCongr_apply_pullbackComp_inv_apply {f f' : X ⟶ Y} (h : f = f') (p : Y ⟶ Z) (M : Z.Modules)
    (y : (((pullback (f ≫ p)).obj M).val.obj (Opposite.op ⊤) : Type u)) :
    (((pullbackCongr h).hom.app ((pullback p).obj M)).val.app (Opposite.op ⊤)).hom
        ((((pullbackComp f p).inv.app M).val.app (Opposite.op ⊤)).hom y) =
      (((pullbackComp f' p).inv.app M).val.app (Opposite.op ⊤)).hom
        ((((pullbackCongr (congrArg (· ≫ p) h)).hom.app M).val.app (Opposite.op ⊤)).hom y) := by
  subst h; rfl

/-- Transport along `f = f'` in the second argument commutes with `(pullbackComp j f).hom`. -/
theorem pullbackComp_hom_apply_map_pullbackCongr {j : X ⟶ Y} {f f' : Y ⟶ Z} (h : f = f') (M : Z.Modules)
    (u : (((pullback j).obj ((pullback f).obj M)).val.obj (Opposite.op ⊤) : Type u)) :
    (((pullbackComp j f').hom.app M).val.app (Opposite.op ⊤)).hom
        ((((pullback j).map ((pullbackCongr h).hom.app M)).val.app (Opposite.op ⊤)).hom u) =
      (((pullbackCongr (congrArg (j ≫ ·) h)).hom.app M).val.app (Opposite.op ⊤)).hom
        ((((pullbackComp j f).hom.app M).val.app (Opposite.op ⊤)).hom u) := by
  subst h
  have e : (pullbackCongr (rfl : f = f)).hom.app M = 𝟙 _ := rfl
  rw [e, CategoryTheory.Functor.map_id]
  rfl

/-- `AlgebraicGeometry.Scheme.Modules.ModuleSections.pullback_comp` in `.val.app` form: j^*(f^*s) ↦ (j ≫ f)^*s. -/
theorem pullbackComp_hom_apply_sectionPullbackAlong_sectionPullbackAlong (j : X ⟶ Y) (f : Y ⟶ Z) (M : Z.Modules)
    (s : (M.val.obj (Opposite.op ⊤) : Type u)) :
    (((pullbackComp j f).hom.app M).val.app (Opposite.op ⊤)).hom
        (sectionPullbackAlong j (sectionPullbackAlong f s)) = sectionPullbackAlong (j ≫ f) s :=
  AlgebraicGeometry.Scheme.Modules.ModuleSections.pullback_comp j f s

theorem pullbackComp_hom_apply_inv_apply (j : X ⟶ Y) (f : Y ⟶ Z) (M : Z.Modules)
    (y : (((pullback (j ≫ f)).obj M).val.obj (Opposite.op ⊤) : Type u)) :
    (((pullbackComp j f).hom.app M).val.app (Opposite.op ⊤)).hom
        ((((pullbackComp j f).inv.app M).val.app (Opposite.op ⊤)).hom y) = y :=
  congrArg (fun φ => ((φ.val.app (Opposite.op ⊤)).hom y)) (Iso.inv_hom_id_app (pullbackComp j f) M)

theorem pullbackComp_inv_apply_hom_apply (j : X ⟶ Y) (f : Y ⟶ Z) (M : Z.Modules)
    (u : (((pullback j).obj ((pullback f).obj M)).val.obj (Opposite.op ⊤) : Type u)) :
    (((pullbackComp j f).inv.app M).val.app (Opposite.op ⊤)).hom
        ((((pullbackComp j f).hom.app M).val.app (Opposite.op ⊤)).hom u) = u :=
  congrArg (fun φ => ((φ.val.app (Opposite.op ⊤)).hom u)) (Iso.hom_inv_id_app (pullbackComp j f) M)

theorem map_pullbackComp_inv_apply_map_hom_apply (j : X ⟶ Y) (f : Y ⟶ Z) (q : Z ⟶ W) (M : W.Modules)
    (w : (((pullback j).obj ((pullback f).obj ((pullback q).obj M))).val.obj (Opposite.op ⊤) : Type u)) :
    (((pullback j).map ((pullbackComp f q).inv.app M)).val.app (Opposite.op ⊤)).hom
        ((((pullback j).map ((pullbackComp f q).hom.app M)).val.app (Opposite.op ⊤)).hom w) = w := by
  have e : (pullback j).map ((pullbackComp f q).hom.app M) ≫ (pullback j).map ((pullbackComp f q).inv.app M) =
      𝟙 _ := by
    rw [← CategoryTheory.Functor.map_comp, Iso.hom_inv_id_app, CategoryTheory.Functor.map_id]
  exact congrArg (fun φ => ((φ.val.app (Opposite.op ⊤)).hom w)) e

/-- Associativity coherence of `pullbackComp` at the level of global sections: Mathlib's
`Scheme.Modules.pseudofunctor_associativity`, whose right-hand side `eqToHom _` is `pullbackCongr` of
`Category.assoc` (same `eqToHom`, proofs irrelevant), applied at `M` and `⊤`. -/
theorem pullbackComp_assoc_apply (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ W) (M : W.Modules)
    (x : (((pullback (f ≫ g ≫ h)).obj M).val.obj (Opposite.op ⊤) : Type u)) :
    (((pullbackComp (f ≫ g) h).hom.app M).val.app (Opposite.op ⊤)).hom
        ((((pullbackComp f g).hom.app ((pullback h).obj M)).val.app (Opposite.op ⊤)).hom
          ((((pullback f).map ((pullbackComp g h).inv.app M)).val.app (Opposite.op ⊤)).hom
            ((((pullbackComp f (g ≫ h)).inv.app M).val.app (Opposite.op ⊤)).hom x))) =
      (((pullbackCongr (Category.assoc f g h).symm).hom.app M).val.app (Opposite.op ⊤)).hom x := by
  have e := pseudofunctor_associativity f g h
  exact congrArg (fun τ => ((τ.app M).val.app (Opposite.op ⊤)).hom x) e

/-- Associativity, `inv` form: pushing `j^*((f ≫ p)^*M) → j^*(f^*(p^*M))` through `pullbackComp j f`
equals going to `(j ≫ f ≫ p)^*M` first and then using `(pullbackComp (j ≫ f) p).inv`. -/
theorem pullbackComp_hom_apply_map_pullbackComp_inv (j : X ⟶ Y) (f : Y ⟶ Z) (p : Z ⟶ W) (M : W.Modules)
    (u : (((pullback j).obj ((pullback (f ≫ p)).obj M)).val.obj (Opposite.op ⊤) : Type u)) :
    (((pullbackComp j f).hom.app ((pullback p).obj M)).val.app (Opposite.op ⊤)).hom
        ((((pullback j).map ((pullbackComp f p).inv.app M)).val.app (Opposite.op ⊤)).hom u) =
      (((pullbackComp (j ≫ f) p).inv.app M).val.app (Opposite.op ⊤)).hom
        ((((pullbackCongr (Category.assoc j f p).symm).hom.app M).val.app (Opposite.op ⊤)).hom
          ((((pullbackComp j (f ≫ p)).hom.app M).val.app (Opposite.op ⊤)).hom u)) := by
  have e := pullbackComp_assoc_apply j f p M
    ((((pullbackComp j (f ≫ p)).hom.app M).val.app (Opposite.op ⊤)).hom u)
  rw [pullbackComp_inv_apply_hom_apply] at e
  rw [← e, pullbackComp_inv_apply_hom_apply]

/-- Associativity, `hom` form. -/
theorem pullbackComp_hom_apply_map_pullbackComp_hom (j : X ⟶ Y) (f : Y ⟶ Z) (q : Z ⟶ W) (M : W.Modules)
    (w : (((pullback j).obj ((pullback f).obj ((pullback q).obj M))).val.obj (Opposite.op ⊤) : Type u)) :
    (((pullbackComp j (f ≫ q)).hom.app M).val.app (Opposite.op ⊤)).hom
        ((((pullback j).map ((pullbackComp f q).hom.app M)).val.app (Opposite.op ⊤)).hom w) =
      (((pullbackCongr (Category.assoc j f q)).hom.app M).val.app (Opposite.op ⊤)).hom
        ((((pullbackComp (j ≫ f) q).hom.app M).val.app (Opposite.op ⊤)).hom
          ((((pullbackComp j f).hom.app ((pullback q).obj M)).val.app (Opposite.op ⊤)).hom w)) := by
  have e := pullbackComp_assoc_apply j f q M
    ((((pullbackComp j (f ≫ q)).hom.app M).val.app (Opposite.op ⊤)).hom
      ((((pullback j).map ((pullbackComp f q).hom.app M)).val.app (Opposite.op ⊤)).hom w))
  rw [pullbackComp_inv_apply_hom_apply, map_pullbackComp_inv_apply_map_hom_apply] at e
  rw [e, pullbackCongr_apply_pullbackCongr_apply]
  rfl

end AlgebraicGeometry.Scheme.Modules

/-- Two `Over.homMk` are equal only if their `left` components are. -/
theorem CategoryTheory.Over.left_eq_of_homMk_eq {T : Type u'} [Category.{v'} T] {X : T} {U V : Over X}
    {a b : U.left ⟶ V.left} (w : a ≫ V.hom = U.hom) (w' : b ≫ V.hom = U.hom)
    (h : Over.homMk a w = Over.homMk b w') : a = b :=
  congrArg CommaMorphism.left h



/-- `left_eq_of_homMk_eq` with `U = Over.mk f` (so that `f` is exposed instead of `(Over.mk f).hom`). -/
theorem CategoryTheory.Over.left_eq_of_homMk_eq_mk {T : Type u'} [Category.{v'} T] {X S : T} {f : S ⟶ X}
    {V : Over X} {a b : S ⟶ V.left} (w : a ≫ V.hom = f) (w' : b ≫ V.hom = f)
    (h : (Over.homMk a w : Over.mk f ⟶ V) = Over.homMk b w') : a = b :=
  congrArg CommaMorphism.left h


/-- `(Over.mk f).hom = f` (stated here so that concrete proofs never rely on this defeq). -/
theorem CategoryTheory.Over.mk_hom_eq {T : Type u'} [Category.{v'} T] {X S : T} (f : S ⟶ X) :
    (Over.mk f).hom = f := rfl


/-- `toBase` unfolded. -/
theorem AlgebraicGeometry.Scheme.totalSpacePunctured.toBase_eq {X : AlgebraicGeometry.Scheme.{u}}
    (V : X.Modules) [V.IsLocallyFree] [V.IsFiniteType] :
    AlgebraicGeometry.Scheme.totalSpacePunctured.toBase V =
      (AlgebraicGeometry.Scheme.totalSpacePunctured V).ι ≫ (AlgebraicGeometry.Scheme.totalSpace V).hom := rfl


namespace AlgebraicGeometry.Scheme.Modules

variable {P C S S' : AlgebraicGeometry.Scheme.{u}}

/-- Step S1 (β-side). Notation: Ψ_f := `(pullbackComp f p).inv` : Γ(-, (f ≫ p)^*A) → Γ(-, f^*(p^*A)).
β^*(Ψ_g z), pushed through `pullbackComp β g` and transported along β ≫ g = π, equals Ψ_π of the
transported C-level pullback `(pullbackComp β (g ≫ p)).hom (β^*z)`. -/
theorem pullbackCongr_pullbackComp_sectionPullbackAlong_pullbackComp_inv
    (β : S' ⟶ S) (g : S ⟶ P) (p : P ⟶ C) (π : S' ⟶ P) (hβ1 : β ≫ g = π) (A : C.Modules)
    (z : (((pullback (g ≫ p)).obj A).val.obj (Opposite.op ⊤) : Type u)) :
    (((pullbackCongr hβ1).hom.app ((pullback p).obj A)).val.app (Opposite.op ⊤)).hom
        ((((pullbackComp β g).hom.app ((pullback p).obj A)).val.app (Opposite.op ⊤)).hom
          (sectionPullbackAlong β ((((pullbackComp g p).inv.app A).val.app (Opposite.op ⊤)).hom z))) =
      (((pullbackComp π p).inv.app A).val.app (Opposite.op ⊤)).hom
        ((((pullbackCongr ((Category.assoc β g p).symm.trans (congrArg (· ≫ p) hβ1))).hom.app A).val.app
          (Opposite.op ⊤)).hom
          ((((pullbackComp β (g ≫ p)).hom.app A).val.app (Opposite.op ⊤)).hom (sectionPullbackAlong β z))) := by
  subst hβ1
  rw [pullbackCongr_apply_self, sectionPullbackAlong_naturality β, pullbackComp_hom_apply_map_pullbackComp_inv]

/-- Step S2 (α-side): α^*(Ψ_π Y) pushed through `pullbackComp α π` equals Ψ_{α ≫ π} of the transported
C-level pullback of Y. -/
theorem pullbackComp_sectionPullbackAlong_pullbackComp_inv
    (α : S ⟶ S') (π : S' ⟶ P) (p : P ⟶ C) (A : C.Modules)
    (Y : (((pullback (π ≫ p)).obj A).val.obj (Opposite.op ⊤) : Type u)) :
    (((pullbackComp α π).hom.app ((pullback p).obj A)).val.app (Opposite.op ⊤)).hom
        (sectionPullbackAlong α ((((pullbackComp π p).inv.app A).val.app (Opposite.op ⊤)).hom Y)) =
      (((pullbackComp (α ≫ π) p).inv.app A).val.app (Opposite.op ⊤)).hom
        ((((pullbackCongr (Category.assoc α π p).symm).hom.app A).val.app (Opposite.op ⊤)).hom
          ((((pullbackComp α (π ≫ p)).hom.app A).val.app (Opposite.op ⊤)).hom (sectionPullbackAlong α Y))) := by
  rw [sectionPullbackAlong_naturality α, pullbackComp_hom_apply_map_pullbackComp_inv]

/-- Step S3 (composite): α^* of the transported C-level pullback β^*z, pushed through `pullbackComp α`,
equals the transported (α ≫ β)^*z. -/
theorem pullbackComp_sectionPullbackAlong_pullbackCongr_pullbackComp_sectionPullbackAlong
    (α : S ⟶ S') (β : S' ⟶ S) (r : S ⟶ C) (r' : S' ⟶ C) (E : β ≫ r = r') (A : C.Modules)
    (z : (((pullback r).obj A).val.obj (Opposite.op ⊤) : Type u)) :
    (((pullbackComp α r').hom.app A).val.app (Opposite.op ⊤)).hom
        (sectionPullbackAlong α
          ((((pullbackCongr E).hom.app A).val.app (Opposite.op ⊤)).hom
            ((((pullbackComp β r).hom.app A).val.app (Opposite.op ⊤)).hom (sectionPullbackAlong β z)))) =
      (((pullbackCongr ((Category.assoc α β r).trans (congrArg (α ≫ ·) E))).hom.app A).val.app
        (Opposite.op ⊤)).hom
        ((((pullbackComp (α ≫ β) r).hom.app A).val.app (Opposite.op ⊤)).hom (sectionPullbackAlong (α ≫ β) z)) := by
  subst E
  rw [pullbackCongr_apply_self, sectionPullbackAlong_naturality α, pullbackComp_hom_apply_map_pullbackComp_hom,
    pullbackComp_hom_apply_sectionPullbackAlong_sectionPullbackAlong]

/-- Abstract core of α ≫ β = 𝟙 (eq. (2.1) of the paper). Data: p : P → C (here pr₁ : C ×ₖ X → C),
A on C, g : S → P (here Z^× → C ×ₖ X), π : S' → P (here Tot(L)^× → C ×ₖ X), α, β with α ≫ π = g and
β ≫ g = π, t : S → C with g ≫ p = t, and z ∈ Γ(S, t^*A) (a coordinate z_i).
Write Ψ z := (pullbackComp g p).inv (transport z) ∈ Γ(S, g^*p^*A) (this is `coordOverProduct`),
Φ_β := transport ∘ pullbackComp β g ∘ β^*, Φ_α := transport ∘ pullbackComp α π ∘ α^*.
Hypothesis H: Φ_α(Φ_β(Ψ z)) = Ψ z. Conclusion: the C-level pullback (α ≫ β)^*z, pushed through
`pullbackComp (α ≫ β) t` and transported along (α ≫ β) ≫ t = t, is z.

Proof: `subst` t and g; then S1, S2 rewrite the left side of H into Ψ_g(transport (pullbackComp α (π ≫ p)
(α^*Y))) with Y the transported C-level β^*z; cancel Ψ_g (`pullbackComp_hom_apply_inv_apply`); S3 turns
the inner term into the transported (α ≫ β)^*z; the transports compose (`pullbackCongr_apply_pullbackCongr_apply`)
and proofs of the same equality are irrelevant. -/
theorem coordinate_comp_eq_of_pullback_pullback_eq
    (p : P ⟶ C) (A : C.Modules)
    (g : S ⟶ P) (π : S' ⟶ P) (α : S ⟶ S') (β : S' ⟶ S) (hα1 : α ≫ π = g) (hβ1 : β ≫ g = π)
    (t : S ⟶ C) (ht : g ≫ p = t)
    (z : (((pullback t).obj A).val.obj (Opposite.op ⊤) : Type u))
    (H : (((pullbackCongr hα1).hom.app _).val.app (Opposite.op ⊤)).hom
        ((((pullbackComp α π).hom.app _).val.app (Opposite.op ⊤)).hom
          (sectionPullbackAlong α
            ((((pullbackCongr hβ1).hom.app _).val.app (Opposite.op ⊤)).hom
              ((((pullbackComp β g).hom.app _).val.app (Opposite.op ⊤)).hom
                (sectionPullbackAlong β
                  ((((pullbackComp g p).inv.app A).val.app (Opposite.op ⊤)).hom
                    ((((pullbackCongr ht.symm).hom.app A).val.app (Opposite.op ⊤)).hom z))))))) =
      (((pullbackComp g p).inv.app A).val.app (Opposite.op ⊤)).hom
        ((((pullbackCongr ht.symm).hom.app A).val.app (Opposite.op ⊤)).hom z))
    (hφ : (α ≫ β) ≫ t = t) :
    (((pullbackCongr hφ).hom.app A).val.app (Opposite.op ⊤)).hom
        ((((pullbackComp (α ≫ β) t).hom.app A).val.app (Opposite.op ⊤)).hom
          (sectionPullbackAlong (α ≫ β) z)) = z := by
  subst ht
  subst hα1
  rw [pullbackCongr_apply_self, pullbackCongr_apply_self,
    pullbackCongr_pullbackComp_sectionPullbackAlong_pullbackComp_inv,
    pullbackComp_sectionPullbackAlong_pullbackComp_inv] at H
  have H2 := congrArg ((((pullbackComp (α ≫ π) p).hom.app A).val.app (Opposite.op ⊤)).hom) H
  rw [pullbackComp_hom_apply_inv_apply, pullbackComp_hom_apply_inv_apply,
    pullbackComp_sectionPullbackAlong_pullbackCongr_pullbackComp_sectionPullbackAlong,
    pullbackCongr_apply_pullbackCongr_apply] at H2
  exact H2

end AlgebraicGeometry.Scheme.Modules

end
