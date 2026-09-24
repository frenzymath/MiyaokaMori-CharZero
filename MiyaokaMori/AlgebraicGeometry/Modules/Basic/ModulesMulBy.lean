import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Cohomology.Basic.SheafCohomologyModule

/-! # Multiplication by a global function as an endomorphism of a sheaf of modules

Statement: `X` a scheme, `M` an `O_X`-module on `X`, `r ∈ Γ(X, ⊤)` a global function. Then
"multiplication by `r`" is an **endomorphism of `O_X`-modules** `M.mulBy r : M ⟶ M` (multiplication by
`r|_U` on an open `U`; since `O_X` is commutative this is indeed `O_X`-linear). It satisfies:
(1) on the underlying abelian sheaf it is `smulEnd`: `(SheafOfModules.toSheaf _).map (M.mulBy r) = M.smulEnd r`;
(2) for a morphism of schemes `i : Z → X` and `r ∈ Γ(X, ⊤)`:
    `(Scheme.Modules.pushforward i).map (M.mulBy (i.appTop r)) = ((Scheme.Modules.pushforward i).obj M).mulBy r`,
    i.e. `i_*(multiplication by i^♯ r) = multiplication by r`;
(3) `mulBy` is a ring homomorphism in `r` (up to order): `mulBy 1 = 𝟙`, `mulBy (r*s) = mulBy r ≫ mulBy s`,
    `mulBy (r+s) = mulBy r + mulBy s`.

Proof:
1. Define `app U` as multiplication by `r|_U` (`LinearMap.lsmul`; `Γ(X, U)` is commutative, so this is
   `Γ(X, U)`-linear); naturality (restriction commutes with multiplication by `r`) comes from the
   semilinearity of the restriction maps of a `PresheafOfModules` (`PresheafOfModules.map_smul`) and
   functoriality of restriction in `O_X` (restricting `r` to `U` and then to `V` equals restricting to `V`
   directly, since homs in `Opens` form a subsingleton).
2. `SheafOfModules.toSheaf` on morphisms takes the underlying additive map, whose `app` agrees pointwise
   with that of `smulEnd` (both are multiplication by `r|_U`); the two are definitionally equal.
3. Pushforward: `((pushforward i).map φ).app U = φ.app (i⁻¹U)` (`pushforward_map_app`, definitional), and
   the `Γ(X, U)`-action on `(pushforward i).obj M` over `U` is obtained by restricting scalars along
   `i^♯_U`; so it suffices that `(i^♯_⊤ r)|_{i⁻¹U} = i^♯_U (r|_U)`, which is the naturality of `i.c`
   (`Scheme.Hom.naturality`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

variable {X : AlgebraicGeometry.Scheme.{u}}

/-- Restricting a global function `r` to `U` and then to `V` is the same as restricting directly to `V`
(homs in `Opens` form a subsingleton). -/
theorem res_top_res' (r : Γ(X, ⊤)) {U V : (Opens X)ᵒᵖ} (f : U ⟶ V) :
    (X.ringCatSheaf.obj.map f) ((X.presheaf.map (homOfLE (le_top : U.unop ≤ ⊤)).op) r)
      = (X.presheaf.map (homOfLE (le_top : V.unop ≤ ⊤)).op) r := by
  show (ConcreteCategory.hom (X.presheaf.map f))
      ((ConcreteCategory.hom (X.presheaf.map (homOfLE (le_top : U.unop ≤ ⊤)).op)) r) = _
  rw [← CategoryTheory.comp_apply, ← Functor.map_comp,
    Subsingleton.elim ((homOfLE (le_top : U.unop ≤ ⊤)).op ≫ f)
      (homOfLE (le_top : V.unop ≤ ⊤)).op]

/-- The endomorphism "multiplication by `r`" of the `O_X`-module `M`, for a global function `r`
(multiplication by `r|_U` on an open `U`). -/
def mulBy (M : X.Modules) (r : Γ(X, ⊤)) : M ⟶ M :=
  (⟨{ app := fun U => ModuleCat.ofHom
        (LinearMap.lsmul Γ(X, U.unop) Γ(M, U.unop)
          ((X.presheaf.map (homOfLE (le_top : U.unop ≤ ⊤)).op) r))
      naturality := fun {U V} f => by
        ext x
        have h := M.val.map_smul f
          ((X.presheaf.map (homOfLE (le_top : U.unop ≤ ⊤)).op) r) x
        rw [res_top_res' r f] at h
        exact h.symm }⟩ : SheafOfModules.Hom M M)

@[simp]
theorem mulBy_app (M : X.Modules) (r : Γ(X, ⊤)) (U : X.Opens) (x : Γ(M, U)) :
    (M.mulBy r).app U x = (X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op) r • x := rfl

/-- On the underlying abelian sheaf, `mulBy` is `smulEnd`. -/
theorem toSheaf_map_mulBy (M : X.Modules) (r : Γ(X, ⊤)) :
    (SheafOfModules.toSheaf X.ringCatSheaf).map (M.mulBy r) = M.smulEnd r := rfl

theorem mulBy_one (M : X.Modules) : M.mulBy 1 = 𝟙 M := by
  refine AlgebraicGeometry.Scheme.Modules.hom_ext _ _ fun U => ?_
  ext x
  show (X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op) (1 : Γ(X, ⊤)) • x = x
  rw [map_one, one_smul]

theorem mulBy_mul (M : X.Modules) (r s : Γ(X, ⊤)) :
    M.mulBy (r * s) = M.mulBy r ≫ M.mulBy s := by
  refine AlgebraicGeometry.Scheme.Modules.hom_ext _ _ fun U => ?_
  ext x
  show (X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op) (r * s) • x
    = (X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op) s •
      ((X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op) r • x)
  rw [map_mul, mul_comm, mul_smul]

theorem mulBy_add (M : X.Modules) (r s : Γ(X, ⊤)) :
    M.mulBy (r + s) = M.mulBy r + M.mulBy s := by
  refine AlgebraicGeometry.Scheme.Modules.hom_ext _ _ fun U => ?_
  ext x
  show (X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op) (r + s) • x
    = (X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op) r • x
      + (X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op) s • x
  rw [map_add, add_smul]

/-- `i^♯` is compatible with restriction to opens: `(i^♯_⊤ r)|_{i⁻¹U} = i^♯_U (r|_U)` (`Scheme.Hom.naturality`). -/
theorem res_appTop {Z : AlgebraicGeometry.Scheme.{u}} (i : Z ⟶ X) (r : Γ(X, ⊤)) (U : X.Opens) :
    (Z.presheaf.map (homOfLE (le_top : (i ⁻¹ᵁ U) ≤ ⊤)).op) (i.appTop r)
      = i.app U ((X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op) r) := by
  have h2 : i.app U ((X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op) r)
      = (Z.presheaf.map ((Opens.map i.base).map (homOfLE (le_top : U ≤ ⊤))).op) (i.appTop r) :=
    congrArg (fun g : Γ(X, ⊤) ⟶ Γ(Z, i ⁻¹ᵁ U) => ConcreteCategory.hom g r)
      (i.naturality (U' := ⊤) (U := U) (homOfLE (le_top : U ≤ ⊤)).op)
  have hsub : (homOfLE (le_top : (i ⁻¹ᵁ U) ≤ ⊤)).op
      = ((Opens.map i.base).map (homOfLE (le_top : U ≤ ⊤))).op := Subsingleton.elim _ _
  rw [hsub, h2]
  rfl

/-- Pushforward is compatible with multiplication by a global function: `i_*(mult. by i^♯ r) = mult. by r`. -/
theorem pushforward_map_mulBy {Z : AlgebraicGeometry.Scheme.{u}} (i : Z ⟶ X) (M : Z.Modules)
    (r : Γ(X, ⊤)) :
    (AlgebraicGeometry.Scheme.Modules.pushforward i).map (M.mulBy (i.appTop r))
      = ((AlgebraicGeometry.Scheme.Modules.pushforward i).obj M).mulBy r := by
  refine AlgebraicGeometry.Scheme.Modules.hom_ext _ _ fun U => ?_
  ext x
  exact congrArg (fun t : Γ(Z, i ⁻¹ᵁ U) => t • (id (α := ↑Γ(M, i ⁻¹ᵁ U)) x)) (res_appTop i r U)

end AlgebraicGeometry.Scheme.Modules

end
