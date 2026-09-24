import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Cohomology.Vanishing.Stacks02uxAux
import Mathlib.Topology.Sheaves.Skyscraper

/-! # Sections of the constant sheaf `ℤ_T`

Mathlib's `constantSheaf` is the sheafification of the constant presheaf, so its sections are abstract. This file
provides the small API that Stacks 0A38 needs:
* `constSec V z ∈ ℤ_T(V)`: the constant section `z` over `V` (the image of `z` under `toSheafify`), additive in `z`
  and compatible with restriction (`constSec_res`, `constSec_add`, `zsmul_constSec`);
* `exists_locally_constSec`: every section of `ℤ_T` is locally a constant section (`toSheafify` is locally
  surjective, Mathlib `Presheaf.isLocallySurjective_toSheafify'`);
* `constSec_injective`: over a nonempty open `W`, `z ↦ constSec W z` is injective (detected by the map to the
  skyscraper sheaf at a point `p ∈ W`, which on the constant presheaf is the identity at every open containing `p`).

Source: Stacks 0A38 proof, paragraph 1 ("a section of `ℤ_X` over `U` is a locally constant function `U → ℤ`"). -/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

noncomputable section

namespace TopCat.Sheaf

variable {T : Type u} [TopologicalSpace T]

/-- the constant presheaf on the topological space `T` with value `ULift ℤ` (the same as `constZPresheaf U` of
`Stacks02uxFinGeneratedColimit.lean`, but for an arbitrary space rather than an open of `X`) -/
abbrev constZPresheafOn (T : Type u) [TopologicalSpace T] : (Opens T)ᵒᵖ ⥤ AddCommGrpCat.{u} :=
  (Functor.const (Opens T)ᵒᵖ).obj (AddCommGrpCat.of (ULift.{u} ℤ))

/-- `ℤ_T`: the constant sheaf on `T` with value `ULift ℤ` (Mathlib's `constantSheaf`, the sheafification of
`constZPresheafOn T`) -/
abbrev constZ (T : Type u) [TopologicalSpace T] :
    CategoryTheory.Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{u} :=
  (CategoryTheory.constantSheaf (Opens.grothendieckTopology T) AddCommGrpCat.{u}).obj
    (AddCommGrpCat.of (ULift.{u} ℤ))

theorem constZ_obj_eq : (constZ T).obj = sheafify (Opens.grothendieckTopology T) (constZPresheafOn T) := rfl

/-- `toSheafify` at `V`, viewed as a morphism `ULift ℤ ⟶ ℤ_T(V)` (this ascription of the codomain keeps the
additive lemmas below type-correct) -/
def constSecHom (V : Opens T) : AddCommGrpCat.of (ULift.{u} ℤ) ⟶ (constZ T).obj.obj (op V) :=
  (toSheafify (Opens.grothendieckTopology T) (constZPresheafOn T)).app (op V)

/-- the constant section `z` of `ℤ_T` over `V` -/
def constSec (V : Opens T) (z : ℤ) : (constZ T).obj.obj (op V) :=
  (constSecHom V).hom ⟨z⟩

theorem constSec_res {V W : Opens T} (h : W ≤ V) (z : ℤ) :
    ((constZ T).obj.map (homOfLE h).op).hom (constSec V z) = constSec W z := by
  have := congrArg (fun g => g.hom (⟨z⟩ : ULift.{u} ℤ))
    ((toSheafify (Opens.grothendieckTopology T) (constZPresheafOn T)).naturality (homOfLE h).op)
  exact this.symm

theorem constSec_add (V : Opens T) (z z' : ℤ) : constSec V (z + z') = constSec V z + constSec V z' := by
  unfold constSec
  rw [← map_add]
  rfl

theorem constSec_zero (V : Opens T) : constSec V 0 = 0 := by
  unfold constSec
  rw [← map_zero (constSecHom V).hom]
  rfl

theorem constSec_neg (V : Opens T) (z : ℤ) : constSec V (-z) = -constSec V z := by
  unfold constSec
  rw [← map_neg]
  rfl

theorem zsmul_constSec (V : Opens T) (z z' : ℤ) : z • constSec V z' = constSec V (z * z') := by
  have h : (⟨z * z'⟩ : ULift.{u} ℤ) = z • ⟨z'⟩ := by ext; simp
  unfold constSec
  rw [h, map_zsmul]

theorem zsmul_constSec_one (V : Opens T) (z : ℤ) : z • constSec V 1 = constSec V z := by
  rw [zsmul_constSec, mul_one]

/-- every section of `ℤ_T` is locally a constant section (`toSheafify` is locally surjective) -/
theorem exists_locally_constSec (V : Opens T) (s : (constZ T).obj.obj (op V)) (x : T) (hx : x ∈ V) :
    ∃ (W : Opens T) (hW : W ≤ V), x ∈ W ∧
      ∃ z : ℤ, ((constZ T).obj.map (homOfLE hW).op).hom s = constSec W z := by
  have h := CategoryTheory.Presheaf.imageSieve_mem (Opens.grothendieckTopology T)
    (toSheafify (Opens.grothendieckTopology T) (constZPresheafOn T)) (U := op V) s
  rw [Opens.mem_grothendieckTopology] at h
  obtain ⟨W, f, ⟨z, hz⟩, hxW⟩ := h x hx
  refine ⟨W, f.le, hxW, z.down, ?_⟩
  have hf : homOfLE f.le = f := rfl
  rw [hf]
  exact hz.symm

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- over a nonempty open, the constant sections `z` are pairwise distinct (detected by the skyscraper sheaf at a
point of the open; Mathlib's skyscraper presheaf has `if`-dependent types, hence the two `backward` options,
as in Mathlib's own `fromStalk_to_skyscraper`) -/
theorem constSec_injective {X : TopCat.{u}} (W : Opens X) (hW : (W : Set X).Nonempty) :
    Function.Injective (constSec (T := X) W) := by
  classical
  obtain ⟨p, hp⟩ := hW
  let A : AddCommGrpCat.{u} := AddCommGrpCat.of (ULift.{u} ℤ)
  let c : Cocone ((OpenNhds.inclusion p).op ⋙ constZPresheafOn X) :=
    { pt := A
      ι := { app := fun _ => 𝟙 A
             naturality := by intros; rfl } }
  let d : TopCat.Presheaf.stalk (constZPresheafOn X) p ⟶ A := colimit.desc _ c
  let η : constZPresheafOn X ⟶ skyscraperPresheaf p A :=
    StalkSkyscraperPresheafAdjunctionAuxs.toSkyscraperPresheaf p d
  let θ : sheafify (Opens.grothendieckTopology X) (constZPresheafOn X) ⟶ skyscraperPresheaf p A :=
    sheafifyLift (Opens.grothendieckTopology X) η (skyscraperPresheaf_isSheaf p A)
  have key : ∀ x : ULift.{u} ℤ,
      (θ.app (op W)).hom (((toSheafify (Opens.grothendieckTopology X) (constZPresheafOn X)).app (op W)).hom x) =
        (η.app (op W)).hom x := fun x =>
    congrArg (fun g => (g.app (op W)).hom x) (toSheafify_sheafifyLift _ η _)
  -- the retraction `(skyscraper)(W) = A ⟶ A`
  let ev : (skyscraperPresheaf p A).obj (op W) ⟶ A := eqToHom (if_pos hp)
  have hη : η.app (op W) ≫ ev = 𝟙 A := by
    have h1 : TopCat.Presheaf.germ (constZPresheafOn X) W p hp ≫ d = 𝟙 A := colimit.ι_desc c (op ⟨W, hp⟩)
    rw [StalkSkyscraperPresheafAdjunctionAuxs.toSkyscraperPresheaf_app]
    split_ifs with h
    · rw [Category.assoc, Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id, h1]
    · exact absurd hp h
  have hinj : Function.Injective (η.app (op W)).hom := by
    intro x y hxy
    have := congrArg ev.hom hxy
    have e : ∀ t : ULift.{u} ℤ, ev.hom ((η.app (op W)).hom t) = t := fun t =>
      congrArg (fun g => g.hom t) hη
    rwa [e, e] at this
  intro z z' h
  have h2 : (η.app (op W)).hom ⟨z⟩ = (η.app (op W)).hom ⟨z'⟩ := by
    rw [← key, ← key]
    exact congrArg (θ.app (op W)).hom h
  exact congrArg ULift.down (hinj h2)

end TopCat.Sheaf

end
