import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.RankAtStalkLocalIso
import MiyaokaMori.AlgebraicGeometry.Modules.Stalk.FreeModuleStalkBasisSpan
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.SheafOfModulesIsLineBundle

/-! # Stalks of line bundles are free

Statement: `X` a scheme, `E` an `O_X`-module on `X`. (1) If `x ∈ U` and `E` is trivialized on `U` as the
free sheaf `O_U^{(I)}` on a finite index set `I`, then the stalk `E_x` is a free `O_{X,x}`-module; (2) in
particular, the stalk at every point of a line bundle (`[E.IsLineBundle]`) is a free `O_{X,x}`-module
(of rank 1).

Proof:
1. Write `y := ⟨x, hx⟩ : U`. The canonical isomorphism between restriction and pullback
   (`Scheme.Modules.restrictFunctorIsoPullback`) turns the given `(U.ι)^*E ≅ O_U^{(I)}` into `E|_U ≅ O_U^{(I)}`.
2. The stalk at `y` of the free sheaf `O_U^{(I)}` has a basis indexed by `I`: `linearIndependent_b` and
   `span_b_eq_top` of the stalk basis lemma for free modules (`I` finite).
3. The stalk functor `moduleStalkFunctor` turns the isomorphism of step 1 into an `O_{U,y}`-linear
   equivalence and transports the basis to `(E|_U)_y`.
4. `LineGenericCoordinates.moduleRestrictStalkEquiv` gives a semilinear equivalence `(E|_U)_y ≃ E_x` (over
   the ring isomorphism `σ = U.stalkIso y`, i.e. `O_{U,y} ≅ O_{X,x}`); `MiyaokaMori.basis_of_semilinearEquiv`
   transports the basis along the semilinear equivalence to `E_x`, giving
   `Module.Free (X.presheaf.stalk x) (E.presheaf.stalk x)`.
5. (2) Line bundle: take `U ∋ x` and `E|_U ≅ O_U` from `IsLineBundle.locally_trivial`, write `O_U` as the free
   sheaf on the one-point index set `PUnit` via `coproductUniqueIso`, and apply (1).

Steps 1–4 are the first half of the proof of `rankAtStalk_of_restrict_iso_free` (which takes `finrank` at the
end, whereas here `Module.Free` itself is the conclusion). Used to show that a line bundle is flat along a
flat morphism (free stalks).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- The stalk at `y` of the free sheaf `O_Y^{(I)}` (`I` finite) has a basis indexed by `I`
(the same as the private lemma of the same name used for `rankAtStalk_of_restrict_iso_free`). -/
private theorem free_stalk_basis {Y : AlgebraicGeometry.Scheme.{u}} (I : Type u) [Finite I]
    (y : Y) :
    Nonempty (Module.Basis I (Y.presheaf.stalk y)
      ((MiyaokaMori.FreeStalk.freeM Y I).presheaf.stalk y)) :=
  ⟨Module.Basis.mk (MiyaokaMori.FreeStalk.linearIndependent_b I y)
    (MiyaokaMori.FreeStalk.span_b_eq_top I y).ge⟩

/-- A module trivialized on some open as a free sheaf of finite rank has free stalks there. -/
theorem AlgebraicGeometry.Scheme.Modules.free_stalk_of_restrict_iso_free
    {X : AlgebraicGeometry.Scheme.{u}} (E : X.Modules) (U : X.Opens) (I : Type u) [Finite I]
    (e : (AlgebraicGeometry.Scheme.Modules.pullback U.ι).obj E ≅
      SheafOfModules.free (R := U.toScheme.ringCatSheaf) I)
    (x : X) (hx : x ∈ U) :
    Module.Free (X.presheaf.stalk x) (E.presheaf.stalk x) := by
  let y : U := ⟨x, hx⟩
  let e' : E.restrict U.ι ≅ SheafOfModules.free (R := U.toScheme.ringCatSheaf) I :=
    (AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback U.ι).app E ≪≫ e
  let := AlgebraicGeometry.Scheme.Modules.moduleStalkModule U.toScheme (E.restrict U.ι) y
  let := AlgebraicGeometry.Scheme.Modules.moduleStalkModule U.toScheme (MiyaokaMori.FreeStalk.freeM U.toScheme I) y
  let := AlgebraicGeometry.Scheme.Modules.moduleStalkModule X E x
  let L := ((AlgebraicGeometry.Scheme.Modules.moduleStalkFunctor U.toScheme y).mapIso e').toLinearEquiv
  obtain ⟨b0⟩ := free_stalk_basis (Y := U.toScheme) I y
  let b1 := b0.map L.symm
  let σ := (U.stalkIso y).commRingCatIsoToRingEquiv
  have := RingHomInvPair.of_ringEquiv σ
  have := RingHomInvPair.of_ringEquiv_symm σ
  obtain ⟨b2⟩ := MiyaokaMori.basis_of_semilinearEquiv
    (AlgebraicGeometry.Divisors.LineGenericCoordinates.moduleRestrictStalkEquiv X E U y) b1
  exact Module.Free.of_basis b2

/-- The stalk of a line bundle at every point is a free `O_{X,x}`-module. -/
theorem AlgebraicGeometry.Scheme.Modules.free_stalk_of_isLineBundle
    {X : AlgebraicGeometry.Scheme.{u}} (M : X.Modules) [M.IsLineBundle] (x : X) :
    Module.Free (X.presheaf.stalk x) (M.presheaf.stalk x) := by
  obtain ⟨U, hxU, ⟨e⟩⟩ := SheafOfModules.IsLineBundle.locally_trivial (M := M) x
  exact AlgebraicGeometry.Scheme.Modules.free_stalk_of_restrict_iso_free M U PUnit.{u + 1}
    ((AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback U.ι).symm.app M ≪≫ e ≪≫
      (CategoryTheory.Limits.coproductUniqueIso
        (fun _ : PUnit.{u + 1} => SheafOfModules.unit U.toScheme.ringCatSheaf)).symm) x hxU

end
