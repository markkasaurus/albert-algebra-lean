import AlbertAlgebraStatement
import AlbertAlgebra

/-!
# Verification entry points

The public statements are discharged by the completed proofs.
-/

noncomputable section

namespace Albert.Verification

universe u

theorem jordan_identity : Statement.jordanIdentity := by
  intro x y
  exact Albert.jordan_identity x y

theorem glennie_violation : Statement.glennieViolation := by
  refine ⟨GlennieWitness.glennieX, GlennieWitness.glennieY,
    GlennieWitness.glennieZ, ?_⟩
  exact GlennieWitness.violates_glennie_identity

theorem non_speciality : Statement.nonSpeciality.{u} := by
  intro A _ _ _ f hmul
  exact Albert.no_faithful_special_embedding f hmul

end Albert.Verification
