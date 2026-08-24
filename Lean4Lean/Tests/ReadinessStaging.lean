import Lean4Lean.Verify.Environment.NormalizationReadiness
import Lean4Lean.Verify.Environment.Extension

/-!
# Family-staging readiness surface

These guards pin the trust boundary for transporting projection and
structure-eta capabilities across retained family-only declaration traces.
-/

namespace Lean4Lean.Tests.ReadinessStaging

#check AddInductive.declaredInductiveInfos_singleton
#check ProjectionReady.of_constants_eq
#check StructureEtaReady.of_constants_eq
#check ProjectionReady.addInductInfo
#check StructureEtaReady.addInductInfo
#check AddInduct.constructorHead
#check AddInductBlock.constructorHead
#check AddInductNested.constructorHead
#check VInductDecl.declarationTraceMultiConstructorReadiness
#check VEnv.AddStructEtas.ordered
#check VEnv.AddStructEtas.registered
#check VEnv.AddStructEtas.exists_of_forallWF
#check StructureEtaRegistrationArtifact.toStructureEtaArtifact_of_completion
#check StructureEtaRegistrationCoverage.toStructureEtaReady

/--
info: 'Lean4Lean.AddInductive.declaredInductiveInfos_singleton' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms AddInductive.declaredInductiveInfos_singleton

/--
info: 'Lean4Lean.ProjectionReady.of_constants_eq' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms ProjectionReady.of_constants_eq

/--
info: 'Lean4Lean.StructureEtaReady.of_constants_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms StructureEtaReady.of_constants_eq

/--
info: 'Lean4Lean.ProjectionReady.addInductInfo' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Lean.PersistentHashMap.findAux_isSome,
 Lean.PersistentHashMap.WF.find?_eq,
 Lean.PersistentHashMap.WF.toList'_insert]
-/
#guard_msgs in
#print axioms ProjectionReady.addInductInfo

/--
info: 'Lean4Lean.StructureEtaReady.addInductInfo' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Lean.PersistentHashMap.findAux_isSome,
 Lean.PersistentHashMap.WF.find?_eq,
 Lean.PersistentHashMap.WF.toList'_insert]
-/
#guard_msgs in
#print axioms StructureEtaReady.addInductInfo

/--
info: 'Lean4Lean.VInductDecl.declarationTraceMultiConstructorReadiness' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Lean.PersistentHashMap.findAux_isSome,
 Lean.PersistentHashMap.WF.find?_eq,
 Lean.PersistentHashMap.WF.toList'_insert]
-/
#guard_msgs in
#print axioms VInductDecl.declarationTraceMultiConstructorReadiness

/--
info: 'Lean4Lean.VEnv.AddStructEtas.exists_of_forallWF' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms VEnv.AddStructEtas.exists_of_forallWF

/--
info: 'Lean4Lean.StructureEtaRegistrationArtifact.toStructureEtaArtifact_of_completion' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms StructureEtaRegistrationArtifact.toStructureEtaArtifact_of_completion

/--
info: 'Lean4Lean.StructureEtaRegistrationCoverage.toStructureEtaReady' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms StructureEtaRegistrationCoverage.toStructureEtaReady

end Lean4Lean.Tests.ReadinessStaging
