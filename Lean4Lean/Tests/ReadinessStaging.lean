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
#check ProjectionArtifactResolver
#check ProjectionArtifactInventoryResolver
#check ProjectionArtifactResolver.toInventory
#check ProjectionArtifactResolver.toResolutionReady
#check StructureEtaReady.of_constants_eq
#check ProjectionReady.addInductInfo
#check StructureEtaReady.addInductInfo
#check AddInduct.constructorHead
#check AddInductBlock.constructorHead
#check AddInductNested.constructorHead
#check VInductDecl.declarationTraceMultiConstructorReadiness
#check VEnv.AddStructEtas.ordered
#check VEnv.AddStructEtas.registered
#check VEnv.AddStructEtas.of_forallWF
#check VEnv.AddStructEtas.exists_of_forallWF
#check StructureEtaRegistrationArtifact.ofProjection
#check StructureEtaRegistrationArtifact.ofProjectionReady
#check StructureEtaRegistrationArtifactResolution.ofProjectionResolution
#check StructureEtaRegistrationArtifact.toStructureEtaArtifact_of_completion
#check StructureEtaRegistrationEntry.ruleWF
#check StructureEtaRegistrationObservationData.find?
#check StructureEtaRegistrationObservationData.toObservation
#check StructureEtaRegistrationObservation.toEntry
#check StructureEtaRegistrationObservation.toEntryOfInventory
#check StructureEtaRegistrationObservation.toEntryNonempty
#check StructureEtaRegistrationEntryBatch.ofResolver
#check StructureEtaRegistrationEntryBatch.ofInventoryResolver
#check StructureEtaRegistrationEntryBatch.nonempty
#check StructureEtaRegistrationPlan.rules
#check StructureEtaRegistrationPlan.rulesWF
#check StructureEtaRegistrationPlan.toCoverage
#check StructureEtaRegistrationPlan.ofFamilyNamesWithResolver
#check StructureEtaRegistrationPlan.ofFamilyNamesWithInventoryResolver
#check StructureEtaRegistrationPlan.nonemptyOfFamilyNames
#check StructureEtaRegistrationPlan.ofFamilyNames
#check StructureEtaRegistrationCoverage.mono
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
info: 'Lean4Lean.VEnv.AddStructEtas.of_forallWF' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms VEnv.AddStructEtas.of_forallWF

/--
info: 'Lean4Lean.VEnv.AddStructEtas.exists_of_forallWF' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms VEnv.AddStructEtas.exists_of_forallWF

/--
info: 'Lean4Lean.StructureEtaRegistrationArtifact.ofProjection' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms StructureEtaRegistrationArtifact.ofProjection

/--
info: 'Lean4Lean.StructureEtaRegistrationArtifact.ofProjectionReady' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms StructureEtaRegistrationArtifact.ofProjectionReady

/--
info: 'Lean4Lean.StructureEtaRegistrationArtifact.toStructureEtaArtifact_of_completion' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms StructureEtaRegistrationArtifact.toStructureEtaArtifact_of_completion

/--
info: 'Lean4Lean.StructureEtaRegistrationObservationData.find?' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms StructureEtaRegistrationObservationData.find?

/--
info: 'Lean4Lean.StructureEtaRegistrationPlan.nonemptyOfFamilyNames' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms StructureEtaRegistrationPlan.nonemptyOfFamilyNames

/--
info: 'Lean4Lean.StructureEtaRegistrationPlan.rulesWF' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms StructureEtaRegistrationPlan.rulesWF

/--
info: 'Lean4Lean.StructureEtaRegistrationPlan.toCoverage' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms StructureEtaRegistrationPlan.toCoverage

/--
info: 'Lean4Lean.StructureEtaRegistrationPlan.ofFamilyNames' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms StructureEtaRegistrationPlan.ofFamilyNames

/--
info: 'Lean4Lean.StructureEtaRegistrationCoverage.mono' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms StructureEtaRegistrationCoverage.mono

/--
info: 'Lean4Lean.StructureEtaRegistrationCoverage.toStructureEtaReady' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms StructureEtaRegistrationCoverage.toStructureEtaReady

end Lean4Lean.Tests.ReadinessStaging
