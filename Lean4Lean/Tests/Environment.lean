import Lean4Lean.Verify.Environment

/-!
Front-end declaration checks that are not covered by `Lean4Lean.Tests.KernelHardening`.

The mutual-block level parameter and duplicate name checks live there, since v4.33.0-rc2
made the kernel reject both (lean4#14608).
-/

namespace Lean4Lean.Tests.Environment

open Lean

#check Lean4Lean.ElimNestedInductive.Result.canonicalPrimitive_noop
#check Lean4Lean.AddInductive.EnvironmentInductiveExecution.canonicalPrimitive_noop
#check Lean4Lean.primitiveCandidateObserversOfNestedRun
#check Lean4Lean.addDecl.inductDecl_WF_of_split_primitive_transactions_default
#check Lean4Lean.VPrimitiveInductive.canonicalDecl
#check Lean4Lean.VPrimitiveInductive.canonicalDecl_constants
#check Lean4Lean.VPrimitiveInductive.boolGeneration
#check Lean4Lean.VPrimitiveInductive.natGeneration
#check Lean4Lean.VPrimitiveInductive.canonicalGeneration
#check Lean4Lean.VPrimitiveInductive.boolGeneration_wf
#check Lean4Lean.VPrimitiveInductive.natGeneration_wf
#check Lean4Lean.AddInductive.EnvironmentInductiveExecution.flattenedValidationLparams_eq
#check Lean4Lean.EnvironmentInductiveInputClosed
#check Lean4Lean.Environment.checkInductiveInput.WF
#check Lean4Lean.VInductDecl.CandidateBlockFamilyTypeSourceListInput.exists_ofProduced
#check Lean4Lean.VInductDecl.CandidateConstructorSourceListInput.exists_ofProduced
#check Lean4Lean.VInductDecl.CandidateBlockSourceListInput
#check Lean4Lean.VInductDecl.CandidateBlockFamilyTypeSourceListInput.withConstructors
#check Lean4Lean.VInductDecl.CandidateBlockSourceListInput.exists_ofProduced
#check Lean4Lean.VInductDecl.BlockGenerationChecked.recursor_of_family
#check Lean4Lean.VInductDecl.BlockGenerationChecked.WF.mono
#check Lean4Lean.AddInductConstants.replay
#check Lean4Lean.AddInductBlockTrace.replay
#check Lean4Lean.AddInductBlockTrace.coherentReplay
#check Lean4Lean.AddInductNestedTrace.replay
#check Lean4Lean.AddInductNestedTrace.coherentReplay
#check Lean4Lean.AddInductive.EnvironmentInductiveExecution.CoherentPrimitivePreservingTransactions.SafeReplay
#check Lean4Lean.AddInductive.EnvironmentInductiveExecution.CoherentPrimitivePreservingTransactions.ofOrdinarySafeTrace
#check Lean4Lean.AddInductive.EnvironmentInductiveExecution.CoherentPrimitivePreservingTransactions.ofNestedSafeTrace
#check Lean4Lean.AddInductive.declaredInductiveInfos_name
#check Lean4Lean.AddInductive.declareRecursors_info_of_family
#check Lean4Lean.AddInductive.EnvironmentInductiveExecution.ordinaryFamilyLookupCases
#check Lean4Lean.AddInductive.EnvironmentInductiveExecution.ordinaryConstructorLookupCases
#check Lean4Lean.AddInductive.EnvironmentInductiveExecution.ordinaryRecursorLookupCases
#check Lean4Lean.DeclareRestoredInfoListRun.map_wf
#check Lean4Lean.DeclareRestoredInfoListRun.map_fresh
#check Lean4Lean.DeclareRestoredInfoListRun.map_lookup_cases
#check Lean4Lean.DeclareRestoredInfoListRun.family_map_lookup_cases
#check Lean4Lean.DeclareRestoredInfoListRun.constructor_map_lookup_cases
#check Lean4Lean.DeclareRestoredInfoListRun.recursor_map_lookup_cases
#check Lean4Lean.restoredNestedInfos_family_cases
#check Lean4Lean.restoredNestedInfos_constructor_cases
#check Lean4Lean.restoredNestedInfos_recursor_of_family
#check Lean4Lean.AddInductive.EnvironmentInductiveExecution.nestedFamilyLookupCases
#check Lean4Lean.AddInductive.EnvironmentInductiveExecution.nestedConstructorLookupCases
#check Lean4Lean.AddInductive.EnvironmentInductiveExecution.nestedRecursorLookupCases
#check Lean4Lean.AddInductive.EnvironmentInductiveExecution.nestedRecursorLookupOfSourceFamily
#check Lean4Lean.AddInductive.EnvironmentInductiveExecution.CoherentPrimitivePreservingTransactions.ordinaryStructureEtaRegistrationCoverage
#check Lean4Lean.AddInductive.EnvironmentInductiveExecution.CoherentPrimitivePreservingTransactions.nestedStructureEtaRegistrationCoverage
#check Lean4Lean.AddInductive.EnvironmentInductiveExecution.canonicalPrimitiveFamilyEvidence
#check Lean4Lean.AddInductive.EnvironmentInductiveExecution.canonicalPrimitiveFamilyInsertion
#check Lean4Lean.AddInductive.EnvironmentInductiveExecution.canonicalPrimitiveGenerationWF
#check Lean4Lean.AddInductive.EnvironmentInductiveExecution.canonicalPrimitiveConstructorEvidence
#check Lean4Lean.AddInductive.EnvironmentInductiveExecution.canonicalPrimitiveConstructorInsertion
#check Lean4Lean.AddInductive.EnvironmentInductiveExecution.CanonicalPrimitiveReplay
#check Lean4Lean.AddInductive.EnvironmentInductiveExecution.CanonicalPrimitiveReplay.ofInsertions
#check Lean4Lean.AddInductive.EnvironmentInductiveExecution.CanonicalPrimitiveReplay.toTrace
#check Lean4Lean.AddInductive.EnvironmentInductiveExecution.CoherentCanonicalPrimitiveReplay
#check Lean4Lean.AddInductive.EnvironmentInductiveExecution.CoherentCanonicalPrimitiveReplay.trace
#check Lean4Lean.AddInductive.EnvironmentInductiveExecution.CoherentCanonicalPrimitiveReplay.trace_generation
#check Lean4Lean.AddInductive.EnvironmentInductiveExecution.CanonicalPrimitiveTransactionalVEnvsExtension
#check Lean4Lean.AddInductive.EnvironmentInductiveExecution.CanonicalPrimitiveTransactionalVEnvsExtension.ofReplay
#check Lean4Lean.AddInductive.EnvironmentInductiveExecution.CanonicalPrimitiveTransactionalVEnvsExtension.ofExecution
#check Lean4Lean.AddInductive.EnvironmentInductiveExecution.CanonicalPrimitiveTransactionalVEnvsExtension.toTransactionalVEnvsExtension
#check Lean4Lean.AddInductive.EnvironmentInductiveExecution.ReadinessCompletedNonprimitiveVEnvsExtension.ofRules
#check Lean4Lean.AddInductive.EnvironmentInductiveExecution.ReadinessCompletedNonprimitiveVEnvsExtension.ofSafeRules
#check Lean4Lean.AddInductive.EnvironmentInductiveExecution.ReadinessCompletedNonprimitiveVEnvsExtension.ofSafePlan
#check Lean4Lean.AddInductive.EnvironmentInductiveExecution.ReadinessCompletedNonprimitiveVEnvsExtension.ofSafeFamilyNames
#check Lean4Lean.AddInductive.EnvironmentInductiveExecution.ReadinessCompletedNonprimitiveVEnvsExtension.ofOrdinaryTransaction
#check Lean4Lean.AddInductive.EnvironmentInductiveExecution.ReadinessCompletedNonprimitiveVEnvsExtension.ofNestedTransaction
#check Lean4Lean.AddInductive.EnvironmentInductiveExecution.ReadinessCompletedNonprimitiveVEnvsExtension.ofTransaction
#check Lean4Lean.AddInductive.EnvironmentInductiveExecution.ReadinessCompletedNonprimitiveVEnvsExtension.ofSafeReplay
#check Lean4Lean.DeclarationInductiveSafe
#check Lean4Lean.addDecl.WF

/-- info: 'Lean4Lean.AddInductive.declareRecursors_info_of_family' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Lean4Lean.AddInductive.declareRecursors_info_of_family

/--
info: 'Lean4Lean.AddInductive.EnvironmentInductiveExecution.CoherentPrimitivePreservingTransactions.ordinaryStructureEtaRegistrationCoverage' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 PersistentHashMap.findAux_isSome,
 PersistentHashMap.WF.find?_eq,
 PersistentHashMap.WF.toList'_insert]
-/
#guard_msgs in
#print axioms Lean4Lean.AddInductive.EnvironmentInductiveExecution.CoherentPrimitivePreservingTransactions.ordinaryStructureEtaRegistrationCoverage

/-- info: 'Lean4Lean.restoredNestedInfos_recursor_of_family' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Lean4Lean.restoredNestedInfos_recursor_of_family

/--
info: 'Lean4Lean.AddInductive.EnvironmentInductiveExecution.CoherentPrimitivePreservingTransactions.nestedStructureEtaRegistrationCoverage' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 PersistentHashMap.findAux_isSome,
 PersistentHashMap.WF.find?_eq,
 PersistentHashMap.WF.toList'_insert]
-/
#guard_msgs in
#print axioms Lean4Lean.AddInductive.EnvironmentInductiveExecution.CoherentPrimitivePreservingTransactions.nestedStructureEtaRegistrationCoverage

/--
info: 'Lean4Lean.AddInductive.EnvironmentInductiveExecution.ReadinessCompletedNonprimitiveVEnvsExtension.ofRules' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Lean4Lean.AddInductive.EnvironmentInductiveExecution.ReadinessCompletedNonprimitiveVEnvsExtension.ofRules

/--
info: 'Lean4Lean.AddInductive.EnvironmentInductiveExecution.ReadinessCompletedNonprimitiveVEnvsExtension.ofSafeRules' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Lean4Lean.AddInductive.EnvironmentInductiveExecution.ReadinessCompletedNonprimitiveVEnvsExtension.ofSafeRules

/--
info: 'Lean4Lean.AddInductive.EnvironmentInductiveExecution.ReadinessCompletedNonprimitiveVEnvsExtension.ofSafePlan' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Lean4Lean.AddInductive.EnvironmentInductiveExecution.ReadinessCompletedNonprimitiveVEnvsExtension.ofSafePlan

/--
info: 'Lean4Lean.AddInductive.EnvironmentInductiveExecution.ReadinessCompletedNonprimitiveVEnvsExtension.ofSafeFamilyNames' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Lean4Lean.AddInductive.EnvironmentInductiveExecution.ReadinessCompletedNonprimitiveVEnvsExtension.ofSafeFamilyNames

/--
info: 'Lean4Lean.AddInductive.EnvironmentInductiveExecution.ReadinessCompletedNonprimitiveVEnvsExtension.ofOrdinaryTransaction' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 PersistentHashMap.findAux_isSome,
 PersistentHashMap.WF.find?_eq,
 PersistentHashMap.WF.toList'_insert]
-/
#guard_msgs in
#print axioms Lean4Lean.AddInductive.EnvironmentInductiveExecution.ReadinessCompletedNonprimitiveVEnvsExtension.ofOrdinaryTransaction

/--
info: 'Lean4Lean.AddInductive.EnvironmentInductiveExecution.ReadinessCompletedNonprimitiveVEnvsExtension.ofTransaction' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 PersistentHashMap.findAux_isSome,
 PersistentHashMap.WF.find?_eq,
 PersistentHashMap.WF.toList'_insert]
-/
#guard_msgs in
#print axioms Lean4Lean.AddInductive.EnvironmentInductiveExecution.ReadinessCompletedNonprimitiveVEnvsExtension.ofTransaction

/--
info: 'Lean4Lean.AddInductBlockTrace.coherentReplay' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 PersistentHashMap.findAux_isSome,
 PersistentHashMap.WF.find?_eq,
 PersistentHashMap.WF.toList'_insert]
-/
#guard_msgs in
#print axioms Lean4Lean.AddInductBlockTrace.coherentReplay

/--
info: 'Lean4Lean.AddInductNestedTrace.coherentReplay' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 PersistentHashMap.findAux_isSome,
 PersistentHashMap.WF.find?_eq,
 PersistentHashMap.WF.toList'_insert]
-/
#guard_msgs in
#print axioms Lean4Lean.AddInductNestedTrace.coherentReplay

/--
info: 'Lean4Lean.AddInductive.EnvironmentInductiveExecution.CoherentPrimitivePreservingTransactions.ofOrdinarySafeTrace' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 PersistentHashMap.findAux_isSome,
 PersistentHashMap.WF.find?_eq,
 PersistentHashMap.WF.toList'_insert]
-/
#guard_msgs in
#print axioms Lean4Lean.AddInductive.EnvironmentInductiveExecution.CoherentPrimitivePreservingTransactions.ofOrdinarySafeTrace

/--
info: 'Lean4Lean.AddInductive.EnvironmentInductiveExecution.CoherentPrimitivePreservingTransactions.ofNestedSafeTrace' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 PersistentHashMap.findAux_isSome,
 PersistentHashMap.WF.find?_eq,
 PersistentHashMap.WF.toList'_insert]
-/
#guard_msgs in
#print axioms Lean4Lean.AddInductive.EnvironmentInductiveExecution.CoherentPrimitivePreservingTransactions.ofNestedSafeTrace

run_meta
  let env ← Lean.getEnv
  let some (.defnInfo natAdd) := env.toKernelEnv.find? ``Nat.add
    | throwError "Nat.add is not a definition"
  let partialNatAdd := { natAdd with safety := DefinitionSafety.partial }
  match (Lean4Lean.Environment.checkPrimitiveDef partialNatAdd).run env.toKernelEnv
      (lparams := partialNatAdd.levelParams) with
  | .ok false => pure ()
  | .ok true => throwError "a partial definition was accepted as a primitive"
  | .error _ => throwError "the partial primitive check failed unexpectedly"

end Lean4Lean.Tests.Environment
