import Lean4Lean.Verify.Environment.NormalizationElimination

/-! Regression pins for the retained normalization-to-elimination producer.
These operational bridges must remain inside the ordinary logical baseline;
the later semantic interpreter has its separately audited research frontier. -/

/--
info: 'Lean4Lean.AddInductive.NormalizationEliminationExecution.normalization_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Lean4Lean.AddInductive.NormalizationEliminationExecution.normalization_run

/--
info: 'Lean4Lean.AddInductive.NormalizationEliminationExecution.produces' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Lean4Lean.AddInductive.NormalizationEliminationExecution.produces

/--
info: 'Lean4Lean.AddInductive.CheckerBlockEliminationRun.build?' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Lean4Lean.AddInductive.CheckerBlockEliminationRun.build?

/--
info: 'Lean4Lean.AddInductive.CheckerBlockEliminationRun.large_result_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Lean4Lean.AddInductive.CheckerBlockEliminationRun.large_result_iff

/--
info: 'Lean4Lean.VInductDecl.ProducedBlockGenerationShapeCandidate.eq_of_execution_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Lean4Lean.VInductDecl.ProducedBlockGenerationShapeCandidate.eq_of_execution_eq

/--
info: 'Lean4Lean.VInductDecl.checkName_constants_fresh' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Lean.PersistentHashMap.findAux_isSome]
-/
#guard_msgs in
#print axioms Lean4Lean.VInductDecl.checkName_constants_fresh

/--
info: 'Lean4Lean.VInductDecl.familyDeclarationStaging' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Lean.PersistentHashMap.findAux_isSome]
-/
#guard_msgs in
#print axioms Lean4Lean.VInductDecl.familyDeclarationStaging

/--
info: 'Lean4Lean.VInductDecl.constructorDeclarationStaging' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Lean.PersistentHashMap.findAux_isSome,
 Lean.PersistentHashMap.WF.find?_eq,
 Lean.PersistentHashMap.WF.toList'_insert]
-/
#guard_msgs in
#print axioms Lean4Lean.VInductDecl.constructorDeclarationStaging

/--
info: 'Lean4Lean.VInductDecl.produceBlockEliminationShapeCandidate_eq_ok' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Lean4Lean.VInductDecl.produceBlockEliminationShapeCandidate_eq_ok

/--
info: 'Lean4Lean.AddInductive.DeclareRecursorInfoListRun.run' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Lean4Lean.AddInductive.DeclareRecursorInfoListRun.run

/--
info: 'Lean4Lean.AddInductive.declareRecursors_infos_kTarget' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Lean4Lean.AddInductive.declareRecursors_infos_kTarget

/--
info: 'Lean4Lean.AddInductive.NormalizationRecursorExecution.addInductiveRun' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Lean4Lean.AddInductive.NormalizationRecursorExecution.addInductiveRun

/--
info: 'Lean4Lean.AddInductive.NormalizationRecursorExecution.complete_of_normalization' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Lean4Lean.AddInductive.NormalizationRecursorExecution.complete_of_normalization

/--
info: 'Lean4Lean.AddInductive.NormalizationCandidateExecution.completeForRun_of_candidateObservers' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Lean4Lean.AddInductive.NormalizationCandidateExecution.completeForRun_of_candidateObservers

/--
info: 'Lean4Lean.AddInductive.EnvironmentInductiveExecution.addInductiveRun' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Lean4Lean.AddInductive.EnvironmentInductiveExecution.addInductiveRun

/--
info: 'Lean4Lean.AddInductive.EnvironmentInductiveExecution.buildExecution_addInductiveRun' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Lean4Lean.AddInductive.EnvironmentInductiveExecution.buildExecution_addInductiveRun

/--
info: 'Lean4Lean.AddInductive.EnvironmentInductiveExecution.complete_of_normalization' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Lean4Lean.AddInductive.EnvironmentInductiveExecution.complete_of_normalization

/--
info: 'Lean4Lean.AddInductive.EnvironmentInductiveExecution.complete_of_candidateObservers' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Lean4Lean.AddInductive.EnvironmentInductiveExecution.complete_of_candidateObservers

/--
info: 'Lean4Lean.AddInductive.NormalizationRecursorExecution.quotInit_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Lean4Lean.AddInductive.NormalizationRecursorExecution.quotInit_eq

/--
info: 'Lean4Lean.AddInductive.EnvironmentInductiveExecution.quotInit_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Lean4Lean.AddInductive.EnvironmentInductiveExecution.quotInit_eq

/--
info: 'Lean4Lean.AddInductive.EnvironmentInductiveExecution.ExactSemanticTransaction.trEnv' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Lean4Lean.AddInductive.EnvironmentInductiveExecution.ExactSemanticTransaction.trEnv

/--
info: 'Lean4Lean.AddInductive.EnvironmentInductiveExecution.ExactSemanticTransaction.le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Lean4Lean.AddInductive.EnvironmentInductiveExecution.ExactSemanticTransaction.le

/--
info: 'Lean4Lean.AddInductive.EnvironmentInductiveExecution.addDeclRun' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Lean4Lean.AddInductive.EnvironmentInductiveExecution.addDeclRun

/--
info: 'Lean4Lean.AddInductive.EnvironmentInductiveExecution.buildExecution_addDeclRun' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Lean4Lean.AddInductive.EnvironmentInductiveExecution.buildExecution_addDeclRun

/--
info: 'Lean4Lean.VInductDecl.recursorDeclarationStaging' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Lean.PersistentHashMap.findAux_isSome,
 Lean.PersistentHashMap.WF.find?_eq,
 Lean.PersistentHashMap.WF.toList'_insert]
-/
#guard_msgs in
#print axioms Lean4Lean.VInductDecl.recursorDeclarationStaging

/--
info: 'Lean4Lean.VInductDecl.recursorInfoTranslationList_of_option_beq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Lean.Expr.eqv_eq,
 Lean.Level.instLawfulBEqLevel,
 Lean.Syntax.structEq_eq]
-/
#guard_msgs in
#print axioms Lean4Lean.VInductDecl.recursorInfoTranslationList_of_option_beq

/--
info: 'Lean4Lean.VInductDecl.trConstVal_of_translation_header' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Lean.Expr.eqv_eq,
 Lean.Level.instLawfulBEqLevel,
 Lean.Syntax.structEq_eq]
-/
#guard_msgs in
#print axioms Lean4Lean.VInductDecl.trConstVal_of_translation_header

/--
info: 'Lean4Lean.VInductDecl.restoredConstantDeclarationStaging' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Lean.PersistentHashMap.findAux_isSome]
-/
#guard_msgs in
#print axioms Lean4Lean.VInductDecl.restoredConstantDeclarationStaging

/--
info: 'Lean4Lean.VInductDecl.ExactProducedBlockRecursorRun.metadataPrefix' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Lean4Lean.ptrEqConstantInfo_eq,
 Lean4Lean.ptrEqExpr_eq,
 Quot.sound,
 Lean.Expr.abstractRange_eq,
 Lean.Expr.abstract_eq,
 Lean.Expr.eqv_eq,
 Lean.Expr.hasLooseBVar_eq,
 Lean.Expr.instantiate1_eq,
 Lean.Expr.instantiateRange_eq,
 Lean.Expr.instantiateRevRange_eq,
 Lean.Expr.instantiateRev_eq,
 Lean.Expr.instantiate_eq,
 Lean.Expr.looseBVarRange_eq,
 Lean.Expr.lowerLooseBVars_eq,
 Lean.Expr.mkAppData_eq,
 Lean.Expr.mkData_eq,
 Lean.Expr.replace_eq,
 Lean.Level.hasParam_eq,
 Lean.Level.instLawfulBEqLevel,
 Lean.Level.isExplicitSubsumedAux_eq,
 Lean.Level.normalize_eq,
 Lean.PersistentArray.toList'_push,
 Lean.PersistentHashMap.findAux_isSome,
 Lean.Syntax.structEq_eq,
 Lean.PersistentHashMap.WF.find?_eq,
 Lean.PersistentHashMap.WF.toList'_insert]
-/
#guard_msgs in
#print axioms Lean4Lean.VInductDecl.ExactProducedBlockRecursorRun.metadataPrefix

/--
info: 'Lean4Lean.VInductDecl.ExactProducedBlockMetadataPrefixRun.addInductBlockTrace' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Lean4Lean.ptrEqConstantInfo_eq,
 Lean4Lean.ptrEqExpr_eq,
 Quot.sound,
 Lean.Expr.abstractRange_eq,
 Lean.Expr.abstract_eq,
 Lean.Expr.eqv_eq,
 Lean.Expr.hasLooseBVar_eq,
 Lean.Expr.instantiate1_eq,
 Lean.Expr.instantiateRange_eq,
 Lean.Expr.instantiateRevRange_eq,
 Lean.Expr.instantiateRev_eq,
 Lean.Expr.instantiate_eq,
 Lean.Expr.looseBVarRange_eq,
 Lean.Expr.lowerLooseBVars_eq,
 Lean.Expr.mkAppData_eq,
 Lean.Expr.mkData_eq,
 Lean.Expr.replace_eq,
 Lean.Level.hasParam_eq,
 Lean.Level.instLawfulBEqLevel,
 Lean.Level.isExplicitSubsumedAux_eq,
 Lean.Level.normalize_eq,
 Lean.PersistentArray.toList'_push,
 Lean.PersistentHashMap.findAux_isSome,
 Lean.Syntax.structEq_eq,
 Lean.PersistentHashMap.WF.find?_eq,
 Lean.PersistentHashMap.WF.toList'_insert]
-/
#guard_msgs in
#print axioms Lean4Lean.VInductDecl.ExactProducedBlockMetadataPrefixRun.addInductBlockTrace
