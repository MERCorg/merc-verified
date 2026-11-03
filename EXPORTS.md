# Exports of `MercLib` and `MercVerified`

Human-vetted. Everything a downstream import can see, by module; checked by
`scripts/CheckExports.lean` and regenerated with its `--write` flag. In proof modules,
every export other than a headline theorem of the comparator configs is tagged
*not a headline*.

## `MercLib.Graph.Proofs.Scc_Proofs` (proofs)

* axiom `MercLib.Graph.Reach.mem_of_ne` *not a headline*
* axiom `MercLib.Graph.Reach.refl` *not a headline*
* axiom `MercLib.Graph.Reach.single` *not a headline*
* axiom `MercLib.Graph.Reach.trans` *not a headline*
* axiom `MercLib.Graph.finalSCCExists`

## `MercLib.Graph.Proofs.TarjanInv_Proofs` (proofs)

* def `MercLib.Tarjan.Done` *not a headline*
* def `MercLib.Tarjan.Examined` *not a headline*
* def `MercLib.Tarjan.Init` *not a headline*
* inductive `MercLib.Tarjan.Inv` *not a headline*
* def `MercLib.Tarjan.Reach` *not a headline*

## `MercLib.Graph.Proofs.TarjanMain_Proofs` (proofs)

* axiom `MercLib.Tarjan.tarjanCorrect`
* axiom `MercLib.Tarjan.tarjanTerminates`

## `MercLib.Graph.Proofs.TarjanScan_Proofs` (proofs)

* inductive `MercLib.Tarjan.ScanRes` *not a headline*

## `MercLib.Graph.Proofs.TarjanScc_Proofs` (proofs)

* axiom `MercLib.Tarjan.IsSccPartition.isSCC`

## `MercLib.Graph.Scc`

* def `MercLib.Graph.FinalSCCExists`
* def `MercLib.Graph.IsFinalSCC`
* def `MercLib.Graph.IsSCC`
* def `MercLib.Graph.Reach`
* def `MercLib.Graph.finalSCC`

## `MercLib.Graph.Tarjan`

* inductive `MercLib.Tarjan.Ctx`
* def `MercLib.Tarjan.Ctx.noConfusionType`
* def `MercLib.Tarjan.Edge`
* inductive `MercLib.Tarjan.Graph`
* def `MercLib.Tarjan.Graph.noConfusionType`
* def `MercLib.Tarjan.IsSccPartition`
* inductive `MercLib.Tarjan.Out`
* def `MercLib.Tarjan.Out.ctorElimType`
* def `MercLib.Tarjan.Out.noConfusionType`
* def `MercLib.Tarjan.Step`
* def `MercLib.Tarjan.TarjanCorrect`
* def `MercLib.Tarjan.TarjanTerminates`
* def `MercLib.Tarjan.finish`
* def `MercLib.Tarjan.init`
* def `MercLib.Tarjan.initNode`
* def `MercLib.Tarjan.measure`
* def `MercLib.Tarjan.popComp`
* def `MercLib.Tarjan.scan`
* def `MercLib.Tarjan.step`

## `MercLib.HybridSI.Algorithm`

* inductive `MercLib.HybridSI.Step`
* def `MercLib.HybridSI.Step.ctorElimType`
* def `MercLib.HybridSI.Step.noConfusionType`
* def `MercLib.HybridSI.argmaxKey`
* def `MercLib.HybridSI.bestOf`
* def `MercLib.HybridSI.filtered`
* def `MercLib.HybridSI.hbRun`
* def `MercLib.HybridSI.hbSolve`
* def `MercLib.HybridSI.hbStep`
* def `MercLib.HybridSI.improving`
* def `MercLib.HybridSI.initProfile`
* def `MercLib.HybridSI.keyDefault`
* def `MercLib.HybridSI.keyTable`
* def `MercLib.HybridSI.ownedBy`
* def `MercLib.HybridSI.respond`
* def `MercLib.HybridSI.respondRound`
* def `MercLib.HybridSI.succList`

## `MercLib.HybridSI.AlgorithmPoly`

* def `MercLib.HybridSI.HBPolyCorrect`
* def `MercLib.HybridSI.HBRunCost`
* def `MercLib.HybridSI.HBStepCost`
* def `MercLib.HybridSI.hbRunPoly`
* def `MercLib.HybridSI.hbStepBound`
* def `MercLib.HybridSI.hbStepPoly`
* def `MercLib.HybridSI.keyTableT`

## `MercLib.HybridSI.BestResponse`

* def `MercLib.HybridSI.BestResponseCost`
* def `MercLib.HybridSI.BestResponseOptimal`
* def `MercLib.HybridSI.allowed`
* def `MercLib.HybridSI.argmaxBy`
* def `MercLib.HybridSI.bestResponse`
* def `MercLib.HybridSI.bestResponseBound`
* def `MercLib.HybridSI.bestResponseT`
* def `MercLib.HybridSI.bfInit`
* def `MercLib.HybridSI.bfRound`
* def `MercLib.HybridSI.bfVal`
* def `MercLib.HybridSI.bfValT`
* def `MercLib.HybridSI.bfWeight`
* def `MercLib.HybridSI.cands`
* def `MercLib.HybridSI.classStep`
* def `MercLib.HybridSI.classStepT`
* def `MercLib.HybridSI.classes`
* def `MercLib.HybridSI.classesT`
* def `MercLib.HybridSI.edgeCount`
* def `MercLib.HybridSI.favours`
* def `MercLib.HybridSI.hsucc`
* def `MercLib.HybridSI.isTarget`
* def `MercLib.HybridSI.iterT`
* def `MercLib.HybridSI.mat`
* def `MercLib.HybridSI.matV`
* def `MercLib.HybridSI.movesOf`
* def `MercLib.HybridSI.opens`
* def `MercLib.HybridSI.pw`
* def `MercLib.HybridSI.reachFrom`
* def `MercLib.HybridSI.reachFromT`
* def `MercLib.HybridSI.reachRound`
* def `MercLib.HybridSI.roundCost`
* def `MercLib.HybridSI.scale`
* def `MercLib.HybridSI.unclassified`

## `MercLib.HybridSI.Bounds`

* def `MercLib.HybridSI.Autonomy`
* def `MercLib.HybridSI.Closed`
* def `MercLib.HybridSI.ClosedIterations`
* def `MercLib.HybridSI.LowerBelowUpper`
* def `MercLib.HybridSI.Saddle`
* def `MercLib.HybridSI.SaddleExists`
* def `MercLib.HybridSI.SaddleUnique`
* def `MercLib.HybridSI.Sandwich`
* def `MercLib.HybridSI.instDecidableRelSubtypeMemFinsetEdgeSubgame`
* def `MercLib.HybridSI.subgame`

## `MercLib.HybridSI.Correctness`

* def `MercLib.HybridSI.FilterNonempty`
* def `MercLib.HybridSI.HBCorrect`
* def `MercLib.HybridSI.HBPolyIterations`
* def `MercLib.HybridSI.HBTerminates`
* def `MercLib.HybridSI.RespondPolyRounds`
* def `MercLib.HybridSI.hbFuel`

## `MercLib.HybridSI.Counting`

* def `MercLib.HybridSI.EpochIterations`
* def `MercLib.HybridSI.KStarBlock`
* def `MercLib.HybridSI.KStarCount`
* def `MercLib.HybridSI.kstarChangeRounds`
* def `MercLib.HybridSI.kstarOf`

## `MercLib.HybridSI.Epoch`

* def `MercLib.HybridSI.EpochBound`
* def `MercLib.HybridSI.numEven`

## `MercLib.HybridSI.Potential`

* def `MercLib.HybridSI.CycleMaxChanges`
* def `MercLib.HybridSI.RunTrace`
* def `MercLib.HybridSI.RunTraceOfRun`
* def `MercLib.HybridSI.TopChanges`
* def `MercLib.HybridSI.ValuationMonotone`
* def `MercLib.HybridSI.VertexCycMaxChanges`
* def `MercLib.HybridSI.cycMaxChangeRounds`
* def `MercLib.HybridSI.oddChangeRounds`
* def `MercLib.HybridSI.topChangeRounds`
* def `MercLib.HybridSI.topClass`

## `MercLib.HybridSI.Proofs.AlgorithmPoly_Proofs` (proofs)

* theorem `MercLib.HybridSI.bestResponse.congr_simp` *not a headline*
* theorem `MercLib.HybridSI.bestResponseT.congr_simp` *not a headline*
* axiom `MercLib.HybridSI.hbPolyCorrect`
* theorem `MercLib.HybridSI.hbRunPoly.congr_simp` *not a headline*
* axiom `MercLib.HybridSI.hbRunPoly_cost`
* theorem `MercLib.HybridSI.hbStepPoly.congr_simp` *not a headline*
* axiom `MercLib.HybridSI.hbStepPoly_cost`

## `MercLib.HybridSI.Proofs.BestResponse_Classes_Proofs` (proofs)

* inductive `MercLib.HybridSI.ClsInv` *not a headline*
* theorem `MercLib.HybridSI.ClsInv.congr_simp` *not a headline*
* axiom `MercLib.HybridSI.Reach.congr` *not a headline*
* axiom `MercLib.HybridSI.Reach.mono` *not a headline*
* def `MercLib.HybridSI.Rset` *not a headline*
* theorem `MercLib.HybridSI.classes.congr_simp` *not a headline*
* theorem `MercLib.HybridSI.hsucc.congr_simp` *not a headline*
* theorem `MercLib.HybridSI.opens.congr_simp` *not a headline*
* def `MercLib.HybridSI.plr` *not a headline*
* def `MercLib.HybridSI.rr` *not a headline*

## `MercLib.HybridSI.Proofs.BestResponse_Graph_Proofs` (proofs)

* def `MercLib.HybridSI.Reach` *not a headline*

## `MercLib.HybridSI.Proofs.BestResponse_Proofs` (proofs)

* theorem `MercLib.HybridSI.allowed.congr_simp` *not a headline*
* axiom `MercLib.HybridSI.bestResponse_cost`
* axiom `MercLib.HybridSI.bestResponse_optimal`
* theorem `MercLib.HybridSI.classesT.congr_simp` *not a headline*
* theorem `MercLib.HybridSI.edgeCount.congr_simp` *not a headline*

## `MercLib.HybridSI.Proofs.Bounds_Autonomy_Proofs` (proofs)

* axiom `MercLib.HybridSI.autonomy`
* axiom `MercLib.HybridSI.closedIterations`

## `MercLib.HybridSI.Proofs.Bounds_Proofs` (proofs)

* axiom `MercLib.HybridSI.lowerBelowUpper`
* axiom `MercLib.HybridSI.saddleExists`
* axiom `MercLib.HybridSI.saddleUnique`
* axiom `MercLib.HybridSI.sandwich`

## `MercLib.HybridSI.Proofs.Bounds_Subgame_Proofs` (proofs)

* theorem `MercLib.HybridSI.subgame.congr_simp` *not a headline*

## `MercLib.HybridSI.Proofs.Correctness_Proofs` (proofs)

* theorem `MercLib.HybridSI.filtered.congr_simp` *not a headline*
* axiom `MercLib.HybridSI.hbCorrect`
* theorem `MercLib.HybridSI.hbRun.congr_simp` *not a headline*
* theorem `MercLib.HybridSI.hbStep.congr_simp` *not a headline*
* theorem `MercLib.HybridSI.improving.congr_simp` *not a headline*
* theorem `MercLib.HybridSI.initProfile.congr_simp` *not a headline*
* theorem `MercLib.HybridSI.respond.congr_simp` *not a headline*
* theorem `MercLib.HybridSI.respondRound.congr_simp` *not a headline*
* theorem `MercLib.HybridSI.succList.congr_simp` *not a headline*

## `MercLib.HybridSI.Proofs.Counting_Proofs` (proofs)

* axiom `MercLib.HybridSI.epochIterations`
* axiom `MercLib.HybridSI.kstarBlock`
* axiom `MercLib.HybridSI.kstarCount`
* theorem `MercLib.HybridSI.kstarOf.congr_simp` *not a headline*

## `MercLib.HybridSI.Proofs.Epoch_Proofs` (proofs)

* axiom `MercLib.HybridSI.epochBound`

## `MercLib.HybridSI.Proofs.Filter_Proofs` (proofs)

* axiom `MercLib.HybridSI.filterNonempty`

## `MercLib.HybridSI.Proofs.Key_Proofs` (proofs)

* def `MercLib.HybridSI.Good` *not a headline*
* def `MercLib.HybridSI.instDecidableGood` *not a headline*
* def `MercLib.HybridSI.rI` *not a headline*

## `MercLib.HybridSI.Proofs.Potential_Proofs` (proofs)

* theorem `MercLib.HybridSI.RunTrace.congr_simp` *not a headline*
* axiom `MercLib.HybridSI.cycleMaxChanges`
* axiom `MercLib.HybridSI.runTraceOfRun`
* axiom `MercLib.HybridSI.topChanges`
* axiom `MercLib.HybridSI.valuationMonotone`
* axiom `MercLib.HybridSI.vertexCycMaxChanges`

## `MercLib.HybridSI.Proofs.Termination_Proofs` (proofs)

* axiom `MercLib.HybridSI.hbTerminates`

## `MercLib.HybridSI.Valuation`

* def `MercLib.HybridSI.Key`
* def `MercLib.HybridSI.bSet`
* def `MercLib.HybridSI.cycMax`
* def `MercLib.HybridSI.iter`
* def `MercLib.HybridSI.key`
* def `MercLib.HybridSI.keyWinner`
* def `MercLib.HybridSI.look`
* def `MercLib.HybridSI.playPrefix`
* def `MercLib.HybridSI.rank`
* def `MercLib.HybridSI.stepsTo`
* def `MercLib.HybridSI.tabulate`
* def `MercLib.HybridSI.univList`
* def `MercLib.HybridSI.weight`
* def `MercLib.ParityGame.Game.Relabelled`

## `MercLib.LTS.BranchingBisimilarity`

* def `MercLib.LTS.BranchingBisimilarity`
* def `MercLib.LTS.IsBranchingBisimulation`
* def `MercLib.LTS.IsHomBranchingBisimulation`
* axiom `MercLib.LTS.«term_≈br[_]_»`

## `MercLib.LTS.Proofs.BranchingBisimilarity_Transitivity_Proofs` (proofs)

* axiom `MercLib.LTS.BranchingBisimilarity.refl`
* axiom `MercLib.LTS.BranchingBisimilarity.symm`
* axiom `MercLib.LTS.BranchingBisimilarity.trans`

## `MercLib.ParityGame.Attractor`

* def `MercLib.ParityGame.Game.attr`
* def `MercLib.ParityGame.Game.attrRank`
* def `MercLib.ParityGame.Game.attrStage`
* def `MercLib.ParityGame.Game.attrStrategy`

## `MercLib.ParityGame.FatalAttractor`

* def `MercLib.ParityGame.Game.FatalAttractorWins`
* def `MercLib.ParityGame.Game.IsFatal`
* def `MercLib.ParityGame.Game.ma`
* def `MercLib.ParityGame.Game.mattr`
* def `MercLib.ParityGame.Game.mattrRank`
* def `MercLib.ParityGame.Game.mattrStage`
* def `MercLib.ParityGame.Game.mattrStrategy`
* def `MercLib.ParityGame.Game.mpre`

## `MercLib.ParityGame.Game`

* inductive `MercLib.ParityGame.Game`
* def `MercLib.ParityGame.Game.ConformingPlay`
* def `MercLib.ParityGame.Game.IsSubgame`
* def `MercLib.ParityGame.Game.MaxInfPrio`
* def `MercLib.ParityGame.Game.PlayWonBy`
* def `MercLib.ParityGame.Game.Solves`
* def `MercLib.ParityGame.Game.Step`
* def `MercLib.ParityGame.Game.WinsFrom`
* def `MercLib.ParityGame.Game.noConfusionType`
* inductive `MercLib.ParityGame.Player`
* def `MercLib.ParityGame.Player.ctorElimType`
* def `MercLib.ParityGame.Player.noConfusionType`
* def `MercLib.ParityGame.Player.ofNat`
* axiom `MercLib.ParityGame.Player.ofNat_ctorIdx`
* def `MercLib.ParityGame.Player.ofPrio`
* def `MercLib.ParityGame.Player.opp`
* inductive `MercLib.ParityGame.Solution`
* def `MercLib.ParityGame.Solution.noConfusionType`
* def `MercLib.ParityGame.Strategy`
* def `MercLib.ParityGame.instDecidableEqPlayer`

## `MercLib.ParityGame.Implementation`

* def `MercLib.ParityGame.Game.FatalAttractorOriginalSound`
* def `MercLib.ParityGame.Game.IsClosedWinningRegion`
* def `MercLib.ParityGame.Game.SoundPartial`
* def `MercLib.ParityGame.Game.acceptFatal`
* def `MercLib.ParityGame.Game.attrWithTau`
* def `MercLib.ParityGame.Game.fatalAttractorOriginal`

## `MercLib.ParityGame.Proofs.Attractor_Proofs` (proofs)

* axiom `MercLib.ParityGame.Game.attractorCorrect`

## `MercLib.ParityGame.Proofs.FatalAttractor_Proofs` (proofs)

* axiom `MercLib.ParityGame.Game.fatalAttractorWins`

## `MercLib.ParityGame.Proofs.Game_Proofs` (proofs)

* axiom `MercLib.ParityGame.Game.playHasUniqueWinner`

## `MercLib.ParityGame.Proofs.Implementation_Proofs` (proofs)

* axiom `MercLib.ParityGame.Game.fatalAttractorOriginalSound`

## `MercLib.ParityGame.Proofs.Region_Proofs` (proofs)

* inductive `MercLib.ParityGame.Game.Region` *not a headline*
* inductive `MercLib.ParityGame.Game.Strong` *not a headline*

## `MercLib.ParityGame.Proofs.Zielonka_Proofs` (proofs)

* axiom `MercLib.ParityGame.Game.zielonka_correct`

## `MercLib.ParityGame.Zielonka`

* def `MercLib.ParityGame.Game.ZielonkaCorrect`
* def `MercLib.ParityGame.Game.anyMove`
* def `MercLib.ParityGame.Game.maxPrio`
* def `MercLib.ParityGame.Game.wonAll`
* def `MercLib.ParityGame.Game.wonSplit`
* def `MercLib.ParityGame.Game.zielonka`
* def `MercLib.ParityGame.Game.zielonkaAux`
* def `MercLib.ParityGame.Solution.empty`

## `MercLib.Refinement.Algorithm`

* def `MercLib.Refinement.outgoing`
* def `MercLib.Refinement.refinesNew`

## `MercLib.Refinement.AlgorithmImpossibleFutures`

* def `MercLib.Refinement.NegSound`
* def `MercLib.Refinement.PosSound`
* def `MercLib.Refinement.toList`
* def `MercLib.Refinement.weakImpossibleFuturesOpt`
* def `MercLib.Refinement.weakTraceOpt`

## `MercLib.Refinement.Antichain`

* inductive `MercLib.Refinement.Antichain`
* def `MercLib.Refinement.Antichain.Mem`
* def `MercLib.Refinement.Antichain.empty`
* def `MercLib.Refinement.Antichain.insert`
* def `MercLib.Refinement.Antichain.instInsert`
* def `MercLib.Refinement.Antichain.noConfusionType`
* axiom `MercLib.Refinement.Antichain.«term_⊑_»`
* def `MercLib.Refinement.IsMonotoneNormalForm`
* def `MercLib.Refinement.ProductLE`

## `MercLib.Refinement.ImpossibleFutures`

* def `MercLib.Refinement.Convergent`
* def `MercLib.Refinement.ImpossibleFuturesRefines`
* def `MercLib.Refinement.IsIFWitness`
* def `MercLib.Refinement.IsStableIFWitness`
* def `MercLib.Refinement.impossibleFutures`
* axiom `MercLib.Refinement.«term_⊑if[_,_]_»`

## `MercLib.Refinement.Product`

* def `MercLib.Refinement.FdrNormTr`
* def `MercLib.Refinement.IsFDWitness`
* def `MercLib.Refinement.IsSFWitness`
* def `MercLib.Refinement.IsTRWitness`
* def `MercLib.Refinement.NormInit`
* def `MercLib.Refinement.NormTr`
* def `MercLib.Refinement.SetDivergent`
* def `MercLib.Refinement.product`

## `MercLib.Refinement.Proofs.AlgorithmImpossibleFutures_Proofs` (proofs)

* axiom `MercLib.Refinement.weakImpossibleFuturesOptCorrect`
* theorem `MercLib.Refinement.weakTraceOpt.congr_simp` *not a headline*
* axiom `MercLib.Refinement.weakTraceOptCorrect`

## `MercLib.Refinement.Proofs.Algorithm_Proofs` (proofs)

* inductive `MercLib.Refinement.ExploreInv` *not a headline*
* inductive `MercLib.Refinement.SuccFacts` *not a headline*
* theorem `MercLib.Refinement.outgoing.congr_simp` *not a headline*
* axiom `MercLib.Refinement.refinesNewCorrect`
* def `MercLib.Refinement.succSpec` *not a headline*

## `MercLib.Refinement.Proofs.ImpossibleFutures_Proofs` (proofs)

* axiom `MercLib.Refinement.impossibleFuturesRefines_iff_not_reachable_ifWitness`
* axiom `MercLib.Refinement.impossibleFuturesRefines_iff_of_tauCycle`

## `MercLib.Refinement.Proofs.Product_Proofs` (proofs)

* axiom `MercLib.Refinement.failuresDivergencesRefines_iff_not_reachable_fdWitness`
* axiom `MercLib.Refinement.stableFailuresRefines_iff_not_reachable_sfWitness`
* axiom `MercLib.Refinement.traceRefines_iff_not_reachable_trWitness`

## `MercLib.Refinement.Semantics`

* def `MercLib.Refinement.FailuresDivergencesRefines`
* def `MercLib.Refinement.IsVisible`
* def `MercLib.Refinement.Stable`
* def `MercLib.Refinement.StableFailuresRefines`
* def `MercLib.Refinement.TraceRefines`
* inductive `MercLib.Refinement.WeakTr`
* inductive `MercLib.Refinement.WeakTr.below`
* axiom `MercLib.Refinement.WeakTr.brecOn`
* axiom `MercLib.Refinement.WeakTr.visible`
* def `MercLib.Refinement.divergences`
* def `MercLib.Refinement.failures`
* def `MercLib.Refinement.failuresBot`
* def `MercLib.Refinement.refusals`
* def `MercLib.Refinement.refusalsOf`
* def `MercLib.Refinement.weaktraces`
* axiom `MercLib.Refinement.«term_⊑fdr[_,_]_»`
* axiom `MercLib.Refinement.«term_⊑sfr[_,_]_»`
* axiom `MercLib.Refinement.«term_⊑tr[_,_]_»`

## `MercLib.Rewriting.Confluence`

* def `MercLib.Rewriting.NormalFormsInjective`

## `MercLib.Rewriting.Proofs.Confluence_Proofs` (proofs)

* axiom `MercLib.Rewriting.confluent_of_model`
* axiom `MercLib.Rewriting.existsUnique_normalForm`

## `MercLib.Rewriting.Proofs.Soundness_Proofs` (proofs)

* axiom `MercLib.Rewriting.Steps.eval_eq`

## `MercLib.Rewriting.Proofs.Termination_Proofs` (proofs)

* axiom `MercLib.Rewriting.terminating_of_interpretation`
* axiom `MercLib.Rewriting.terminating_of_measure`

## `MercLib.Rewriting.Rewrite`

* def `MercLib.Rewriting.ArgsStep`
* inductive `MercLib.Rewriting.ArgsStepWith`
* inductive `MercLib.Rewriting.ArgsStepWith.below`
* axiom `MercLib.Rewriting.ArgsStepWith.brecOn`
* inductive `MercLib.Rewriting.Cond`
* def `MercLib.Rewriting.Cond.noConfusionType`
* def `MercLib.Rewriting.Normal`
* def `MercLib.Rewriting.Reducible`
* inductive `MercLib.Rewriting.Rule`
* def `MercLib.Rewriting.Rule.noConfusionType`
* def `MercLib.Rewriting.Step`
* inductive `MercLib.Rewriting.StepWith`
* inductive `MercLib.Rewriting.StepWith.below`
* axiom `MercLib.Rewriting.StepWith.brecOn`
* def `MercLib.Rewriting.Steps`
* def `MercLib.Rewriting.TRS`
* def `MercLib.Rewriting.Terminating`
* def `MercLib.Rewriting.argsStepAt`
* def `MercLib.Rewriting.rel`
* def `MercLib.Rewriting.stepAt`

## `MercLib.Rewriting.Signature`

* inductive `MercLib.Rewriting.Algebra`
* def `MercLib.Rewriting.Algebra.noConfusionType`
* inductive `MercLib.Rewriting.Args`
* axiom `MercLib.Rewriting.Args.brecOn.eq`
* def `MercLib.Rewriting.Args.brecOn.go`
* def `MercLib.Rewriting.Args.ctorElimType`
* def `MercLib.Rewriting.Args.eval`
* def `MercLib.Rewriting.Args.noConfusionType`
* def `MercLib.Rewriting.Args.subst`
* def `MercLib.Rewriting.Ground`
* inductive `MercLib.Rewriting.Signature`
* def `MercLib.Rewriting.Signature.noConfusionType`
* inductive `MercLib.Rewriting.Term`
* def `MercLib.Rewriting.Term.Subst`
* axiom `MercLib.Rewriting.Term.brecOn.eq`
* def `MercLib.Rewriting.Term.brecOn.go`
* def `MercLib.Rewriting.Term.ctorElimType`
* def `MercLib.Rewriting.Term.eval`
* def `MercLib.Rewriting.Term.noConfusionType`
* def `MercLib.Rewriting.Term.subst`
* def `MercLib.Rewriting.Term.substValuation`
* def `MercLib.Rewriting.Vals`
* def `MercLib.Rewriting.Valuation`
* def `MercLib.Rewriting.VarSet`

## `MercLib.Rewriting.Soundness`

* def `MercLib.Rewriting.Model`

## `MercLib.Rewriting.Termination`

* def `MercLib.Rewriting.Decreasing`
* inductive `MercLib.Rewriting.MonotoneAlgebra`
* def `MercLib.Rewriting.MonotoneAlgebra.noConfusionType`
* def `MercLib.Rewriting.ValsLt`

## `MercLib.Signatures.InductiveSignatures`

* def `MercLib.Signatures.InductiveBranchingFixPoint`
* def `MercLib.Signatures.PreSig`
* def `MercLib.Signatures.Sig`
* def `MercLib.Signatures.TauLoopFree`

## `MercLib.Signatures.Proofs.InductiveSignatures_Proofs` (proofs)

* axiom `MercLib.Signatures.BranchingBisimilarity.inductiveBranchingFixPoint`
* axiom `MercLib.Signatures.InductiveBranchingFixPoint.branchingBisimilarity`
* axiom `MercLib.Signatures.IsStable.branchingBisimilarity_inductive`

## `MercLib.Signatures.Proofs.Signature_Proofs` (proofs)

* axiom `MercLib.Signatures.BranchingBisimilarity.branchingFixPoint`
* axiom `MercLib.Signatures.BranchingFixPoint.branchingBisimilarity`
* axiom `MercLib.Signatures.IsStable.bisimilarity`
* axiom `MercLib.Signatures.IsStable.branchingBisimilarity`
* axiom `MercLib.Signatures.StrongFixPoint.bisimilarity`
* axiom `MercLib.Signatures.strongFixPoint`

## `MercLib.Signatures.Signature`

* def `MercLib.Signatures.BranchingFixPoint`
* def `MercLib.Signatures.BranchingSignature`
* def `MercLib.Signatures.FixPoint`
* def `MercLib.Signatures.IsStable`
* def `MercLib.Signatures.SplitFixPoint`
* def `MercLib.Signatures.SplitSignature`
* def `MercLib.Signatures.StrongFixPoint`
* def `MercLib.Signatures.StrongSignature`

## `MercLib.Sigref.Branching`

* inductive `MercLib.Sigref.BranchingInv`
* def `MercLib.Sigref.BranchingSigrefCorrect`
* def `MercLib.Sigref.BranchingSigrefTerminates`
* def `MercLib.Sigref.BranchingSigrefTotal`
* def `MercLib.Sigref.BranchingStep`
* inductive `MercLib.Sigref.StepFacts`
* def `MercLib.Sigref.branchRel`
* def `MercLib.Sigref.inertClosure`
* def `MercLib.Sigref.predB`

## `MercLib.Sigref.Defs`

* inductive `MercLib.Sigref.Config`
* def `MercLib.Sigref.Config.noConfusionType`
* def `MercLib.Sigref.Saturated`
* def `MercLib.Sigref.splitRel`
* def `MercLib.Sigref.splitSetoid`

## `MercLib.Sigref.Iteration`

* inductive `MercLib.Sigref.RP.IsSplit`
* def `MercLib.Sigref.RP.Iter`
* def `MercLib.Sigref.RP.RPSigrefCorrect`
* def `MercLib.Sigref.RP.RPSigrefTerminates`
* def `MercLib.Sigref.RP.RPSigrefTotal`
* def `MercLib.Sigref.RP.init`
* def `MercLib.Sigref.RP.markTargets`

## `MercLib.Sigref.KeyComp`

* inductive `MercLib.Sigref.BD`
* def `MercLib.Sigref.BD.noConfusionType`
* def `MercLib.Sigref.BD.setoid`
* inductive `MercLib.Sigref.KC`
* def `MercLib.Sigref.KC.noConfusionType`
* inductive `MercLib.Sigref.KSig`
* def `MercLib.Sigref.KSig.noConfusionType`
* inductive `MercLib.Sigref.RP.BlockInv`
* def `MercLib.Sigref.RP.IterK`
* def `MercLib.Sigref.RP.RPSigrefKCorrect`
* def `MercLib.Sigref.RP.RPSigrefKTerminates`
* def `MercLib.Sigref.RP.RPSigrefKTotal`
* def `MercLib.Sigref.RP.SubsetExcl`
* def `MercLib.Sigref.RP.TopoSorted`
* def `MercLib.Sigref.RP.flatSig`
* def `MercLib.Sigref.RP.intern`
* def `MercLib.Sigref.RP.kcRun`
* def `MercLib.Sigref.RP.kcStep`
* def `MercLib.Sigref.RP.keysOf`
* def `MercLib.Sigref.RP.renumber`
* def `MercLib.Sigref.RP.sortedDirty`
* def `MercLib.Sigref.RP.toBD`

## `MercLib.Sigref.Proofs.Branching_Proofs` (proofs)

* axiom `MercLib.Sigref.branchingSigrefCorrect`
* axiom `MercLib.Sigref.branchingSigrefTerminates`
* axiom `MercLib.Sigref.branchingSigrefTotal`

## `MercLib.Sigref.Proofs.CountingSort_Proofs` (proofs)

* def `MercLib.Sigref.cumS` *not a headline*
* def `MercLib.Sigref.posOf` *not a headline*
* def `MercLib.Sigref.rankOf` *not a headline*

## `MercLib.Sigref.Proofs.IterK_Proofs` (proofs)

* axiom `MercLib.Sigref.RP.rpSigrefKCorrect`
* axiom `MercLib.Sigref.RP.rpSigrefKTerminates`
* axiom `MercLib.Sigref.RP.rpSigrefKTotal`

## `MercLib.Sigref.Proofs.Iteration_Proofs` (proofs)

* axiom `MercLib.Sigref.RP.rpSigrefCorrect`
* axiom `MercLib.Sigref.RP.rpSigrefTerminates`
* axiom `MercLib.Sigref.RP.rpSigrefTotal`

## `MercLib.Sigref.Proofs.KeyComp_Proofs` (proofs)

* inductive `MercLib.Sigref.RP.Env` *not a headline*
* def `MercLib.Sigref.RP.Env.noConfusionType` *not a headline*
* inductive `MercLib.Sigref.RP.KInv` *not a headline*
* def `MercLib.Sigref.RP.fsig` *not a headline*

## `MercLib.Sigref.Proofs.Refinable_Proofs` (proofs)

* inductive `MercLib.Sigref.RP.LoopInv` *not a headline*
* theorem `MercLib.Sigref.RP.lastClean.congr_simp` *not a headline*

## `MercLib.Sigref.Proofs.SigE_Proofs` (proofs)

* def `MercLib.Sigref.SigData.PS` *not a headline*

## `MercLib.Sigref.Proofs.Split_Proofs` (proofs)

* def `MercLib.Sigref.RP.blockSize` *not a headline*
* def `MercLib.Sigref.RP.blockStates` *not a headline*
* def `MercLib.Sigref.RP.clsL` *not a headline*
* axiom `MercLib.Sigref.RP.clsL_getElem` *not a headline*
* axiom `MercLib.Sigref.RP.clsL_getElem_state` *not a headline*
* def `MercLib.Sigref.RP.keepPiece` *not a headline*
* axiom `MercLib.Sigref.RP.keepPiece_lt` *not a headline*
* def `MercLib.Sigref.RP.numPieces` *not a headline*
* def `MercLib.Sigref.RP.pieces` *not a headline*
* def `MercLib.Sigref.RP.rAt` *not a headline*
* def `MercLib.Sigref.RP.rr` *not a headline*
* axiom `MercLib.Sigref.RP.rr_eq_iff` *not a headline*
* def `MercLib.Sigref.RP.szsL` *not a headline*
* axiom `MercLib.Sigref.RP.szs_count` *not a headline*
* axiom `MercLib.Sigref.RP.szs_length` *not a headline*

## `MercLib.Sigref.Proofs.Strong_Proofs` (proofs)

* axiom `MercLib.Sigref.strongSigrefCorrect`
* axiom `MercLib.Sigref.strongSigrefTerminates`

## `MercLib.Sigref.Proofs.TopoSort_Proofs` (proofs)

* inductive `MercLib.Sigref.Topo.Ext` *not a headline*
* inductive `MercLib.Sigref.Topo.Good` *not a headline*
* inductive `MercLib.Sigref.Topo.Root` *not a headline*

## `MercLib.Sigref.Refinable`

* inductive `MercLib.Sigref.RP`
* def `MercLib.Sigref.RP.Dirty`
* def `MercLib.Sigref.RP.DirtyClosure`
* inductive `MercLib.Sigref.RP.WF`
* def `MercLib.Sigref.RP.closure`
* def `MercLib.Sigref.RP.closureLoop`
* def `MercLib.Sigref.RP.config`
* def `MercLib.Sigref.RP.lastClean`
* def `MercLib.Sigref.RP.mark`
* def `MercLib.Sigref.RP.markList`
* def `MercLib.Sigref.RP.noConfusionType`
* def `MercLib.Sigref.RP.setoid`

## `MercLib.Sigref.RelBisim`

* def `MercLib.Sigref.E`
* def `MercLib.Sigref.InertReach`
* def `MercLib.Sigref.InertTr`
* def `MercLib.Sigref.relHasTau`
* def `MercLib.Sigref.relLTS`

## `MercLib.Sigref.Scc`

* def `MercLib.Sigref.IsCrossBB`
* def `MercLib.Sigref.IsTauSccPartition`
* def `MercLib.Sigref.TauScc`
* def `MercLib.Sigref.quotientTau`

## `MercLib.Sigref.SigData`

* inductive `MercLib.Sigref.SigData`
* def `MercLib.Sigref.SigData.noConfusionType`

## `MercLib.Sigref.Strong`

* inductive `MercLib.Sigref.StrongInv`
* def `MercLib.Sigref.StrongSigrefCorrect`
* def `MercLib.Sigref.StrongSigrefTerminates`
* def `MercLib.Sigref.StrongStep`
* def `MercLib.Sigref.cls`
* axiom `MercLib.Sigref.cls_saturated`
* def `MercLib.Sigref.initConfig`
* def `MercLib.Sigref.predS`
* def `MercLib.Sigref.sigS`
* def `MercLib.Sigref.stepSetoid`
* def `MercLib.Sigref.topSetoid`

## `MercLib.Sigref.TopoSort`

* def `MercLib.Sigref.Topo.Acyclic`
* inductive `MercLib.Sigref.Topo.Cfg`
* def `MercLib.Sigref.Topo.Cfg.noConfusionType`
* inductive `MercLib.Sigref.Topo.Mark`
* def `MercLib.Sigref.Topo.Mark.ctorElimType`
* def `MercLib.Sigref.Topo.Mark.noConfusionType`
* def `MercLib.Sigref.Topo.Mark.ofNat`
* axiom `MercLib.Sigref.Topo.Mark.ofNat_ctorIdx`
* def `MercLib.Sigref.Topo.init`
* def `MercLib.Sigref.Topo.instDecidableEqMark`
* def `MercLib.Sigref.Topo.measure`
* def `MercLib.Sigref.Topo.pushSuccs`
* def `MercLib.Sigref.Topo.step`

## `MercLib.Sigref.Worklist`

* inductive `MercLib.Sigref.RP.Ctx`
* def `MercLib.Sigref.RP.Ctx.noConfusionType`
* inductive `MercLib.Sigref.RP.WLInv`
* def `MercLib.Sigref.RP.markAllW`
* def `MercLib.Sigref.RP.markW`

## `MercVerified.Code.Funs`

* def `verified.Pair.Insts.CoreCmpEq`
* def `verified.Pair.Insts.CoreCmpOrd`
* def `verified.Pair.Insts.CoreCmpPartialEqPair`
* def `verified.Pair.Insts.CoreCmpPartialOrdPair`
* def `verified.Pair.Insts.CoreHashHash`
* def `verified.Slice.Insts.CoreOpsIndexIndexTagIndexU.index`
* def `verified.Usize.Insts.CoreFmtDisplay`
* def `verified.Usize.Insts.CoreHashHash`
* def `verified.Usize.Insts.Merc_collectionsCompressed_vecCompressedEntry`
* def `verified.alloc.vec.Vec.Insts.CoreCmpEq`
* def `verified.alloc.vec.Vec.Insts.CoreHashHash`
* def `verified.alloc.vec.Vec.Insts.CoreOpsIndexIndexMutTagIndexU.index_mut`
* def `verified.alloc.vec.Vec.Insts.CoreOpsIndexIndexTagIndexU.index`
* def `verified.core.borrow.Borrow.Blanket`
* def `verified.merc_collections.indexed_partition.IndexedPartition.Insts.Merc_reductionPartitionPartition`
* def `verified.merc_collections.indexed_partition.IndexedPartition.Insts.Merc_reductionPartitionPartition.block_number`
* def `verified.merc_collections.indexed_partition.IndexedPartition.Insts.Merc_reductionPartitionPartition.len`
* def `verified.merc_collections.indexed_partition.IndexedPartition.Insts.Merc_reductionPartitionPartition.num_of_blocks`
* def `verified.merc_collections.indexed_partition.IndexedPartition.block`
* def `verified.merc_collections.indexed_partition.IndexedPartition.impl.num_of_blocks`
* def `verified.merc_collections.indexed_partition.IndexedPartition.len`
* def `verified.merc_collections.indexed_partition.IndexedPartition.new`
* def `verified.merc_collections.indexed_partition.IndexedPartition.set_block`
* def `verified.merc_collections.indexed_partition.NOT_IN_PARTITION`
* def `verified.merc_lts.incoming_transitions.FromTransition.new`
* def `verified.merc_lts.incoming_transitions.IncomingTransitions.incoming_silent_transitions`
* def `verified.merc_lts.incoming_transitions.IncomingTransitions.incoming_silent_transitions_loop`
* def `verified.merc_lts.incoming_transitions.IncomingTransitions.incoming_silent_transitions_loop.body`
* def `verified.merc_lts.incoming_transitions.IncomingTransitions.incoming_transitions`
* def `verified.merc_lts.incoming_transitions.IncomingTransitions.incoming_transitions_loop`
* def `verified.merc_lts.incoming_transitions.IncomingTransitions.incoming_transitions_loop.body`
* def `verified.merc_lts.incoming_transitions.IncomingTransitions.new`
* def `verified.merc_lts.incoming_transitions.copy_prefix`
* def `verified.merc_lts.incoming_transitions.copy_prefix_loop`
* def `verified.merc_lts.incoming_transitions.copy_prefix_loop.body`
* def `verified.merc_lts.incoming_transitions.count_all_incoming`
* def `verified.merc_lts.incoming_transitions.count_all_incoming_loop`
* def `verified.merc_lts.incoming_transitions.count_all_incoming_loop.body`
* def `verified.merc_lts.incoming_transitions.count_incoming`
* def `verified.merc_lts.incoming_transitions.count_incoming_loop`
* def `verified.merc_lts.incoming_transitions.count_incoming_loop.body`
* def `verified.merc_lts.incoming_transitions.insert_sorted`
* def `verified.merc_lts.incoming_transitions.insert_sorted_loop`
* def `verified.merc_lts.incoming_transitions.insert_sorted_loop.body`
* def `verified.merc_lts.incoming_transitions.new_counts`
* def `verified.merc_lts.incoming_transitions.new_counts_loop`
* def `verified.merc_lts.incoming_transitions.new_counts_loop.body`
* def `verified.merc_lts.incoming_transitions.new_labels`
* def `verified.merc_lts.incoming_transitions.new_labels_loop`
* def `verified.merc_lts.incoming_transitions.new_labels_loop.body`
* def `verified.merc_lts.incoming_transitions.new_states`
* def `verified.merc_lts.incoming_transitions.new_states_loop`
* def `verified.merc_lts.incoming_transitions.new_states_loop.body`
* def `verified.merc_lts.incoming_transitions.place_all_incoming`
* def `verified.merc_lts.incoming_transitions.place_all_incoming_loop`
* def `verified.merc_lts.incoming_transitions.place_all_incoming_loop.body`
* def `verified.merc_lts.incoming_transitions.place_incoming`
* def `verified.merc_lts.incoming_transitions.place_incoming_loop`
* def `verified.merc_lts.incoming_transitions.place_incoming_loop.body`
* def `verified.merc_lts.incoming_transitions.prefix_sum`
* def `verified.merc_lts.incoming_transitions.prefix_sum_loop`
* def `verified.merc_lts.incoming_transitions.prefix_sum_loop.body`
* def `verified.merc_lts.incoming_transitions.sort_all_incoming`
* def `verified.merc_lts.incoming_transitions.sort_all_incoming_loop`
* def `verified.merc_lts.incoming_transitions.sort_all_incoming_loop.body`
* def `verified.merc_lts.incoming_transitions.sort_incoming`
* def `verified.merc_lts.incoming_transitions.sort_incoming_loop`
* def `verified.merc_lts.incoming_transitions.sort_incoming_loop.body`
* def `verified.merc_lts.labelled_transition_system.LabelledTransitionSystem.Insts.Merc_ltsLtsLTS`
* def `verified.merc_lts.labelled_transition_system.LabelledTransitionSystem.Insts.Merc_ltsLtsLTS.initial_state_index`
* def `verified.merc_lts.labelled_transition_system.LabelledTransitionSystem.Insts.Merc_ltsLtsLTS.is_hidden_label`
* def `verified.merc_lts.labelled_transition_system.LabelledTransitionSystem.Insts.Merc_ltsLtsLTS.iter_states`
* def `verified.merc_lts.labelled_transition_system.LabelledTransitionSystem.Insts.Merc_ltsLtsLTS.iter_states_loop`
* def `verified.merc_lts.labelled_transition_system.LabelledTransitionSystem.Insts.Merc_ltsLtsLTS.iter_states_loop.body`
* def `verified.merc_lts.labelled_transition_system.LabelledTransitionSystem.Insts.Merc_ltsLtsLTS.labels`
* def `verified.merc_lts.labelled_transition_system.LabelledTransitionSystem.Insts.Merc_ltsLtsLTS.num_of_labels`
* def `verified.merc_lts.labelled_transition_system.LabelledTransitionSystem.Insts.Merc_ltsLtsLTS.num_of_states`
* def `verified.merc_lts.labelled_transition_system.LabelledTransitionSystem.Insts.Merc_ltsLtsLTS.num_of_transitions`
* def `verified.merc_lts.labelled_transition_system.LabelledTransitionSystem.Insts.Merc_ltsLtsLTS.outgoing_transitions`
* def `verified.merc_lts.labelled_transition_system.LabelledTransitionSystem.Insts.Merc_ltsLtsLTS.outgoing_transitions_loop`
* def `verified.merc_lts.labelled_transition_system.LabelledTransitionSystem.Insts.Merc_ltsLtsLTS.outgoing_transitions_loop.body`
* def `verified.merc_lts.labelled_transition_system.LabelledTransitionSystem.assert_no_duplicate_transitions`
* def `verified.merc_lts.labelled_transition_system.LabelledTransitionSystem.assert_no_duplicate_transitions_loop0`
* def `verified.merc_lts.labelled_transition_system.LabelledTransitionSystem.assert_no_duplicate_transitions_loop0.body`
* def `verified.merc_lts.labelled_transition_system.LabelledTransitionSystem.assert_no_duplicate_transitions_loop0_loop0`
* def `verified.merc_lts.labelled_transition_system.LabelledTransitionSystem.assert_no_duplicate_transitions_loop0_loop0.body`
* def `verified.merc_lts.labelled_transition_system.LabelledTransitionSystem.assert_offsets_valid`
* def `verified.merc_lts.labelled_transition_system.LabelledTransitionSystem.assert_offsets_valid_loop`
* def `verified.merc_lts.labelled_transition_system.LabelledTransitionSystem.assert_offsets_valid_loop.body`
* def `verified.merc_lts.labelled_transition_system.LabelledTransitionSystem.assert_transition_unique`
* def `verified.merc_lts.labelled_transition_system.LabelledTransitionSystem.assert_transition_unique_loop`
* def `verified.merc_lts.labelled_transition_system.LabelledTransitionSystem.assert_transition_unique_loop.body`
* def `verified.merc_lts.labelled_transition_system.LabelledTransitionSystem.assert_transitions_valid`
* def `verified.merc_lts.labelled_transition_system.LabelledTransitionSystem.assert_transitions_valid_loop`
* def `verified.merc_lts.labelled_transition_system.LabelledTransitionSystem.assert_transitions_valid_loop.body`
* def `verified.merc_lts.labelled_transition_system.LabelledTransitionSystem.assert_valid`
* def `verified.merc_lts.labelled_transition_system.LabelledTransitionSystem.from_raw_parts`
* def `verified.merc_lts.labelled_transition_system.LabelledTransitionSystem.new_from_permutation_vec`
* def `verified.merc_lts.labelled_transition_system.LabelledTransitionSystem.new_from_permutation_vec_loop0`
* def `verified.merc_lts.labelled_transition_system.LabelledTransitionSystem.new_from_permutation_vec_loop0.body`
* def `verified.merc_lts.labelled_transition_system.LabelledTransitionSystem.new_from_permutation_vec_loop0_loop0`
* def `verified.merc_lts.labelled_transition_system.LabelledTransitionSystem.new_from_permutation_vec_loop0_loop0.body`
* def `verified.merc_lts.labelled_transition_system.invert_permutation`
* def `verified.merc_lts.labelled_transition_system.invert_permutation_loop`
* def `verified.merc_lts.labelled_transition_system.invert_permutation_loop.body`
* def `verified.merc_lts.lts.TransitionLabel.is_tau_label.default`
* def `verified.merc_reduction.block_partition.Block.has_marked`
* def `verified.merc_reduction.block_partition.Block.has_unmarked`
* def `verified.merc_reduction.block_partition.Block.iter_marked`
* def `verified.merc_reduction.block_partition.Block.len`
* def `verified.merc_reduction.block_partition.Block.len_marked`
* def `verified.merc_reduction.block_partition.Block.new`
* def `verified.merc_reduction.block_partition.Block.new_unmarked`
* def `verified.merc_reduction.block_partition.Block.unmark_all`
* def `verified.merc_reduction.block_partition.BlockIter.Insts.CoreIterTraitsIteratorIteratorTagIndexUsizeStateTag`
* def `verified.merc_reduction.block_partition.BlockIter.Insts.CoreIterTraitsIteratorIteratorTagIndexUsizeStateTag.next`
* def `verified.merc_reduction.block_partition.BlockPartition.Insts.Merc_reductionPartitionPartition`
* def `verified.merc_reduction.block_partition.BlockPartition.Insts.Merc_reductionPartitionPartition.block_number`
* def `verified.merc_reduction.block_partition.BlockPartition.Insts.Merc_reductionPartitionPartition.len`
* def `verified.merc_reduction.block_partition.BlockPartition.Insts.Merc_reductionPartitionPartition.num_of_blocks`
* def `verified.merc_reduction.block_partition.BlockPartition.block`
* def `verified.merc_reduction.block_partition.BlockPartition.finish_partition_marked`
* def `verified.merc_reduction.block_partition.BlockPartition.finish_partition_marked_loop0`
* def `verified.merc_reduction.block_partition.BlockPartition.finish_partition_marked_loop0.body`
* def `verified.merc_reduction.block_partition.BlockPartition.finish_partition_marked_loop0_loop0`
* def `verified.merc_reduction.block_partition.BlockPartition.finish_partition_marked_loop0_loop0.body`
* def `verified.merc_reduction.block_partition.BlockPartition.is_element_marked`
* def `verified.merc_reduction.block_partition.BlockPartition.is_trivially_partitioned`
* def `verified.merc_reduction.block_partition.BlockPartition.iter_block`
* def `verified.merc_reduction.block_partition.BlockPartition.mark_backward_closure`
* def `verified.merc_reduction.block_partition.BlockPartition.mark_backward_closure_loop0`
* def `verified.merc_reduction.block_partition.BlockPartition.mark_backward_closure_loop0.body`
* def `verified.merc_reduction.block_partition.BlockPartition.mark_backward_closure_loop0_loop0`
* def `verified.merc_reduction.block_partition.BlockPartition.mark_backward_closure_loop0_loop0.body`
* def `verified.merc_reduction.block_partition.BlockPartition.mark_backward_closure_loop0_loop0_loop0`
* def `verified.merc_reduction.block_partition.BlockPartition.mark_backward_closure_loop0_loop0_loop0.body`
* def `verified.merc_reduction.block_partition.BlockPartition.mark_backward_closure_loop0_loop1`
* def `verified.merc_reduction.block_partition.BlockPartition.mark_backward_closure_loop0_loop1.body`
* def `verified.merc_reduction.block_partition.BlockPartition.mark_backward_closure_loop0_loop2`
* def `verified.merc_reduction.block_partition.BlockPartition.mark_backward_closure_loop0_loop2.body`
* def `verified.merc_reduction.block_partition.BlockPartition.mark_backward_closure_loop0_loop2_loop0`
* def `verified.merc_reduction.block_partition.BlockPartition.mark_backward_closure_loop0_loop2_loop0.body`
* def `verified.merc_reduction.block_partition.BlockPartition.mark_backward_closure_loop0_loop3`
* def `verified.merc_reduction.block_partition.BlockPartition.mark_backward_closure_loop0_loop3.body`
* def `verified.merc_reduction.block_partition.BlockPartition.mark_backward_closure_loop0_loop3_loop0`
* def `verified.merc_reduction.block_partition.BlockPartition.mark_backward_closure_loop0_loop3_loop0.body`
* def `verified.merc_reduction.block_partition.BlockPartition.mark_element`
* def `verified.merc_reduction.block_partition.BlockPartition.marked_elements_sorted`
* def `verified.merc_reduction.block_partition.BlockPartition.new`
* def `verified.merc_reduction.block_partition.BlockPartition.new_block_to_swap`
* def `verified.merc_reduction.block_partition.BlockPartition.new_block_to_swap_loop0`
* def `verified.merc_reduction.block_partition.BlockPartition.new_block_to_swap_loop0.body`
* def `verified.merc_reduction.block_partition.BlockPartition.new_block_to_swap_loop0_loop0`
* def `verified.merc_reduction.block_partition.BlockPartition.new_block_to_swap_loop0_loop0.body`
* def `verified.merc_reduction.block_partition.BlockPartition.new_loop`
* def `verified.merc_reduction.block_partition.BlockPartition.new_loop.body`
* def `verified.merc_reduction.block_partition.BlockPartition.num_of_blocks`
* def `verified.merc_reduction.block_partition.BlockPartition.swap_blocks`
* def `verified.merc_reduction.block_partition.BlockPartition.swap_blocks_loop0`
* def `verified.merc_reduction.block_partition.BlockPartition.swap_blocks_loop0.body`
* def `verified.merc_reduction.block_partition.BlockPartition.swap_blocks_loop0_loop0`
* def `verified.merc_reduction.block_partition.BlockPartition.swap_blocks_loop0_loop0.body`
* def `verified.merc_reduction.block_partition.BlockPartition.swap_elements`
* def `verified.merc_reduction.block_partition.BlockPartition.trivial_partition_marked`
* def `verified.merc_reduction.block_partition.BlockPartitionBuilder.Insts.CoreDefaultDefault.default`
* def `verified.merc_reduction.divergence_preserving.DivergencePreservingLts.Insts.Merc_ltsLtsLTS`
* def `verified.merc_reduction.divergence_preserving.DivergencePreservingLts.Insts.Merc_ltsLtsLTS.initial_state_index`
* def `verified.merc_reduction.divergence_preserving.DivergencePreservingLts.Insts.Merc_ltsLtsLTS.is_hidden_label`
* def `verified.merc_reduction.divergence_preserving.DivergencePreservingLts.Insts.Merc_ltsLtsLTS.iter_states`
* def `verified.merc_reduction.divergence_preserving.DivergencePreservingLts.Insts.Merc_ltsLtsLTS.labels`
* def `verified.merc_reduction.divergence_preserving.DivergencePreservingLts.Insts.Merc_ltsLtsLTS.num_of_labels`
* def `verified.merc_reduction.divergence_preserving.DivergencePreservingLts.Insts.Merc_ltsLtsLTS.num_of_states`
* def `verified.merc_reduction.divergence_preserving.DivergencePreservingLts.Insts.Merc_ltsLtsLTS.num_of_transitions`
* def `verified.merc_reduction.divergence_preserving.DivergencePreservingLts.Insts.Merc_ltsLtsLTS.outgoing_transitions`
* def `verified.merc_reduction.divergence_preserving.DivergencePreservingLts.new`
* def `verified.merc_reduction.divergence_preserving.DivergencePreservingLts.new_loop`
* def `verified.merc_reduction.divergence_preserving.DivergencePreservingLts.new_loop.body`
* def `verified.merc_reduction.divergence_preserving.rename_tau_self_loops`
* def `verified.merc_reduction.divergence_preserving.rename_tau_self_loops_loop`
* def `verified.merc_reduction.divergence_preserving.rename_tau_self_loops_loop.body`
* def `verified.merc_reduction.partition.Partition.is_empty.default`
* def `verified.merc_reduction.quotient.push_transitions`
* def `verified.merc_reduction.quotient.push_transitions_loop`
* def `verified.merc_reduction.quotient.push_transitions_loop.body`
* def `verified.merc_reduction.quotient.quotient_build`
* def `verified.merc_reduction.quotient.quotient_build_loop`
* def `verified.merc_reduction.quotient.quotient_build_loop.body`
* def `verified.merc_reduction.quotient.quotient_collect_transitions`
* def `verified.merc_reduction.quotient.quotient_collect_transitions_loop0`
* def `verified.merc_reduction.quotient.quotient_collect_transitions_loop0.body`
* def `verified.merc_reduction.quotient.quotient_collect_transitions_loop0_loop0`
* def `verified.merc_reduction.quotient.quotient_collect_transitions_loop0_loop0.body`
* def `verified.merc_reduction.quotient.quotient_collect_transitions_loop0_loop0_loop0`
* def `verified.merc_reduction.quotient.quotient_collect_transitions_loop0_loop0_loop0.body`
* def `verified.merc_reduction.quotient.quotient_lts_naive`
* def `verified.merc_reduction.scc_decomposition.SCC_UNVISITED`
* def `verified.merc_reduction.scc_decomposition.scc_finish`
* def `verified.merc_reduction.scc_decomposition.scc_next_child`
* def `verified.merc_reduction.scc_decomposition.scc_next_child_loop`
* def `verified.merc_reduction.scc_decomposition.scc_next_child_loop.body`
* def `verified.merc_reduction.scc_decomposition.scc_pop_component`
* def `verified.merc_reduction.scc_decomposition.scc_pop_component_loop`
* def `verified.merc_reduction.scc_decomposition.scc_pop_component_loop.body`
* def `verified.merc_reduction.scc_decomposition.scc_process_work`
* def `verified.merc_reduction.scc_decomposition.scc_process_work_loop`
* def `verified.merc_reduction.scc_decomposition.scc_process_work_loop.body`
* def `verified.merc_reduction.scc_decomposition.scc_step`
* def `verified.merc_reduction.scc_decomposition.scc_visit_roots`
* def `verified.merc_reduction.scc_decomposition.scc_visit_roots_loop`
* def `verified.merc_reduction.scc_decomposition.scc_visit_roots_loop.body`
* def `verified.merc_reduction.scc_decomposition.tau_scc_decomposition_iterative`
* def `verified.merc_reduction.signature_refinement.branching_bisim_sigref`
* def `verified.merc_reduction.signature_refinement.branching_bisim_sigref_impl`
* def `verified.merc_reduction.signature_refinement.branching_bisim_sigref_impl.closure.Insts.CoreOpsFunctionFnOnceTupleBlockPartition`
* def `verified.merc_reduction.signature_refinement.branching_bisim_sigref_impl.closure.Insts.CoreOpsFunctionFnOnceTupleBlockPartition.call_once`
* def `verified.merc_reduction.signature_refinement.branching_partition_marked`
* def `verified.merc_reduction.signature_refinement.branching_process_marked_elements`
* def `verified.merc_reduction.signature_refinement.branching_process_marked_elements_loop`
* def `verified.merc_reduction.signature_refinement.branching_process_marked_elements_loop.body`
* def `verified.merc_reduction.signature_refinement.branching_process_worklist_block`
* def `verified.merc_reduction.signature_refinement.branching_run_worklist_loop`
* def `verified.merc_reduction.signature_refinement.branching_run_worklist_loop_loop`
* def `verified.merc_reduction.signature_refinement.branching_run_worklist_loop_loop.body`
* def `verified.merc_reduction.signature_refinement.branching_signature_index`
* def `verified.merc_reduction.signature_refinement.branching_signature_refinement`
* def `verified.merc_reduction.signature_refinement.branching_signature_refinement.closure.Insts.CoreOpsFunctionFnMutTupleTagIndexUsizeBlockTag`
* def `verified.merc_reduction.signature_refinement.branching_signature_refinement.closure.Insts.CoreOpsFunctionFnMutTupleTagIndexUsizeBlockTag.call_mut`
* def `verified.merc_reduction.signature_refinement.branching_signature_refinement.closure.Insts.CoreOpsFunctionFnOnceTupleTagIndexUsizeBlockTag`
* def `verified.merc_reduction.signature_refinement.branching_signature_refinement.closure.Insts.CoreOpsFunctionFnOnceTupleTagIndexUsizeBlockTag.call_once`
* def `verified.merc_reduction.signature_refinement.count_block_occurrence`
* def `verified.merc_reduction.signature_refinement.is_subset_excluding`
* def `verified.merc_reduction.signature_refinement.is_subset_excluding_loop`
* def `verified.merc_reduction.signature_refinement.is_subset_excluding_loop.body`
* def `verified.merc_reduction.signature_refinement.mark_dirty_new_blocks`
* def `verified.merc_reduction.signature_refinement.mark_dirty_new_blocks_loop`
* def `verified.merc_reduction.signature_refinement.mark_dirty_new_blocks_loop.body`
* def `verified.merc_reduction.signature_refinement.mark_dirty_states`
* def `verified.merc_reduction.signature_refinement.mark_dirty_states_loop0`
* def `verified.merc_reduction.signature_refinement.mark_dirty_states_loop0.body`
* def `verified.merc_reduction.signature_refinement.mark_dirty_states_loop0_loop0`
* def `verified.merc_reduction.signature_refinement.mark_dirty_states_loop0_loop0.body`
* def `verified.merc_reduction.signature_refinement.maybe_mark_backward_closure`
* def `verified.merc_reduction.signature_refinement.renumber_branching`
* def `verified.merc_reduction.signature_refinement.renumber_branching_loop`
* def `verified.merc_reduction.signature_refinement.renumber_branching_loop.body`
* def `verified.merc_reduction.signature_refinement.strong_bisim_sigref`
* def `verified.merc_reduction.signature_refinement.strong_bisim_sigref.closure.Insts.CoreOpsFunctionFnOnceTupleBlockPartition`
* def `verified.merc_reduction.signature_refinement.strong_bisim_sigref.closure.Insts.CoreOpsFunctionFnOnceTupleBlockPartition.call_once`
* def `verified.merc_reduction.signature_refinement.strong_intern_signature`
* def `verified.merc_reduction.signature_refinement.strong_partition_marked`
* def `verified.merc_reduction.signature_refinement.strong_process_marked_elements`
* def `verified.merc_reduction.signature_refinement.strong_process_marked_elements_loop`
* def `verified.merc_reduction.signature_refinement.strong_process_marked_elements_loop.body`
* def `verified.merc_reduction.signature_refinement.strong_process_worklist_block`
* def `verified.merc_reduction.signature_refinement.strong_run_worklist_loop`
* def `verified.merc_reduction.signature_refinement.strong_run_worklist_loop_loop`
* def `verified.merc_reduction.signature_refinement.strong_run_worklist_loop_loop.body`
* def `verified.merc_reduction.signature_refinement.strong_signature_refinement`
* def `verified.merc_reduction.signature_refinement.strong_signature_refinement.closure.Insts.CoreOpsFunctionFnMutTupleTagIndexUsizeBlockTag`
* def `verified.merc_reduction.signature_refinement.strong_signature_refinement.closure.Insts.CoreOpsFunctionFnMutTupleTagIndexUsizeBlockTag.call_mut`
* def `verified.merc_reduction.signature_refinement.strong_signature_refinement.closure.Insts.CoreOpsFunctionFnOnceTupleTagIndexUsizeBlockTag`
* def `verified.merc_reduction.signature_refinement.strong_signature_refinement.closure.Insts.CoreOpsFunctionFnOnceTupleTagIndexUsizeBlockTag.call_once`
* def `verified.merc_reduction.signatures.branching_bisim_signature`
* def `verified.merc_reduction.signatures.branching_bisim_signature_inductive`
* def `verified.merc_reduction.signatures.branching_bisim_signature_inductive_loop`
* def `verified.merc_reduction.signatures.branching_bisim_signature_inductive_loop.body`
* def `verified.merc_reduction.signatures.branching_bisim_signature_loop0`
* def `verified.merc_reduction.signatures.branching_bisim_signature_loop0.body`
* def `verified.merc_reduction.signatures.branching_bisim_signature_loop0_loop0`
* def `verified.merc_reduction.signatures.branching_bisim_signature_loop0_loop0.body`
* def `verified.merc_reduction.signatures.is_tau_hat`
* def `verified.merc_reduction.signatures.strong_bisim_signature`
* def `verified.merc_reduction.signatures.strong_bisim_signature_loop`
* def `verified.merc_reduction.signatures.strong_bisim_signature_loop.body`
* def `verified.merc_reduction.signatures.tau_cycle_elimination_and_reorder`
* def `verified.merc_reduction.signatures.tau_hat`
* def `verified.merc_reduction.sort_topological.order_to_permutation`
* def `verified.merc_reduction.sort_topological.order_to_permutation_loop`
* def `verified.merc_reduction.sort_topological.order_to_permutation_loop.body`
* def `verified.merc_reduction.sort_topological.push_unvisited_successors`
* def `verified.merc_reduction.sort_topological.push_unvisited_successors_loop`
* def `verified.merc_reduction.sort_topological.push_unvisited_successors_loop.body`
* def `verified.merc_reduction.sort_topological.sort_topological_hidden`
* def `verified.merc_reduction.sort_topological.sort_topological_hidden_loop`
* def `verified.merc_reduction.sort_topological.sort_topological_hidden_loop.body`
* def `verified.merc_reduction.sort_topological.sort_topological_visit_all`
* def `verified.merc_reduction.sort_topological.sort_topological_visit_all_loop`
* def `verified.merc_reduction.sort_topological.sort_topological_visit_all_loop.body`
* def `verified.merc_reduction.sort_topological.sort_topological_visit_hidden`
* def `verified.merc_reduction.sort_topological.sort_topological_visit_hidden_loop`
* def `verified.merc_reduction.sort_topological.sort_topological_visit_hidden_loop.body`
* def `verified.merc_utilities.tagged_index.TagIndex.Insts.CoreCloneClone`
* def `verified.merc_utilities.tagged_index.TagIndex.Insts.CoreCloneClone.clone`
* def `verified.merc_utilities.tagged_index.TagIndex.Insts.CoreCmpEq`
* def `verified.merc_utilities.tagged_index.TagIndex.Insts.CoreCmpOrd`
* def `verified.merc_utilities.tagged_index.TagIndex.Insts.CoreCmpOrd.cmp`
* def `verified.merc_utilities.tagged_index.TagIndex.Insts.CoreCmpPartialEq.eq`
* def `verified.merc_utilities.tagged_index.TagIndex.Insts.CoreCmpPartialEqTagIndex`
* def `verified.merc_utilities.tagged_index.TagIndex.Insts.CoreCmpPartialEqTagIndex.eq`
* def `verified.merc_utilities.tagged_index.TagIndex.Insts.CoreCmpPartialOrdTagIndex`
* def `verified.merc_utilities.tagged_index.TagIndex.Insts.CoreCmpPartialOrdTagIndex.partial_cmp`
* def `verified.merc_utilities.tagged_index.TagIndex.Insts.CoreHashHash`
* def `verified.merc_utilities.tagged_index.TagIndex.Insts.CoreOpsDerefDeref.deref`
* def `verified.merc_utilities.tagged_index.TagIndex.Insts.Merc_collectionsCompressed_vecCompressedEntry`
* def `verified.merc_utilities.tagged_index.TagIndex.new`
* def `verified.merc_utilities.tagged_index.TagIndex.value`
* def `verified.reduction_bridge.branching_bisim_signature`
* def `verified.reduction_bridge.branching_bisim_signature_inductive`
* def `verified.reduction_bridge.branching_bisim_sigref`
* def `verified.reduction_bridge.branching_bisim_sigref_impl`
* def `verified.reduction_bridge.labelled_transition_system_branching_bisim_sigref`
* def `verified.reduction_bridge.labelled_transition_system_strong_bisim_sigref`
* def `verified.reduction_bridge.strong_bisim_signature`
* def `verified.reduction_bridge.strong_bisim_sigref`
* def `verified.reduction_bridge.tau_cycle_elimination_and_reorder`
* def `verified.rustc_hash.FxBuildHasher.Insts.CoreDefaultDefault`
* def `verified.rustc_hash.FxBuildHasher.Insts.CoreHashBuildHasherFxHasher`
* def `verified.rustc_hash.FxHasher.Insts.CoreHashHasher`

## `MercVerified.Code.FunsExternal`

* axiom `Pair.Insts.CoreCmpOrd.cmp_spec`
* axiom `Pair.Insts.CoreCmpPartialEqPair.eq_spec`
* axiom `alloc.vec.Vec.Insts.CoreDefaultDefault.default_spec`
* axiom `alloc.vec.Vec.clear_spec`
* axiom `alloc.vec.Vec.dedup_spec`
* axiom `alloc.vec.Vec.pop_cons_spec`
* axiom `alloc.vec.Vec.pop_nil_spec`
* axiom `alloc.vec.Vec.resize_with_spec`
* def `core.cmp.Eq.IsLawful`
* def `core.cmp.Ord.IsTotalOrder`
* def `core.cmp.PartialEq.IsLawfulEq`
* def `core.hash.Hash.IsTotal`
* def `core.hash.Hasher.IsTotal`
* def `core.ops.function.FnMut.IsTotal`
* axiom `core.slice.Slice.sort_unstable_spec`
* axiom `merc_io.progress.TimeProgress.print_spec`
* axiom `merc_reduction.signature_refinement.new_worklist_progress_spec`
* axiom `merc_utilities.timing.Timing.measure_spec`
* def `verified.core.hash.BuildHasher.IsTotal`

## `MercVerified.Code.FunsExternalSpecs`

* inductive `MercVerified.Refinement.PartInv`
* def `MercVerified.Refinement.blk0`
* def `MercVerified.Refinement.blkAt`
* def `MercVerified.Refinement.e2bAt`
* def `MercVerified.Refinement.eAt`
* def `MercVerified.Refinement.offAt`
* axiom `Pair.Insts.CoreHashHash.isTotal`
* axiom `Usize.Insts.CoreHashHash.isTotal`
* axiom `alloc.vec.Vec.Insts.CoreHashHash.isTotal`
* axiom `alloc.vec.Vec.extend_blockIter_spec`
* axiom `merc_collections.compressed_vec.ByteCompressedVec.index_spec`
* axiom `merc_collections.compressed_vec.ByteCompressedVec.len_spec`
* axiom `merc_collections.compressed_vec.ByteCompressedVec.new_spec`
* axiom `merc_collections.compressed_vec.ByteCompressedVec.push_spec`
* axiom `merc_collections.compressed_vec.ByteCompressedVec.toList`
* def `merc_reduction.block_partition.Block.WellFormed`
* axiom `merc_reduction.block_partition.Block.assert_consistent_ok`
* axiom `merc_reduction.block_partition.BlockPartition.assert_consistent_ok`
* axiom `merc_utilities.tagged_index.TagIndex.Insts.CoreHashHash.isTotal`
* axiom `rustc_hash.FxBuildHasher.Insts.CoreHashBuildHasherFxHasher.isTotal`
* def `std.collections.hash.map.HashMap.AllValues`
* axiom `std.collections.hash.map.HashMap.get_key_value_eq`
* axiom `std.collections.hash.map.HashMap.get_key_value_ok`
* axiom `std.collections.hash.map.HashMap.insert_allValues`
* axiom `std.collections.hash.map.HashMap.insert_get_key_value_other`
* axiom `std.collections.hash.map.HashMap.insert_spec`
* axiom `std.collections.hash.map.HashMapKVSGlobal.default_spec`

## `MercVerified.Code.FunsExternal_Template`

* axiom `Pair.Insts.CoreCmpOrd.cmp`
* axiom `Pair.Insts.CoreCmpPartialEqPair.eq`
* axiom `Pair.Insts.CoreCmpPartialEqPair.ne`
* axiom `Pair.Insts.CoreCmpPartialOrdPair.partial_cmp`
* axiom `Pair.Insts.CoreHashHash.hash`
* axiom `Usize.Insts.CoreHashHash.hash`
* axiom `Usize.Insts.Merc_collectionsCompressed_vecCompressedEntry.bytes_required`
* axiom `Usize.Insts.Merc_collectionsCompressed_vecCompressedEntry.from_bytes`
* axiom `Usize.Insts.Merc_collectionsCompressed_vecCompressedEntry.to_bytes`
* axiom `alloc.vec.Vec.Insts.CoreDefaultDefault.default`
* axiom `alloc.vec.Vec.Insts.CoreHashHash.hash`
* axiom `alloc.vec.Vec.Insts.CoreIterTraitsCollectExtend.extend`
* axiom `alloc.vec.Vec.clear`
* axiom `alloc.vec.Vec.dedup`
* axiom `alloc.vec.Vec.is_empty`
* axiom `alloc.vec.Vec.pop`
* axiom `alloc.vec.Vec.resize_with`
* axiom `core.borrow.Borrow.Blanket.borrow`
* axiom `core.slice.Slice.sort_unstable`
* axiom `merc_collections.compressed_vec.ByteCompressedVec.index`
* axiom `merc_collections.compressed_vec.ByteCompressedVec.len`
* axiom `merc_collections.compressed_vec.ByteCompressedVec.new`
* axiom `merc_collections.compressed_vec.ByteCompressedVec.push`
* axiom `merc_io.progress.TimeProgress.print`
* axiom `merc_reduction.block_partition.Block.assert_consistent`
* axiom `merc_reduction.block_partition.BlockPartition.assert_consistent`
* axiom `merc_reduction.signature_refinement.new_worklist_progress`
* axiom `merc_utilities.tagged_index.TagIndex.Insts.CoreHashHash.hash`
* axiom `merc_utilities.tagged_index.TagIndex.Insts.Merc_collectionsCompressed_vecCompressedEntry.bytes_required`
* axiom `merc_utilities.tagged_index.TagIndex.Insts.Merc_collectionsCompressed_vecCompressedEntry.from_bytes`
* axiom `merc_utilities.tagged_index.TagIndex.Insts.Merc_collectionsCompressed_vecCompressedEntry.to_bytes`
* axiom `merc_utilities.timing.Timing.measure`
* axiom `rustc_hash.FxBuildHasher.Insts.CoreDefaultDefault.default`
* axiom `rustc_hash.FxBuildHasher.Insts.CoreHashBuildHasherFxHasher.build_hasher`
* axiom `rustc_hash.FxHasher.Insts.CoreHashHasher.finish`
* axiom `rustc_hash.FxHasher.Insts.CoreHashHasher.write`
* axiom `std.collections.hash.map.HashMap.get_key_value`
* axiom `std.collections.hash.map.HashMap.insert`
* axiom `std.collections.hash.map.HashMapKVSGlobal.Insts.CoreDefaultDefault.default`
* axiom `std.collections.hash.set.HashSet.clear`
* axiom `std.collections.hash.set.HashSet.contains`
* axiom `std.collections.hash.set.HashSet.insert`

## `MercVerified.Code.Types`

* def `instDiscriminantMarkIsize`
* inductive `verified.core.borrow.Borrow`
* def `verified.core.borrow.Borrow.noConfusionType`
* inductive `verified.core.hash.BuildHasher`
* def `verified.core.hash.BuildHasher.noConfusionType`
* def `verified.core.marker.PhantomData`
* inductive `verified.merc_collections.compressed_vec.CompressedEntry`
* def `verified.merc_collections.compressed_vec.CompressedEntry.noConfusionType`
* def `verified.merc_collections.indexed_partition.BlockTag`
* inductive `verified.merc_collections.indexed_partition.IndexedPartition`
* def `verified.merc_collections.indexed_partition.IndexedPartition.noConfusionType`
* inductive `verified.merc_lts.incoming_transitions.FromTransition`
* def `verified.merc_lts.incoming_transitions.FromTransition.noConfusionType`
* inductive `verified.merc_lts.incoming_transitions.IncomingTransitions`
* def `verified.merc_lts.incoming_transitions.IncomingTransitions.noConfusionType`
* inductive `verified.merc_lts.labelled_transition_system.LabelledTransitionSystem`
* def `verified.merc_lts.labelled_transition_system.LabelledTransitionSystem.noConfusionType`
* inductive `verified.merc_lts.lts.LTS`
* def `verified.merc_lts.lts.LTS.noConfusionType`
* def `verified.merc_lts.lts.LabelTag`
* def `verified.merc_lts.lts.StateTag`
* inductive `verified.merc_lts.lts.Transition`
* def `verified.merc_lts.lts.Transition.noConfusionType`
* inductive `verified.merc_lts.lts.TransitionLabel`
* def `verified.merc_lts.lts.TransitionLabel.noConfusionType`
* inductive `verified.merc_reduction.block_partition.Block`
* def `verified.merc_reduction.block_partition.Block.noConfusionType`
* inductive `verified.merc_reduction.block_partition.BlockIter`
* def `verified.merc_reduction.block_partition.BlockIter.noConfusionType`
* inductive `verified.merc_reduction.block_partition.BlockPartition`
* def `verified.merc_reduction.block_partition.BlockPartition.noConfusionType`
* inductive `verified.merc_reduction.block_partition.BlockPartitionBuilder`
* def `verified.merc_reduction.block_partition.BlockPartitionBuilder.noConfusionType`
* inductive `verified.merc_reduction.divergence_preserving.DivergencePreservingLts`
* def `verified.merc_reduction.divergence_preserving.DivergencePreservingLts.noConfusionType`
* inductive `verified.merc_reduction.partition.Partition`
* def `verified.merc_reduction.partition.Partition.noConfusionType`
* inductive `verified.merc_reduction.scc_decomposition.SccContext`
* def `verified.merc_reduction.scc_decomposition.SccContext.noConfusionType`
* inductive `verified.merc_reduction.signature_refinement.WorklistContextBranching`
* def `verified.merc_reduction.signature_refinement.WorklistContextBranching.noConfusionType`
* inductive `verified.merc_reduction.signature_refinement.WorklistContextStrong`
* def `verified.merc_reduction.signature_refinement.WorklistContextStrong.noConfusionType`
* def `verified.merc_reduction.signature_refinement.branching_bisim_sigref_impl.closure`
* def `verified.merc_reduction.signature_refinement.branching_signature_refinement.closure`
* def `verified.merc_reduction.signature_refinement.strong_bisim_sigref.closure`
* def `verified.merc_reduction.signature_refinement.strong_signature_refinement.closure`
* inductive `verified.merc_reduction.sort_topological.Mark`
* def `verified.merc_reduction.sort_topological.Mark.ctorElimType`
* def `verified.merc_reduction.sort_topological.Mark.noConfusionType`
* def `verified.merc_reduction.sort_topological.Mark.read_discriminant`
* inductive `verified.merc_utilities.tagged_index.TagIndex`
* def `verified.merc_utilities.tagged_index.TagIndex.noConfusionType`
* def `verified.rustc_hash.FxBuildHasher`

## `MercVerified.Code.TypesExternal_Template`

* axiom `merc_collections.compressed_vec.ByteCompressedVec`
* axiom `merc_io.progress.TimeProgress`
* axiom `merc_utilities.timing.Timing`
* axiom `rustc_hash.FxHasher`
* axiom `std.collections.hash.map.HashMap`
* axiom `std.collections.hash.set.HashSet`

## `MercVerified.Lts.Lts`

* def `MercVerified.Lts.NonEmpty`
* def `MercVerified.Lts.WellFormed`
* def `MercVerified.Lts.instHasTauTagIndexUsizeLabelTag`
* def `MercVerified.Lts.tauLabelIndex`
* def `MercVerified.Lts.toLTS`
* def `MercVerified.Lts.tr`

## `MercVerified.Lts.Proofs.Foundation_Proofs` (proofs)

* def `MercVerified.Lts.Proofs.Sz` *not a headline*
* def `MercVerified.Lts.Proofs.uTag` *not a headline*
* def `MercVerified.Lts.Proofs.uTotal` *not a headline*

## `MercVerified.Lts.Proofs.IncomingTransitions_Proofs` (proofs)

* def `MercVerified.Lts.Proofs.outVec` *not a headline*

## `MercVerified.Lts.Proofs.LtsData_Proofs` (proofs)

* inductive `MercVerified.Lts.Proofs.RawGood` *not a headline*
* inductive `MercVerified.Lts.Proofs.RawOf` *not a headline*

## `MercVerified.Refinement.Proofs.BranchingClosure_Proofs` (proofs)

* inductive `MercVerified.Refinement.Proofs.Mono` *not a headline*

## `MercVerified.Refinement.Proofs.BranchingProcess_Proofs` (proofs)

* inductive `MercVerified.Refinement.Proofs.BrSem` *not a headline*
* theorem `MercVerified.Refinement.Proofs.BrSem.congr_simp` *not a headline*
* inductive `MercVerified.Refinement.Proofs.CEnv` *not a headline*
* def `MercVerified.Refinement.Proofs.aLTS` *not a headline*
* def `MercVerified.Refinement.Proofs.absInit` *not a headline*
* def `MercVerified.Refinement.Proofs.absOf` *not a headline*
* def `MercVerified.Refinement.Proofs.bdOf` *not a headline*
* def `MercVerified.Refinement.Proofs.decodeSig` *not a headline*
* def `MercVerified.Refinement.Proofs.keyOf` *not a headline*
* def `MercVerified.Refinement.Proofs.stOf` *not a headline*
* def `MercVerified.Refinement.Proofs.toFin` *not a headline*
* theorem `MercVerified.Refinement.Proofs.toFin.congr_simp` *not a headline*

## `MercVerified.Refinement.Proofs.BranchingSignature_Proofs` (proofs)

* inductive `MercVerified.Refinement.Proofs.BrOk` *not a headline*

## `MercVerified.Refinement.Proofs.BranchingStep_Proofs` (proofs)

* inductive `MercVerified.Refinement.Proofs.BrLoopInv` *not a headline*
* def `MercVerified.Refinement.Proofs.cfgOf` *not a headline*

## `MercVerified.Refinement.Proofs.BranchingTop_Proofs` (proofs)

* axiom `MercVerified.Refinement.Proofs.branching_bisim_sigref_impl_correct`

## `MercVerified.Refinement.Proofs.Intern_Proofs` (proofs)

* def `MercVerified.Refinement.Proofs.IdInv` *not a headline*
* axiom `MercVerified.Refinement.Proofs.IdInv.new` *not a headline*
* axiom `MercVerified.Refinement.Proofs.IdInv.nodup` *not a headline*
* axiom `MercVerified.Refinement.Proofs.IdInv.of_empty` *not a headline*
* def `MercVerified.Refinement.Proofs.internGet` *not a headline*

## `MercVerified.Refinement.Proofs.MarkDirty_Proofs` (proofs)

* def `MercVerified.Refinement.Proofs.DirtyInv` *not a headline*

## `MercVerified.Refinement.Proofs.PartitionInv_Proofs` (proofs)

* def `MercVerified.Refinement.Proofs.IsMarked` *not a headline*
* def `MercVerified.Refinement.Proofs.zBT` *not a headline*
* def `MercVerified.Refinement.Proofs.zST` *not a headline*

## `MercVerified.Refinement.Proofs.PreprocessRust_Proofs` (proofs)

* axiom `MercVerified.Refinement.Proofs.branching_bisim_sigref_correct`

## `MercVerified.Refinement.Proofs.QuotientRust_Proofs` (proofs)

* inductive `MercVerified.Refinement.Proofs.BuildInv` *not a headline*
* def `MercVerified.Refinement.Proofs.QElem` *not a headline*
* def `MercVerified.Refinement.Proofs.offs` *not a headline*
* def `MercVerified.Refinement.Proofs.rowOf` *not a headline*
* def `MercVerified.Refinement.Proofs.tot` *not a headline*

## `MercVerified.Refinement.Proofs.QuotientSort_Proofs` (proofs)

* def `MercVerified.Refinement.Proofs.QElem'` *not a headline*
* def `MercVerified.Refinement.Proofs.qLt` *not a headline*

## `MercVerified.Refinement.Proofs.Refinement_Proofs` (proofs)

* theorem `Aeneas.Std.toStr.congr_simp` *not a headline*
* axiom `MercVerified.Refinement.Proofs.strong_bisim_sigref_correct`
* axiom `MercVerified.Refinement.Proofs.strong_bisim_sigref_same_block_iff_bisimilar`

## `MercVerified.Refinement.Proofs.ScatterLoop_Proofs` (proofs)

* inductive `MercVerified.Refinement.Proofs.ScInv` *not a headline*
* def `MercVerified.Refinement.Proofs.labelNat` *not a headline*

## `MercVerified.Refinement.Proofs.SccRust_Proofs` (proofs)

* theorem `MercLib.Tarjan.Graph.mk.congr_simp` *not a headline*
* def `MercVerified.Refinement.Proofs.SC` *not a headline*
* inductive `MercVerified.Refinement.Proofs.SR` *not a headline*
* def `MercVerified.Refinement.Proofs.view` *not a headline*

## `MercVerified.Refinement.Proofs.SigKey_Proofs` (proofs)

* def `MercVerified.Refinement.Proofs.SigEntry` *not a headline*
* def `MercVerified.Refinement.Proofs.entLt` *not a headline*

## `MercVerified.Refinement.Proofs.Spme_Proofs` (proofs)

* def `MercVerified.Refinement.Proofs.IsSigKey` *not a headline*
* inductive `MercVerified.Refinement.Proofs.SpmeInv` *not a headline*
* inductive `MercVerified.Refinement.Proofs.SpmeSem` *not a headline*
* def `MercVerified.Refinement.Proofs.clsAt` *not a headline*
* def `MercVerified.Refinement.Proofs.emptyKey` *not a headline*

## `MercVerified.Refinement.Proofs.TopoSortRust_Proofs` (proofs)

* def `MercVerified.Refinement.Proofs.Eout` *not a headline*
* inductive `MercVerified.Refinement.Proofs.RI` *not a headline*
* def `MercVerified.Refinement.Proofs.RMark` *not a headline*
* def `MercVerified.Refinement.Proofs.mOf` *not a headline*
* def `MercVerified.Refinement.Proofs.mkOf` *not a headline*
* def `MercVerified.Refinement.Proofs.outLen` *not a headline*
* def `MercVerified.Refinement.Proofs.potSum` *not a headline*
* axiom `MercVerified.Refinement.Proofs.potSum_update_none` *not a headline*

## `MercVerified.Refinement.Proofs.WorklistLoop_Proofs` (proofs)

* def `MercVerified.Refinement.Proofs.BT` *not a headline*
* def `MercVerified.Refinement.Proofs.InternMap` *not a headline*
* def `MercVerified.Refinement.Proofs.LoopStepEq` *not a headline*
* def `MercVerified.Refinement.Proofs.ST` *not a headline*
* def `MercVerified.Refinement.Proofs.SigKey` *not a headline*
* def `MercVerified.Refinement.Proofs.SigPair` *not a headline*
* def `MercVerified.Refinement.Proofs.SpmeState` *not a headline*
* def `MercVerified.Refinement.Proofs.VecTy` *not a headline*
* def `MercVerified.Refinement.Proofs.internBuildHasher` *not a headline*
* def `MercVerified.Refinement.Proofs.internEqInst` *not a headline*
* def `MercVerified.Refinement.Proofs.internHashInst` *not a headline*
* inductive `MercVerified.Refinement.Proofs.spmeTable` *not a headline*
* inductive `MercVerified.Refinement.Proofs.spmeTable.below` *not a headline*
* axiom `MercVerified.Refinement.Proofs.spmeTable.brecOn` *not a headline*

## `MercVerified.Refinement.Refinement`

* def `MercVerified.Refinement.BranchingBisimSigrefCorrectSpec`
* def `MercVerified.Refinement.BranchingBisimSigrefImplCorrectSpec`
* def `MercVerified.Refinement.BranchingLtsAssumptions`
* def `MercVerified.Refinement.PartitionWellFormed`
* def `MercVerified.Refinement.PreprocessAssumptions`
* def `MercVerified.Refinement.StateCountFits`
* def `MercVerified.Refinement.StrongBisimSigrefCorrectSpec`
