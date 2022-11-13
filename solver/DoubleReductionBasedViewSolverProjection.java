package in.ac.iisc.cds.dsl.cdgvendor.solver;

/*
 * How to read code by dk:
 * Before every chunk of code a variable is defined. The value of that variable is found out in the corresponding code. The name of variable tells what the code is doing
 */

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.ListIterator;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.Stack;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.FileWriter;
import java.io.IOException;
import java.io.ObjectOutputStream;
import java.time.temporal.TemporalField;

import org.jgrapht.Graphs;
import org.jgrapht.UndirectedGraph;
import org.jgrapht.alg.ConnectivityInspector;
import org.jgrapht.graph.DefaultEdge;
import org.jgrapht.graph.SimpleGraph;
import org.json.JSONArray;
import org.json.JSONObject;

import com.microsoft.z3.ArithExpr;
import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.Context;
import com.microsoft.z3.IntExpr;
import com.microsoft.z3.IntNum;
import com.microsoft.z3.Model;
import com.microsoft.z3.Optimize;
import com.microsoft.z3.Solver;
import com.microsoft.z3.Status;

import in.ac.iisc.cds.dsl.cdgvendor.constants.PostgresVConfig;
import in.ac.iisc.cds.dsl.cdgvendor.constants.PostgresVConfig.Key;
import in.ac.iisc.cds.dsl.cdgvendor.lpSolver.LPSolver;
import in.ac.iisc.cds.dsl.cdgvendor.model.ProjectionStuffInColumn;
import in.ac.iisc.cds.dsl.cdgvendor.model.ProjectionStuffInSSPRegion;
import in.ac.iisc.cds.dsl.cdgvendor.model.SkewRegion;
import in.ac.iisc.cds.dsl.cdgvendor.model.SolverViewStats;
import in.ac.iisc.cds.dsl.cdgvendor.model.ValueCombination;
import in.ac.iisc.cds.dsl.cdgvendor.model.ValueCombinationF;
import in.ac.iisc.cds.dsl.cdgvendor.model.VariableValuePair;
import in.ac.iisc.cds.dsl.cdgvendor.model.ViewInfo;
import in.ac.iisc.cds.dsl.cdgvendor.model.ViewSolution;
import in.ac.iisc.cds.dsl.cdgvendor.model.ViewSolutionInMemory;
import in.ac.iisc.cds.dsl.cdgvendor.model.ViewSolutionRegion;
import in.ac.iisc.cds.dsl.cdgvendor.model.ViewSolutionWithSolverStats;
import in.ac.iisc.cds.dsl.cdgvendor.model.formal.FormalCondition;
import in.ac.iisc.cds.dsl.cdgvendor.model.formal.FormalConditionAggregate;
import in.ac.iisc.cds.dsl.cdgvendor.model.formal.FormalConditionAnd;
import in.ac.iisc.cds.dsl.cdgvendor.model.formal.FormalConditionBaseAggregate;
import in.ac.iisc.cds.dsl.cdgvendor.model.formal.FormalConditionComposite;
import in.ac.iisc.cds.dsl.cdgvendor.model.formal.FormalConditionOr;
import in.ac.iisc.cds.dsl.cdgvendor.model.formal.FormalConditionSOP;
import in.ac.iisc.cds.dsl.cdgvendor.model.formal.FormalConditionSimpleInt;
import in.ac.iisc.cds.dsl.cdgvendor.model.formal.Symbol;
import in.ac.iisc.cds.dsl.cdgvendor.reducer.Bucket;
import in.ac.iisc.cds.dsl.cdgvendor.reducer.BucketF;
import in.ac.iisc.cds.dsl.cdgvendor.reducer.BucketStructure;
import in.ac.iisc.cds.dsl.cdgvendor.reducer.BucketStructureF;
import in.ac.iisc.cds.dsl.cdgvendor.reducer.DatabaseSummaryProjection;
import in.ac.iisc.cds.dsl.cdgvendor.reducer.Partition;
import in.ac.iisc.cds.dsl.cdgvendor.reducer.ProjectionVariable;
import in.ac.iisc.cds.dsl.cdgvendor.reducer.Reducer;
import in.ac.iisc.cds.dsl.cdgvendor.reducer.Region;
import in.ac.iisc.cds.dsl.cdgvendor.reducer.RegionF;
import in.ac.iisc.cds.dsl.cdgvendor.reducer.RegionSummaryProjection;
import in.ac.iisc.cds.dsl.cdgvendor.solver.ModifiedTree.Node;
import in.ac.iisc.cds.dsl.cdgvendor.solver.Z3Solver.ConsistencyMakerType;
import in.ac.iisc.cds.dsl.cdgvendor.utils.DebugHelper;
import in.ac.iisc.cds.dsl.cdgvendor.utils.FileUtils;
import in.ac.iisc.cds.dsl.cdgvendor.utils.MutablePair;
import in.ac.iisc.cds.dsl.cdgvendor.utils.Pair;
import in.ac.iisc.cds.dsl.cdgvendor.utils.StopWatch;
import in.ac.iisc.cds.dsl.cdgvendor.utils.Triplet;
import in.ac.iisc.cds.dsl.dirty.DirtyCode;
import in.ac.iisc.cds.dsl.dirty.DirtyDatabaseSummary;
import in.ac.iisc.cds.dsl.dirty.DirtyValueCombinationWithProjectionValues;
import in.ac.iisc.cds.dsl.dirty.DirtyValueInterval;
import in.ac.iisc.cds.dsl.dirty.DirtyValueIntervalWithCount;
import in.ac.iisc.cds.dsl.dirty.DirtyVariableValuePairWithProjectionValues;
import in.ac.iisc.cds.dsl.dirty.DirtyViewSolution;
import in.ac.iisc.cds.dsl.dirty.ProjectionValues;
import it.unimi.dsi.fastutil.ints.IntArrayList;
import it.unimi.dsi.fastutil.ints.IntIterator;
import it.unimi.dsi.fastutil.ints.IntList;
import it.unimi.dsi.fastutil.ints.IntOpenHashSet;
import it.unimi.dsi.fastutil.longs.LongArrayList;
import it.unimi.dsi.fastutil.longs.LongList;

public class DoubleReductionBasedViewSolverProjection extends AbstractCliqueFinder {

	private final SolverViewStats solverStats;

	private final String slackVarNamePrefix = "slack_";

	// added by tarun
	List<LongList> cliqueIdxtoConditionBValuesList;
	List<Partition> cliqueIdxtoPList;
	List<List<IntList>> cliqueIdxtoPSimplifiedList;

	List<HashMap<Integer, Integer>> mappedIndexOfConsistencyConstraint; // Required by CONSISTENCYFILTERS type of
																		// consistency maker
	List<Integer> cliqueWiseTotalSingleSplitPointRegions; // per clique
	List<List<Pair<Integer, Boolean>>> applicableConditionsOnClique;
	List<CliqueIntersectionInfo> cliqueIntersectionInfos; // Required by BRUTEFORCE type of consistency make

	// variables for shadab
	List<List<RegionSummaryProjection>> cliqueToRegionsSummary = new ArrayList<>();

	List<List<Double>> bucketSplitPoints;
	List<List<Long>> splitPointsCount;
	boolean wantPowerset = true;
	boolean wantComplexityAnalysis = false;
	boolean datasynthcomp = false;
	boolean wantAccuracy = true;// only works for projection CCs
	boolean tupleGen = false;//printing takes a lot of time, keep false as default
	List<RegionSummaryProjection> finalRegionSummaryGlobal; //This is the summary for projections
	ListIterator<RegionSummaryProjection> summIter;
	RegionSummaryProjection regSum;
	// end
	HashMap<String, Long> allIntervalRegionValueMap = new HashMap<>();
	HashMap<String, Long> allIntervalisedRegionsMap = new HashMap<>();
	HashMap<String, Long> allDxValuesMap = new HashMap<>();

	Map<Set<String>, List<List<Integer>>> cliqueToIntervalMap = new HashMap<>();

	List<Set<String>> orderedCliques = new ArrayList<>();
	List<List<String>> borrowedAttrPerClique = new ArrayList<>();

	// dividing skew
	Map<String, Integer> fkeyToCliqueIdx = new HashMap<>();

	// Skew Variables came from clique 0
	// List of fkeys
	// Corresponding pk Columns of fkeys
	// Correspondng intervalised region
	// Corresponding df vector of intervalised region
	Map<String, List<String>> fkeyToPkColumnsMap = new HashMap<>();
	Map<String, List<String>> fkeyToIntervalRegionMap = new HashMap<>();
	Map<String, List<List<Integer>>> allIntervalRegionsPerFKey = new HashMap<>();
	Map<String, Map<String, List<String>>> du = new HashMap<>();
	Map<String, HashMap<Integer, List<String>>> intervalToDxValuePerFkey = new HashMap<>();
	Map<String, Map<String, Region>> fkeyToActualInteervalisedRegMap = new HashMap<>();

	Map<String, Map<Long, List<Long>>> varPKValDistribution = new HashMap<>();

	Map<String, Region> intervalisedRegionMap = new HashMap<>();

	Map<String, Map<String, List<String>>> varToIntervalisedRegionMapPerFkey;
	
	//PKR
	Map<String, ConsistencyMakerType> consistencyMakerTypeHashmap = new HashMap<>();
	//Map<String, FormalCondition> consistencyConstraintsHashmap = new HashMap<>();
	Map<String, List<Map<List<String>, List<Integer>>>> cliqueToGroupkeyToRegionIdxHashmap = new HashMap<>();
	Map<String, List<Map<List<String>, Map<FormalConditionAggregate, List<Integer>>>> > cliqueToGroupkeyConditionToRegionIdxHashmap = new HashMap<>();
	Map<String, List<Map<List<String>, List<ProjectionVariable>>>> cliqueToGroupkeyToProjectionVariablesOptimizedHashmap = new HashMap<>();
	Map<String, HashMap<Set<String>, Set<String>>> cliquesToFKeyCoverageHashmap = new HashMap<>();

	boolean unifiedLP = false;

	public DoubleReductionBasedViewSolverProjection(String viewname, ViewInfo viewInfo, List<boolean[]> allTrueBS,
			List<Set<String>> arasuCliques, Map<String, IntList> bucketFloorsByColumns) {
		super(viewname, viewInfo, allTrueBS, arasuCliques, bucketFloorsByColumns);
		solverStats = new SolverViewStats();
		solverStats.relRowCount = viewInfo.getRowcount();

		// variables added here by tarun -- starts
		cliqueIdxtoConditionBValuesList = new ArrayList<>(cliqueCount);
		cliqueIdxtoPList = new ArrayList<>(cliqueCount);
		cliqueIdxtoPSimplifiedList = new ArrayList<>(cliqueCount);

		mappedIndexOfConsistencyConstraint = new ArrayList<>(); // Required by CONSISTENCYFILTERS type of consistency
																// maker
		cliqueWiseTotalSingleSplitPointRegions = new ArrayList<>(); // per clique
		applicableConditionsOnClique = new ArrayList<>();
		cliqueIntersectionInfos = new ArrayList<>(); // Required by BRUTEFORCE type of consistency make
		// variables added here by tarun ends --

	}

//	@Override
	public ViewSolutionWithSolverStats solveViewProjection(List<FormalCondition> conditions, List<Region> conditionRegions,
			FormalCondition consistencyConstraints[], ConsistencyMakerType consistencyMakerType) {

		StopWatch formulationPlusSolvingSW = new StopWatch("LP-SolvingPlusPostSolving-" + viewname);
		beginLPFormulation();
		List<LinkedList<VariableValuePair>> cliqueIdxToVarValuesList;

			cliqueIdxToVarValuesList = formulateAndSolve(conditions, conditionRegions, consistencyConstraints,
					consistencyMakerType);
		
		mergeCliqueSolutionsRegionwiseProjection(conditions, conditionRegions);
		finishSolving();

		if (PostgresVConfig.hydraVersions.contains(PostgresVConfig.HydraTypes.duplicationHydra)) {
			 dividingSkew(conditions);
		}

	
		finishPostSolving();
		solverStats.millisToSolve = formulationPlusSolvingSW.getTimeAndDispose();
	
		return null;
	}

//	@Override
	public HashMap<String, List<VariableValuePair>> unifiedsolveViewProjection(HashMap<String, List<List<IntList>>> viewTocliqueIdxtoPSimplifiedList, HashMap<String, List<LongList>> viewTocliqueIdxtoConditionBValuesList, HashMap<String, List<List<Double>>> viewTobucketSplitPoints, HashMap<String, HashMap<Set<String>, Set<String>>> viewTocliquesToFKeyCoverage, HashMap<String, List<Map<List<String>, List<Region>>>> viewTocliqueGroupkeyToConditionRegions, 
			HashMap<String, List<Map<List<String>, List<FormalConditionAggregate>>>> viewTocliqueGroupkeyToConditions, 
			HashMap<String, List<Partition>> viewTocliqueIdxtoPList, Context unifiedctx, Optimize unifiedsolver, 
			List<FormalCondition> conditions, List<Region> conditionRegions, FormalCondition consistencyConstraints[], 
			ConsistencyMakerType consistencyMakerType) {

		StopWatch formulationPlusSolvingSW = new StopWatch("LP-SolvingPlusPostSolving-" + viewname);
		beginLPFormulation();
		List<LinkedList<VariableValuePair>> cliqueIdxToVarValuesList;
		HashMap<String, List<VariableValuePair>> viewToVVPMap = new HashMap<>();

		viewToVVPMap = unifiedformulateAndSolve(viewTocliqueIdxtoPSimplifiedList, viewTocliqueIdxtoConditionBValuesList, viewTobucketSplitPoints, viewTocliquesToFKeyCoverage, viewTocliqueGroupkeyToConditionRegions, viewTocliqueGroupkeyToConditions, 
				viewTocliqueIdxtoPList, unifiedctx, unifiedsolver, conditions, conditionRegions, consistencyConstraints,
				consistencyMakerType);
		//comment by PKR
//		mergeCliqueSolutionsRegionwiseProjection(conditions, conditionRegions);
		finishSolving();

		if (PostgresVConfig.hydraVersions.contains(PostgresVConfig.HydraTypes.duplicationHydra)) {
			 dividingSkew(conditions);
		}

	
		finishPostSolving();
		solverStats.millisToSolve = formulationPlusSolvingSW.getTimeAndDispose();
	
		return viewToVVPMap;
	}	
	
	private void dividingSkew(List<FormalCondition> conditions) {

		for (String fkey : fkeyToCliqueIdx.keySet()) {

			int cliqueIdx = fkeyToCliqueIdx.get(fkey);
			Set<String> currentClique = this.arasuCliques.get(cliqueIdx);

			Partition partition = this.cliqueIdxtoPList.get(cliqueIdx);

			Map<String, List<FormalCondition>> regionToCCMap = new HashMap<>();

			Map<String, Region> intervalisedRegions = fkeyToActualInteervalisedRegMap.get(fkey);

			List<String> allTrueRegions = new ArrayList<>();

			for (String varname : varToIntervalisedRegionMapPerFkey.get(fkey).keySet()) {

				for (String regname : varToIntervalisedRegionMapPerFkey.get(fkey).get(varname)) {
					Long val = allIntervalisedRegionsMap.get(regname);
					if (val == 0) {
						continue;
					}
					boolean flag = false;
					Region intervalisedRegion = intervalisedRegions.get(regname);
					for (int c = 0; c < conditions.size(); c++) {
						FormalCondition curCondition = conditions.get(c);
						Set<String> appearingCols = new HashSet<>();
						getAppearingCols(appearingCols, curCondition);

						if (currentClique.containsAll(appearingCols)) {

							if (checkCCSatifyRegion(intervalisedRegion, appearingCols, curCondition)) {

								// System.out.println("Clique_" + i + "Region" + j + " -> " + " CC_" + c);

								if (!regionToCCMap.containsKey(regname)) {
									regionToCCMap.put(regname, new ArrayList<>());
								}

								regionToCCMap.get(regname).add(conditions.get(c));
								flag = true;

							}

						}

					}
					if (!flag) {
						allTrueRegions.add(regname);
					}
				}

			}

			// CC to region Map
			Map<FormalCondition, List<String>> CCToRegionMap = new HashMap<>();
			for (String regionName : regionToCCMap.keySet()) {

				for (FormalCondition fc : regionToCCMap.get(regionName)) {
					if (!CCToRegionMap.containsKey(fc)) {
						CCToRegionMap.put(fc, new ArrayList<>());
					}
					CCToRegionMap.get(fc).add(regionName);

				}

			}

			List<String> orderedRegions = new ArrayList<>(); // orderedRegions on the basis of most intersecting CCs
																// with a region
			List<Integer> orderedRegionsCCcount = new ArrayList<>();
			for (String region : regionToCCMap.keySet()) {
				if (orderedRegions.isEmpty()) {
					orderedRegions.add(region);
					orderedRegionsCCcount.add(regionToCCMap.get(region).size());
				} else {
					int i = 0;
					for (i = 0; i < orderedRegions.size(); i++) {

						if (regionToCCMap.get(region).size() >= orderedRegionsCCcount.get(i)) {
							break;
						}
					}

					orderedRegions.add(i, region);
					orderedRegionsCCcount.add(i, regionToCCMap.get(region).size());
				}
			}

			// All true region finding
			Set<Integer> CCSet = new HashSet<>();
			CCSet.addAll(cliqueIdxtoPSimplifiedList.get(cliqueIdx).get(0));
			for (int i = 1; i < cliqueIdxtoPSimplifiedList.get(cliqueIdx).size(); i++) {
				CCSet.retainAll(cliqueIdxtoPSimplifiedList.get(cliqueIdx).get(i));
			}

			if (CCSet.size() != 1) {
				throw new RuntimeException(" not expecting this");
			}
			int allTrueRegionIdx = -1; // var number of all left over of true region
			for (int i = 0; i < cliqueIdxtoPSimplifiedList.get(cliqueIdx).size(); i++) {

				Set<Integer> cp = new HashSet<>(cliqueIdxtoPSimplifiedList.get(cliqueIdx).get(i));

				if (CCSet.equals(cp)) {

					allTrueRegionIdx = i;
					break;

				}
			}

			for (String reg : allTrueRegions) {
				Integer Idx = Integer.parseInt(reg.split("var")[1].split("_")[1]);
				if (Idx != allTrueRegionIdx) {
					throw new RuntimeException("Something Wrong");
				}
			}

			// solveDF(orderedRegions, regionToCCMap, CCToRegionMap, fkey, cliqueIdx,
			// allTrueRegionIdx);

			// solveDFPerFK(orderedRegions, regionToCCMap, CCToRegionMap, fkey, cliqueIdx,
			// allTrueRegionIdx);
			solveDFPerFK1(orderedRegions, regionToCCMap, CCToRegionMap, fkey, cliqueIdx, allTrueRegionIdx,
					allTrueRegions);

			checkCCsAccuracy(CCToRegionMap, fkey);

		}

		checkEverything();

	}

	private void checkCCsAccuracy(Map<FormalCondition, List<String>> cCToRegionMap, String fkey) {

		// ss_sold_date_sk___2_q002.json
		if (PostgresVConfig.ccsDFvectors.containsKey("ss_sold_date_sk___2_q002.json")) {
			DFvector dfvector = PostgresVConfig.ccsDFvectors.get("ss_sold_date_sk___2_q002.json");
			System.out.print("");
		}

		for (FormalCondition condition : cCToRegionMap.keySet()) {

			String actualFkeyName = PostgresVConfig.reverseColumnAnonyMap.get(fkey);
			Integer counter = condition.getCounter();
			String queryname = condition.getQueryname();
			String dfVecKey = actualFkeyName + "___" + counter + "_" + queryname;
			Map<String, DFvector> ccsDFvectors = PostgresVConfig.ccsDFvectors;
			if (ccsDFvectors.containsKey(dfVecKey)) {
				DFvector dfvector = ccsDFvectors.get(dfVecKey);
				List<String> regionsList = cCToRegionMap.get(condition);
				List<Long> allPkVals = new ArrayList<>();
				Map<Long, Long> pkValCount = new HashMap<>();
				for (int i = 0; i < regionsList.size(); i++) {

					Map<Long, List<Long>> pkValDistribution = this.varPKValDistribution.get(regionsList.get(i));
					for (Long di : pkValDistribution.keySet()) {

						for (Long pkVal : pkValDistribution.get(di)) {

							if (!pkValCount.containsKey(pkVal)) {
								pkValCount.put(pkVal, 0L);
							}
							pkValCount.put(pkVal, pkValCount.get(pkVal) + di);

						}

					}

				}

				Map<Long, Long> dfMap = new HashMap<>();
				for (Long pkVal : pkValCount.keySet()) {

					Long dVal = pkValCount.get(pkVal);
					if (!dfMap.containsKey(dVal)) {
						dfMap.put(dVal, 0L);
					}
					dfMap.put(dVal, dfMap.get(dVal) + 1);

				}

				System.out.print("");
				List<Long> dValues = new ArrayList<>();
				List<Long> fValues = new ArrayList<>();
				for (long d : dfMap.keySet()) {
					dValues.add(d);
					fValues.add(dfMap.get(d));
				}
				DFvector generatedDFvector = new DFvector(dValues, fValues);
				long tupleCount = condition.getOutputCardinality();
				float error = dfvector.findError(generatedDFvector);

				System.out.println("Error : " + error);

			}

		}

	}

	private void checkEverything() {

		// Check all intervalised region tuplecount

		for (String regionName : this.varPKValDistribution.keySet()) {

			Long val = this.allIntervalisedRegionsMap.get(regionName);

			Long tupleCount = 0L;
			for (Long dVal : this.varPKValDistribution.get(regionName).keySet()) {

				tupleCount += dVal * this.varPKValDistribution.get(regionName).get(dVal).size();

			}

			if (tupleCount.longValue() != val.longValue()) {

				System.out.print("");
			}

		}

	}

	@SuppressWarnings("unused")
	private void solveDFPerFK1(List<String> orderedRegions, Map<String, List<FormalCondition>> regionToCCMap,
			Map<FormalCondition, List<String>> cCToRegionMap, String fkey, int cliqueIdx, int allTrueRegionIdx,
			List<String> allTrueRegions) {

		// IntervalBoundaries
		List<Long> pkValBoundaryList = new ArrayList<>();
		Map<Integer, Integer> intervalIdxMap = new HashMap<>();
		Long sumx = 0L;
		pkValBoundaryList.add(sumx);
		for (int i = 0; i < this.fkeyToIntervalRegionMap.get(fkey).size(); i++) {
			// t17_c018_clique0interval0
			intervalIdxMap.put(Integer.parseInt(this.fkeyToIntervalRegionMap.get(fkey).get(i).split("interval")[1]), i);

			sumx += this.relationCardinality;
			pkValBoundaryList.add(sumx);
		}

		Map<Integer, Map<Long, List<Long>>> futureFKValToAdd = new HashMap<>();

		HashMap<Integer, List<String>> intervalToRegions = new HashMap<>();
		Map<String, Long> tuplesPerRegionCovered = new HashMap<>();
		for (String regionname : orderedRegions) {

			// t17_c018_var0_0_interval_1
			int intervalIdx = Integer.parseInt(regionname.split("_")[5]);
			tuplesPerRegionCovered.put(regionname, 0L);
			if (!intervalToRegions.containsKey(intervalIdx)) {
				intervalToRegions.put(intervalIdx, new ArrayList<>());
			}
			intervalToRegions.get(intervalIdx).add(regionname);
		}

		for (String regionname : allTrueRegions) {
			tuplesPerRegionCovered.put(regionname, 0L);
		}

		Map<String, Set<String>> fkeyToBorrowedAttr = PostgresVConfig.fkeyToBorrowedAttr.get(viewname);
		Set<String> borrowedAttrs = fkeyToBorrowedAttr.get(fkey);

		if (borrowedAttrs.isEmpty()) {
			// System.out.print("NO need to manage fkey ");
			throw new RuntimeException("Can't possible to reach here");
		}

		List<String> sortedBorrowedAttr = new ArrayList<>(borrowedAttrs);
		Collections.sort(sortedBorrowedAttr);
		List<String> currentCliqueSorted = new ArrayList<>(this.arasuCliques.get(cliqueIdx));
		Collections.sort(currentCliqueSorted);

		Map<String, List<String>> varToIntervalisedRegionMap = this.varToIntervalisedRegionMapPerFkey.get(fkey);

		JSONArray dfJSONVector = PostgresVConfig.fkeySkewVectors.getJSONObject(viewname).getJSONArray(fkey);
		JSONArray d = dfJSONVector.getJSONArray(0);
		JSONArray f = dfJSONVector.getJSONArray(1);

		// Mapping each interval to dfvetor
		List<String> intervalRegionsList = this.fkeyToIntervalRegionMap.get(fkey);
		Map<String, DFvector> intervalToDFVectorMap = new HashMap<>();

		for (int i = 0; i < intervalRegionsList.size(); i++) {

			String intervalName = intervalRegionsList.get(i);
			int intervalIdx = Integer.parseInt(intervalName.split("interval")[1]);
			List<Long> dList = new ArrayList<>();
			List<Long> fList = new ArrayList<>();
			for (int j = 0; j < d.length(); j++) {
				// t17_c018_interval_0_d_1
				String dxVal = fkey + "_interval_" + intervalIdx + "_d_" + j;
				if (!this.allDxValuesMap.containsKey(dxVal)) {
					continue;
				}
				Long fval = this.allDxValuesMap.get(fkey + "_interval_" + intervalIdx + "_d_" + j);

				dList.add(d.getLong(j));
				fList.add(fval.longValue());
			}
			DFvector dfVec = new DFvector(dList, fList);
			intervalToDFVectorMap.put(intervalName, dfVec);

		}

		// Mapping each CC to dfVector
		Map<FormalCondition, DFvector> conditionToDFMap = new HashMap<>();
		Set<String> removedRegion = new HashSet<>();
		List<FormalCondition> removeList = new ArrayList<>();
		for (FormalCondition condition : cCToRegionMap.keySet()) {

			String actualFkeyName = PostgresVConfig.reverseColumnAnonyMap.get(fkey);
			Integer counter = condition.getCounter();
			String queryname = condition.getQueryname();
			String dfVecKey = actualFkeyName + "___" + counter + "_" + queryname;
			Map<String, DFvector> ccsDFvectors = PostgresVConfig.ccsDFvectors;
			if (ccsDFvectors.containsKey(dfVecKey)) {
				DFvector dfvector = ccsDFvectors.get(dfVecKey);
				DFvector dfvectorCopy = dfvector.copy();
				conditionToDFMap.put(condition, dfvectorCopy);
			} else {

				// remove that CC for now will add it later
				List<String> regionList = cCToRegionMap.get(condition);
				removedRegion.addAll(regionList);
				for (String region : regionList) {

					regionToCCMap.get(region).remove(condition);

				}

				removeList.add(condition);
			}

		}

		// removing CCs just because don't have df vector for it ..
		for (FormalCondition condition : removeList) {
			cCToRegionMap.remove(condition);
		}

		// Interval -> [ [d][f] -> pkVal ]
		Map<Integer, Map<DFvector, List<Long>>> futurePkValDFToAdd = new HashMap<>();
		// Keeps track of tuplesCovered by each region

		Map<String, Long> tuplesPerIntervalCovered = new HashMap<>();

		for (String interval : intervalToDFVectorMap.keySet()) {
			tuplesPerIntervalCovered.put(interval, 0L);
		}

		// Select maxd from set of intervals and and satisy that
		// and go on
		System.out.println("FKey going on " + fkey);
		Integer loop = 1;

		while (true) {

			long maxd = -1;
			long maxf = -1;

			String selectedInterval = null; // maxd interval

			// if all interval df values are finished
			if (intervalToDFVectorMap.isEmpty()) {
				break;
			}

			for (String interval : intervalToDFVectorMap.keySet()) {

				DFvector dfVector = intervalToDFVectorMap.get(interval);
				if (maxd < dfVector.getD().get(0)) {
					maxd = dfVector.getD().get(0);
					maxf = dfVector.getF().get(0);
					selectedInterval = interval;
				}

			}

			List<FormalCondition> ignoreCondition = new ArrayList<>();
			for (FormalCondition condition : conditionToDFMap.keySet()) {

				DFvector dfVector = conditionToDFMap.get(condition);
				List<Long> dValues = dfVector.getD();
				if (dValues.get(dValues.size() - 1) > maxd) {
					ignoreCondition.add(condition);
				}

			}

			// t17_c018_clique0interval1
			int intervalIdx = Integer.parseInt(selectedInterval.split("interval")[1]);

			// all true region in current Interval
			List<String> intervalAllTrueRegionList = new ArrayList<>();
			for (String region : allTrueRegions) {
				int regionInterval = Integer.parseInt(region.split("interval_")[1]);
				if (regionInterval == intervalIdx) {
					intervalAllTrueRegionList.add(region);
				}
			}
			if (intervalAllTrueRegionList.size() > 1) {
				throw new RuntimeException(" Was not expecting this ");
			}

			// intervalRemoved Region
			List<String> intervalRemovedRegionList = new ArrayList<>();
			for (String region : removedRegion) {

				if (intervalIdx == Integer.parseInt(region.split("interval_")[1])) {
					intervalRemovedRegionList.add(region);
				}

			}

			/*
			 * ------------ All True Region Covering ---------------
			 * 
			 */

			// intervalToRegions contains all left over region yet to finished
			// allTrue Region check

			if (!intervalToRegions.containsKey(intervalIdx)) {

				// Either interval is finished
				// If all true region only left in that interval
				// once we are here we can completely cover whole interval

				// Pass it to future it will handle

				if (!futurePkValDFToAdd.containsKey(intervalIdx)) {
					futurePkValDFToAdd.put(intervalIdx, new HashMap<>());
				}

				if (!tuplesPerIntervalCovered.containsKey(selectedInterval)) {
					tuplesPerIntervalCovered.put(selectedInterval, 0L);
				}
				DFvector dfvector = intervalToDFVectorMap.get(selectedInterval);
				Long tupleSum = 0L;

				for (int di = 0; di < dfvector.size(); di++) {

					List<Long> dValues = new ArrayList<>();
					List<Long> fValues = new ArrayList<>();
					dValues.add(dfvector.getD().get(di));
					fValues.add(dfvector.getF().get(di));
					Long pkValStart = pkValBoundaryList.get(intervalIdxMap.get(intervalIdx));
					DFvector dfvec = new DFvector(dValues, fValues);

					if (!futurePkValDFToAdd.get(intervalIdx).containsKey(dfvec)) {
						futurePkValDFToAdd.get(intervalIdx).put(dfvec, new ArrayList<>());
					}
					futurePkValDFToAdd.get(intervalIdx).get(dfvec).add(pkValStart);
					pkValBoundaryList.set(intervalIdxMap.get(intervalIdx), pkValStart + dfvector.getF().get(di));
					tupleSum += dfvec.getD().get(0) * dfvec.getF().get(0);

				}

				tuplesPerIntervalCovered.put(selectedInterval,
						tuplesPerIntervalCovered.get(selectedInterval) + tupleSum);

				// introduce check stmt for boundary check
				if (this.allIntervalRegionValueMap.get(selectedInterval).longValue() != tuplesPerIntervalCovered
						.get(selectedInterval).longValue()) {

					throw new RuntimeException("Interval values covered should match");

				}

				intervalToDFVectorMap.remove(selectedInterval);

				continue;

			}

			// Now we have maxd and maxf
			//
			List<String> overlappingRegionsWithInterval = intervalToRegions.get(intervalIdx);
			List<Set<FormalCondition>> overlappingCCsSet = new ArrayList<>();
			HashMap<FormalCondition, List<Integer>> conditionsToOverlappingRegions = new HashMap<>();
			for (int i = 0; i < overlappingRegionsWithInterval.size(); i++) {

				String regionname = overlappingRegionsWithInterval.get(i);
				List<FormalCondition> ccs = new ArrayList<>(regionToCCMap.get(regionname));
				HashSet<FormalCondition> ccsTempSet = new HashSet<>(ccs);
				ccsTempSet.removeAll(ignoreCondition);
				if (ccsTempSet.isEmpty()) {
					continue;
				}

				String overlappingRegion = overlappingRegionsWithInterval.get(i);
				if (allTrueRegions.contains(overlappingRegion)) {
					continue;
				}
				Set<FormalCondition> overlappingCCs = new HashSet<>(regionToCCMap.get(overlappingRegion));
				overlappingCCsSet.add(overlappingCCs);
				for (FormalCondition fc : overlappingCCs) {
					if (!conditionsToOverlappingRegions.containsKey(fc)) {
						conditionsToOverlappingRegions.put(fc, new ArrayList<>());
					}
					conditionsToOverlappingRegions.get(fc).add(i);
				}
			}

			if (conditionsToOverlappingRegions.isEmpty()) {

				if (!futurePkValDFToAdd.containsKey(intervalIdx)) {
					futurePkValDFToAdd.put(intervalIdx, new HashMap<>());
				}

				if (!tuplesPerIntervalCovered.containsKey(selectedInterval)) {
					tuplesPerIntervalCovered.put(selectedInterval, 0L);
				}
				DFvector dfvector = intervalToDFVectorMap.get(selectedInterval);
				Long tupleSum = 0L;

				for (int di = 0; di < dfvector.size(); di++) {

					List<Long> dValues = new ArrayList<>();
					List<Long> fValues = new ArrayList<>();
					dValues.add(dfvector.getD().get(di));
					fValues.add(dfvector.getF().get(di));
					Long pkValStart = pkValBoundaryList.get(intervalIdxMap.get(intervalIdx));
					DFvector dfvec = new DFvector(dValues, fValues);

					if (!futurePkValDFToAdd.get(intervalIdx).containsKey(dfvec)) {
						futurePkValDFToAdd.get(intervalIdx).put(dfvec, new ArrayList<>());
					}
					futurePkValDFToAdd.get(intervalIdx).get(dfvec).add(pkValStart);
					pkValBoundaryList.set(intervalIdxMap.get(intervalIdx), pkValStart + dfvector.getF().get(di));
					tupleSum += dfvec.getD().get(0) * dfvec.getF().get(0);

				}

				tuplesPerIntervalCovered.put(selectedInterval,
						tuplesPerIntervalCovered.get(selectedInterval) + tupleSum);

				// introduce check stmt for boundary check
				if (this.allIntervalRegionValueMap.get(selectedInterval).longValue() != tuplesPerIntervalCovered
						.get(selectedInterval).longValue()) {

					throw new RuntimeException("Interval values covered should match");

				}

				intervalToDFVectorMap.remove(selectedInterval);

				continue;

			}

			// handle things at region level
			// remove things from other area
			// do the things in much better way
			// take care of region cardinality
			// remove CC cardinality accordingly as per reduction

			// Earlier grouping of regions
			// find overlapping nature of intervalised regions inside current interval

			int[][] overlappingRegionNature = new int[overlappingRegionsWithInterval
					.size()][overlappingRegionsWithInterval.size()];
			int mostIntersectingRegionIdx = findAllRegionsOverlappingNature(overlappingRegionsWithInterval, intervalIdx,
					overlappingRegionNature);

			String mostIntersectingRegion = overlappingRegionsWithInterval.get(mostIntersectingRegionIdx);

			// CCs intersecting with mostIntersectingRegion
			List<FormalCondition> mostIntersectingRegionCCs = regionToCCMap.get(mostIntersectingRegion);

			// Extracting regions that overlaps with the current set of CCs
			List<String> regionsToBeConsidered = new ArrayList<>();
			for (String regionname : overlappingRegionsWithInterval) {

				if (allTrueRegions.contains(regionname)) {
					continue;
				}
				List<FormalCondition> ccs = new ArrayList<>(regionToCCMap.get(regionname));

				HashSet<FormalCondition> ccsTempSet = new HashSet<>(ccs);
				ccsTempSet.removeAll(ignoreCondition);
				if (ccsTempSet.isEmpty()) {
					continue;
				}

				ccs.retainAll(mostIntersectingRegionCCs);
				if (!ccs.isEmpty()) {
					regionsToBeConsidered.add(regionname);
				}

			}

			List<DFvector> dfVectorList = new ArrayList<>();
			for (FormalCondition condition : mostIntersectingRegionCCs) {
				dfVectorList.add(conditionToDFMap.get(condition));
			}

			// topo seq number assigning
			Map<String, Set<String>> precedenceMap = new HashMap<>();
			Map<String, List<String>> edgeInfoMap = new HashMap<>();
			List<List<String>> topologicalWay = topoSeqAss(regionsToBeConsidered, mostIntersectingRegionCCs,
					regionToCCMap, dfVectorList, precedenceMap, mostIntersectingRegion, edgeInfoMap);

			Map<String, Set<String>> revPrecedenceMap = getRevPrecedenceMap(precedenceMap);

			List<Long> appropriateDF = new ArrayList<>();
			Map<Set<FormalCondition>, Long> fAssignedToCCListMap = new HashMap<>();

			Map<String, List<Long>> regToAppDF = new HashMap<>();
			// findAppropriateDF(appropriateDF , dfVectorList , maxd, maxf);
			boolean distributionType = newFindAppDF(mostIntersectingRegion, revPrecedenceMap, maxd, maxf,
					conditionToDFMap, regionToCCMap, cCToRegionMap, edgeInfoMap, fAssignedToCCListMap, regToAppDF,
					ignoreCondition, intervalAllTrueRegionList, tuplesPerRegionCovered);

			DFvector dfvectorRemovedFromInterval = new DFvector(new ArrayList<>(), new ArrayList<>());

			newDistributeDFWithPK(regToAppDF, pkValBoundaryList, distributionType, intervalIdx,
					dfvectorRemovedFromInterval, intervalIdxMap);
			/*
			 * Map<String, DFvector> regionDFAssignedMap = newDistributeDF(appropriateDF,
			 * dfVectorList, maxd, maxf,mostIntersectingRegionCCs,regionToCCMap,
			 * topologicalWay, precedenceMap, futurePkValDFToAdd, pkValBoundaryList,
			 * mostIntersectingRegion, revPrecedenceMap,
			 * edgeInfoMap,conditionToDFMap,dfvectorRemovedFromInterval);
			 * 
			 * 
			 * // Number of tuples covered in region tracker also need to be made // and
			 * also one time ordering inside each region can also be done
			 * deductFromCCs(regionDFAssignedMap, conditionToDFMap, regionToCCMap);
			 */

			newDeductFromCCs(regToAppDF, conditionToDFMap, regionToCCMap, distributionType, ignoreCondition);

			// Once we know overlapping nature
			// Call findApprox
			// Then deduct from interval region and CC
			// and process continues

			// Assign appD,appF to current region
			// and other regions overlapping with it distribute rest of the regions

			// distributeDF(appropriateDF, dfVectorList, maxd, maxf,
			// overlappingRegionNature, overlappingRegionsWithInterval,
			// futurePkValDFToAdd,mostIntersectingRegionIdx,pkValBoundaryList,regionToCCMap);

			// removal from intervalTODfVector
			DFvector intervalDFvector = intervalToDFVectorMap.get(selectedInterval);
			if (dfvectorRemovedFromInterval != null && dfvectorRemovedFromInterval.getD().get(0) > 0) {
				intervalDFvector.removeDF(dfvectorRemovedFromInterval);
				Long dVal = dfvectorRemovedFromInterval.getD().get(0);
				Long fVal = dfvectorRemovedFromInterval.getF().get(0);
				tuplesPerIntervalCovered.put(selectedInterval,
						dVal.longValue() * fVal.longValue() + tuplesPerIntervalCovered.get(selectedInterval));
				if (this.allIntervalRegionValueMap.get(selectedInterval).longValue() == tuplesPerIntervalCovered
						.get(selectedInterval).longValue()) {
					intervalToDFVectorMap.remove(selectedInterval);
				}

			} else {

				continue;
			}

		}

		leftOverDF(futurePkValDFToAdd, pkValBoundaryList, tuplesPerIntervalCovered, tuplesPerRegionCovered,
				orderedRegions, allTrueRegions);

	}

	private void leftOverDF(Map<Integer, Map<DFvector, List<Long>>> futurePkValDFToAdd, List<Long> pkValBoundaryList,
			Map<String, Long> tuplesPerIntervalCovered, Map<String, Long> tuplesPerRegionCovered,
			List<String> orderedRegions, List<String> allTrueRegions) {

		for (Integer intervalIdx : futurePkValDFToAdd.keySet()) {

			// extracting regions of current interval
			List<String> leftRegionsList = new ArrayList<>();
			for (String region : tuplesPerRegionCovered.keySet()) {

				if (tuplesPerRegionCovered.get(region) > this.allIntervalisedRegionsMap.get(region)) {
					leftRegionsList.add(region);
				} else if (tuplesPerRegionCovered.get(region) > this.allIntervalisedRegionsMap.get(region)) {
					throw new RuntimeException("More tuples assigned to the region");
				}

			}

			for (DFvector dfvector : futurePkValDFToAdd.get(intervalIdx).keySet()) {

				while (true) {
					String currentRegion = leftRegionsList.get(0);
					long appD = dfvector.getD().get(0);
					long appF = dfvector.getF().get(0);
					long toBeAddedTuples = appD * appF;
					long totalTuplesCount = this.allIntervalisedRegionsMap.get(currentRegion);
					long tuplesCoveredCount = tuplesPerRegionCovered.get(currentRegion);
					long leftTuples = totalTuplesCount - tuplesCoveredCount;

					if (leftTuples >= toBeAddedTuples) {
						assignFKVal(currentRegion, appD, appF, pkValBoundaryList);
					} else {

						if (leftTuples > appD) {

							long newf = leftTuples / appD;
							assignFKVal(currentRegion, appD, newf, pkValBoundaryList);

						} else {
							// assign left over f values

						}

					}

					// if region tuples

				}

			}

		}

	}

	private void newDeductFromCCs(Map<String, List<Long>> regToAppDF, Map<FormalCondition, DFvector> conditionToDFMap,
			Map<String, List<FormalCondition>> regionToCCMap, boolean distributionType,
			List<FormalCondition> ignoreCondition) {

		Map<FormalCondition, DFvector> dfToCCAllocatedMap = new HashMap<>();
		/*
		 * distributionType yes : fdistribution no : dDistribution
		 */

		for (String reg : regToAppDF.keySet()) {
			List<Long> appropriateDF = regToAppDF.get(reg);

			List<FormalCondition> ccList = regionToCCMap.get(reg);
			for (FormalCondition cc : ccList) {

				if (ignoreCondition.contains(cc)) {
					continue;
				}

				long appD = appropriateDF.get(0).longValue();
				long appF = appropriateDF.get(1).longValue();
				List<Long> dValues = new ArrayList<>();
				List<Long> fValues = new ArrayList<>();
				dValues.add(appD);
				fValues.add(appF);
				DFvector dfVector = new DFvector(dValues, fValues);
				if (!dfToCCAllocatedMap.containsKey(cc)) {
					dfToCCAllocatedMap.put(cc, dfVector);
				} else {
					DFvector dfVec = dfToCCAllocatedMap.get(cc);
					for (int i = 0; i < dfVec.getD().size(); i++) {

						if (distributionType && dfVec.getD().get(i) == appD) {
							dfVec.getF().set(i, dfVec.getF().get(i) + appF);

						} else if (!distributionType && dfVec.getF().get(i) == appF) {
							dfVec.getD().set(i, dfVec.getD().get(i) + appD);
						} else {
							// Some problem in dividing the d,f in other regions
							throw new RuntimeException("Not expecting this.");
						}

					}
				}

			}

		}

		// remove from conditionToDF
		for (FormalCondition currentCC : dfToCCAllocatedMap.keySet()) {

			DFvector dfVector = conditionToDFMap.get(currentCC);
			dfVector.removeDF(dfToCCAllocatedMap.get(currentCC));
			if (dfVector.isEmpty()) {
				dfToCCAllocatedMap.remove(currentCC);
			}

		}
		System.out.print("");

	}

	private DFvector newDistributeDFWithPK(Map<String, List<Long>> regToAppDF, List<Long> pkValBoundaryList,
			boolean distributionType, int intervalIdx, DFvector dfvectorRemovedFromInterval,
			Map<Integer, Integer> intervalIdxMap) {

		// true means f divide
		// false means d divide
		List<Long> dValues = dfvectorRemovedFromInterval.getD();
		List<Long> fValues = dfvectorRemovedFromInterval.getF();
		if (distributionType) {

			long fixedF = -1;
			long fixedAppD = -1;
			Long sumf = 0L;
			for (String reg : regToAppDF.keySet()) {

				Long appD = regToAppDF.get(reg).get(0);
				Long appF = regToAppDF.get(reg).get(1);
				fixedF = appF.longValue();
				sumf += appF.longValue();
				fixedAppD = appD;
				assignFKVal(reg, appD, appF, pkValBoundaryList);
			}

			pkValBoundaryList.set(intervalIdxMap.get(intervalIdx),
					pkValBoundaryList.get(intervalIdxMap.get(intervalIdx)) + fixedF);
			dValues.add(fixedAppD);
			fValues.add(sumf);

		} else {

			Long sumD = 0L;
			Long fixedF = 0L;
			for (String reg : regToAppDF.keySet()) {

				Long appD = regToAppDF.get(reg).get(0);
				Long appF = regToAppDF.get(reg).get(1);
				assignFKVal(reg, appD, appF, pkValBoundaryList);
				pkValBoundaryList.set(intervalIdxMap.get(intervalIdx),
						pkValBoundaryList.get(intervalIdxMap.get(intervalIdx)) + appF);
				sumD += appD.longValue();
				fixedF = appF.longValue();

			}
			dValues.add(sumD);
			fValues.add(fixedF);
		}

		DFvector dfVector = new DFvector(dValues, fValues);
		return dfVector;

	}

	private boolean newFindAppDF(String mostIntersectingRegion, Map<String, Set<String>> revPrecedenceMap, long maxd,
			long maxf, Map<FormalCondition, DFvector> conditionToDFMap,
			Map<String, List<FormalCondition>> regionToCCMap, Map<FormalCondition, List<String>> cCToRegionMap,
			Map<String, List<String>> edgeInfoMap, Map<Set<FormalCondition>, Long> fAssignedToCCListMap,
			Map<String, List<Long>> regToAppDF, List<FormalCondition> ignoreCondition,
			List<String> intervalAllTrueRegionList, Map<String, Long> tuplesPerRegionCovered) {

		// Predetermined df values for all regions
		System.out.println("");
		List<Long> globalAppF = new ArrayList<>();
		globalAppF.add(0L);
		// Map<String,List<Long>> regToAppDF = new HashMap<>();

		boolean dType = recursiveFunction(mostIntersectingRegion, edgeInfoMap, maxd, maxf, conditionToDFMap,
				regionToCCMap, globalAppF, regToAppDF, fAssignedToCCListMap, ignoreCondition, tuplesPerRegionCovered);

		List<Long> dfVals = regToAppDF.get(mostIntersectingRegion);

		if (!intervalAllTrueRegionList.isEmpty()) {
			if (dfVals.get(0) < maxd) {
				// tuplecount check left
				List<Long> allTrueDF = new ArrayList<>();
				allTrueDF.add(maxd - dfVals.get(0));
				allTrueDF.add(dfVals.get(1));
				regToAppDF.put(intervalAllTrueRegionList.get(0), allTrueDF);
			}

		}

		// for tuples covered by region

		// Also need to add somewhere down below the where tuple check is done before
		// assigning

		for (String region : regToAppDF.keySet()) {
			long d = regToAppDF.get(region).get(0);
			long f = regToAppDF.get(region).get(1);
			if ((tuplesPerRegionCovered.get(region) + d * f) < this.allIntervalisedRegionsMap.get(region)) {
				tuplesPerRegionCovered.put(region, d * f);
			} else {

				long leftTuples = this.allIntervalisedRegionsMap.get(region)
						- (tuplesPerRegionCovered.get(region) + d * f);
				if (leftTuples > maxd) {
					long newf = leftTuples / maxd;
					regToAppDF.get(region).set(1, newf);
					tuplesPerRegionCovered.put(region, d * newf);
				} else {
					// remove the entry from that region and also from other respective areas
					regToAppDF.remove(region);
					// maybe needed to remove data from other places as well just have a look
				}

			}

		}

		System.out.print("");

		return dType;

	}

	private boolean recursiveFunction(String mostIntersectingRegion, Map<String, List<String>> edgeInfoMap, long maxd,
			long maxf, Map<FormalCondition, DFvector> conditionToDFMap,
			Map<String, List<FormalCondition>> regionToCCMap, List<Long> globalAppF, Map<String, List<Long>> regToAppDF,
			Map<Set<FormalCondition>, Long> fAssignedToCCListMap, List<FormalCondition> ignoreCondition,
			Map<String, Long> tuplesPerRegionCovered) {

		List<FormalCondition> mostIntersectingRegionCCs = regionToCCMap.get(mostIntersectingRegion);

		List<DFvector> dfVectorList = new ArrayList<>();
		for (FormalCondition condition : mostIntersectingRegionCCs) {
			dfVectorList.add(conditionToDFMap.get(condition));
		}

		List<Long> appropriateDF = new ArrayList<>();
		findAppropriateDF(appropriateDF, dfVectorList, maxd, maxf);
		if (maxd == appropriateDF.get(0).longValue()) {
			recursiveFunctionForF(mostIntersectingRegion, edgeInfoMap, maxd, maxf, conditionToDFMap, regionToCCMap,
					globalAppF, regToAppDF, fAssignedToCCListMap, ignoreCondition, tuplesPerRegionCovered);
			return true;
		} else if (maxd > appropriateDF.get(0).longValue()) {
			recursiveFunctionForD(mostIntersectingRegion, edgeInfoMap, maxd, maxf, conditionToDFMap, regionToCCMap,
					globalAppF, regToAppDF, fAssignedToCCListMap, ignoreCondition, tuplesPerRegionCovered);
			return false;
		} else {
			throw new RuntimeException("No hopes just distribute it");
		}

	}

	private void recursiveFunctionForD(String mostIntersectingRegion, Map<String, List<String>> edgeInfoMap, long maxd,
			long maxf, Map<FormalCondition, DFvector> conditionToDFMap,
			Map<String, List<FormalCondition>> regionToCCMap, List<Long> globalAppD, Map<String, List<Long>> regToAppDF,
			Map<Set<FormalCondition>, Long> dAssignedToCCListMap, List<FormalCondition> ignoreCondition,
			Map<String, Long> tuplesPerRegionCovered) {

		// Modify it for d value version
		List<FormalCondition> mostIntersectingRegionCCs = regionToCCMap.get(mostIntersectingRegion);

		List<DFvector> dfVectorList = new ArrayList<>();
		for (FormalCondition condition : mostIntersectingRegionCCs) {
			if (ignoreCondition.contains(condition)) {
				continue;
			}
			dfVectorList.add(conditionToDFMap.get(condition));
		}
		List<Long> appropriateDF = new ArrayList<>();
		findAppropriateDF(appropriateDF, dfVectorList, maxd, maxf);
		long currentTupleCount = tuplesPerRegionCovered.get(mostIntersectingRegion);
		long tupleToBeAdded = appropriateDF.get(0) * appropriateDF.get(1);
		long leftTuples = allIntervalisedRegionsMap.get(mostIntersectingRegion) - currentTupleCount;
		if (tupleToBeAdded > leftTuples) {

			if (appropriateDF.get(0) > leftTuples) {
				long newD = leftTuples / appropriateDF.get(0);
				appropriateDF.set(1, newD);

			} else {
				appropriateDF.set(1, 0L);
			}

		}
		// Set<FormalCondition> ccs = new HashSet<>(mostIntersectingRegionCCs);
		for (Set<FormalCondition> ccSet : dAssignedToCCListMap.keySet()) {
			Set<FormalCondition> ccs = new HashSet<>(mostIntersectingRegionCCs);
			ccs.removeAll(ccSet);
			if (ccs.isEmpty()) {
				// ccs fully subsumed in ccSet
				appropriateDF.set(0, appropriateDF.get(0) - dAssignedToCCListMap.get(ccSet));

			} else {
				// assign all appD, appF
			}
		}

		if (appropriateDF.get(0) > 0) {
			globalAppD.set(0, globalAppD.get(0) + appropriateDF.get(1));
			regToAppDF.put(mostIntersectingRegion, appropriateDF);
			Set<FormalCondition> ccs = new HashSet<>(mostIntersectingRegionCCs);
			dAssignedToCCListMap.put(ccs, appropriateDF.get(1));
		}

		if (edgeInfoMap.containsKey(mostIntersectingRegion)) {
			List<String> associatedRegs = edgeInfoMap.get(mostIntersectingRegion);
			for (String reg : associatedRegs) {
				maxf = maxf - globalAppD.get(0);
				recursiveFunctionForD(reg, edgeInfoMap, maxd, maxf, conditionToDFMap, regionToCCMap, globalAppD,
						regToAppDF, dAssignedToCCListMap, ignoreCondition, tuplesPerRegionCovered);
			}
		}

	}

	private void recursiveFunctionForF(String mostIntersectingRegion, Map<String, List<String>> edgeInfoMap, long maxd,
			long maxf, Map<FormalCondition, DFvector> conditionToDFMap,
			Map<String, List<FormalCondition>> regionToCCMap, List<Long> globalAppF, Map<String, List<Long>> regToAppDF,
			Map<Set<FormalCondition>, Long> fAssignedToCCListMap, List<FormalCondition> ignoreCondition,
			Map<String, Long> tuplesPerRegionCovered) {

		List<FormalCondition> mostIntersectingRegionCCs = regionToCCMap.get(mostIntersectingRegion);

		List<DFvector> dfVectorList = new ArrayList<>();
		for (FormalCondition condition : mostIntersectingRegionCCs) {
			if (ignoreCondition.contains(condition)) {
				continue;
			}
			dfVectorList.add(conditionToDFMap.get(condition));
		}

		List<Long> appropriateDF = new ArrayList<>();
		findAppropriateDF(appropriateDF, dfVectorList, maxd, maxf);
		long currentTupleCount = tuplesPerRegionCovered.get(mostIntersectingRegion);
		long tupleToBeAdded = appropriateDF.get(0) * appropriateDF.get(1);
		long leftTuples = allIntervalisedRegionsMap.get(mostIntersectingRegion) - currentTupleCount;
		if (tupleToBeAdded > leftTuples) {

			if (appropriateDF.get(0) > leftTuples) {
				long newD = leftTuples / appropriateDF.get(0);
				appropriateDF.set(1, newD);

			} else {
				appropriateDF.set(1, 0L);
			}

		}

		// Set<FormalCondition> ccs = new HashSet<>(mostIntersectingRegionCCs);
		for (Set<FormalCondition> ccSet : fAssignedToCCListMap.keySet()) {
			Set<FormalCondition> ccs = new HashSet<>(mostIntersectingRegionCCs);
			ccs.removeAll(ccSet);
			if (ccs.isEmpty()) {
				// ccs fully subsumed in ccSet
				appropriateDF.set(1, appropriateDF.get(1) - fAssignedToCCListMap.get(ccSet));

			} else {
				// assign all appD, appF

			}
		}

		if (appropriateDF.get(1) > 0) {
			globalAppF.set(0, globalAppF.get(0) + appropriateDF.get(1));
			regToAppDF.put(mostIntersectingRegion, appropriateDF);
			Set<FormalCondition> ccs = new HashSet<>(mostIntersectingRegionCCs);
			fAssignedToCCListMap.put(ccs, appropriateDF.get(1));
		}

		if (edgeInfoMap.containsKey(mostIntersectingRegion)) {
			List<String> associatedRegs = edgeInfoMap.get(mostIntersectingRegion);
			for (String reg : associatedRegs) {
				maxf = maxf - globalAppF.get(0);
				recursiveFunctionForF(reg, edgeInfoMap, maxd, maxf, conditionToDFMap, regionToCCMap, globalAppF,
						regToAppDF, fAssignedToCCListMap, ignoreCondition, tuplesPerRegionCovered);
			}
		}

	}

	private DFvector deductFromCCs(Map<String, DFvector> regionDFAssignedMap,
			Map<FormalCondition, DFvector> conditionToDFMap, Map<String, List<FormalCondition>> regionToCCMap) {

		Map<FormalCondition, DFvector> dfToCCAllocatedMap = new HashMap<>();

		for (String reg : regionDFAssignedMap.keySet()) {
			DFvector dfVector = regionDFAssignedMap.get(reg);
			long appD = dfVector.getD().get(0);
			long appF = dfVector.getF().get(0);

			List<FormalCondition> ccList = regionToCCMap.get(reg);
			for (FormalCondition cc : ccList) {

				if (!dfToCCAllocatedMap.containsKey(cc)) {
					dfToCCAllocatedMap.put(cc, dfVector);
				} else {
					DFvector dfVec = dfToCCAllocatedMap.get(cc);
					for (int i = 0; i < dfVec.getD().size(); i++) {

						if (dfVec.getD().get(i) == appD) {
							dfVec.getF().set(i, dfVec.getF().get(i) + appF);

						} else {
							// Some problem in dividing the d,f in other regions
							throw new RuntimeException("Not expecting this.");
						}

					}
				}

			}

		}

		// remove from conditionToDF
		for (FormalCondition currentCC : dfToCCAllocatedMap.keySet()) {

			DFvector dfVector = conditionToDFMap.get(currentCC);
			dfVector.removeDF(dfToCCAllocatedMap.get(currentCC));
			if (dfVector.isEmpty()) {
				dfToCCAllocatedMap.remove(currentCC);
			}

		}
		System.out.print("");
		return null;

	}

	private Map<String, Set<String>> getRevPrecedenceMap(Map<String, Set<String>> precedenceMap) {
		// TODO Auto-generated method stub
		Map<String, Set<String>> revPrecedenceMap = new HashMap<>();
		for (String key : precedenceMap.keySet()) {

			for (String reg : precedenceMap.get(key)) {

				if (!revPrecedenceMap.containsKey(reg)) {
					revPrecedenceMap.put(reg, new HashSet<>());
				}
				revPrecedenceMap.get(reg).add(key);

			}
		}

		return revPrecedenceMap;
	}

	private List<List<String>> topoSeqAss(List<String> regionsToBeConsidered,
			List<FormalCondition> mostIntersectingRegionCCs, Map<String, List<FormalCondition>> regionToCCMap,
			List<DFvector> dfVectorList, Map<String, Set<String>> precedenceMap, String mostIntersectingRegion,
			Map<String, List<String>> edgeInfoMap) {

		// Only those regions which have common CCs
		/*
		 * Topological ordering index number indicates number of CCs matched
		 */

		List<List<String>> topologicalWay = new ArrayList<>();

		for (int i = 0; i < mostIntersectingRegionCCs.size(); i++) {
			topologicalWay.add(new ArrayList<>());
		}

		for (String regionname : regionsToBeConsidered) {

			List<FormalCondition> ccs = new ArrayList<>(regionToCCMap.get(regionname));
			ccs.retainAll(mostIntersectingRegionCCs);

			if (ccs.size() <= 0 || ccs.size() > mostIntersectingRegionCCs.size()) {
				throw new RuntimeException("Unexpected point");
			}

			topologicalWay.get(ccs.size() - 1).add(regionname);

		}

		// Now defining edges between the nodes of toplogicalWay
		// using precedence map
		for (int i = topologicalWay.size() - 1; i >= 0; i--) {

			for (int j = 0; j < topologicalWay.get(i).size(); j++) {

				String currentReg = topologicalWay.get(i).get(j);
				List<FormalCondition> currentRegCCs = new ArrayList<>(regionToCCMap.get(currentReg));
				currentRegCCs.retainAll(mostIntersectingRegionCCs);

				Set<String> regionsList = new HashSet<>();

				for (int k = i + 1; k < topologicalWay.size(); k++) {

					for (int l = 0; l < topologicalWay.get(k).size(); l++) {
						String otherReg = topologicalWay.get(k).get(l);
						List<FormalCondition> otherRegCCs = new ArrayList<>(regionToCCMap.get(otherReg));
						otherRegCCs.retainAll(mostIntersectingRegionCCs);

						currentRegCCs.retainAll(otherRegCCs);
						// if CCs intersects then it will be non empty
						if (!currentRegCCs.isEmpty()) {
							regionsList.add(otherReg);
						}

					}

				}

				precedenceMap.put(currentReg, regionsList);

			}

		}

		// create new map and remove transitive edges
		for (int i = topologicalWay.size() - 2; i >= 0; i--) {

			for (int j = 0; j < topologicalWay.get(i).size(); j++) {

				String currentReg = topologicalWay.get(i).get(j);
				if (i + 1 <= topologicalWay.size() - 1) {

					for (int k = 0; k < topologicalWay.get(i + 1).size(); k++) {

						if (precedenceMap.get(currentReg).contains(topologicalWay.get(i + 1).get(k))) {
							if (!edgeInfoMap.containsKey(topologicalWay.get(i + 1).get(k))) {
								edgeInfoMap.put(topologicalWay.get(i + 1).get(k), new ArrayList<>());
							}
							edgeInfoMap.get(topologicalWay.get(i + 1).get(k)).add(currentReg);
						}

					}
				}
			}
		}

		return topologicalWay;

	}

	private Map<String, DFvector> newDistributeDF(List<Long> appropriateDF, List<DFvector> dfVectorList, long maxd,
			long maxf, List<FormalCondition> mostIntersectingRegionCCs,
			Map<String, List<FormalCondition>> regionToCCMap, List<List<String>> topologicalWay,
			Map<String, Set<String>> precedenceMap, Map<Integer, Map<DFvector, List<Long>>> futurePkValDFToAdd,
			List<Long> pkValBoundaryList, String mostIntersectingRegion, Map<String, Set<String>> revPrecedenceMap,
			Map<String, List<String>> edgeInfoMap, Map<FormalCondition, DFvector> conditionToDFMap,
			DFvector dfvectorRemovedFromInterval) {

		//
		Map<String, DFvector> regionDFAssignedMap = new HashMap<>();

		Long appD = appropriateDF.get(0);
		Long appF = appropriateDF.get(1);

		// assigns df to current region
		assignFKVal(mostIntersectingRegion, appD, appF, pkValBoundaryList);

		List<Long> dValue = new ArrayList<>();
		dValue.add(appD);
		List<Long> fValue = new ArrayList<>();
		fValue.add(appF);
		regionDFAssignedMap.put(mostIntersectingRegion, new DFvector(dValue, fValue));

		// create diff ordered list to be used one by one for
		// left over data
		// creating this list

		// assign leftover appropriateDF values
		List<String> regionsCovered = new ArrayList<>();
		regionsCovered.add(mostIntersectingRegion);

		// Different cases
		// if appD == maxD then all good
		// no need to do anything and continue the
		// if appD < maxD,then remaining D needs to be added

		if (appD == maxd) {

			// No need of extra addition of D
			List<Long> tempDValues = dfvectorRemovedFromInterval.getD();
			tempDValues.add(appD);
			List<Long> tempFValues = dfvectorRemovedFromInterval.getF();
			tempFValues.add(appF);

			System.out.print("");

		} else if (appD < maxd) {

			long leftD = maxd - appD;

			List<String> currentList = new ArrayList<>();
			currentList.add(mostIntersectingRegion);

			// Used stack for dfs traversal
			Stack<String> regionStack = new Stack<>();

			regionStack.add(mostIntersectingRegion);
			while (!regionStack.isEmpty()) {

				// distribute among the current list
				String currentTop = regionStack.peek();
				regionStack.pop();
				if (edgeInfoMap.containsKey(currentTop)) {
					List<String> associatedRegions = edgeInfoMap.get(currentTop);

					for (String reg : associatedRegions) {

						List<FormalCondition> ccsList = regionToCCMap.get(reg);
						ccsList.retainAll(mostIntersectingRegionCCs);
						List<DFvector> newDfVectorList = new ArrayList<>();
						for (FormalCondition condition : ccsList) {
							newDfVectorList.add(conditionToDFMap.get(condition));
						}
						List<Long> appropriateDFnew = new ArrayList<>();
						// need to create modified findAppropriateDF
						// which finds the closest to required d value
						// newD = maxD-appD
						// recursive

						// find best d values that can be used
						// may require some changes
						allocateAppropriateDF(appropriateDFnew, conditionToDFMap, leftD, appF, appD, reg, edgeInfoMap,
								regionToCCMap);

					}

					// Add regions on the basis of closest to appD
					regionStack.addAll(associatedRegions);
				}

				// Maximum allocation possible f value

				assignFKVal(currentTop, appD, appF, pkValBoundaryList);

			}

		} else {

		}

		// Traverse all regions one by one and add CCs and
		// distribution

		return regionDFAssignedMap;

	}

	private void allocateAppropriateDF(List<Long> appropriateDFnew, Map<FormalCondition, DFvector> conditionToDFMap,
			long leftD, Long appF, Long appD, String reg, Map<String, List<String>> edgeInfoMap,
			Map<String, List<FormalCondition>> regionToCCMap) {

		List<FormalCondition> ccList = regionToCCMap.get(reg);

		// now create CC sets which

	}

	private void findAppropriateDF(List<Long> appropriateDF, List<DFvector> dfVectorList, long leftD, Long maxf,
			Long appD, String reg, Map<String, List<String>> edgeInfoMap,
			Map<String, List<FormalCondition>> regionToCCMap) {

		// find appropriateDF

		// find maxd available
		boolean flag = false;
		for (int i = 0; i < dfVectorList.size(); i++) {

			List<Long> dList = dfVectorList.get(i).getD();

			if (dList.get(0) - appD >= leftD) {
				flag = true;
			}

		}
		if (!flag) {
			appropriateDF.add((long) -1);
			appropriateDF.add((long) -1);
			// Don't assign -1, Assign best possible value and leave rest for the future.
			// Best possible value from
			findAppropriateDF(appropriateDF, dfVectorList, leftD, maxf);

		} else {

			Long appropriateD = null;
			for (int i = 0; i < dfVectorList.size(); i++) {

				if (appropriateD == null) {

					appropriateD = dfVectorList.get(i).getD().get(0);

				} else {

					if (appropriateD > dfVectorList.get(i).getD().get(0)) {
						appropriateD = dfVectorList.get(i).getD().get(0);
					}

				}

			}

			Long appropriateF = null;
			for (int i = 0; i < dfVectorList.size(); i++) {
				List<Long> dValues = dfVectorList.get(i).getD();
				List<Long> fValues = dfVectorList.get(i).getF();
				Long sumf = 0L;
				for (int di = 0; di < dValues.size(); di++) {

					if (dValues.get(di) < appropriateD) {
						break;
					} else {

						sumf += fValues.get(di);
					}

				}
				if (appropriateF == null) {
					appropriateF = sumf;
				} else {

					if (appropriateF > sumf) {
						sumf = appropriateF;
					}

				}

			}

			if (appropriateF > maxf) {
				appropriateF = maxf;
			}

			appropriateDF.add(appropriateD);
			appropriateDF.add(appropriateF);

		}

	}

	private void distributeDF(List<Long> appropriateDF, List<DFvector> dfVectorList, long maxd, long maxf,
			int[][] overlappingRegionNature, List<String> overlappingRegionsWithInterval,
			Map<Integer, Map<DFvector, List<Long>>> futurePkValDFToAdd, int mostIntersectingRegionIdx,
			List<Long> pkValBoundaryList, Map<String, List<FormalCondition>> regionToCCMap) {

		// Give appD,appF to region
		// and remaining to leftover
		// varPKValDistribution
		// futurePkValDFToAdd

		// Assigns arbitrary FK value

		Long appD = appropriateDF.get(0);
		Long appF = appropriateDF.get(1);

		String mostIntersectingRegion = overlappingRegionsWithInterval.get(mostIntersectingRegionIdx);

		// assigns df to current region
		assignFKVal(mostIntersectingRegion, appD, appF, pkValBoundaryList);

		// now its time for other regions
		long leftd = maxd - appD;

		// f value would be appf only

		otherRegionsInInterval(leftd, appF, pkValBoundaryList, overlappingRegionsWithInterval,
				mostIntersectingRegionIdx, overlappingRegionNature, futurePkValDFToAdd, dfVectorList, regionToCCMap);

		// Deduct the DC after deduction

	}

	private void otherRegionsInInterval(long leftd, Long appF, List<Long> pkValBoundaryList,
			List<String> overlappingRegionsWithInterval, int mostIntersectingRegionIdx, int[][] overlappingRegionNature,
			Map<Integer, Map<DFvector, List<Long>>> futurePkValDFToAdd, List<DFvector> dfVectorList,
			Map<String, List<FormalCondition>> regionToCCMap) {

		/*
		 * 2 : Region 2 subsumes Region 1 3 : Partially overlaps
		 */

		List<Integer> subsumingRegionsIdx = new ArrayList<>();
		List<Integer> partiallyRegionsIdx = new ArrayList<>();

		for (int i = 0; i < overlappingRegionNature.length; i++) {

			String regionname = overlappingRegionsWithInterval.get(i);

			List<FormalCondition> overlappingCCsWithCurrentRegion = regionToCCMap.get(regionname);
			List<FormalCondition> conditionList = regionToCCMap.get(overlappingRegionsWithInterval.get(i));
			overlappingCCsWithCurrentRegion.retainAll(conditionList);

			// removes those regions whose CCs don't overlap with current set of CCs
			if (!overlappingCCsWithCurrentRegion.isEmpty()) {
				continue;
			}

			if (i != mostIntersectingRegionIdx) {

				if (overlappingRegionNature[mostIntersectingRegionIdx][i] == 2) {
					subsumingRegionsIdx.add(i);
				} else if (overlappingRegionNature[mostIntersectingRegionIdx][i] == 3) {
					partiallyRegionsIdx.add(i);
				}

			}

		}

		// sort subsuming regionIDx on the basis of number

		// Outer Loop that covers things
		List<Integer> coveredRegion = new ArrayList<>();
		while (true) {

			while (true) {

				for (int i = 0; i < subsumingRegionsIdx.size(); i++) {

				}

			}

		}

	}

	private void assignFKVal(String mostIntersectingRegion, Long appD, Long appF, List<Long> pkValBoundaryList) {
		// TODO Auto-generated method stub

		// t17_c018_var0_3_interval_1

		int intervalIdx = Integer.parseInt(mostIntersectingRegion.split("_interval_")[1]);

		if (!this.varPKValDistribution.containsKey(mostIntersectingRegion)) {

			this.varPKValDistribution.put(mostIntersectingRegion, new HashMap<>());

		}

		if (!this.varPKValDistribution.get(mostIntersectingRegion).containsKey(appD)) {
			this.varPKValDistribution.get(mostIntersectingRegion).put(appD, new ArrayList<>());
		}

		for (long i = 0; i < appF; i++) {

			this.varPKValDistribution.get(mostIntersectingRegion).get(appD).add(pkValBoundaryList.get(intervalIdx) + i);
		}

	}

	private int findAllRegionsOverlappingNature(List<String> overlappingRegionsWithInterval, int intervalIdx,
			int[][] overlappingRegionNature) {

		int mostOverlappingRegion = 0;
		int maxIntersectionCount = -1;
		for (int i = 0; i < overlappingRegionsWithInterval.size(); i++) {

			String regionName = overlappingRegionsWithInterval.get(i);
			int intersectionCount = 0;
			for (int j = i + 1; j < overlappingRegionsWithInterval.size(); j++) {
				String otherRegionName = overlappingRegionsWithInterval.get(j);
				int val = findOverlappingNature(regionName, otherRegionName, intervalIdx);
				overlappingRegionNature[i][j] = val;
				overlappingRegionNature[j][i] = val;
				if (val == 1 || val == 0 || val == 3) {
					intersectionCount++;
				}

			}
			if (maxIntersectionCount < intersectionCount) {
				maxIntersectionCount = intersectionCount;
				mostOverlappingRegion = i;
			}
		}
		return mostOverlappingRegion;

	}

	private int findOverlappingNature(String regionName, String otherRegionName, int intervalIdx) {

		// Both regions will always be in same clique as they belongs to same fkey
		int cliqueIdx = Integer.parseInt(regionName.split("var")[1].split("_")[0]);
		List<String> sortedCliqueColumns = new ArrayList<>(this.arasuCliques.get(cliqueIdx));
		Collections.sort(sortedCliqueColumns);

		Region region1 = this.intervalisedRegionMap.get(regionName);
		Region region2 = this.intervalisedRegionMap.get(otherRegionName);

		Region modifiedRegion1 = new Region();
		Region modifiedRegion2 = new Region();

		for (BucketStructure bs : region1.getAll()) {
			BucketStructure newBs = new BucketStructure();
			int c = 0;
			for (Bucket b : bs.getAll()) {
				String currentCol = this.sortedViewColumns.get(c);
				if (sortedCliqueColumns.contains(currentCol)) {
					newBs.add(b);
				}
				c++;
			}
			modifiedRegion1.add(newBs);
		}

		for (BucketStructure bs : region2.getAll()) {
			BucketStructure newBs = new BucketStructure();
			int c = 0;
			for (Bucket b : bs.getAll()) {
				String currentCol = this.sortedViewColumns.get(c);
				if (sortedCliqueColumns.contains(currentCol)) {
					newBs.add(b);
				}
				c++;
			}

			modifiedRegion2.add(newBs);
		}

		// check for overlapping nature for the non-attributes,
		// since borrowed attributes are same and lies in same interval.
		// Whole region can also be passed

		/*
		 * -1 : non-intersecting 0 : fully intersecting 1 : Region 1 subsumes Region 2 2
		 * : Region 2 subsumes Region 1 3 : Partially overlaps
		 */

		Region minus1 = modifiedRegion1.minus(modifiedRegion2);
		Region minus2 = modifiedRegion2.minus(modifiedRegion1);

		if (minus1.isEmpty() && minus2.isEmpty()) {
			// either no intersection or fully overlap
			Region intersectingRegion = modifiedRegion1.intersection(modifiedRegion2);
			if (intersectingRegion.isEmpty()) {
				// no intersection
				return -1;
			} else {
				// fully intersecting
				return 0;

			}
		} else if (minus1.isEmpty()) {
			// Region2 is bigger and overlaps with region1
			return 2;
		} else if (minus2.isEmpty()) {
			// Region2 is bigger and overlaps with region1
			return 1;
		} else {
			// Both regions partially overlaps each other
			return 3;
		}

	}

	private void solveDFPerFK(List<String> orderedRegions, Map<String, List<FormalCondition>> regionToCCMap,
			Map<FormalCondition, List<String>> cCToRegionMap, String fkey, int cliqueIdx, int allTrueRegionIdx) {

		// IntervalBoundaries
		List<Long> pkValBoundaryList = new ArrayList<>();
		Map<Integer, Integer> intervalIdxMap = new HashMap<>();
		Long sumx = 0L;
		pkValBoundaryList.add(sumx);
		for (int i = 0; i < this.fkeyToIntervalRegionMap.get(fkey).size(); i++) {
			// t17_c018_clique0interval0
			intervalIdxMap.put(Integer.parseInt(this.fkeyToIntervalRegionMap.get(fkey).get(i).split("interval")[1]), i);

			sumx += this.relationCardinality;
			pkValBoundaryList.add(sumx);
		}

		HashMap<Integer, List<String>> intervalToRegions = new HashMap<>();
		for (String regionname : orderedRegions) {

			// t17_c018_var0_0_interval_1
			int intervalIdx = Integer.parseInt(regionname.split("_")[5]);
			if (!intervalToRegions.containsKey(intervalIdx)) {
				intervalToRegions.put(intervalIdx, new ArrayList<>());
			}
			intervalToRegions.get(intervalIdx).add(regionname);
		}

		Map<String, Set<String>> fkeyToBorrowedAttr = PostgresVConfig.fkeyToBorrowedAttr.get(viewname);
		Set<String> borrowedAttrs = fkeyToBorrowedAttr.get(fkey);

		if (borrowedAttrs.isEmpty()) {
			// System.out.print("NO need to manage fkey ");
			throw new RuntimeException("Can't possible to reach here");
		}

		List<String> sortedBorrowedAttr = new ArrayList<>(borrowedAttrs);
		Collections.sort(sortedBorrowedAttr);
		List<String> currentCliqueSorted = new ArrayList<>(this.arasuCliques.get(cliqueIdx));
		Collections.sort(currentCliqueSorted);

		Map<String, List<String>> varToIntervalisedRegionMap = this.varToIntervalisedRegionMapPerFkey.get(fkey);

		JSONArray dfJSONVector = PostgresVConfig.fkeySkewVectors.getJSONObject(viewname).getJSONArray(fkey);
		JSONArray d = dfJSONVector.getJSONArray(0);
		JSONArray f = dfJSONVector.getJSONArray(1);

		// Mapping each interval to dfvetor
		List<String> intervalRegionsList = this.fkeyToIntervalRegionMap.get(fkey);
		Map<String, DFvector> intervalToDFVectorMap = new HashMap<>();

		for (int i = 0; i < intervalRegionsList.size(); i++) {

			String intervalName = intervalRegionsList.get(i);
			int intervalIdx = Integer.parseInt(intervalName.split("interval")[1]);
			List<Long> dList = new ArrayList<>();
			List<Long> fList = new ArrayList<>();
			for (int j = 0; j < d.length(); j++) {
				// t17_c018_interval_0_d_1
				String dxVal = fkey + "_interval_" + intervalIdx + "_d_" + j;
				if (!this.allDxValuesMap.containsKey(dxVal)) {
					continue;
				}
				Long fval = this.allDxValuesMap.get(fkey + "_interval_" + intervalIdx + "_d_" + j);

				dList.add(d.getLong(j));
				fList.add(fval.longValue());
			}
			DFvector dfVec = new DFvector(dList, fList);
			intervalToDFVectorMap.put(intervalName, dfVec);

		}

		// Mapping each CC to dfVector
		Map<FormalCondition, DFvector> conditionToDFMap = new HashMap<>();
		Set<String> removedRegion = new HashSet<>();
		List<FormalCondition> removeList = new ArrayList<>();
		for (FormalCondition condition : cCToRegionMap.keySet()) {

			String actualFkeyName = PostgresVConfig.reverseColumnAnonyMap.get(fkey);
			Integer counter = condition.getCounter();
			String queryname = condition.getQueryname();
			String dfVecKey = actualFkeyName + "___" + counter + "_" + queryname;
			Map<String, DFvector> ccsDFvectors = PostgresVConfig.ccsDFvectors;
			if (ccsDFvectors.containsKey(dfVecKey)) {
				DFvector dfvector = ccsDFvectors.get(dfVecKey);
				DFvector dfvectorCopy = dfvector.copy();
				conditionToDFMap.put(condition, dfvectorCopy);
			} else {

				// remove that CC for now will add it later
				List<String> regionList = cCToRegionMap.get(condition);
				removedRegion.addAll(regionList);
				for (String region : regionList) {

					regionToCCMap.get(region).remove(condition);

				}

				removeList.add(condition);
			}

		}

		// removing CCs just because don't have df vector for it ..
		for (FormalCondition condition : removeList) {
			cCToRegionMap.remove(condition);
		}

		List<String> allTrueRegionList = varToIntervalisedRegionMap.get("var" + cliqueIdx + "_" + allTrueRegionIdx);

		// Interval -> [ [d][f] -> pkVal ]
		Map<Integer, Map<DFvector, List<Long>>> futurePkValDFToAdd = new HashMap<>();
		// Keeps track of tuplesCovered by each region
		Map<String, Long> tuplesPerRegionCovered = new HashMap<>();
		Map<String, Long> tuplesPerIntervalCovered = new HashMap<>();

		// Select maxd from set of intervals and and satisy that
		// and go on
		System.out.println("FKey going on " + fkey);
		Integer loop = 1;
		while (true) {

			loop += 1;

			long maxd = -1;
			long maxf = -1;
			String selectedInterval = null; // maxd interval
			if (intervalToDFVectorMap.isEmpty()) {
				break;
			}

			for (String interval : intervalToDFVectorMap.keySet()) {

				DFvector dfVector = intervalToDFVectorMap.get(interval);
				if (maxd < dfVector.getD().get(0)) {
					maxd = dfVector.getD().get(0);
					maxf = dfVector.getF().get(0);
					selectedInterval = interval;
				}

			}

			// t17_c018_clique0interval1
			int intervalIdx = Integer.parseInt(selectedInterval.split("interval")[1]);

			// all true region in current Interval
			List<String> intervalAllTrueRegionList = new ArrayList<>();

			if (intervalAllTrueRegionList.size() > 1) {
				throw new RuntimeException(" Was not expecting this ");
			}

			// intervalRemoved Region
			List<String> intervalRemovedRegionList = new ArrayList<>();
			for (String region : removedRegion) {

				if (intervalIdx == Integer.parseInt(region.split("interval_")[1])) {
					intervalRemovedRegionList.add(region);
				}

			}

			/*
			 * ------------ All True Region Covering ---------------
			 * 
			 */

			// intervalToRegions contains all left over region yet to finished
			// allTrue REgion check

			if (!intervalToRegions.containsKey(intervalIdx)) {

				// Either interval is finished
				// If all true region only left in that interval
				// once we are here we can completely cover whole interval

				// Pass it to future it will handle

				if (!futurePkValDFToAdd.containsKey(intervalIdx)) {
					futurePkValDFToAdd.put(intervalIdx, new HashMap<>());
				}

				if (!tuplesPerIntervalCovered.containsKey(selectedInterval)) {
					tuplesPerIntervalCovered.put(selectedInterval, 0L);
				}
				DFvector dfvector = intervalToDFVectorMap.get(selectedInterval);
				Long tupleSum = 0L;

				for (int di = 0; di < dfvector.size(); di++) {

					List<Long> dValues = new ArrayList<>();
					List<Long> fValues = new ArrayList<>();
					dValues.add(dfvector.getD().get(di));
					fValues.add(dfvector.getF().get(di));
					Long pkValStart = pkValBoundaryList.get(intervalIdxMap.get(intervalIdx));
					DFvector dfvec = new DFvector(dValues, fValues);

					if (!futurePkValDFToAdd.get(intervalIdx).containsKey(dfvec)) {
						futurePkValDFToAdd.get(intervalIdx).put(dfvec, new ArrayList<>());
					}
					futurePkValDFToAdd.get(intervalIdx).get(dfvec).add(pkValStart);
					pkValBoundaryList.set(intervalIdxMap.get(intervalIdx), pkValStart + dfvector.getF().get(di));
					tupleSum += dfvec.getD().get(0) * dfvec.getF().get(0);

				}

				tuplesPerIntervalCovered.put(selectedInterval,
						tuplesPerIntervalCovered.get(selectedInterval) + tupleSum);

				// introduce check stmt for boundary check
				if (this.allIntervalRegionValueMap.get(selectedInterval).longValue() != tuplesPerIntervalCovered
						.get(selectedInterval).longValue()) {

					throw new RuntimeException("Interval values covered should match");

				}

				intervalToDFVectorMap.remove(selectedInterval);

				continue;

			}

			// Now we have maxd and maxf
			// have

			List<String> overlappingRegionsWithInterval = intervalToRegions.get(intervalIdx);
			List<Set<FormalCondition>> overlappingCCsSet = new ArrayList<>();
			HashMap<FormalCondition, List<Integer>> conditionsToOverlappingRegions = new HashMap<>();
			for (int i = 0; i < overlappingRegionsWithInterval.size(); i++) {

				String overlappingRegion = overlappingRegionsWithInterval.get(i);
				Set<FormalCondition> overlappingCCs = new HashSet<>(regionToCCMap.get(overlappingRegion));
				overlappingCCsSet.add(overlappingCCs);
				for (FormalCondition fc : overlappingCCs) {
					if (!conditionsToOverlappingRegions.containsKey(fc)) {
						conditionsToOverlappingRegions.put(fc, new ArrayList<>());
					}
					conditionsToOverlappingRegions.get(fc).add(i);
				}
			}

			// Grouping conditions on the basis same regions overlapping

			HashMap<List<Integer>, List<FormalCondition>> groupMap = new HashMap<>();
			for (FormalCondition formalCondition : conditionsToOverlappingRegions.keySet()) {
				List<Integer> regionList = conditionsToOverlappingRegions.get(formalCondition);
				if (!groupMap.containsKey(regionList)) {
					groupMap.put(regionList, new ArrayList<>());
				}
				groupMap.get(regionList).add(formalCondition);

			}

			// SuperSet Map
			HashMap<List<Integer>, Set<List<Integer>>> superSetMap = new HashMap<>();
			int maxlen = -1;
			Set<List<Integer>> groupKeys = groupMap.keySet();
			for (List<Integer> groupKey : groupKeys) {
				if (maxlen < groupKey.size()) {
					maxlen = groupKey.size();
				}
				superSetMap.put(groupKey, new HashSet<>());
				for (List<Integer> key : groupKeys) {

					Set<Integer> keySet = new HashSet<>(groupKey);
					keySet.removeAll(key);
					if (keySet.isEmpty()) {
						superSetMap.get(groupKey).add(key);

					}

				}

			}

			// sorting on basis of List<Integer>
			List<List<Integer>> sortedGroupIdxs = new ArrayList<>();
			for (int i = 1; i <= maxlen; i++) {

				for (List<Integer> groupIdx : groupMap.keySet()) {

					if (groupIdx.size() == i) {
						sortedGroupIdxs.add(groupIdx);
					}

				}

			}

			// Group to region map
			Set<String> regionsCovered = new HashSet<>();
			HashMap<List<Integer>, String> groupToRegionMap = new HashMap<>();
			for (List<Integer> groupKey : sortedGroupIdxs) {

				List<FormalCondition> conditionList = groupMap.get(groupKey);
				for (FormalCondition fc : conditionList) {

					List<Integer> regionIdxList = conditionsToOverlappingRegions.get(fc);
					Set<String> regionsSet = new HashSet<>();
					for (int i : regionIdxList) {
						String region = overlappingRegionsWithInterval.get(i);
						regionsSet.add(region);
					}
					regionsSet.removeAll(regionsCovered);
					if (!regionsSet.isEmpty()) {
						if (regionsSet.size() != 1) {
							throw new RuntimeException(" Not expecting this");
						}

						List<String> regionsList = new ArrayList<>(regionsSet);
						String region = regionsList.get(0);
						groupToRegionMap.put(groupKey, region);
						regionsCovered.add(region);
					}

				}

			}

			/*
			 * 1. Find max d closest in all group 2. If exact match found in any group then
			 * directly replace 3. If exact match not found and divide the d into all groups
			 * 4. No hopes flag will be there after that whatever is there just put it
			 * 
			 * 
			 */

			// Step 1 : Find max d closest to maxd for each group
			Map<List<Integer>, List<Long>> appropriateDFMap = new HashMap<>();
			Map<List<Integer>, List<Integer>> dLocationsMap = new HashMap<>();
			Integer minLength = null;
			Integer maxLength = null;

			for (List<Integer> groupIdx : groupMap.keySet()) {

				List<FormalCondition> conditionList = groupMap.get(groupIdx);
				List<DFvector> dfVectorList = new ArrayList<>();

				for (FormalCondition condition : conditionList) {
					DFvector dfvector = conditionToDFMap.get(condition);
					if (dfvector.isEmpty()) {
						continue;
					}
					dfVectorList.add(dfvector);
				}
				List<Long> appropriateDF = new ArrayList<>();

				if (dfVectorList.isEmpty()) {
					continue;
				}

				boolean flag = findAppropriateDF(appropriateDF, dfVectorList, maxd, maxf);
				if (flag == false) {
					break;
				}

				if (appropriateDF.get(0) <= maxd) {
					appropriateDFMap.put(groupIdx, appropriateDF);

				}

				if (minLength == null) {
					minLength = groupIdx.size();
					maxLength = groupIdx.size();
				} else {

					if (groupIdx.size() > maxLength) {
						maxLength = groupIdx.size();
					}
					if (groupIdx.size() < minLength) {
						minLength = groupIdx.size();
					}

				}

			}

			System.out.print("");

			/*
			 * FROM SET OF DF's available
			 * 
			 * 1. if any of d value is equal to maxd choose it 2. if any of d Value is
			 * greater than maxd and other have smaller
			 */

			/*
			 * No appropriate df found end up this interval
			 */

			if (appropriateDFMap.isEmpty()) {

				System.out.print("");
				// Shift everything to future
				// Since nothing is left in df vector to pull off
				DFvector dfvector = intervalToDFVectorMap.get(selectedInterval);
				for (int di = 0; di < dfvector.getD().size(); di++) {

					Long dVal = dfvector.getD().get(di);
					Long fVal = dfvector.getF().get(di);
					ArrayList<Long> dList = new ArrayList<>();
					dList.add(dVal);
					ArrayList<Long> fList = new ArrayList<>();
					fList.add(fVal);
					DFvector dfvec = new DFvector(dList, fList);

					Long pkValStart = pkValBoundaryList.get(intervalIdxMap.get(intervalIdx));

					if (!futurePkValDFToAdd.containsKey(intervalIdx)) {
						futurePkValDFToAdd.put(intervalIdx, new HashMap<>());
					}
					if (!futurePkValDFToAdd.get(intervalIdx).containsKey(dfvec)) {
						futurePkValDFToAdd.get(intervalIdx).put(dfvec, new ArrayList<>());
					}
					futurePkValDFToAdd.get(intervalIdx).get(dfvec).add(pkValStart);

					pkValBoundaryList.set(intervalIdxMap.get(intervalIdx), pkValStart + fVal);

				}

				if (!tuplesPerIntervalCovered.containsKey(selectedInterval)) {
					tuplesPerIntervalCovered.put(selectedInterval, 0L);
				}

				Long tupleSum = 0L;
				for (int di = 0; di < dfvector.size(); di++) {

					tupleSum += dfvector.getD().get(di) * dfvector.getF().get(di);

				}

				tuplesPerIntervalCovered.put(selectedInterval,
						tuplesPerIntervalCovered.get(selectedInterval) + tupleSum);
				long val = this.allIntervalRegionValueMap.get(selectedInterval).longValue();
				// introduce check stmt for boundary check
				if (val != tuplesPerIntervalCovered.get(selectedInterval).longValue()) {

					throw new RuntimeException("Interval values covered should match");

				}

				intervalToDFVectorMap.remove(selectedInterval);
				continue;

			}

			// From each group find maximum f that can taken from all groups
			Long minFofAll = null;
			for (List<Integer> groupIdx : appropriateDFMap.keySet()) {
				Long fVal = appropriateDFMap.get(groupIdx).get(1);
				if (minFofAll == null) {
					minFofAll = fVal;
				} else {
					if (minFofAll > fVal) {
						minFofAll = fVal;
					}
				}

			}

			// find smallest d value among all groups
			Long minD = null;
			List<Integer> currentGroup = null;
			for (List<Integer> groupIdx : appropriateDFMap.keySet()) {

				if (minD == null) {
					minD = appropriateDFMap.get(groupIdx).get(0);
					currentGroup = groupIdx;
				} else if (minD > appropriateDFMap.get(groupIdx).get(0)) {

					minD = appropriateDFMap.get(groupIdx).get(0);
					currentGroup = groupIdx;

				}
			}

			List<Long> appropriateDF = appropriateDFMap.get(currentGroup);
			Long dVal = appropriateDF.get(0);
			Long fVal = appropriateDF.get(1);
			Long dCompleted = 0L;
			boolean maxdDone = false;

			if (dVal < maxd) {

				// cover all supersets
				// Remove all respective df value from current group and supeset group
				// if there is advance pkVal exercise that also
				Set<List<Integer>> supersetGroups = superSetMap.get(currentGroup);
				List<List<Integer>> sortedSuperSetGroups = new ArrayList<>();
				for (List<Integer> groupIdx : sortedGroupIdxs) {

					if (sortedSuperSetGroups.contains(groupIdx)) {
						sortedSuperSetGroups.add(groupIdx);
					}

				}

				Map<FormalCondition, Map<Integer, List<Long>>> ccsToPKValDFMap = new HashMap<>();

				Long pkValStart = pkValBoundaryList.get(intervalIdxMap.get(intervalIdx));

				List<List<Integer>> groupsUsedEqualDValue = new ArrayList<>();
				List<List<Integer>> groupsUsedLTdValue = new ArrayList<>(); // less than
				List<Long> dUsedByLTgroups = new ArrayList<>();

				for (List<Integer> groupIdx : supersetGroups) {

					if (!appropriateDFMap.containsKey(groupIdx)) {
						continue;
					}

					Long dValue = appropriateDFMap.get(groupIdx).get(0);
					String regionName = groupToRegionMap.get(groupIdx);
					if (regionName == null) {
						continue;
					}
					if (!this.varPKValDistribution.containsKey(regionName)) {
						this.varPKValDistribution.put(regionName, new HashMap<>());
					}
					// can create issue
					Long val = this.allIntervalisedRegionsMap.get(regionName);
					Long noOFtuplesToBeCovered = dValue * minFofAll;
					if (!tuplesPerRegionCovered.containsKey(regionName)) {
						tuplesPerRegionCovered.put(regionName, 0L);
					}
					if (tuplesPerRegionCovered.get(regionName) + noOFtuplesToBeCovered > val) {
						// will lead to negative tuple
						// add to future
						break;
					} else {

						if (dValue.longValue() == dVal) {

							for (int i = 0; i < minFofAll; i++) {

								if (!this.varPKValDistribution.get(regionName).containsKey(dVal)) {
									this.varPKValDistribution.get(regionName).put(dVal, new ArrayList<>());
								}
								this.varPKValDistribution.get(regionName).get(dValue).add(pkValStart + i);

							}
							tuplesPerRegionCovered.put(regionName,
									tuplesPerRegionCovered.get(regionName) + dValue * minFofAll);
							dCompleted += dValue;
							groupsUsedEqualDValue.add(groupIdx);

						}

						else if (dValue.longValue() > dVal) {

							long availableD = dValue - dCompleted;
							Long usedD = null;
							if (availableD + dCompleted < maxd) {
								// assign availabled

								usedD = availableD;
								dCompleted += usedD;

							} else {
								// assign whatever left to current region(availableD + dCompleted >= maxd)

								usedD = (maxd - dCompleted);
								maxdDone = true;

							}

							for (int i = 0; i < minFofAll; i++) {

								if (!this.varPKValDistribution.get(regionName).containsKey(usedD)) {
									this.varPKValDistribution.get(regionName).put(usedD, new ArrayList<>());
								}
								this.varPKValDistribution.get(regionName).get(usedD).add(pkValStart + i);

							}

							tuplesPerRegionCovered.put(regionName,
									tuplesPerRegionCovered.get(regionName) + usedD * minFofAll);
							groupsUsedLTdValue.add(groupIdx);
							dUsedByLTgroups.add(usedD);

							if (maxdDone == true) {
								break;
							}

						}

						else {

							throw new RuntimeException("Doing something wrong, dValue should <= maxd");
						}

					}

				}

				// Future additon comes here
				if (dCompleted.longValue() < maxd) {

					List<Long> dValues = new ArrayList<>();
					List<Long> fValues = new ArrayList<>();
					dValues.add(maxd - dCompleted.longValue());
					fValues.add(minFofAll);

					DFvector dfvector = new DFvector(dValues, fValues);

					if (!futurePkValDFToAdd.containsKey(intervalIdx)) {
						futurePkValDFToAdd.put(intervalIdx, new HashMap<>());
					}
					if (!futurePkValDFToAdd.get(intervalIdx).containsKey(dfvector)) {
						futurePkValDFToAdd.get(intervalIdx).put(dfvector, new ArrayList<>());
					}
					futurePkValDFToAdd.get(intervalIdx).get(dfvector).add(pkValStart);
					maxdDone = true;

				} else {

					if (maxd > dCompleted.longValue()) {
						throw new RuntimeException("Doing wrong ");
					}
					if (maxd == dCompleted && maxdDone == false) {

						throw new RuntimeException(" maxdDone is not getting updated");
					}

				}

				/*
				 * Remove CCs df from CCToDFvector
				 * 
				 */
				// remove (dVal,minFForALl) from all CCs
				for (List<Integer> groupIdx : groupsUsedEqualDValue) {

					List<FormalCondition> conditionList = groupMap.get(groupIdx);
					for (FormalCondition condition : conditionList) {

						DFvector dfvector = conditionToDFMap.get(condition);
						List<Long> dValues = dfvector.getD();
						Integer pos = null;
						for (int i = 0; i < dValues.size(); i++) {

							if (dValues.get(i).intValue() == dVal.intValue()) {
								pos = i;
								break;
							}

						}

						if (pos == null) {
							continue;
						}

						Long fValue = dfvector.getF().get(pos);
						if (fValue.longValue() > minFofAll.longValue()) {

							dfvector.update(pos, fValue - minFofAll);

						} else if (fValue.longValue() == minFofAll.longValue()) {

							dfvector.remove(pos);

						} else {

							throw new RuntimeException(" Doing something wrong with minFofAll ");

						}
					}
				}

				for (int i = 0; i < groupsUsedLTdValue.size(); i++) {

					List<FormalCondition> conditionList = groupMap.get(groupsUsedLTdValue.get(i));
					Long dUsed = dUsedByLTgroups.get(i);
					for (FormalCondition condition : conditionList) {

						DFvector dfvector = conditionToDFMap.get(condition);
						List<Long> dValues = dfvector.getD();
						Integer pos = null;
						for (int di = 0; di < dValues.size(); di++) {

							if (dValues.get(di).longValue() == dUsed.longValue()) {
								pos = di;
								break;
							}

						}

						if (pos == null) {

							// if usedD not found go on
							continue;
						}

						Long fValue = dfvector.getF().get(0);
						if (fValue.intValue() > minFofAll.intValue()) {

							dfvector.update(pos, fValue - minFofAll);

						} else if (fValue.longValue() == minFofAll.intValue()) {

							dfvector.remove(pos);

						} else {

							throw new RuntimeException(" Doing something wrong with minFofAll ");

						}
					}

				}

				pkValBoundaryList.set(intervalIdxMap.get(intervalIdx), pkValStart + minFofAll);

			} else if (dVal == maxd) {

				// Assign tuples to all region
				// remove df value from all overlapping CCs
				Long pkValStart = pkValBoundaryList.get(intervalIdxMap.get(intervalIdx));
				Set<List<Integer>> supersetGroups = superSetMap.get(currentGroup);
				String regionName = groupToRegionMap.get(currentGroup);

				Long val = this.allIntervalisedRegionsMap.get(regionName);

				Long noOFtuplesToBeCovered = dVal * minFofAll;

				if (!tuplesPerRegionCovered.containsKey(regionName)) {
					tuplesPerRegionCovered.put(regionName, 0L);
				}

				if (tuplesPerRegionCovered.get(regionName) + noOFtuplesToBeCovered > val) {
					// will lead to negative tuple
					// add to future
					// make maxdDone true
					List<Long> dValues = new ArrayList<>();
					List<Long> fValues = new ArrayList<>();
					dValues.add(dVal);
					fValues.add(minFofAll);

					DFvector dfvector = new DFvector(dValues, fValues);

					if (!futurePkValDFToAdd.containsKey(intervalIdx)) {
						futurePkValDFToAdd.put(intervalIdx, new HashMap<>());
					}
					if (!futurePkValDFToAdd.get(intervalIdx).containsKey(dfvector)) {
						futurePkValDFToAdd.get(intervalIdx).put(dfvector, new ArrayList<>());
					}
					futurePkValDFToAdd.get(intervalIdx).get(dfvector).add(pkValStart);

					maxdDone = true;

				} else {

					if (!this.varPKValDistribution.containsKey(regionName)) {
						this.varPKValDistribution.put(regionName, new HashMap<>());
					}

					if (!this.varPKValDistribution.get(regionName).containsKey(dVal)) {
						this.varPKValDistribution.get(regionName).put(dVal, new ArrayList<>());
					}

					for (int i = 0; i < minFofAll; i++) {

						this.varPKValDistribution.get(regionName).get(dVal).add(pkValStart + i);

					}
					tuplesPerRegionCovered.put(regionName,
							tuplesPerRegionCovered.get(regionName) + noOFtuplesToBeCovered);
					pkValBoundaryList.set(intervalIdxMap.get(intervalIdx), pkValStart + minFofAll);

					maxdDone = true;

					Set<FormalCondition> doneFormalCondition = new HashSet<>();
					for (List<Integer> groupIdx : supersetGroups) {

						if (!appropriateDFMap.containsKey(groupIdx)) {
							continue;
						}
						Long dValue = appropriateDFMap.get(groupIdx).get(0);

						if (dValue.longValue() == dVal.longValue()) {

							List<FormalCondition> conditionList = groupMap.get(groupIdx);
							for (FormalCondition condition : conditionList) {

								if (doneFormalCondition.contains(condition)) {
									continue;
								} else {
									doneFormalCondition.add(condition);
								}

								DFvector dfvector = conditionToDFMap.get(condition);
								List<Long> dValues = dfvector.getD();
								if (dValues.isEmpty()) {
									continue;
								}
								Integer pos = null;
								for (int i = 0; i < dValues.size(); i++) {

									if (dValues.get(i).longValue() == dVal.longValue()) {
										pos = i;
										break;
									}

								}

								Long fValue = dfvector.getF().get(pos);
								if (fValue.intValue() > minFofAll.intValue()) {

									dfvector.update(pos, fValue - minFofAll);

								} else if (fValue.intValue() == minFofAll.intValue()) {

									dfvector.remove(pos);

								} else {

									throw new RuntimeException(" Doing something wrong with minFofAll ");

								}

							}

						} else if (dValue > dVal) {

							throw new RuntimeException("Handle case");
						}

						else {
							throw new RuntimeException("Not expecting this");
						}

					}

				}

			}

			else {
				throw new RuntimeException("No hopes : distribute to future ");

			}

			if (maxdDone) {

				if (maxf == minFofAll) {
					// remove df from interval
					// remove <maxd,f> from that interval df
					intervalToDFVectorMap.get(selectedInterval).remove(0);

					// if dfVector becomes empty then remove from intervalToDFVectorMap
					if (intervalToDFVectorMap.get(selectedInterval).isEmpty()) {

						intervalToDFVectorMap.remove(selectedInterval);

					}

					if (!tuplesPerIntervalCovered.containsKey(selectedInterval)) {
						tuplesPerIntervalCovered.put(selectedInterval, 0L);
					}
					Long val = this.allIntervalRegionValueMap.get(selectedInterval);
					if (tuplesPerIntervalCovered.get(selectedInterval) + maxd * minFofAll > val) {
						System.out.print("Doing wrong");
					} else {
						tuplesPerIntervalCovered.put(selectedInterval,
								tuplesPerIntervalCovered.get(selectedInterval) + maxd * minFofAll);
					}

				} else {

					if (!tuplesPerIntervalCovered.containsKey(selectedInterval)) {
						tuplesPerIntervalCovered.put(selectedInterval, 0L);
					}
					Long val = this.allIntervalRegionValueMap.get(selectedInterval);
					if (tuplesPerIntervalCovered.get(selectedInterval) + maxd * minFofAll > val) {
						System.out.print("Doing wrong");
					} else {
						tuplesPerIntervalCovered.put(selectedInterval,
								tuplesPerIntervalCovered.get(selectedInterval) + maxd * minFofAll);
					}

					intervalToDFVectorMap.get(selectedInterval).update(0, maxf - minFofAll);

				}

			}

		}

		// now its time for future addition

		for (Integer intervalIdx : futurePkValDFToAdd.keySet()) {

			List<String> regionList = new ArrayList<>();
			Long tupleC = 0L;
			for (DFvector dfvector : futurePkValDFToAdd.get(intervalIdx).keySet()) {

				tupleC += dfvector.getD().get(0) * dfvector.getF().get(0)
						* futurePkValDFToAdd.get(intervalIdx).get(dfvector).size();
			}

			for (String region : this.allIntervalisedRegionsMap.keySet()) {

				if (!region.contains(fkey)) {
					continue;
				}
				if (!region.contains("var" + cliqueIdx)) {
					continue;
				}

				if (Integer.parseInt(region.split("interval_")[1]) == intervalIdx) {
					regionList.add(region);
				}
			}

			List<Long> filledTupleList = new ArrayList<>();
			List<Long> actualTupleCount = new ArrayList<>();
			List<Long> fillingTuples = new ArrayList<>();
			List<Long> copyOfActualTupleCount = new ArrayList<>();
			List<String> copyOfRegions = new ArrayList<>();

			for (String region : regionList) {
				copyOfRegions.add(region);
				Long tupleCount = 0l;
				if (!this.varPKValDistribution.containsKey(region)) {
					tupleCount = 0l;
				} else {
					for (Long di : this.varPKValDistribution.get(region).keySet()) {
						tupleCount += di * this.varPKValDistribution.get(region).get(di).size();
					}
				}

				filledTupleList.add(tupleCount);
				fillingTuples.add(tupleCount);

				tupleCount = this.allIntervalisedRegionsMap.get(region);
				actualTupleCount.add(tupleCount);
				copyOfActualTupleCount.add(tupleCount);

			}

			// check consistency of code
			Long sum1 = 0L;
			Long sum2 = 0L;
			Long before = 0L;
			Long after = 0L;
			for (int ci = 0; ci < actualTupleCount.size(); ci++) {

				sum1 += actualTupleCount.get(ci);
				sum2 += filledTupleList.get(ci);

			}

			if ((sum1 - sum2) != tupleC.longValue()) {
				throw new RuntimeException("Above code is wrong");
			}

			Long addedTupleCount = 0L;
			int currentRegIdx = 0;
			List<DFvector> dfvectorList = new ArrayList<>(futurePkValDFToAdd.get(intervalIdx).keySet());
			while (!dfvectorList.isEmpty()) {
				DFvector dfvector = dfvectorList.get(0);

				if (dfvector.isEmpty()) {
					dfvectorList.remove(0);
					continue;
				}
				Long dVal = dfvector.getD().get(0);
				Long fVal = dfvector.getF().get(0);
				List<Long> pkValList = futurePkValDFToAdd.get(intervalIdx).get(dfvector);

				while (!pkValList.isEmpty()) {

					Long pkStart = pkValList.get(0);

					long leftCount = actualTupleCount.get(0) - filledTupleList.get(0);

					if (leftCount < 0) {
						throw new RuntimeException("Wrong implementation");
					}

					if (leftCount >= dVal * fVal) {
						long tupleCheck = 0L;
						before = getTupleCount(regionList.get(0));
						for (int fi = 0; fi < fVal; fi++) {
							if (!this.varPKValDistribution.containsKey(regionList.get(0))) {
								this.varPKValDistribution.put(regionList.get(0), new HashMap<>());
							}

							if (!this.varPKValDistribution.get(regionList.get(0)).containsKey(dVal)) {
								this.varPKValDistribution.get(regionList.get(0)).put(dVal, new ArrayList<>());
							}
							this.varPKValDistribution.get(regionList.get(0)).get(dVal).add(pkStart + fi);
							tupleCheck += dVal;
						}
						after = getTupleCount(regionList.get(0));
						if (tupleCheck != dVal * fVal) {
							throw new RuntimeException("Prob;lem");
						}

						if (before + dVal * fVal != after) {
							throw new RuntimeException("Prob;lem");
						}

						addedTupleCount += dVal * fVal;
						filledTupleList.set(0, filledTupleList.get(0) + dVal * fVal);
						fillingTuples.set(currentRegIdx, fillingTuples.get(currentRegIdx) + dVal * fVal);

						if (leftCount == dVal * fVal) {

							// region is finised
							// time for next region
							regionList.remove(0);
							actualTupleCount.remove(0);
							filledTupleList.remove(0);
							currentRegIdx++;

							if (regionList.isEmpty()) {
								// current pkVal is finished
								pkValList.remove(0);
								dfvectorList.remove(0);
							}

							continue;
						}

						// current pkVal is finished
						pkValList.remove(0);
						dfvectorList.remove(0);

					}

					else if (leftCount >= dVal) {

						Long newf = leftCount / dVal;
						fVal = fVal - newf;
						long tupleCheck = 0L;
						before = getTupleCount(regionList.get(0));
						for (int fi = 0; fi < newf; fi++) {
							if (!this.varPKValDistribution.containsKey(regionList.get(0))) {
								this.varPKValDistribution.put(regionList.get(0), new HashMap<>());
							}

							if (!this.varPKValDistribution.get(regionList.get(0)).containsKey(dVal)) {
								this.varPKValDistribution.get(regionList.get(0)).put(dVal, new ArrayList<>());
							}
							this.varPKValDistribution.get(regionList.get(0)).get(dVal).add(pkStart + fi);
							tupleCheck += dVal;
						}
						after = getTupleCount(regionList.get(0));
						if (tupleCheck != dVal * newf) {
							throw new RuntimeException("Prob;lem");
						}
						if (before + dVal * newf != after) {
							throw new RuntimeException("Prob;lem");
						}
						fillingTuples.set(currentRegIdx, fillingTuples.get(currentRegIdx) + dVal * newf);
						if (leftCount == dVal * newf) {
							regionList.remove(0);
							actualTupleCount.remove(0);
							filledTupleList.remove(0);
							currentRegIdx++;
							if (regionList.isEmpty()) {
								// current pkVal is finished
								pkValList.remove(0);
								dfvectorList.remove(0);
							}

						}

					} else {

						// leftCount < dVal
						fVal = fVal - 1;

						// completing current region and invoking next region
						long tupleCheck = 0;
						before = getTupleCount(regionList.get(0));
						for (int fi = 0; fi < 1; fi++) {
							if (!this.varPKValDistribution.containsKey(regionList.get(0))) {
								this.varPKValDistribution.put(regionList.get(0), new HashMap<>());
							}

							if (!this.varPKValDistribution.get(regionList.get(0)).containsKey(leftCount)) {
								this.varPKValDistribution.get(regionList.get(0)).put(leftCount, new ArrayList<>());
							}
							this.varPKValDistribution.get(regionList.get(0)).get(leftCount).add(pkStart + fi);
							tupleCheck += leftCount;
						}
						after = getTupleCount(regionList.get(0));
						if (tupleCheck != leftCount) {
							throw new RuntimeException("Prob;lem");
						}
						if (before + leftCount != after) {
							throw new RuntimeException("Prob;lem");
						}
						fillingTuples.set(currentRegIdx, fillingTuples.get(currentRegIdx) + leftCount);
						Long tempD = (dVal - leftCount);

						regionList.remove(0);
						actualTupleCount.remove(0);
						filledTupleList.remove(0);
						currentRegIdx++;
						if (regionList.isEmpty()) {
							// current pkVal is finished
							pkValList.remove(0);
							dfvectorList.remove(0);
							break;
						}

						while (true) {

							leftCount = actualTupleCount.get(0) - filledTupleList.get(0);
							if (leftCount == 0) {
								regionList.remove(0);
								actualTupleCount.remove(0);
								filledTupleList.remove(0);
								currentRegIdx++;
								if (regionList.isEmpty()) {
									// current pkVal is finished
									pkValList.remove(0);
									dfvectorList.remove(0);
									break;

								}
								break;
							}

							if (tempD >= leftCount) {
								tupleCheck = 0L;
								before = getTupleCount(regionList.get(0));
								for (int fi = 0; fi < 1; fi++) {
									if (!this.varPKValDistribution.containsKey(regionList.get(0))) {
										this.varPKValDistribution.put(regionList.get(0), new HashMap<>());
									}

									if (!this.varPKValDistribution.get(regionList.get(0)).containsKey(leftCount)) {
										this.varPKValDistribution.get(regionList.get(0)).put(leftCount,
												new ArrayList<>());
									}
									this.varPKValDistribution.get(regionList.get(0)).get(leftCount).add(pkStart + fi);
									tupleCheck += leftCount;
									;
								}
								after = getTupleCount(regionList.get(0));
								if (tupleCheck != leftCount) {
									throw new RuntimeException("Prob;lem");
								}
								if (before + leftCount != after) {
									throw new RuntimeException("Prob;lem");
								}

								fillingTuples.set(currentRegIdx, fillingTuples.get(currentRegIdx) + leftCount);
								regionList.remove(0);
								actualTupleCount.remove(0);
								filledTupleList.remove(0);
								currentRegIdx++;
								if (regionList.isEmpty()) {
									// current pkVal is finished
									pkValList.remove(0);
									dfvectorList.remove(0);
									break;

								}

							}

							else {

								tupleCheck = 0;
								before = getTupleCount(regionList.get(0));
								for (int fi = 0; fi < 1; fi++) {
									if (!this.varPKValDistribution.containsKey(regionList.get(0))) {
										this.varPKValDistribution.put(regionList.get(0), new HashMap<>());
									}

									if (!this.varPKValDistribution.get(regionList.get(0)).containsKey(tempD)) {
										this.varPKValDistribution.get(regionList.get(0)).put(tempD, new ArrayList<>());
									}
									this.varPKValDistribution.get(regionList.get(0)).get(tempD).add(pkStart + fi);
									tupleCheck += tempD;
								}
								after = getTupleCount(regionList.get(0));
								if (tupleCheck != tempD) {
									throw new RuntimeException("Prob;lem");
								}
								if (before + tempD != after) {
									throw new RuntimeException("Prob;lem");
								}

								filledTupleList.set(0, filledTupleList.get(0) + tempD);
								fillingTuples.set(currentRegIdx, fillingTuples.get(currentRegIdx) + tempD);
								break;
							}

						}

						if (fVal == 0) {

							if (!pkValList.isEmpty()) {
								pkValList.remove(0);
							}
							if (!dfvectorList.isEmpty()) {
								dfvectorList.remove(0);
							}

						}

					}

				}

			}

			for (String regionName : copyOfRegions) {
				Long val = this.allIntervalisedRegionsMap.get(regionName);

				Long tupleCount = 0L;
				for (Long dVal : this.varPKValDistribution.get(regionName).keySet()) {

					tupleCount += dVal * this.varPKValDistribution.get(regionName).get(dVal).size();

				}

				if (tupleCount.longValue() != val.longValue()) {

					throw new RuntimeException("Problem here");
				}

			}

			System.out.print("");

		}

	}

	public Long getTupleCount(String regionName) {

		Long tupleCount = 0L;
		if (!this.varPKValDistribution.containsKey(regionName)) {
			return 0L;
		}
		for (Long dVal : this.varPKValDistribution.get(regionName).keySet()) {

			tupleCount += dVal * this.varPKValDistribution.get(regionName).get(dVal).size();

		}
		return tupleCount;

	}

	private boolean findAppropriateDF(List<Long> appropriateDF, List<DFvector> dfVectorList, Long maxd, Long maxf) {
		// TODO Auto-generated method stub

		// first find common d values in all dfVectorList<>
		/*
		 * List<Long> commonDValuesSet = new ArrayList<>(dfVectorList.get(0).getD());
		 * for(int i=1; i < dfVectorList.size(); i++) {
		 * 
		 * commonDValuesSet.retainAll(dfVectorList.get(i).getD()); }
		 * 
		 * // decreasing order sort Collections.sort(commonDValuesSet,
		 * Collections.reverseOrder()); // find d closest to maxd in commonDValuesSet
		 * 
		 * // 10 -> [9 or 11] give it to 11 Since no way 11 can come in maxd
		 * 
		 * if(commonDValuesSet.isEmpty()) { return false; //throw new
		 * RuntimeException(" Was not expecting this, think something to solve this"); }
		 * 
		 * int di=0; boolean foundFlag = false; for(; di < commonDValuesSet.size();
		 * di++) {
		 * 
		 * if(commonDValuesSet.get(di) == maxd) { // found maxd foundFlag = true; break;
		 * } else if(commonDValuesSet.get(di) < maxd) { break; }
		 * 
		 * }
		 * 
		 * Long appropriateD = null; if(di == 0) { // no dValues is more than maxd //
		 * choose max(dValues) appropriateD = commonDValuesSet.get(0);
		 * 
		 * } else if(foundFlag) { appropriateD = commonDValuesSet.get(di);
		 * 
		 * } else { appropriateD = commonDValuesSet.get(di-1);
		 * 
		 * }
		 * 
		 * // find appropriateF Long appropriateF = null;
		 * 
		 * for(int i=0; i < dfVectorList.size(); i++) { List<Long> dValues =
		 * dfVectorList.get(i).getD(); List<Long> fValues = dfVectorList.get(i).getF();
		 * for(di=0; di < dValues.size(); di++) {
		 * 
		 * if(dValues.get(di) == appropriateD) { if(appropriateF == null) { appropriateF
		 * = fValues.get(di);
		 * 
		 * } else if(appropriateF > fValues.get(di)) { appropriateF = fValues.get(di);
		 * 
		 * } break;
		 * 
		 * }
		 * 
		 * } }
		 * 
		 */

		Long appropriateD = null;
		for (int i = 0; i < dfVectorList.size(); i++) {

			List<Long> dValues = dfVectorList.get(i).getD();
			for (int di = 0; di < dValues.size(); di++) {

				if (dValues.get(di) > maxd) {
					continue;
				} else {
					if (appropriateD == null) {

						appropriateD = dValues.get(di);

					} else {

						if (appropriateD > dValues.get(di)) {
							appropriateD = dValues.get(di);
						}

					}
				}

			}

			if (appropriateD == null) {

				appropriateD = dfVectorList.get(i).getD().get(0);

			} else {

				if (appropriateD > dfVectorList.get(i).getD().get(0)) {
					appropriateD = dfVectorList.get(i).getD().get(0);
				}

			}

		}

		Long appropriateF = null;
		for (int i = 0; i < dfVectorList.size(); i++) {
			List<Long> dValues = dfVectorList.get(i).getD();
			List<Long> fValues = dfVectorList.get(i).getF();
			Long sumf = 0L;

			if (appropriateD == maxd) {

				for (int di = dValues.size() - 1; di >= 0; di--) {
					if (dValues.get(di) >= maxd) {

						if (appropriateF == null) {
							appropriateF = fValues.get(di);
						} else {

							if (appropriateF > fValues.get(di)) {
								appropriateF = fValues.get(di);
							}

						}
						break;
					}
				}
			} else {

				for (int di = 0; di < dValues.size(); di++) {

					if (dValues.get(di) < appropriateD) {
						break;
					} else {

						sumf += fValues.get(di);
					}

				}
				if (appropriateF == null) {
					appropriateF = sumf;
				} else {

					if (appropriateF > sumf) {
						sumf = appropriateF;
					}

				}
			}

		}

		if (appropriateF > maxf) {
			appropriateF = maxf;
		}

		appropriateDF.add(appropriateD);
		appropriateDF.add(appropriateF);

		return true;

	}

	private int checkIntersection(Map<String, Set<Integer>> map, Map<String, Set<Integer>> map2) {

		if (map.keySet().size() != map2.keySet().size()) {
			System.out.print("");
		}

		List<Integer> allIntersectionVals = new ArrayList<>();
		for (String column : map.keySet()) {

			Set<Integer> set = new HashSet<>(map.get(column));
			Set<Integer> set2 = new HashSet<>(map2.get(column));

			if (set.equals(set2)) {
				allIntersectionVals.add(0);

			} else {
				Set<Integer> testSet = new HashSet<>(set);
				testSet.retainAll(set2);
				if (!testSet.isEmpty()) {
					allIntersectionVals.add(1);

				} else {
					allIntersectionVals.add(-1);

				}
			}

			System.out.print("");

		}

		return 0;
	}

	private void findAssociatedVal(List<String> sortedBorrowedAttr, List<FormalCondition> conditions,
			Map<String, Set<Integer>> smallbfc) {
		// TODO Auto-generated method stub

		for (FormalCondition condition : conditions) {

			if (condition instanceof FormalConditionComposite) {
				findAssociatedVal(sortedBorrowedAttr, ((FormalConditionComposite) condition).getConditionList(),
						smallbfc);
			} else if (condition instanceof FormalConditionSimpleInt) {

				FormalConditionSimpleInt formalConditionSimpleInt = (FormalConditionSimpleInt) condition;
				String columnName = formalConditionSimpleInt.getColumnname();
				int a = formalConditionSimpleInt.getValue();
				if (!sortedBorrowedAttr.contains(columnName)) {
					continue;
				}
				Set<Integer> integerSet = smallbfc.get(columnName);
				IntList intervals = this.bucketFloorsByColumns.get(columnName);
				switch (formalConditionSimpleInt.getSymbol()) {
				case LT: {

					for (int i = 0; i < intervals.size(); i++) {
						if (intervals.get(i) < a) {
							integerSet.add(a);
						}
					}

					break;
				}

				case LE: {

					for (int i = 0; i < intervals.size(); i++) {
						if (intervals.get(i) <= a) {
							integerSet.add(a);
						}
					}

					break;
				}
				case GT: {

					for (int i = 0; i < intervals.size(); i++) {
						if (intervals.get(i) > a) {
							integerSet.add(a);
						}
					}

					break;
				}
				case GE: {

					for (int i = 0; i < intervals.size(); i++) {
						if (intervals.get(i) >= a) {
							integerSet.add(a);
						}
					}

					break;
				}
				case EQ: {

					for (int i = 0; i < intervals.size(); i++) {
						if (intervals.get(i) == a) {
							integerSet.add(a);
						}
					}

					break;
				}
				default:
					throw new RuntimeException("Unrecognized Symbol " + formalConditionSimpleInt.getSymbol());

				}
			} else if (condition instanceof FormalConditionBaseAggregate) {

			} else
				throw new RuntimeException("Unrecognized type of FormalCondition " + condition.getClass());

		}

	}

	public void solveView1(List<FormalCondition> conditions, List<Region> conditionRegions,
			FormalCondition consistencyConstraints[], ConsistencyMakerType consistencyMakerType,
			Map<String, List<Region>> aggregateColumnsToSingleSplitPointRegions) {

		StopWatch formulationPlusSolvingSW = new StopWatch("LP-Solving (meging cliques not included)" + viewname);
		beginLPFormulation();
		List<LinkedList<VariableValuePair>> cliqueIdxToVarValuesList = formulateAndSolve(conditions, conditionRegions,
				consistencyConstraints, consistencyMakerType);
		finishSolving();
		solverStats.millisToSolve = formulationPlusSolvingSW.getTimeAndDispose();
		return;
	}

	public ViewSolutionWithSolverStats mergeCliques(List<LinkedList<VariableValuePair>> cliqueIdxToVarValuesList) {

		ViewSolution viewSolution = mergeCliqueSolutions(cliqueIdxToVarValuesList);
		finishPostSolving();
		return new ViewSolutionWithSolverStats(viewSolution, solverStats);
	}

	private ViewSolutionInMemory mergeCliqueSolutionsRegionwise(
			List<LinkedList<VariableValuePair>> cliqueIdxToVarValuesList) {

		IntList mergedColIndxs = new IntArrayList();
		List<ValueCombination> mergedValueCombinations = new ArrayList<>();
		// S
		List<VariableValuePair> mergedVarValuePairs = new ArrayList();
		// arasuCliquesAsColIndxs --list of list of columns index (only those present in
		// some constraint) in a subview.
		mergedColIndxs.addAll(arasuCliquesAsColIndxs.get(0));
		// Instantiating variables of first clique
		for (VariableValuePair varValuePair : cliqueIdxToVarValuesList.get(0)) {
			mergedVarValuePairs.add(varValuePair);
		}
		// Shadab, mergeWithAlignmentRegionwise deletes the regions from
		// arasuCliquesAsColIndxs. So if regions are needed post merging too, then make
		// a deep copy in the function.
		for (int i = 1; i < cliqueCount; i++) {
			mergeWithAlignmentRegionwise(mergedColIndxs, mergedVarValuePairs, arasuCliquesAsColIndxs.get(i),
					cliqueIdxToVarValuesList.get(i));
		}
		System.gc();
		// added by Shadab for disjoint check
		areDisjointCheck(mergedVarValuePairs);
		/*
		 * for(VariableValuePair var:mergedVarValuePairs) { IntList columnValues =
		 * getFloorInstantiation(var.variable);
		 * 
		 * ValueCombination valueCombination = new ValueCombination(columnValues,
		 * var.rowcount); mergedValueCombinations.add(valueCombination);
		 * var.variable=getExpandedRegion(var.variable);
		 * 
		 * 
		 * } for (ListIterator<ValueCombination> iter =
		 * mergedValueCombinations.listIterator(); iter.hasNext();) { ValueCombination
		 * valueCombination = iter.next(); valueCombination =
		 * getReverseMappedValueCombination(valueCombination); valueCombination =
		 * getExpandedValueCombination(valueCombination); iter.set(valueCombination); }
		 */
		// Shadab code
		for (VariableValuePair var : mergedVarValuePairs) {

			var.variable = getReverseMappedRegion(var.variable);
			var.variable = getExpandedRegion(var.variable);
			IntList columnValues = getFloorInstantiation(var.variable);
			ValueCombination valueCombination = new ValueCombination(columnValues, var.rowcount);// if you wish to get
																									// the
																									// valuecombination
																									// too
			mergedValueCombinations.add(valueCombination);

		}

		ViewSolutionInMemory viewSolutionInMemory = new ViewSolutionInMemory(mergedValueCombinations.size(),
				mergedVarValuePairs);
		for (ValueCombination mergedValueCombination : mergedValueCombinations) {
			viewSolutionInMemory.addValueCombination(mergedValueCombination);
		}
		// ViewSolutionRegion viewSolution=new
		// ViewSolutionRegion(viewSolutionInMemory,mergedVarValuePairs);

		return viewSolutionInMemory;
		// commented by shadab return viewSolutionInMemory;
	}

	private void mergeWithAlignmentRegionwise(IntList lhsColIndxs, List<VariableValuePair> lhsVarValuePairs,
			IntList rhsColIndxs, LinkedList<VariableValuePair> rhsVarValuePairs) {
		for (VariableValuePair var : lhsVarValuePairs) {
			if (var.rowcount == 0)
				System.out.print("sd");
		}
		for (VariableValuePair var : rhsVarValuePairs) {
			if (var.rowcount == 0)
				System.out.print("sd");
		}
		List<VariableValuePair> mergedVarValuePairs = new ArrayList<>();// new table after merging
		// Shadab-"snitches get stitches"
		// System.out.println("Shadab has reached here");
		IntList tempColIndxs = new IntArrayList(rhsColIndxs);
		tempColIndxs.removeAll(lhsColIndxs);
		IntList sharedColIndxs = new IntArrayList(rhsColIndxs);
		sharedColIndxs.removeAll(tempColIndxs);
		IntList posInLHS = new IntArrayList(sharedColIndxs.size());
		IntList posInRHS = new IntArrayList(sharedColIndxs.size());
		for (IntIterator iter = sharedColIndxs.iterator(); iter.hasNext();) {
			int sharedColIndx = iter.nextInt();
			posInLHS.add(lhsColIndxs.indexOf(sharedColIndx));
			posInRHS.add(rhsColIndxs.indexOf(sharedColIndx));
		}

		IntList mergedColIndxsList = new IntArrayList(lhsColIndxs);
		mergedColIndxsList.addAll(rhsColIndxs);
		mergedColIndxsList = new IntArrayList(new IntOpenHashSet(mergedColIndxsList));
		Collections.sort(mergedColIndxsList);

		boolean[] fromLHS = new boolean[mergedColIndxsList.size()];
		int[] correspOriginalIndx = new int[mergedColIndxsList.size()];
		for (int i = 0; i < mergedColIndxsList.size(); i++) {
			fromLHS[i] = lhsColIndxs.contains(mergedColIndxsList.get(i));
			if (fromLHS[i]) {
				correspOriginalIndx[i] = lhsColIndxs.indexOf(mergedColIndxsList.get(i));
			} else {
				correspOriginalIndx[i] = rhsColIndxs.indexOf(mergedColIndxsList.get(i));
			}
		}
		// adds the index of merged columns(from rhs or lhs)
		int count = 0;
		// List<RegionSummaryProjection>mergedRegionsSummary=new ArrayList<>();
		// List<RegionSummaryProjection> mergedSum= new ArrayList<>();// new table after merging
		for (VariableValuePair lhsVarValue : lhsVarValuePairs) {
			Region lhsRegion = lhsVarValue.variable;
			long lhsRowcount = lhsVarValue.rowcount;
			List<VariableValuePair> compatitbleRegions = new ArrayList<>();
			List<VariableValuePair> mergedVars = new ArrayList<>();
			boolean check = false;
			count++;
			int ind = 0;
			for (ListIterator<VariableValuePair> rhsIter = rhsVarValuePairs.listIterator(); rhsIter.hasNext();) {
				VariableValuePair rhsVarValuePair = rhsIter.next();
				Region rhsVariable = rhsVarValuePair.variable;
				long rhsRowcount = rhsVarValuePair.rowcount;
				ind++;
				// if (checkCompatibleRegions(posInLHS, lhsRegion, posInRHS, rhsVariable)) {//
				// if rhsregion is compatible
				// check = true;

				Region mergedTemp = new Region();// contains the region for the intersection of the two regions
				int totBS = 0;

				for (int i = 0; i < lhsRegion.size(); i++) {// iterate over each clause
					BucketStructure lhsBS = lhsRegion.at(i);
					int totmatch = 0;
					for (int j = 0; j < rhsVariable.size(); j++) {
						BucketStructure rhsBS = rhsVariable.at(j);
						BucketStructure mergedBS = new BucketStructure();// chceck -----------------contains the new
						// clause
						if (isCompatibleBS(posInLHS, lhsBS, posInRHS, rhsBS)) {
							totmatch++;
							totBS++;
							int counter = 0;
							for (int k = 0; k < mergedColIndxsList.size(); k++) {
								if (sharedColIndxs.size() > counter
										&& mergedColIndxsList.get(k) == sharedColIndxs.get(counter)) {
									int lhsInd = posInLHS.get(counter);
									int rhsInd = posInRHS.get(counter);
									counter++;
									Bucket inter = Bucket.getIntersection(lhsBS.at(lhsInd), rhsBS.at(rhsInd));

									mergedBS.add(inter);
								} else if (fromLHS[k]) {
									mergedBS.add(lhsBS.at(correspOriginalIndx[k]));
									// mergedColValues.add(lhsColValues.getInt(correspOriginalIndx[j]));
								} else {
									mergedBS.add(rhsBS.at(correspOriginalIndx[k]));
								}
							}
							mergedTemp.add(mergedBS);
						}

					}
				}
				if (mergedTemp.isEmpty())
					continue;
				else {
					VariableValuePair mergedVar = new VariableValuePair(mergedTemp, 0);
					compatitbleRegions.add(rhsVarValuePair);
					mergedVars.add(mergedVar);
					check = true;
				}
			}
			
			if (compatitbleRegions.size() == 0)
				throw new RuntimeException("You Failed!!!!!Couldn't find a region in rhs for lhs region:" + lhsRegion);

			mergeUniform(lhsVarValue, compatitbleRegions, mergedVars);
			mergedVarValuePairs.addAll(mergedVars);
			for (ListIterator<VariableValuePair> rhsIter = rhsVarValuePairs.listIterator(); rhsIter.hasNext();) {
				if (rhsIter.next().rowcount == 0)
					rhsIter.remove();
			}
		}
		for (VariableValuePair lhsRegion : lhsVarValuePairs) {
			if (lhsRegion.rowcount != 0)
				throw new RuntimeException(
						"Found while merge ValueCombination " + lhsRegion + " in LHS with unmet rowcount");
		}
		for (VariableValuePair var : rhsVarValuePairs) {
			if (var.rowcount != 0)
				throw new RuntimeException("Found while merge LHS variables not getting exhausted");
		}
		for (ListIterator<VariableValuePair> Iter = mergedVarValuePairs.listIterator(); Iter.hasNext();) {
			VariableValuePair var = Iter.next();
			if (var.rowcount == 0)
				Iter.remove();
			if (var.rowcount < 0) {
				System.out.println("vvp ng" + var.rowcount);
			}

		}
		// Updating targetColIndxs
		lhsColIndxs.clear();
		lhsColIndxs.addAll(mergedColIndxsList);

		lhsVarValuePairs.clear();
		lhsVarValuePairs.addAll(mergedVarValuePairs);

	}

	private void mergeUniform(VariableValuePair lhsVarValue, List<VariableValuePair> compatitbleRegions,
			List<VariableValuePair> mergedVars) {
		Long totRowcount = 0L;
		Long lhsRowcount = lhsVarValue.rowcount;
		for (VariableValuePair var : compatitbleRegions) {
			totRowcount += var.rowcount;
		}
		if (lhsRowcount > totRowcount) {
			System.out.print("tot" + lhsRowcount + " : " + totRowcount);
		}
		for (int i = 0; i < compatitbleRegions.size() - 1; i++) {
			VariableValuePair rhsvar = compatitbleRegions.get(i);
			VariableValuePair mergedVar = mergedVars.get(i);
			double ratio = rhsvar.rowcount / (double) totRowcount;

			Long card = Math.min(Math.round(ratio * lhsRowcount), lhsVarValue.rowcount);

			if (card < 0) {
				System.out.println("card " + card + "ratio :" + ratio + " lhsCount : " + lhsRowcount);
			}

			if (card > rhsvar.rowcount) {
				System.out.println("card > rhsvar.rowcount" + card + " : " + rhsvar.rowcount);
			}
			mergedVar.rowcount = card;
			if (mergedVar.rowcount < 0) {
				System.out.println("mergedVar " + mergedVar.rowcount + "card :" + card + "ratio :" + ratio
						+ " lhsCount : " + lhsRowcount);
			}
			lhsVarValue.rowcount -= card;
			rhsvar.rowcount -= card;
			if (lhsVarValue.rowcount == 0) {
				// System.out.println("lhsVarValue.rowcount : " + lhsVarValue.rowcount);
				return;
			}
			// divideCard(var,card);
		}

		VariableValuePair lastmerged = mergedVars.get(compatitbleRegions.size() - 1);
		lastmerged.rowcount = lhsVarValue.rowcount;
		if (lastmerged.rowcount < 0) {
			System.out.println("lastmerged.rowcount < 0" + lastmerged.rowcount);
		}
		VariableValuePair lastrhs = compatitbleRegions.get(compatitbleRegions.size() - 1);
		lastrhs.rowcount -= lhsVarValue.rowcount;
		lhsVarValue.rowcount = 0;

		if (lastrhs.rowcount < 0L)
			throw new RuntimeException("check mergeuniform");

	}

	private static boolean checkCompatibleRegions(IntList posInLHS, Region lhsRegion, IntList posInRHS,
			Region rhsRegion) {
		// returns true if two regions are consistent.

		for (IntIterator iterLHS = posInLHS.iterator(), iterRHS = posInRHS.iterator(); iterLHS.hasNext();) {
			int posL = iterLHS.nextInt();
			int posR = iterRHS.nextInt();
			Bucket lB = new Bucket();
			Bucket rB = new Bucket();

			for (BucketStructure bs : lhsRegion.getAll())
				lB = Bucket.union(lB, bs.at(posL));
			// lhsUnion.add(lB);
			for (BucketStructure bs : rhsRegion.getAll())
				rB = Bucket.union(rB, bs.at(posR));
			// lhsUnion.add(rB);
			if (!lB.isEqual(rB))
				return false;
		}
		return true;
	}

	private static boolean isCompatibleBS(IntList posInLHS, BucketStructure lhsBs, IntList posInRHS,
			BucketStructure rhsBs) {

		for (IntIterator iterLHS = posInLHS.iterator(), iterRHS = posInRHS.iterator(); iterLHS.hasNext();) {
			int posL = iterLHS.nextInt();
			int posR = iterRHS.nextInt();
			Bucket lB = lhsBs.at(posL);
			Bucket rB = rhsBs.at(posR);
			if (Bucket.getIntersection(lB, rB) == null)
				return false;

		}

		return true;
	}




	
	private List<LinkedList<VariableValuePair>> formulateAndSolve(List<FormalCondition> conditions,
			List<Region> conditionRegions, FormalCondition consistencyConstraints[],
			ConsistencyMakerType consistencyMakerType) {

		// TODO : remove IntExpr with their original String names in projection code
		// shadab start
		bucketSplitPoints = new ArrayList<>();
		splitPointsCount = new ArrayList<>();
		for (boolean[] allTrueB : allTrueBS) {

			List<Double> splits = new ArrayList<>();
			for (int i = 0; i < allTrueB.length; i++) {
				splits.add((double) (i));
			}
			bucketSplitPoints.add(splits);
		}
		// shadab end

		HashMap<Set<String>, Set<String>> cliquesToFKeyCoverage = new HashMap<>();

		// USed by duplication code get fkeys in each clique knowledge
		if (PostgresVConfig.fkeyToBorrowedAttr.containsKey(this.viewname)) {
			Map<String, Set<String>> fkeyToB = PostgresVConfig.fkeyToBorrowedAttr.get(this.viewname);

			for (String fkey : fkeyToB.keySet()) {
				Set<String> borrowedColumns = fkeyToB.get(fkey);
				boolean okFlag = false;
				for (Set<String> clique : arasuCliques) {

					Set<String> tempClique = new HashSet<>(borrowedColumns);
					tempClique.removeAll(clique);
					if (tempClique.isEmpty()) {
						okFlag = true;

						if (!cliquesToFKeyCoverage.containsKey(clique)) {
							cliquesToFKeyCoverage.put(clique, new HashSet<>());
						}
						cliquesToFKeyCoverage.get(clique).add(fkey);
						if (cliquesToFKeyCoverage.get(clique).size() > 1) {
							System.out.print("");
						}
						break;
					}

				}
				if (!okFlag) {
					System.out.print("");
				}
			}
		}

		StopWatch onlyReductionSW = new StopWatch("LP-OnlyReduction" + viewname);

		// STEP 1: For each clique find set of applicable conditions and call variable
		// reduction
		// modified by shadab
		List<List<FormalCondition>> cliqueToAggregateConditions = new ArrayList<>();

		List<List<Region>> cliqueToCRegions = new ArrayList<>();
		for (int i = 0; i < cliqueCount; i++) {
			LongList bvalues = new LongArrayList();
			Set<String> clique = arasuCliques.get(i); // set of columns
			System.out.println(i + "  " + clique);
			List<Region> cRegions = new ArrayList<>();

			List<FormalCondition> aggregateConditions = new ArrayList<>();
			for (int j = 0; j < conditions.size(); j++) {
				FormalCondition curCondition = conditions.get(j);
				Set<String> appearingCols = new HashSet<>();
				getAppearingCols(appearingCols, curCondition); // appearing columns will have columns appeared in
																// current condition

				if (clique.containsAll(appearingCols)) {
					cRegions.add(conditionRegions.get(j));
					bvalues.add(curCondition.getOutputCardinality());
					if (curCondition instanceof FormalConditionAggregate) {
						aggregateConditions.add(curCondition);// codeS
					}
				}

			}
			cliqueToAggregateConditions.add(aggregateConditions);
			// shadab code ends

			// Adding extra cRegion for all 1's condition
			Region allOnesCRegion = new Region();
			BucketStructure subConditionBS = new BucketStructure();
			for (int j = 0; j < allTrueBS.size(); j++) {
				Bucket bucket = new Bucket();
				for (int k = 0; k < allTrueBS.get(j).length; k++) {
					if (allTrueBS.get(j)[k]) { // Is this check needed?
						bucket.add(k);
					}
				}
				subConditionBS.add(bucket);
			}
			allOnesCRegion.add(subConditionBS);
			cRegions.add(allOnesCRegion);
			bvalues.add(relationCardinality);
			cliqueIdxtoConditionBValuesList.add(bvalues);

///////////////// Start dk
			if (consistencyMakerType == ConsistencyMakerType.CONSISTENCYFILTERS) {
				HashMap<Integer, Integer> indexKeeperForConsistency = new HashMap<>();
				int tempIndexForConsistency = 0;
				for (int j = 0; j < consistencyConstraints.length; j++) {
					FormalCondition condition = consistencyConstraints[j];
					Set<String> appearingCols = new HashSet<>();
					// changed

					getAppearingColsTemp(appearingCols, condition);
					// removeAggregateCols(appearingCols,(FormalConditionAggregate)condition);
					if (clique.containsAll(appearingCols)) {
//						System.out.println("cons const no" + j);
						indexKeeperForConsistency.put(j, tempIndexForConsistency++);
						cRegions.add(conditionRegions.get(conditions.size() + j));
					}
				}

				mappedIndexOfConsistencyConstraint.add(indexKeeperForConsistency);
			}

///////////////// End dk
			DebugHelper.printInfo("Bachaaaao!");
			DebugHelper.printInfo(viewname + " " + clique + " " + cRegions);

			Set<String> fkeysList = cliquesToFKeyCoverage.get(clique);

			Set<String> borrowedAttr = new HashSet<>();
			if (PostgresVConfig.fkeyToBorrowedAttr.containsKey(viewname) && cliquesToFKeyCoverage.containsKey(clique)) {

				Set<String> fkeys = cliquesToFKeyCoverage.get(clique);
				for (String fkey : fkeys) {
					borrowedAttr.addAll(PostgresVConfig.fkeyToBorrowedAttr.get(viewname).get(fkey));
				}

			}
			// Reducer reducer = new Reducer(allTrueBS, cRegions);
			Reducer reducer = new Reducer(allTrueBS, cRegions, borrowedAttr, clique, sortedViewColumns);
			// Map<IntList, Region> P = reducer.getMinPartition();

			// Added by Anupam for Skew Mimicking
			reducer.refineRegionsforSkewMimicking();

			// Using varIds instead of old variable regions
			List<Region> oldVarList = new ArrayList<>(); // List of regions corresponding to below labels
			List<IntList> conditionIdxsList = new ArrayList<>(); // List of labels
			reducer.getVarsAndConditionsSimplified(oldVarList, conditionIdxsList);

			Partition cliqueP = new Partition(new ArrayList<>(oldVarList));
			cliqueIdxtoPList.add(cliqueP);

			cliqueIdxtoPSimplifiedList.add(conditionIdxsList);
		}
		
		// all partitions are stored in cliqueIdxtoPList
		
		
		// code by shadab

		// generating a map from groupkey to aggregate condition having the group key
		List<Map<List<String>, List<FormalConditionAggregate>>> cliqueGroupkeyToConditions = new ArrayList<>();
		List<Map<List<String>, List<Region>>> cliqueGroupkeyToConditionRegions = new ArrayList<>();
		for (int i = 0; i < cliqueCount; i++) {
			List<FormalCondition> aggregateConditions = cliqueToAggregateConditions.get(i);// gets
																							// aggregatecondition
																							// for the current
																							// clique

			Map<List<String>, List<FormalConditionAggregate>> groupkeyToConditions = new HashMap<>();
			Map<List<String>, List<Region>> groupkeyToConditionRegion = new HashMap<>();

			for (FormalCondition condition : aggregateConditions) {

				Region cRegion = getConditionRegion(condition, allTrueBS, sortedViewColumns, bucketFloorsByColumns);
				List<String> groupKey = ((FormalConditionAggregate) condition).getGroupKey();
				if (!groupkeyToConditions.containsKey(groupKey)) {
					groupkeyToConditions.put(groupKey, new ArrayList<>());
					groupkeyToConditionRegion.put(groupKey, new ArrayList<>());
				}
				groupkeyToConditions.get(groupKey).add(((FormalConditionAggregate) condition));
				groupkeyToConditionRegion.get(groupKey).add((cRegion));

			}
			cliqueGroupkeyToConditions.add(groupkeyToConditions);
			cliqueGroupkeyToConditionRegions.add(groupkeyToConditionRegion);
		}

		long varcountDRold = 0;

		for (int i = 0; i < cliqueCount; i++) {
			varcountDRold += cliqueIdxtoPList.get(i).getAll().size();
		}
		DebugHelper.printInfo("Number of variables after double reduction before making symmetric " + varcountDRold);

		// -----------------------------Symmetric
		// RefinementStarts----------------------------------------------------
		int newRegionsCount = 0;
		int numOfUnsymmReg = 0;

		boolean areUnsymm = false;
		List<List<Region>> cliqueToNewRegions = new ArrayList<>();

		for (int i = 0; i < cliqueCount; i++) {

			List<Region> newRegions = new ArrayList<>();// contains the newly created regions after breaking of
														// unsymmetric regions
			List<Region> regionList = cliqueIdxtoPList.get(i).getAll();

			for (int j = 0; j < regionList.size(); j++) {
				Region region = regionList.get(j);
				//
//								System.out.println(
//										getTruncatedRegion(region, arasuCliquesAsColIndxs.get(i)) + "--------end check");

				for (List<String> groupKey : cliqueGroupkeyToConditions.get(i).keySet()) {

					for (int k = 0; k < cliqueGroupkeyToConditions.get(i).get(groupKey).size(); k++) {

						Region cRegion = cliqueGroupkeyToConditionRegions.get(i).get(groupKey).get(k);

						if (cRegion.contains(region)) {// if the groupkey acts on the current region, make it
														// symmetric wrt the current groupkey.
							if (!symmetryCheck(region, getColumnsIdx(groupKey))) {
								List<Region> symmRegions = makeSymmetricNew(region, getColumnsIdx(groupKey));
								newRegions.addAll(symmRegions);
								numOfUnsymmReg++;
								areUnsymm = true;
								newRegionsCount += symmRegions.size();
							}

							break;
						}
					}
				}
			}
			cliqueToNewRegions.add(newRegions);

		}
		// if (numOfUnsymmReg != 0)
		System.out.println("Number of unsymm regions" + " =" + numOfUnsymmReg);
		System.out.println("Number of broken regions" + " =" + newRegionsCount);

		long varcountDRSymRef = (areUnsymm) ? 0 : varcountDRold;
		if (areUnsymm) {// only if there are unsymmetric regions, consitency needs to done.
//							Due to the newly broken regions, the consistency boundaries along different cliques may change.
			int consistencyConstraintNum = consistencyConstraints.length;
			
			//Blackbox s
			
			for (int i = 0; i < cliqueCount; i++) {
				IntList clique1 = arasuCliquesAsColIndxs.get(i);
				for (int j = i + 1; j < cliqueCount; j++) {
					IntList common = new IntArrayList();
					common.addAll(arasuCliquesAsColIndxs.get(j));

					common.retainAll(clique1);
					if (common.isEmpty())
						continue;
//									if two cliques have common attributes then add the intervals for the new regions.
//									intervals are added so that other regions in the clique pair also split accordingly.
					for (Region reg : cliqueToNewRegions.get(i)) {
						Region currInterval = getIntervalRegion(reg, common);
						cliqueToCRegions.get(i).add(currInterval);
						cliqueToCRegions.get(j).add(currInterval);

						mappedIndexOfConsistencyConstraint.get(i).put(consistencyConstraintNum,
								mappedIndexOfConsistencyConstraint.get(i).size());
						mappedIndexOfConsistencyConstraint.get(j).put(consistencyConstraintNum,
								mappedIndexOfConsistencyConstraint.get(j).size());
						consistencyConstraintNum++;
					}

					for (Region reg : cliqueToNewRegions.get(j)) {
						Region currInterval = getIntervalRegion(reg, common);
						cliqueToCRegions.get(i).add(currInterval);
						cliqueToCRegions.get(j).add(currInterval);
						mappedIndexOfConsistencyConstraint.get(i).put(consistencyConstraintNum,
								mappedIndexOfConsistencyConstraint.get(i).size());
						mappedIndexOfConsistencyConstraint.get(j).put(consistencyConstraintNum,
								mappedIndexOfConsistencyConstraint.get(j).size());
						consistencyConstraintNum++;
					}

				}
			}

			// Domain partitioning on the basis of new regions formed after symmetry

			cliqueIdxtoPSimplifiedList.clear();
			cliqueIdxtoPList.clear();
			for (int i = 0; i < cliqueCount; i++) {
				Reducer reducer = new Reducer(allTrueBS, cliqueToCRegions.get(i));
				List<Region> oldVarList = new ArrayList<>(); // List of regions corresponding to below labels
				List<IntList> conditionIdxsList = new ArrayList<>(); // List of labels
				reducer.getVarsAndConditionsSimplified(oldVarList, conditionIdxsList);

				Partition cliqueP = new Partition(new ArrayList<>(oldVarList));
				cliqueIdxtoPList.add(cliqueP);

				cliqueIdxtoPSimplifiedList.add(conditionIdxsList);
//								for (Region reg : cliqueP.getAll()) {
//									System.out.println(getTruncatedRegion(reg, arasuCliquesAsColIndxs.get(i)) + "--------end");
//								}
			}

			for (int i = 0; i < cliqueCount; i++) {

				IntList clique1 = arasuCliquesAsColIndxs.get(i);
				for (int j = i + 1; j < cliqueCount; j++) {
					;
					IntList common = new IntArrayList();
					common.addAll(arasuCliquesAsColIndxs.get(j));
					common.retainAll(clique1);
					if (common.isEmpty())
						continue;
					List<Region> lhsRegions = cliqueIdxtoPList.get(i).getAll();
					List<Region> rhsRegions = cliqueIdxtoPList.get(j).getAll();

					for (int idx = 0; idx < lhsRegions.size(); idx++) {
						Region lhsRegion = lhsRegions.get(idx);

						boolean check = false;

						for (Region rhsRegion : rhsRegions) {
							for (int k = 0; k < lhsRegion.size(); k++) {// iterate over each clause
								BucketStructure lhsBS = lhsRegion.at(k);
								for (int l = 0; l < rhsRegion.size(); l++) {
									BucketStructure rhsBS = rhsRegion.at(l);
									if (isCompatibleBS(common, lhsBS, common, rhsBS)) {
										check = true;
										if (!isFullOverlap(common, lhsRegion, common, rhsRegion)) {
											throw new RuntimeException("partially overlapping regions!!!");
										}
										break;
									}
								}
								if (check)
									break;
							}

						}
						if (!check)
							throw new RuntimeException("Not consisitent!");
					}

				}
			}

			// need to do symmetric refinement again.
			for (int i = 0; i < cliqueCount; i++) {
				List<Region> regionList = cliqueIdxtoPList.get(i).getAll();

				for (int j = 0; j < regionList.size(); j++) {
					Region region = regionList.get(j);
//									System.out.println("check please"
//											+ getTruncatedRegion(region, arasuCliquesAsColIndxs.get(i)) + "--------end");
					for (List<String> groupKey : cliqueGroupkeyToConditions.get(i).keySet()) {

						for (int k = 0; k < cliqueGroupkeyToConditions.get(i).get(groupKey).size(); k++) {

							Region cRegion = cliqueGroupkeyToConditionRegions.get(i).get(groupKey).get(k);

							if (cRegion.contains(region)) {
								if (!symmetryCheck(region, getColumnsIdx(groupKey))) {
//													System.out.println("initial Region "
//															+ getTruncatedRegion(region, arasuCliquesAsColIndxs.get(i))
//															+ "--------end");
									List<Region> symmRegions = makeSymmetricNew(region, getColumnsIdx(groupKey));
									region = symmRegions.get(0);
									regionList.set(j, symmRegions.get(0));
									regionList.addAll(symmRegions.subList(1, symmRegions.size()));
								}
								break;
							}
						}
					}
				}
			}

			for (int i = 0; i < cliqueCount; i++) {
				varcountDRSymRef += cliqueIdxtoPList.get(i).getAll().size();
				List<Region> regionList = cliqueIdxtoPList.get(i).getAll();
				isUniverseCheck(regionList, allTrueBS); //
				// check if overlapping regions
				for (int j = 0; j < regionList.size(); j++) {
					Region reg_j = regionList.get(j); //
//									System.out
//											.println(getTruncatedRegion(reg_j, arasuCliquesAsColIndxs.get(i)) + "--------end");
					for (int k = j + 1; k < regionList.size(); k++) {
						Region reg_k = regionList.get(k); // for (Region reg : cliqueP.getAll()) { //
//										System.out.println(
//												getTruncatedRegion(reg_k, arasuCliquesAsColIndxs.get(i)) + "--------end");

						if (!(regionList.get(j).intersection(regionList.get(k)).isEmpty()))
							throw new RuntimeException("Overlapping regions!!!");
					}
				}
			}

//						---------------Construct to check consistency among cliques--------------------------
			for (int i = 0; i < cliqueCount; i++) {

				IntList clique1 = arasuCliquesAsColIndxs.get(i);
				for (int j = i + 1; j < cliqueCount; j++) {
					;
					IntList common = new IntArrayList();
					common.addAll(arasuCliquesAsColIndxs.get(j));
					common.retainAll(clique1);
					if (common.isEmpty())
						continue;
					List<Region> lhsRegions = cliqueIdxtoPList.get(i).getAll();
					List<Region> rhsRegions = cliqueIdxtoPList.get(j).getAll();

					for (int idx = 0; idx < lhsRegions.size(); idx++) {
						Region lhsRegion = lhsRegions.get(idx);

						boolean check = false;

						for (Region rhsRegion : rhsRegions) {
							for (int k = 0; k < lhsRegion.size(); k++) {// iterate over each clause
								BucketStructure lhsBS = lhsRegion.at(k);
								for (int l = 0; l < rhsRegion.size(); l++) {
									BucketStructure rhsBS = rhsRegion.at(l);
									if (isCompatibleBS(common, lhsBS, common, rhsBS)) {
										check = true;
										if (!isFullOverlap(common, lhsRegion, common, rhsRegion)) {
											throw new RuntimeException("partially overlapping regions!!!");
										}
										break;
									}
								}
								if (check)
									break;
							}

						}
						if (!check)
							throw new RuntimeException("Not consisitent!");
					}

				}
			}
//							Done checking
			
			
			List<List<IntList>> cliqueIdxtoPSimplifiedListNew = new ArrayList<>();

			for (int i = 0; i < cliqueCount; i++) {

				List<IntList> PSimplifiedListNew = new ArrayList<>();
				List<Region> regionList = cliqueIdxtoPList.get(i).getAll();

				List<Region> cRegions = cliqueToCRegions.get(i);
				for (int j = 0; j < regionList.size(); j++) {
					IntList listNew = new IntArrayList();
					Region reg = regionList.get(j);
					for (int k = 0; k < cRegions.size(); k++) {
						Region cReg = cRegions.get(k);
						if (cReg.contains(reg))
							listNew.add(k);
					}

					PSimplifiedListNew.add(listNew);

				}
				cliqueIdxtoPSimplifiedListNew.add(PSimplifiedListNew);

			}
			
			//blackbox end
			cliqueIdxtoPSimplifiedList = cliqueIdxtoPSimplifiedListNew;
			//we can now export cliqueIdxtoPSimplifiedList

			
//			List<List<Region>> cliqueIdxtoPListCompTemp = new ArrayList<>();
//			for (int i = 0; i < cliqueCount; i++) {
//
//				List<Region> PListComp = new ArrayList<>();
//				for (int idx = 0; idx < cliqueIdxtoPList.get(i).size(); idx++) {
//					Region reg = cliqueIdxtoPList.get(i).getAll().get(idx);
//
//					PListComp.add(reg);
//				}
//				cliqueIdxtoPListCompTemp.add(PListComp);
//
//			}
			/*
			 * for (int i = 0; i < cliqueCount; i++) { varcountDR +=
			 * cliqueIdxtoPList.get(i).getAll().size(); List<Region> regionList =
			 * cliqueIdxtoPList.get(i).getAll(); isUniverseCheck(regionList, allTrueBS); //
			 * check if overlapping regions for (int j = 0; j < regionList.size(); j++) {
			 * for (int k = j + 1; k < regionList.size(); k++) if
			 * (!(regionList.get(j).intersection(regionList.get(k)).isEmpty())) throw new
			 * RuntimeException("Overlapping regions!!!"); } }
			 */
		}

		DebugHelper.printInfo("Number of variables after double reduction after making symmetric " + varcountDRSymRef);

//		regionPartitioning.displayTimeAndDispose();

		// ---------------------------------Region Partitioning +Symmetric refinement
		// Done---------------
		onlyReductionSW.displayTimeAndDispose();

//		------------------------projection preprocessing starts--------------------------

		StopWatch psdSW = new StopWatch("Projection Subspace Division time for " + viewname);

		List<Map<List<String>, Map<FormalConditionAggregate, List<Integer>>>> cliqueToGroupkeyConditionToRegionIdx = new ArrayList<>();
		List<Map<List<String>, List<Integer>>> cliqueToGroupkeyToRegionIdx = new ArrayList<>();
		
		for (int i = 0; i < cliqueCount; i++) {
			Map<List<String>, Map<FormalConditionAggregate, List<Integer>>> groupkeyConditionToRegionIdx = new HashMap<>();
			Map<List<String>, List<Integer>> groupkeyToregionIdx = new HashMap<>();
			List<Region> regionList = cliqueIdxtoPList.get(i).getAll();
			for (List<String> groupKey : cliqueGroupkeyToConditions.get(i).keySet()) {
				// if(!groupkeyConditionToRegionIdx.containsKey(groupKey))
				groupkeyConditionToRegionIdx.put(groupKey, new HashMap<>());
				groupkeyToregionIdx.put(groupKey, new ArrayList<>());
				for (int k = 0; k < cliqueGroupkeyToConditions.get(i).get(groupKey).size(); k++) {
					FormalConditionAggregate condition = cliqueGroupkeyToConditions.get(i).get(groupKey).get(k);
					Region cRegion = cliqueGroupkeyToConditionRegions.get(i).get(groupKey).get(k);
					List<Integer> toAdd = new ArrayList<>();
					groupkeyConditionToRegionIdx.get(groupKey).put(condition, toAdd);
					for (int j = 0; j < regionList.size(); j++) {
						Region region = regionList.get(j);
						if (cRegion.contains(region)) {
							toAdd.add(j);
							if (!groupkeyToregionIdx.get(groupKey).contains(j))
								groupkeyToregionIdx.get(groupKey).add(j);
						}
					}
				}
			}

			cliqueToGroupkeyConditionToRegionIdx.add(groupkeyConditionToRegionIdx);
			cliqueToGroupkeyToRegionIdx.add(groupkeyToregionIdx);

		}
		//pas to region map is now available in cliqueToGroupkeyToRegionIdx
		//pas to condition to region in cliqueToGroupkeyConditionToRegionIdx
		// index to regions in cliqueIdxtoPList 
		
		
		// -------------------------preprocessimg
		// finished----------------------------------------

		List<Map<List<String>, List<ProjectionVariable>>> cliqueToGroupkeyToProjectionVariablesOptimized = new ArrayList<>(); // stores CPBs corresponding to each PAS
		List<Map<List<String>, Map<Integer, List<Integer>>>> cliqueToGroupkeyToRegionToProjectionVariablesOptimzed = new ArrayList<>();// CPBs corresponding to each regions for each PAS
		int regionsCount = 0, totalProjectionREgions = 0;

		//blackbox
		if (wantPowerset) {
			for (int i = 0; i < cliqueCount; i++) {
				Map<List<String>, List<ProjectionVariable>> groupkeyToProjectionVariables = new HashMap<>();
				Map<List<String>, Map<Integer, List<Integer>>> groupkeyToRegionToProjectionVariables = new HashMap<>();
				Map<List<String>, List<Integer>> groupkeyToregionIdx = cliqueToGroupkeyToRegionIdx.get(i);
				for (List<String> groupkey : groupkeyToregionIdx.keySet()) {
					Map<Integer, List<Integer>> regionToProjectionVariables = new HashMap<>();

					List<Integer> regionsIdx = groupkeyToregionIdx.get(groupkey);
					List<ProjectionVariable> currProjVariables = getProjectionRegions(regionsIdx,
							getColumnsIdx(groupkey), i);
					totalProjectionREgions += currProjVariables.size();
					System.out.println("For groupkeys " + groupkey + " count=" + currProjVariables.size());
					// List<ProjectionVariable> currProjVariables = new ArrayList<>();
					groupkeyToProjectionVariables.put(groupkey, currProjVariables);

					for (int j = 0; j < currProjVariables.size(); j++) {
						ProjectionVariable var = currProjVariables.get(j);
						for (Integer regionIdx : var.positive) {
							if (!regionToProjectionVariables.containsKey(regionIdx))
								regionToProjectionVariables.put(regionIdx, new ArrayList<>());
							regionToProjectionVariables.get(regionIdx).add(j);
						}
					}
					groupkeyToRegionToProjectionVariables.put(groupkey, regionToProjectionVariables);
				}
				cliqueToGroupkeyToProjectionVariablesOptimized.add(groupkeyToProjectionVariables);
				cliqueToGroupkeyToRegionToProjectionVariablesOptimzed.add(groupkeyToRegionToProjectionVariables);

			}
		}
		//blackbox end
		
		else { // cliqueQMap
			
			//blackbox start

			if (wantComplexityAnalysis) {
				for (int cliqueIndex = 0; cliqueIndex < cliqueCount; cliqueIndex++) {
					Map<List<String>, Map<FormalConditionAggregate, List<Integer>>> groupkeyConditionToRegionIdx = cliqueToGroupkeyConditionToRegionIdx
							.get(cliqueIndex);

					for (List<String> groupkey : groupkeyConditionToRegionIdx.keySet()) {
						List<Integer> projectionColumns = getColumnsIdx(groupkey);
						BucketStructure bs = new BucketStructure();

						// creates a allOnes BS for only projection columns
						for (Integer idx : projectionColumns) {
							Bucket b = new Bucket();
							int points = allTrueBS.get(idx).length;
							for (int i = 0; i < points; i++)
								b.add(i);
							bs.add(b);

						}

						// BucketStructure bsProj = bs.projectBS(projectionColumns);
						List<Integer> positions = new ArrayList<>();
						for (int i = 0; i < projectionColumns.size(); i++) {
							positions.add(0);
						}
						List<BucketStructure> intervals = getProjectionIntervals(bs, positions);
						int maxDeg = 0;
						int totEdges = 0, totVertices = 0;
						for (BucketStructure interval : intervals) {
							Region reg = new Region();
							reg.add(interval);

							Map<FormalConditionAggregate, List<Integer>> conditionToRegionIdx = groupkeyConditionToRegionIdx
									.get(groupkey);
							UndirectedGraph<String, DefaultEdge> projectionConditionGraphPerInterval = new SimpleGraph<>(
									DefaultEdge.class);

							for (FormalConditionAggregate condition : conditionToRegionIdx.keySet()) {

								List<Integer> regionsIdx = conditionToRegionIdx.get(condition);
								for (Integer regionIdx : regionsIdx) {
									Region regU = cliqueIdxtoPList.get(cliqueIndex).at(regionIdx);
									if (!projectRegion(regU, projectionColumns).intersection(reg).isEmpty())
										projectionConditionGraphPerInterval.addVertex(regionIdx.toString());
								}

//						System.out.println("region count for condition ="+countTemp);
								for (int j = 0; j < regionsIdx.size(); j++) {
									Region regU = cliqueIdxtoPList.get(cliqueIndex).at(regionsIdx.get(j));
									if (projectRegion(regU, projectionColumns).intersection(reg).isEmpty()) // if
																											// there
																											// is no
																											// intersection
																											// with
																											// the
																											// current
																											// interval
																											// then
																											// we
																											// ignore
																											// the
																											// region
										continue;
									String u = regionsIdx.get(j).toString();
									for (int k = j + 1; k < regionsIdx.size(); k++) {
										Region regV = cliqueIdxtoPList.get(cliqueIndex).at(regionsIdx.get(k));
										if (projectRegion(regV, projectionColumns).intersection(reg).isEmpty())
											continue;
										String v = regionsIdx.get(k).toString();
										if (!(projectRegion(regU, getColumnsIdx(groupkey))
												.intersection(projectRegion(regV, getColumnsIdx(groupkey))).isEmpty()))
											projectionConditionGraphPerInterval.addEdge(u, v);
									}
								}
							}
							for (String u : projectionConditionGraphPerInterval.vertexSet()) {
								int currDeg = projectionConditionGraphPerInterval.degreeOf(u);
								if (maxDeg < currDeg)
									maxDeg = currDeg;
							}

							totVertices += projectionConditionGraphPerInterval.vertexSet().size();
							totEdges += projectionConditionGraphPerInterval.edgeSet().size();

						}
						float weightedAvgDeg = (float) totEdges / totVertices;
//						System.out.println("Doing the interval " + reg);
						System.out.println("For group key=" + groupkey);
						System.out.println("Max degree=" + maxDeg);
						System.out.println("Weighted Avg degree=" + weightedAvgDeg);
//						System.out.println(
//								"Total vertices= " + projectionConditionGraphPerInterval.vertexSet().size());
//						System.out.println("Edges= " + projectionConditionGraphPerInterval.edgeSet().size());
						System.out.println("Done!!!");
					}
				}
			}
			
			//blackbox end

			//main psd begins
			
			System.out.println("Optimized variables count");
			for (int cliqueIndex = 0; cliqueIndex < cliqueCount; cliqueIndex++) {
				Map<List<String>, List<ProjectionVariable>> groupkeyToProjectionVariablesOptimized = new HashMap<>();
				Map<List<String>, Map<Integer, List<Integer>>> groupkeyToRegionToProjectionVariablesOptimzed = new HashMap<>();
				Map<List<String>, Map<FormalConditionAggregate, List<Integer>>> groupkeyConditionToRegionIdx = cliqueToGroupkeyConditionToRegionIdx
						.get(cliqueIndex);

				int maxDeg = 0;
				for (List<String> groupkey : groupkeyConditionToRegionIdx.keySet()) {
					Map<Integer, List<Integer>> regionToProjectionVariablesOptimzed = new HashMap<>();

					Map<FormalConditionAggregate, List<Integer>> conditionToRegionIdx = groupkeyConditionToRegionIdx
							.get(groupkey);
					UndirectedGraph<String, DefaultEdge> projectionConditionGraph = new SimpleGraph<>(
							DefaultEdge.class);
					// "division graph" as in paper
					
					for (FormalConditionAggregate condition : conditionToRegionIdx.keySet()) {

						List<Integer> regionsIdx = conditionToRegionIdx.get(condition);
						for (Integer regionIdx : regionsIdx) {
							projectionConditionGraph.addVertex(regionIdx.toString());

						}
//						System.out.println("region count for condition ="+countTemp);
						for (int j = 0; j < regionsIdx.size(); j++) {
							Region regU = cliqueIdxtoPList.get(cliqueIndex).at(regionsIdx.get(j));
							String u = regionsIdx.get(j).toString();
							for (int k = j + 1; k < regionsIdx.size(); k++) {
								Region regV = cliqueIdxtoPList.get(cliqueIndex).at(regionsIdx.get(k));
								String v = regionsIdx.get(k).toString();
								if (!(projectRegion(regU, getColumnsIdx(groupkey))
										.intersection(projectRegion(regV, getColumnsIdx(groupkey))).isEmpty()))
									projectionConditionGraph.addEdge(u, v);
							}
						}

						for (int i = 0; i < regionsIdx.size(); i++) {
							String u = regionsIdx.get(i).toString();
							int currDeg = projectionConditionGraph.degreeOf(u);
							if (maxDeg < currDeg)
								maxDeg = currDeg;
//							System.out.println(currDeg);
						}
					}
					for (String u : projectionConditionGraph.vertexSet()) {
						int currDeg = projectionConditionGraph.degreeOf(u);
						if (maxDeg < currDeg)
							maxDeg = currDeg;
					}

					regionsCount += projectionConditionGraph.vertexSet().size();
					System.out.println("For group key=" + groupkey);
					System.out.println("Max degree=" + maxDeg);
					System.out.println("Total vertices= " + projectionConditionGraph.vertexSet().size());
					System.out.println("Edges= " + projectionConditionGraph.edgeSet().size());

//					Call to the Opt_PSD method
					List<ProjectionVariable> varList = getProjectionVariablesOptimized(cliqueIndex,
							projectionConditionGraph, groupkey);

					System.out.println("For groupKey " + groupkey + " CPRs count=" + varList.size());
					totalProjectionREgions += varList.size();
					for (int j = 0; j < varList.size(); j++) {
						ProjectionVariable var = varList.get(j);
						for (Integer pos : var.positive) {
							if (!regionToProjectionVariablesOptimzed.containsKey(pos)) {
								regionToProjectionVariablesOptimzed.put(pos, new ArrayList<>());
							}
							regionToProjectionVariablesOptimzed.get(pos).add(j);
						}
					}
					groupkeyToRegionToProjectionVariablesOptimzed.put(groupkey, regionToProjectionVariablesOptimzed);
					groupkeyToProjectionVariablesOptimized.put(groupkey, varList);
				}
				cliqueToGroupkeyToRegionToProjectionVariablesOptimzed
						.add(groupkeyToRegionToProjectionVariablesOptimzed);
				cliqueToGroupkeyToProjectionVariablesOptimized.add(groupkeyToProjectionVariablesOptimized);

			}
		}

		DebugHelper
				.printInfo("\n\nNumber of variables after double reduction before making symmetric " + varcountDRold);
		DebugHelper.printInfo("Number of variables after double reduction after making symmetric " + varcountDRSymRef);
		System.out.println("Number of unsymm regions" + " =" + numOfUnsymmReg);
		System.out.println("Number of broken regions" + " =" + newRegionsCount);
		System.out.println("Total projection regions=" + totalProjectionREgions);
		System.out.println("Total regions being acted on by projection " + regionsCount);
		System.out.println();
		psdSW.displayTimeAndDispose();
		// --------------------------------variable formulation
		// finished-------------------------------

		StopWatch postVariableFormulationSW = new StopWatch("Post PSD " + viewname);
		
		//interval assignment for CPBs; Used for data generation
		
		for (int i = 0; i < cliqueCount; i++) {

			Map<Integer, List<Integer>> columnTofirstIntervalToProjVar = new HashMap<>();
			Map<Integer, List<Integer>> columnTofirstIntervalToProjVar1 = new HashMap<>();

			Map<List<String>, List<ProjectionVariable>> groupkeyToProjectionVariablesOptimized = cliqueToGroupkeyToProjectionVariablesOptimized
					.get(i);
			for (List<String> groupkey : groupkeyToProjectionVariablesOptimized.keySet()) {
				int colIdx = getColumnsIdx(groupkey).get(0);

				if (!columnTofirstIntervalToProjVar.containsKey(colIdx)) {
					columnTofirstIntervalToProjVar.put(colIdx,
							new ArrayList<>(Collections.nCopies(allTrueBS.get(colIdx).length, 0)));
					columnTofirstIntervalToProjVar1.put(colIdx,
							new ArrayList<>(Collections.nCopies(allTrueBS.get(colIdx).length, 0)));
				}
				List<ProjectionVariable> projectionVariablesOptimized = groupkeyToProjectionVariablesOptimized
						.get(groupkey);
				// List<List<Integer>> projectionVariablesToProjectedSubRegions = new
				// ArrayList<>();
				// Map<Integer,List<Integer>>firstIntervalToProjVar=new HashMap<>();

				for (int j = 0; j < projectionVariablesOptimized.size(); j++) {
					ProjectionVariable var = projectionVariablesOptimized.get(j);
					Region reg = var.intersection;
					int firstInterval = reg.at(0).at(0).at(0);
					columnTofirstIntervalToProjVar.get(colIdx).set(firstInterval,
							columnTofirstIntervalToProjVar.get(colIdx).get(firstInterval) + 1);

				}
			}

			for (List<String> groupkey : groupkeyToProjectionVariablesOptimized.keySet()) {
				int colIdx = getColumnsIdx(groupkey).get(0);
				List<ProjectionVariable> projectionVariablesOptimized = groupkeyToProjectionVariablesOptimized
						.get(groupkey);

				for (int j = 0; j < projectionVariablesOptimized.size(); j++) {
					ProjectionVariable var = projectionVariablesOptimized.get(j);
					Region reg = var.intersection;
					int firstInterval = reg.at(0).at(0).at(0);
					int k = columnTofirstIntervalToProjVar1.get(colIdx).get(firstInterval);
					columnTofirstIntervalToProjVar1.get(colIdx).set(firstInterval, k + 1);
					int n = columnTofirstIntervalToProjVar.get(colIdx).get(firstInterval);

					if (k != 0)
						bucketSplitPoints.get(colIdx).add(firstInterval + (double) k / n);

					RegionF interval = new RegionF();
					BucketStructureF bsF = new BucketStructureF();
					BucketF b = new BucketF();

					b.add(firstInterval + (double) k / n);
					bsF.add(b);
					BucketStructure bs = var.intersection.at(0);

					for (int l = 1; l < bs.size(); l++) {
						BucketF bTemp = new BucketF();
						bTemp.add((double) (bs.at(l).at(0)));
						bsF.add(bTemp);
					}
					interval.add(bsF);
					var.interval = interval;
				}
			}
		}

		for (List<Double> splitPoints : bucketSplitPoints)
			Collections.sort(splitPoints);
		for (List<Double> splitPoints : bucketSplitPoints) {

			List<Long> tempList = new ArrayList<>();
			for (Double temp : splitPoints)
				tempList.add(0L);
			splitPointsCount.add(tempList);
		}

		if (consistencyMakerType == ConsistencyMakerType.BRUTEFORCE) { // Further divide regions for consistency
			for (int i = 0; i < cliqueCount; i++) {
				for (int j = i + 1; j < cliqueCount; j++) {
					IntList intersectingColIndices = getIntersectionColIndices(arasuCliques.get(i),
							arasuCliques.get(j));
					if (intersectingColIndices.isEmpty()) {
						continue;
					}
					CliqueIntersectionInfo cliqueIntersectionInfo = replaceWithFreshVariablesToEnsureConsistency(
							cliqueIdxtoPList, cliqueIdxtoPSimplifiedList, i, j, intersectingColIndices);
					cliqueIntersectionInfos.add(cliqueIntersectionInfo);
				}
			}
		}

		long varcountDR = 0;
		for (int i = 0; i < cliqueCount; i++) {
			varcountDR += cliqueIdxtoPList.get(i).getAll().size();
		}
		DebugHelper.printInfo("Number of variables after double reduction " + varcountDR);
		
		//PKR
		this.consistencyMakerTypeHashmap.put(this.viewname, consistencyMakerType);
		this.cliqueToGroupkeyToRegionIdxHashmap.put(this.viewname, cliqueToGroupkeyToRegionIdx);
		this.cliqueToGroupkeyConditionToRegionIdxHashmap.put(this.viewname, cliqueToGroupkeyConditionToRegionIdx);
		this.cliqueToGroupkeyToProjectionVariablesOptimizedHashmap.put(this.viewname, cliqueToGroupkeyToProjectionVariablesOptimized);
		this.cliquesToFKeyCoverageHashmap.put(this.viewname, cliquesToFKeyCoverage);
		
		if (unifiedLP)
			return formAndSolveLPUnified(consistencyMakerType, consistencyConstraints, conditions, cliqueToGroupkeyToRegionIdx,
					cliqueToGroupkeyConditionToRegionIdx, cliqueToGroupkeyToRegionToProjectionVariablesOptimzed,
					cliqueToGroupkeyToProjectionVariablesOptimized, cliquesToFKeyCoverage);
		else
			return formAndSolveLP(consistencyMakerType, consistencyConstraints, conditions, cliqueToGroupkeyToRegionIdx,
				cliqueToGroupkeyConditionToRegionIdx, cliqueToGroupkeyToRegionToProjectionVariablesOptimzed,
				cliqueToGroupkeyToProjectionVariablesOptimized, cliquesToFKeyCoverage);
	
	}

	private HashMap<String, List<VariableValuePair>> unifiedformulateAndSolve(HashMap<String, List<List<IntList>>> viewTocliqueIdxtoPSimplifiedList, HashMap<String, List<LongList>> viewTocliqueIdxtoConditionBValuesList, HashMap<String, List<List<Double>>> viewTobucketSplitPoints, HashMap<String, HashMap<Set<String>, Set<String>>> viewTocliquesToFKeyCoverage, HashMap<String, List<Map<List<String>, List<Region>>>> viewTocliqueGroupkeyToConditionRegions, 
			HashMap<String, List<Map<List<String>, List<FormalConditionAggregate>>>> viewTocliqueGroupkeyToConditions, 
			HashMap<String, List<Partition>> viewTocliqueIdxtoPList, 
			Context unifiedctx, Optimize unifiedsolver, List<FormalCondition> conditions,
			List<Region> conditionRegions, FormalCondition consistencyConstraints[],
			ConsistencyMakerType consistencyMakerType) {

		// TODO : remove IntExpr with their original String names in projection code
		// shadab start
		bucketSplitPoints = new ArrayList<>();
		splitPointsCount = new ArrayList<>();
		for (boolean[] allTrueB : allTrueBS) {

			List<Double> splits = new ArrayList<>();
			for (int i = 0; i < allTrueB.length; i++) {
				splits.add((double) (i));
			}
			bucketSplitPoints.add(splits);
		}
		// shadab end

		HashMap<Set<String>, Set<String>> cliquesToFKeyCoverage = new HashMap<>();

		// USed by duplication code get fkeys in each clique knowledge
		if (PostgresVConfig.fkeyToBorrowedAttr.containsKey(this.viewname)) {
			Map<String, Set<String>> fkeyToB = PostgresVConfig.fkeyToBorrowedAttr.get(this.viewname);

			for (String fkey : fkeyToB.keySet()) {
				Set<String> borrowedColumns = fkeyToB.get(fkey);
				boolean okFlag = false;
				for (Set<String> clique : arasuCliques) {

					Set<String> tempClique = new HashSet<>(borrowedColumns);
					tempClique.removeAll(clique);
					if (tempClique.isEmpty()) {
						okFlag = true;

						if (!cliquesToFKeyCoverage.containsKey(clique)) {
							cliquesToFKeyCoverage.put(clique, new HashSet<>());
						}
						cliquesToFKeyCoverage.get(clique).add(fkey);
						if (cliquesToFKeyCoverage.get(clique).size() > 1) {
							System.out.print("");
						}
						break;
					}

				}
				if (!okFlag) {
					System.out.print("");
				}
			}
		}

		StopWatch onlyReductionSW = new StopWatch("LP-OnlyReduction" + viewname);

		// STEP 1: For each clique find set of applicable conditions and call variable
		// reduction
		// modified by shadab
		List<List<FormalCondition>> cliqueToAggregateConditions = new ArrayList<>();

		List<List<Region>> cliqueToCRegions = new ArrayList<>();
		for (int i = 0; i < cliqueCount; i++) {
			LongList bvalues = new LongArrayList();
			Set<String> clique = arasuCliques.get(i); // set of columns
			System.out.println(i + "  " + clique);
			List<Region> cRegions = new ArrayList<>();

			List<FormalCondition> aggregateConditions = new ArrayList<>();
			for (int j = 0; j < conditions.size(); j++) {
				FormalCondition curCondition = conditions.get(j);
				Set<String> appearingCols = new HashSet<>();
				getAppearingCols(appearingCols, curCondition); // appearing columns will have columns appeared in
																// current condition

				if (clique.containsAll(appearingCols)) {
					cRegions.add(conditionRegions.get(j));
					bvalues.add(curCondition.getOutputCardinality());
					if (curCondition instanceof FormalConditionAggregate) {
						aggregateConditions.add(curCondition);// codeS
					}
				}

			}
			cliqueToAggregateConditions.add(aggregateConditions);
			// shadab code ends

			// Adding extra cRegion for all 1's condition
			Region allOnesCRegion = new Region();
			BucketStructure subConditionBS = new BucketStructure();
			for (int j = 0; j < allTrueBS.size(); j++) {
				Bucket bucket = new Bucket();
				for (int k = 0; k < allTrueBS.get(j).length; k++) {
					if (allTrueBS.get(j)[k]) { // Is this check needed?
						bucket.add(k);
					}
				}
				subConditionBS.add(bucket);
			}
			allOnesCRegion.add(subConditionBS);
			cRegions.add(allOnesCRegion);
			bvalues.add(relationCardinality);
			cliqueIdxtoConditionBValuesList.add(bvalues);

///////////////// Start dk
			if (consistencyMakerType == ConsistencyMakerType.CONSISTENCYFILTERS) {
				HashMap<Integer, Integer> indexKeeperForConsistency = new HashMap<>();
				int tempIndexForConsistency = 0;
				for (int j = 0; j < consistencyConstraints.length; j++) {
					FormalCondition condition = consistencyConstraints[j];
					Set<String> appearingCols = new HashSet<>();
					// changed

					getAppearingColsTemp(appearingCols, condition);
					// removeAggregateCols(appearingCols,(FormalConditionAggregate)condition);
					if (clique.containsAll(appearingCols)) {
//						System.out.println("cons const no" + j);
						indexKeeperForConsistency.put(j, tempIndexForConsistency++);
						cRegions.add(conditionRegions.get(conditions.size() + j));
					}
				}

				mappedIndexOfConsistencyConstraint.add(indexKeeperForConsistency);
			}

///////////////// End dk
			DebugHelper.printInfo("Bachaaaao!");
			DebugHelper.printInfo(viewname + " " + clique + " " + cRegions);

			Set<String> fkeysList = cliquesToFKeyCoverage.get(clique);

			Set<String> borrowedAttr = new HashSet<>();
			if (PostgresVConfig.fkeyToBorrowedAttr.containsKey(viewname) && cliquesToFKeyCoverage.containsKey(clique)) {

				Set<String> fkeys = cliquesToFKeyCoverage.get(clique);
				for (String fkey : fkeys) {
					borrowedAttr.addAll(PostgresVConfig.fkeyToBorrowedAttr.get(viewname).get(fkey));
				}

			}
			// Reducer reducer = new Reducer(allTrueBS, cRegions);
			Reducer reducer = new Reducer(allTrueBS, cRegions, borrowedAttr, clique, sortedViewColumns);
			// Map<IntList, Region> P = reducer.getMinPartition();

			// Added by Anupam for Skew Mimicking
			reducer.refineRegionsforSkewMimicking();

			// Using varIds instead of old variable regions
			List<Region> oldVarList = new ArrayList<>(); // List of regions corresponding to below labels
			List<IntList> conditionIdxsList = new ArrayList<>(); // List of labels
			reducer.getVarsAndConditionsSimplified(oldVarList, conditionIdxsList);

			Partition cliqueP = new Partition(new ArrayList<>(oldVarList));
			cliqueIdxtoPList.add(cliqueP);

			cliqueIdxtoPSimplifiedList.add(conditionIdxsList);
		}

		// code by shadab

		// generating a map from groupkey to aggregate condition having the group key
		List<Map<List<String>, List<FormalConditionAggregate>>> cliqueGroupkeyToConditions = new ArrayList<>();
		List<Map<List<String>, List<Region>>> cliqueGroupkeyToConditionRegions = new ArrayList<>();
		for (int i = 0; i < cliqueCount; i++) {
			List<FormalCondition> aggregateConditions = cliqueToAggregateConditions.get(i);// gets
																							// aggregatecondition
																							// for the current
																							// clique

			Map<List<String>, List<FormalConditionAggregate>> groupkeyToConditions = new HashMap<>();
			Map<List<String>, List<Region>> groupkeyToConditionRegion = new HashMap<>();

			for (FormalCondition condition : aggregateConditions) {

				Region cRegion = getConditionRegion(condition, allTrueBS, sortedViewColumns, bucketFloorsByColumns);
				List<String> groupKey = ((FormalConditionAggregate) condition).getGroupKey();
				if (!groupkeyToConditions.containsKey(groupKey)) {
					groupkeyToConditions.put(groupKey, new ArrayList<>());
					groupkeyToConditionRegion.put(groupKey, new ArrayList<>());
				}
				groupkeyToConditions.get(groupKey).add(((FormalConditionAggregate) condition));
				groupkeyToConditionRegion.get(groupKey).add((cRegion));

			}
			cliqueGroupkeyToConditions.add(groupkeyToConditions);
			cliqueGroupkeyToConditionRegions.add(groupkeyToConditionRegion);
		}

		long varcountDRold = 0;

		for (int i = 0; i < cliqueCount; i++) {
			varcountDRold += cliqueIdxtoPList.get(i).getAll().size();
		}
		DebugHelper.printInfo("Number of variables after double reduction before making symmetric " + varcountDRold);

		// -----------------------------Symmetric
		// RefinementStarts----------------------------------------------------
		int newRegionsCount = 0;
		int numOfUnsymmReg = 0;

		boolean areUnsymm = false;
		List<List<Region>> cliqueToNewRegions = new ArrayList<>();

		for (int i = 0; i < cliqueCount; i++) {

			List<Region> newRegions = new ArrayList<>();// contains the newly created regions after breaking of
														// unsymmetric regions
			List<Region> regionList = cliqueIdxtoPList.get(i).getAll();

			for (int j = 0; j < regionList.size(); j++) {
				Region region = regionList.get(j);
				//
//								System.out.println(
//										getTruncatedRegion(region, arasuCliquesAsColIndxs.get(i)) + "--------end check");

				for (List<String> groupKey : cliqueGroupkeyToConditions.get(i).keySet()) {

					for (int k = 0; k < cliqueGroupkeyToConditions.get(i).get(groupKey).size(); k++) {

						Region cRegion = cliqueGroupkeyToConditionRegions.get(i).get(groupKey).get(k);

						if (cRegion.contains(region)) {// if the groupkey acts on the current region, make it
														// symmetric wrt the current groupkey.
							if (!symmetryCheck(region, getColumnsIdx(groupKey))) {
								List<Region> symmRegions = makeSymmetricNew(region, getColumnsIdx(groupKey));
								newRegions.addAll(symmRegions);
								numOfUnsymmReg++;
								areUnsymm = true;
								newRegionsCount += symmRegions.size();
							}

							break;
						}
					}
				}
			}
			cliqueToNewRegions.add(newRegions);

		}
		// if (numOfUnsymmReg != 0)
		System.out.println("Number of unsymm regions" + " =" + numOfUnsymmReg);
		System.out.println("Number of broken regions" + " =" + newRegionsCount);

		long varcountDRSymRef = (areUnsymm) ? 0 : varcountDRold;
		if (areUnsymm) {// only if there are unsymmetric regions, consitency needs to done.
//							Due to the newly broken regions, the consistency boundaries along diffferent cliques may change.
			int consistencyConstraintNum = consistencyConstraints.length;

			for (int i = 0; i < cliqueCount; i++) {
				IntList clique1 = arasuCliquesAsColIndxs.get(i);
				for (int j = i + 1; j < cliqueCount; j++) {
					IntList common = new IntArrayList();
					common.addAll(arasuCliquesAsColIndxs.get(j));

					common.retainAll(clique1);
					if (common.isEmpty())
						continue;
//									if two cliques have common attributes then add the intervals for the new regions.
//									intervals are added so that other regions in the clique pair also split accordingly.
					for (Region reg : cliqueToNewRegions.get(i)) {
						Region currInterval = getIntervalRegion(reg, common);
						cliqueToCRegions.get(i).add(currInterval);
						cliqueToCRegions.get(j).add(currInterval);

						mappedIndexOfConsistencyConstraint.get(i).put(consistencyConstraintNum,
								mappedIndexOfConsistencyConstraint.get(i).size());
						mappedIndexOfConsistencyConstraint.get(j).put(consistencyConstraintNum,
								mappedIndexOfConsistencyConstraint.get(j).size());
						consistencyConstraintNum++;
					}

					for (Region reg : cliqueToNewRegions.get(j)) {
						Region currInterval = getIntervalRegion(reg, common);
						cliqueToCRegions.get(i).add(currInterval);
						cliqueToCRegions.get(j).add(currInterval);
						mappedIndexOfConsistencyConstraint.get(i).put(consistencyConstraintNum,
								mappedIndexOfConsistencyConstraint.get(i).size());
						mappedIndexOfConsistencyConstraint.get(j).put(consistencyConstraintNum,
								mappedIndexOfConsistencyConstraint.get(j).size());
						consistencyConstraintNum++;
					}

				}
			}

			// Domain partitioning on the basis of new regions formed after symmetry

			cliqueIdxtoPSimplifiedList.clear();
			cliqueIdxtoPList.clear();
			for (int i = 0; i < cliqueCount; i++) {
				Reducer reducer = new Reducer(allTrueBS, cliqueToCRegions.get(i));
				List<Region> oldVarList = new ArrayList<>(); // List of regions corresponding to below labels
				List<IntList> conditionIdxsList = new ArrayList<>(); // List of labels
				reducer.getVarsAndConditionsSimplified(oldVarList, conditionIdxsList);

				Partition cliqueP = new Partition(new ArrayList<>(oldVarList));
				cliqueIdxtoPList.add(cliqueP);

				cliqueIdxtoPSimplifiedList.add(conditionIdxsList);
//								for (Region reg : cliqueP.getAll()) {
//									System.out.println(getTruncatedRegion(reg, arasuCliquesAsColIndxs.get(i)) + "--------end");
//								}
			}

			for (int i = 0; i < cliqueCount; i++) {

				IntList clique1 = arasuCliquesAsColIndxs.get(i);
				for (int j = i + 1; j < cliqueCount; j++) {
					;
					IntList common = new IntArrayList();
					common.addAll(arasuCliquesAsColIndxs.get(j));
					common.retainAll(clique1);
					if (common.isEmpty())
						continue;
					List<Region> lhsRegions = cliqueIdxtoPList.get(i).getAll();
					List<Region> rhsRegions = cliqueIdxtoPList.get(j).getAll();

					for (int idx = 0; idx < lhsRegions.size(); idx++) {
						Region lhsRegion = lhsRegions.get(idx);

						boolean check = false;

						for (Region rhsRegion : rhsRegions) {
							for (int k = 0; k < lhsRegion.size(); k++) {// iterate over each clause
								BucketStructure lhsBS = lhsRegion.at(k);
								for (int l = 0; l < rhsRegion.size(); l++) {
									BucketStructure rhsBS = rhsRegion.at(l);
									if (isCompatibleBS(common, lhsBS, common, rhsBS)) {
										check = true;
										if (!isFullOverlap(common, lhsRegion, common, rhsRegion)) {
											throw new RuntimeException("partially overlapping regions!!!");
										}
										break;
									}
								}
								if (check)
									break;
							}

						}
						if (!check)
							throw new RuntimeException("Not consisitent!");
					}

				}
			}

			// need to do symmetric refinement again.
			for (int i = 0; i < cliqueCount; i++) {
				List<Region> regionList = cliqueIdxtoPList.get(i).getAll();

				for (int j = 0; j < regionList.size(); j++) {
					Region region = regionList.get(j);
//									System.out.println("check please"
//											+ getTruncatedRegion(region, arasuCliquesAsColIndxs.get(i)) + "--------end");
					for (List<String> groupKey : cliqueGroupkeyToConditions.get(i).keySet()) {

						for (int k = 0; k < cliqueGroupkeyToConditions.get(i).get(groupKey).size(); k++) {

							Region cRegion = cliqueGroupkeyToConditionRegions.get(i).get(groupKey).get(k);

							if (cRegion.contains(region)) {
								if (!symmetryCheck(region, getColumnsIdx(groupKey))) {
//													System.out.println("initial Region "
//															+ getTruncatedRegion(region, arasuCliquesAsColIndxs.get(i))
//															+ "--------end");
									List<Region> symmRegions = makeSymmetricNew(region, getColumnsIdx(groupKey));
									region = symmRegions.get(0);
									regionList.set(j, symmRegions.get(0));
									regionList.addAll(symmRegions.subList(1, symmRegions.size()));
								}
								break;
							}
						}
					}
				}
			}

			for (int i = 0; i < cliqueCount; i++) {
				varcountDRSymRef += cliqueIdxtoPList.get(i).getAll().size();
				List<Region> regionList = cliqueIdxtoPList.get(i).getAll();
				isUniverseCheck(regionList, allTrueBS); //
				// check if overlapping regions
				for (int j = 0; j < regionList.size(); j++) {
					Region reg_j = regionList.get(j); //
//									System.out
//											.println(getTruncatedRegion(reg_j, arasuCliquesAsColIndxs.get(i)) + "--------end");
					for (int k = j + 1; k < regionList.size(); k++) {
						Region reg_k = regionList.get(k); // for (Region reg : cliqueP.getAll()) { //
//										System.out.println(
//												getTruncatedRegion(reg_k, arasuCliquesAsColIndxs.get(i)) + "--------end");

						if (!(regionList.get(j).intersection(regionList.get(k)).isEmpty()))
							throw new RuntimeException("Overlapping regions!!!");
					}
				}
			}

//						---------------Construct to check consistency among cliques--------------------------
			for (int i = 0; i < cliqueCount; i++) {

				IntList clique1 = arasuCliquesAsColIndxs.get(i);
				for (int j = i + 1; j < cliqueCount; j++) {
					;
					IntList common = new IntArrayList();
					common.addAll(arasuCliquesAsColIndxs.get(j));
					common.retainAll(clique1);
					if (common.isEmpty())
						continue;
					List<Region> lhsRegions = cliqueIdxtoPList.get(i).getAll();
					List<Region> rhsRegions = cliqueIdxtoPList.get(j).getAll();

					for (int idx = 0; idx < lhsRegions.size(); idx++) {
						Region lhsRegion = lhsRegions.get(idx);

						boolean check = false;

						for (Region rhsRegion : rhsRegions) {
							for (int k = 0; k < lhsRegion.size(); k++) {// iterate over each clause
								BucketStructure lhsBS = lhsRegion.at(k);
								for (int l = 0; l < rhsRegion.size(); l++) {
									BucketStructure rhsBS = rhsRegion.at(l);
									if (isCompatibleBS(common, lhsBS, common, rhsBS)) {
										check = true;
										if (!isFullOverlap(common, lhsRegion, common, rhsRegion)) {
											throw new RuntimeException("partially overlapping regions!!!");
										}
										break;
									}
								}
								if (check)
									break;
							}

						}
						if (!check)
							throw new RuntimeException("Not consisitent!");
					}

				}
			}
//							Done checking

			List<List<IntList>> cliqueIdxtoPSimplifiedListNew = new ArrayList<>();

			for (int i = 0; i < cliqueCount; i++) {

				List<IntList> PSimplifiedListNew = new ArrayList<>();
				List<Region> regionList = cliqueIdxtoPList.get(i).getAll();

				List<Region> cRegions = cliqueToCRegions.get(i);
				for (int j = 0; j < regionList.size(); j++) {
					IntList listNew = new IntArrayList();
					Region reg = regionList.get(j);
					for (int k = 0; k < cRegions.size(); k++) {
						Region cReg = cRegions.get(k);
						if (cReg.contains(reg))
							listNew.add(k);
					}

					PSimplifiedListNew.add(listNew);

				}
				cliqueIdxtoPSimplifiedListNew.add(PSimplifiedListNew);

			}
			cliqueIdxtoPSimplifiedList = cliqueIdxtoPSimplifiedListNew;
			
//			List<List<Region>> cliqueIdxtoPListCompTemp = new ArrayList<>();
//			for (int i = 0; i < cliqueCount; i++) {
//
//				List<Region> PListComp = new ArrayList<>();
//				for (int idx = 0; idx < cliqueIdxtoPList.get(i).size(); idx++) {
//					Region reg = cliqueIdxtoPList.get(i).getAll().get(idx);
//
//					PListComp.add(reg);
//				}
//				cliqueIdxtoPListCompTemp.add(PListComp);
//
//			}
			/*
			 * for (int i = 0; i < cliqueCount; i++) { varcountDR +=
			 * cliqueIdxtoPList.get(i).getAll().size(); List<Region> regionList =
			 * cliqueIdxtoPList.get(i).getAll(); isUniverseCheck(regionList, allTrueBS); //
			 * check if overlapping regions for (int j = 0; j < regionList.size(); j++) {
			 * for (int k = j + 1; k < regionList.size(); k++) if
			 * (!(regionList.get(j).intersection(regionList.get(k)).isEmpty())) throw new
			 * RuntimeException("Overlapping regions!!!"); } }
			 */
		}

		DebugHelper.printInfo("Number of variables after double reduction after making symmetric " + varcountDRSymRef);

//		regionPartitioning.displayTimeAndDispose();

		// ---------------------------------Region Partitioning +Symmetric refinement
		// Done---------------
		onlyReductionSW.displayTimeAndDispose();

		//PKR
		List<VariableValuePair> unifiedcliqueIdxToVarValuesList = new ArrayList<>(cliqueCount);
		HashMap<String, List<VariableValuePair>> viewtoCCMap = new HashMap<>();

		List<LinkedList<VariableValuePair>> cliqueIdxToVarValuesList = new ArrayList<>(cliqueCount);
		for (int i = 0; i < cliqueCount; i++) {

			IntList colIndxs = arasuCliquesAsColIndxs.get(i);
			Partition partition = cliqueIdxtoPList.get(i);
			LinkedList<VariableValuePair> varValuePairs = new LinkedList<>();
			List<VariableValuePair> unifiedvarValuePairs = new ArrayList<>();
			for (int j = 0; j < partition.size(); j++) {
								
				//PKR: commented "if" condition
//				if (rowcount != 0) {
					Region variable = getTruncatedRegion(partition.at(j), colIndxs);
					VariableValuePair varValuePair = new VariableValuePair(variable, 0);
					varValuePairs.add(varValuePair);
					unifiedvarValuePairs.add(varValuePair);
//				}
			}
			cliqueIdxToVarValuesList.add(varValuePairs);
			//PKR: will only work when we have only one clique
			viewtoCCMap.put(viewname, unifiedvarValuePairs);

		}
		//Maps
		viewTocliqueIdxtoPList.put(viewname,cliqueIdxtoPList);
		viewTocliqueGroupkeyToConditions.put(viewname, cliqueGroupkeyToConditions); 
		viewTocliqueGroupkeyToConditionRegions.put(viewname, cliqueGroupkeyToConditionRegions);
		viewTocliquesToFKeyCoverage.put(viewname, cliquesToFKeyCoverage);
		viewTobucketSplitPoints.put(viewname, bucketSplitPoints);
		viewTocliqueIdxtoConditionBValuesList.put(viewname, cliqueIdxtoConditionBValuesList);
		viewTocliqueIdxtoPSimplifiedList.put(viewname, cliqueIdxtoPSimplifiedList);
		
		return viewtoCCMap;
	}
		
	
//		PKR
	public HashMap<String, List<VariableValuePair>> PSD(Context unifiedctx, Optimize unifiedsolver, String viewname, Integer cliqueCount, List<Partition> cliqueIdxtoPList, 
			List<Map<List<String>, List<FormalConditionAggregate>>> cliqueGroupkeyToConditions, 
			List<Map<List<String>, List<Region>>> cliqueGroupkeyToConditionRegions, 
			ConsistencyMakerType consistencyMakerType, HashMap<Set<String>, Set<String>> cliquesToFKeyCoverage, 
			FormalConditionOr[] consistencyConstraints, List<FormalCondition> conditions, List<List<Double>> bucketSplitPoints, 
			List<LongList> cliqueIdxtoConditionBValuesList, List<List<IntList>> cliqueIdxtoPSimplifiedList) {
	
//		Broke the for loop here; PSD will start now in a different for loop
//		------------------------projection preprocessing starts--------------------------

		List<List<Long>> splitPointsCount = new ArrayList<>();

		
		StopWatch psdSW = new StopWatch("Projection Subspace Division time for " + viewname);

		List<Map<List<String>, Map<FormalConditionAggregate, List<Integer>>>> cliqueToGroupkeyConditionToRegionIdx = new ArrayList<>();
		List<Map<List<String>, List<Integer>>> cliqueToGroupkeyToRegionIdx = new ArrayList<>();

		for (int i = 0; i < cliqueCount; i++) {
			Map<List<String>, Map<FormalConditionAggregate, List<Integer>>> groupkeyConditionToRegionIdx = new HashMap<>();
			Map<List<String>, List<Integer>> groupkeyToregionIdx = new HashMap<>();
			List<Region> regionList = cliqueIdxtoPList.get(i).getAll();
			for (List<String> groupKey : cliqueGroupkeyToConditions.get(i).keySet()) {
				// if(!groupkeyConditionToRegionIdx.containsKey(groupKey))
				groupkeyConditionToRegionIdx.put(groupKey, new HashMap<>());
				groupkeyToregionIdx.put(groupKey, new ArrayList<>());
				for (int k = 0; k < cliqueGroupkeyToConditions.get(i).get(groupKey).size(); k++) {
					FormalConditionAggregate condition = cliqueGroupkeyToConditions.get(i).get(groupKey).get(k);
					Region cRegion = cliqueGroupkeyToConditionRegions.get(i).get(groupKey).get(k);
					List<Integer> toAdd = new ArrayList<>();
					groupkeyConditionToRegionIdx.get(groupKey).put(condition, toAdd);
					for (int j = 0; j < regionList.size(); j++) {
						Region region = regionList.get(j);
						if (cRegion.contains(region)) {
							toAdd.add(j);
							if (!groupkeyToregionIdx.get(groupKey).contains(j))
								groupkeyToregionIdx.get(groupKey).add(j);
						}
					}
				}
			}

			cliqueToGroupkeyConditionToRegionIdx.add(groupkeyConditionToRegionIdx);
			cliqueToGroupkeyToRegionIdx.add(groupkeyToregionIdx);

		}

		// -------------------------preprocessimg
		// finished----------------------------------------

		List<Map<List<String>, List<ProjectionVariable>>> cliqueToGroupkeyToProjectionVariablesOptimized = new ArrayList<>();
		List<Map<List<String>, Map<Integer, List<Integer>>>> cliqueToGroupkeyToRegionToProjectionVariablesOptimzed = new ArrayList<>();// same//
		int regionsCount = 0, totalProjectionREgions = 0;
		; // as
		if (wantPowerset) {
			for (int i = 0; i < cliqueCount; i++) {
				Map<List<String>, List<ProjectionVariable>> groupkeyToProjectionVariables = new HashMap<>();
				Map<List<String>, Map<Integer, List<Integer>>> groupkeyToRegionToProjectionVariables = new HashMap<>();
				Map<List<String>, List<Integer>> groupkeyToregionIdx = cliqueToGroupkeyToRegionIdx.get(i);
				for (List<String> groupkey : groupkeyToregionIdx.keySet()) {
					Map<Integer, List<Integer>> regionToProjectionVariables = new HashMap<>();

					List<Integer> regionsIdx = groupkeyToregionIdx.get(groupkey);
					List<ProjectionVariable> currProjVariables = getProjectionRegions(regionsIdx,
							getColumnsIdx(groupkey), i);
					totalProjectionREgions += currProjVariables.size();
					System.out.println("For groupkeys " + groupkey + " count=" + currProjVariables.size());
					// List<ProjectionVariable> currProjVariables = new ArrayList<>();
					groupkeyToProjectionVariables.put(groupkey, currProjVariables);

					for (int j = 0; j < currProjVariables.size(); j++) {
						ProjectionVariable var = currProjVariables.get(j);
						for (Integer regionIdx : var.positive) {
							if (!regionToProjectionVariables.containsKey(regionIdx))
								regionToProjectionVariables.put(regionIdx, new ArrayList<>());
							regionToProjectionVariables.get(regionIdx).add(j);
						}
					}
					groupkeyToRegionToProjectionVariables.put(groupkey, regionToProjectionVariables);
				}
				cliqueToGroupkeyToProjectionVariablesOptimized.add(groupkeyToProjectionVariables);
				cliqueToGroupkeyToRegionToProjectionVariablesOptimzed.add(groupkeyToRegionToProjectionVariables);

			}
		}

		else { // cliqueQMap

			if (wantComplexityAnalysis) {
				for (int cliqueIndex = 0; cliqueIndex < cliqueCount; cliqueIndex++) {
					Map<List<String>, Map<FormalConditionAggregate, List<Integer>>> groupkeyConditionToRegionIdx = cliqueToGroupkeyConditionToRegionIdx
							.get(cliqueIndex);

					for (List<String> groupkey : groupkeyConditionToRegionIdx.keySet()) {
						List<Integer> projectionColumns = getColumnsIdx(groupkey);
						BucketStructure bs = new BucketStructure();

						// creates a allOnes BS for only projection columns
						for (Integer idx : projectionColumns) {
							Bucket b = new Bucket();
							int points = allTrueBS.get(idx).length;
							for (int i = 0; i < points; i++)
								b.add(i);
							bs.add(b);

						}

						// BucketStructure bsProj = bs.projectBS(projectionColumns);
						List<Integer> positions = new ArrayList<>();
						for (int i = 0; i < projectionColumns.size(); i++) {
							positions.add(0);
						}
						List<BucketStructure> intervals = getProjectionIntervals(bs, positions);
						int maxDeg = 0;
						int totEdges = 0, totVertices = 0;
						for (BucketStructure interval : intervals) {
							Region reg = new Region();
							reg.add(interval);

							Map<FormalConditionAggregate, List<Integer>> conditionToRegionIdx = groupkeyConditionToRegionIdx
									.get(groupkey);
							UndirectedGraph<String, DefaultEdge> projectionConditionGraphPerInterval = new SimpleGraph<>(
									DefaultEdge.class);

							for (FormalConditionAggregate condition : conditionToRegionIdx.keySet()) {

								List<Integer> regionsIdx = conditionToRegionIdx.get(condition);
								for (Integer regionIdx : regionsIdx) {
									Region regU = cliqueIdxtoPList.get(cliqueIndex).at(regionIdx);
									if (!projectRegion(regU, projectionColumns).intersection(reg).isEmpty())
										projectionConditionGraphPerInterval.addVertex(regionIdx.toString());
								}

//						System.out.println("region count for condition ="+countTemp);
								for (int j = 0; j < regionsIdx.size(); j++) {
									Region regU = cliqueIdxtoPList.get(cliqueIndex).at(regionsIdx.get(j));
									if (projectRegion(regU, projectionColumns).intersection(reg).isEmpty()) // if
																											// there
																											// is no
																											// intersection
																											// with
																											// the
																											// current
																											// interval
																											// then
																											// we
																											// ignore
																											// the
																											// region
										continue;
									String u = regionsIdx.get(j).toString();
									for (int k = j + 1; k < regionsIdx.size(); k++) {
										Region regV = cliqueIdxtoPList.get(cliqueIndex).at(regionsIdx.get(k));
										if (projectRegion(regV, projectionColumns).intersection(reg).isEmpty())
											continue;
										String v = regionsIdx.get(k).toString();
										if (!(projectRegion(regU, getColumnsIdx(groupkey))
												.intersection(projectRegion(regV, getColumnsIdx(groupkey))).isEmpty()))
											projectionConditionGraphPerInterval.addEdge(u, v);
									}
								}
							}
							for (String u : projectionConditionGraphPerInterval.vertexSet()) {
								int currDeg = projectionConditionGraphPerInterval.degreeOf(u);
								if (maxDeg < currDeg)
									maxDeg = currDeg;
							}

							totVertices += projectionConditionGraphPerInterval.vertexSet().size();
							totEdges += projectionConditionGraphPerInterval.edgeSet().size();

						}
						float weightedAvgDeg = (float) totEdges / totVertices;
//						System.out.println("Doing the interval " + reg);
						System.out.println("For group key=" + groupkey);
						System.out.println("Max degree=" + maxDeg);
						System.out.println("Weighted Avg degree=" + weightedAvgDeg);
//						System.out.println(
//								"Total vertices= " + projectionConditionGraphPerInterval.vertexSet().size());
//						System.out.println("Edges= " + projectionConditionGraphPerInterval.edgeSet().size());
						System.out.println("Done!!!");
					}
				}
			}
			System.out.println("Optimized variables count");
			for (int cliqueIndex = 0; cliqueIndex < cliqueCount; cliqueIndex++) {
				Map<List<String>, List<ProjectionVariable>> groupkeyToProjectionVariablesOptimized = new HashMap<>();
				Map<List<String>, Map<Integer, List<Integer>>> groupkeyToRegionToProjectionVariablesOptimzed = new HashMap<>();
				Map<List<String>, Map<FormalConditionAggregate, List<Integer>>> groupkeyConditionToRegionIdx = cliqueToGroupkeyConditionToRegionIdx
						.get(cliqueIndex);

				int maxDeg = 0;
				for (List<String> groupkey : groupkeyConditionToRegionIdx.keySet()) {
					Map<Integer, List<Integer>> regionToProjectionVariablesOptimzed = new HashMap<>();

					Map<FormalConditionAggregate, List<Integer>> conditionToRegionIdx = groupkeyConditionToRegionIdx
							.get(groupkey);
					UndirectedGraph<String, DefaultEdge> projectionConditionGraph = new SimpleGraph<>(
							DefaultEdge.class);

					for (FormalConditionAggregate condition : conditionToRegionIdx.keySet()) {

						List<Integer> regionsIdx = conditionToRegionIdx.get(condition);
						for (Integer regionIdx : regionsIdx) {
							projectionConditionGraph.addVertex(regionIdx.toString());

						}
//						System.out.println("region count for condition ="+countTemp);
						for (int j = 0; j < regionsIdx.size(); j++) {
							Region regU = cliqueIdxtoPList.get(cliqueIndex).at(regionsIdx.get(j));
							String u = regionsIdx.get(j).toString();
							for (int k = j + 1; k < regionsIdx.size(); k++) {
								Region regV = cliqueIdxtoPList.get(cliqueIndex).at(regionsIdx.get(k));
								String v = regionsIdx.get(k).toString();
								if (!(projectRegion(regU, getColumnsIdx(groupkey))
										.intersection(projectRegion(regV, getColumnsIdx(groupkey))).isEmpty()))
									projectionConditionGraph.addEdge(u, v);
							}
						}

						for (int i = 0; i < regionsIdx.size(); i++) {
							String u = regionsIdx.get(i).toString();
							int currDeg = projectionConditionGraph.degreeOf(u);
							if (maxDeg < currDeg)
								maxDeg = currDeg;
//							System.out.println(currDeg);
						}
					}
					for (String u : projectionConditionGraph.vertexSet()) {
						int currDeg = projectionConditionGraph.degreeOf(u);
						if (maxDeg < currDeg)
							maxDeg = currDeg;
					}

					regionsCount += projectionConditionGraph.vertexSet().size();
					System.out.println("For group key=" + groupkey);
					System.out.println("Max degree=" + maxDeg);
					System.out.println("Total vertices= " + projectionConditionGraph.vertexSet().size());
					System.out.println("Edges= " + projectionConditionGraph.edgeSet().size());

//					Call to the Opt_PSD method
					List<ProjectionVariable> varList = getProjectionVariablesOptimized(cliqueIndex,
							projectionConditionGraph, groupkey);

					System.out.println("For groupKey " + groupkey + " CPRs count=" + varList.size());
					totalProjectionREgions += varList.size();
					for (int j = 0; j < varList.size(); j++) {
						ProjectionVariable var = varList.get(j);
						for (Integer pos : var.positive) {
							if (!regionToProjectionVariablesOptimzed.containsKey(pos)) {
								regionToProjectionVariablesOptimzed.put(pos, new ArrayList<>());
							}
							regionToProjectionVariablesOptimzed.get(pos).add(j);
						}
					}
					groupkeyToRegionToProjectionVariablesOptimzed.put(groupkey, regionToProjectionVariablesOptimzed);
					groupkeyToProjectionVariablesOptimized.put(groupkey, varList);
				}
				cliqueToGroupkeyToRegionToProjectionVariablesOptimzed
						.add(groupkeyToRegionToProjectionVariablesOptimzed);
				cliqueToGroupkeyToProjectionVariablesOptimized.add(groupkeyToProjectionVariablesOptimized);

			}
		}

		//PKR commented because these variables are not visible after breaking the most outer "for" loop
//		DebugHelper
//				.printInfo("\n\nNumber of variables after double reduction before making symmetric " + varcountDRold);
//		DebugHelper.printInfo("Number of variables after double reduction after making symmetric " + varcountDRSymRef);
//		System.out.println("Number of unsymm regions" + " =" + numOfUnsymmReg);
//		System.out.println("Number of broken regions" + " =" + newRegionsCount);
		System.out.println("Total projection regions=" + totalProjectionREgions);
		System.out.println("Total regions being acted on by projection " + regionsCount);
		System.out.println();
		psdSW.displayTimeAndDispose();
		// --------------------------------variable formulation
		// finished-------------------------------

		StopWatch postVariableFormulationSW = new StopWatch("Post PSD " + viewname);

		for (int i = 0; i < cliqueCount; i++) {

			Map<Integer, List<Integer>> columnTofirstIntervalToProjVar = new HashMap<>();
			Map<Integer, List<Integer>> columnTofirstIntervalToProjVar1 = new HashMap<>();

			Map<List<String>, List<ProjectionVariable>> groupkeyToProjectionVariablesOptimized = cliqueToGroupkeyToProjectionVariablesOptimized
					.get(i);
			for (List<String> groupkey : groupkeyToProjectionVariablesOptimized.keySet()) {
				int colIdx = getColumnsIdx(groupkey).get(0);

				if (!columnTofirstIntervalToProjVar.containsKey(colIdx)) {
					columnTofirstIntervalToProjVar.put(colIdx,
							new ArrayList<>(Collections.nCopies(allTrueBS.get(colIdx).length, 0)));
					columnTofirstIntervalToProjVar1.put(colIdx,
							new ArrayList<>(Collections.nCopies(allTrueBS.get(colIdx).length, 0)));
				}
				List<ProjectionVariable> projectionVariablesOptimized = groupkeyToProjectionVariablesOptimized
						.get(groupkey);
				// List<List<Integer>> projectionVariablesToProjectedSubRegions = new
				// ArrayList<>();
				// Map<Integer,List<Integer>>firstIntervalToProjVar=new HashMap<>();

				for (int j = 0; j < projectionVariablesOptimized.size(); j++) {
					ProjectionVariable var = projectionVariablesOptimized.get(j);
					Region reg = var.intersection;
					int firstInterval = reg.at(0).at(0).at(0);
					columnTofirstIntervalToProjVar.get(colIdx).set(firstInterval,
							columnTofirstIntervalToProjVar.get(colIdx).get(firstInterval) + 1);

				}
			}

			for (List<String> groupkey : groupkeyToProjectionVariablesOptimized.keySet()) {
				int colIdx = getColumnsIdx(groupkey).get(0);
				List<ProjectionVariable> projectionVariablesOptimized = groupkeyToProjectionVariablesOptimized
						.get(groupkey);

				for (int j = 0; j < projectionVariablesOptimized.size(); j++) {
					ProjectionVariable var = projectionVariablesOptimized.get(j);
					Region reg = var.intersection;
					int firstInterval = reg.at(0).at(0).at(0);
					int k = columnTofirstIntervalToProjVar1.get(colIdx).get(firstInterval);
					columnTofirstIntervalToProjVar1.get(colIdx).set(firstInterval, k + 1);
					int n = columnTofirstIntervalToProjVar.get(colIdx).get(firstInterval);

					if (k != 0)
						bucketSplitPoints.get(colIdx).add(firstInterval + (double) k / n);

					RegionF interval = new RegionF();
					BucketStructureF bsF = new BucketStructureF();
					BucketF b = new BucketF();

					b.add(firstInterval + (double) k / n);
					bsF.add(b);
					BucketStructure bs = var.intersection.at(0);

					for (int l = 1; l < bs.size(); l++) {
						BucketF bTemp = new BucketF();
						bTemp.add((double) (bs.at(l).at(0)));
						bsF.add(bTemp);
					}
					interval.add(bsF);
					var.interval = interval;
				}
			}
		}

		for (List<Double> splitPoints : bucketSplitPoints)
			Collections.sort(splitPoints);
		for (List<Double> splitPoints : bucketSplitPoints) {

			List<Long> tempList = new ArrayList<>();
			for (Double temp : splitPoints)
				tempList.add(0L);
			splitPointsCount.add(tempList);
		}

		if (consistencyMakerType == ConsistencyMakerType.BRUTEFORCE) { // Further divide regions for consistency
			for (int i = 0; i < cliqueCount; i++) {
				for (int j = i + 1; j < cliqueCount; j++) {
					IntList intersectingColIndices = getIntersectionColIndices(arasuCliques.get(i),
							arasuCliques.get(j));
					if (intersectingColIndices.isEmpty()) {
						continue;
					}
					CliqueIntersectionInfo cliqueIntersectionInfo = replaceWithFreshVariablesToEnsureConsistency(
							cliqueIdxtoPList, cliqueIdxtoPSimplifiedList, i, j, intersectingColIndices);
					cliqueIntersectionInfos.add(cliqueIntersectionInfo);
				}
			}
		}

		long varcountDR = 0;
		for (int i = 0; i < cliqueCount; i++) {
			varcountDR += cliqueIdxtoPList.get(i).getAll().size();
		}
		DebugHelper.printInfo("Number of variables after double reduction " + varcountDR);
		
		//PKR
		this.consistencyMakerTypeHashmap.put(this.viewname, consistencyMakerType);
		this.cliqueToGroupkeyToRegionIdxHashmap.put(this.viewname, cliqueToGroupkeyToRegionIdx);
		this.cliqueToGroupkeyConditionToRegionIdxHashmap.put(this.viewname, cliqueToGroupkeyConditionToRegionIdx);
		this.cliqueToGroupkeyToProjectionVariablesOptimizedHashmap.put(this.viewname, cliqueToGroupkeyToProjectionVariablesOptimized);
		this.cliquesToFKeyCoverageHashmap.put(this.viewname, cliquesToFKeyCoverage);
		
//		if (unifiedLP)
//			return formAndSolveLPUnified(consistencyMakerType, consistencyConstraints, conditions, cliqueToGroupkeyToRegionIdx,
//					cliqueToGroupkeyConditionToRegionIdx, cliqueToGroupkeyToRegionToProjectionVariablesOptimzed,
//					cliqueToGroupkeyToProjectionVariablesOptimized, cliquesToFKeyCoverage);
//		else
			return unifiedformAndSolveLP(unifiedctx, unifiedsolver, consistencyMakerType, consistencyConstraints, conditions, 
					cliqueToGroupkeyToRegionIdx,cliqueToGroupkeyConditionToRegionIdx, cliqueToGroupkeyToRegionToProjectionVariablesOptimzed,
					cliqueToGroupkeyToProjectionVariablesOptimized, cliquesToFKeyCoverage, cliqueIdxtoConditionBValuesList, cliqueIdxtoPList, cliqueIdxtoPSimplifiedList);
	
	}
	
	
	
//	--------------------------shadab methods---------------------------------------

	private List<ProjectionVariable> getProjectionVariablesOptimized(int cliqueIndex,
			UndirectedGraph<String, DefaultEdge> projectionConditionGraph, List<String> groupkey) {
		// equivalent implementation of OPT-PSD.
		List<String> nodes = new ArrayList<>(projectionConditionGraph.vertexSet());
		Collections.sort(nodes);
		List<ProjectionVariable> varList = new ArrayList<>();

		List<String> visited = new ArrayList<>();
		for (String node : nodes) {
			Region currNodeRegion = cliqueIdxtoPList.get(cliqueIndex).getAll().get(Integer.parseInt(node));
			Region currRegionProjection = projectRegion(currNodeRegion, getColumnsIdx(groupkey));
			List<String> intersectionNeighbourVisited = Graphs.neighborListOf(projectionConditionGraph, node);

			intersectionNeighbourVisited.retainAll(visited);
			ProjectionVariable var = new ProjectionVariable();
			var.positive.add(Integer.parseInt(node));
			// add the visited region in negative region only when it has an intersection
			for (String neg : intersectionNeighbourVisited) {
				Region currNeg = cliqueIdxtoPList.get(cliqueIndex).getAll().get(Integer.parseInt(neg));
				if (currRegionProjection.intersection(projectRegion(currNeg, getColumnsIdx(groupkey))).isEmpty())
					continue;
				var.negative.add(Integer.parseInt(neg));
			}
			var.intersection = currRegionProjection;
			varList.addAll(getProjectionVariablesOptimizedHelper(var, visited, projectionConditionGraph, groupkey,
					cliqueIndex));
			visited.add(node);

		}
		return varList;

	}

	private List<ProjectionVariable> getProjectionVariablesOptimizedHelper(ProjectionVariable var, List<String> visited,
			UndirectedGraph<String, DefaultEdge> projectionConditionGraph, List<String> groupkey, int cliqueIndex) {
		List<ProjectionVariable> ret = new ArrayList<>();

		String vertex = null;

		for (int i = 0; i < var.positive.size(); i++) {
			String currVertex = (var.positive.get(i)).toString();
			if (!visited.contains(currVertex)) {
				vertex = currVertex;
				break;
			}
		}
		if (vertex == null) {
			Set<String> tempNeighbours = new HashSet<>();
			for (Integer pos : var.positive)
				tempNeighbours.addAll(Graphs.neighborListOf(projectionConditionGraph, pos.toString()));
			for (Integer neg : var.negative)
				tempNeighbours.remove(neg.toString());
			for (Integer pos : var.positive)
				tempNeighbours.remove(pos.toString());

			for (String neg : tempNeighbours) {
				var.negative.add(Integer.parseInt(neg));
			}
			ret.add(var);
			return ret;
		}
		List<String> neighbours = Graphs.neighborListOf(projectionConditionGraph, vertex);
		neighbours.removeAll(visited);
		for (Integer neg : var.negative)
			neighbours.remove(neg.toString());
		for (Integer pos : var.positive)
			neighbours.remove(pos.toString());

		List<ProjectionVariable> powerSet = getPowerSetOptimized(var, neighbours, groupkey, cliqueIndex);

		for (ProjectionVariable set : powerSet) {
			List<String> currVisited = new ArrayList<>();
			currVisited.addAll(visited);
			currVisited.add(vertex);
			ret.addAll(getProjectionVariablesOptimizedHelper(set, currVisited, projectionConditionGraph, groupkey,
					cliqueIndex));
		}
		// TODO Auto-generated method stub
		return ret;
	}

	private List<ProjectionVariable> getPowerSetOptimized(ProjectionVariable var, List<String> neighbours,
			List<String> groupkey, int cliqueIndex) {

//		powerset enumeration of of the variable var wrt neighbours
		List<ProjectionVariable> ret = new ArrayList<>();
		if (neighbours.isEmpty()) {
			ret.add(var);
			return ret;
		}
		List<Integer> projectionColumnsIdx = new ArrayList<>();

		// converting col names to index
		for (String projectionColumn : groupkey) {
			projectionColumnsIdx.add(sortedViewColumns.indexOf(projectionColumn));
		}

		// check if var1 is possible
		Region currRegion = cliqueIdxtoPList.get(cliqueIndex).getAll().get(Integer.parseInt(neighbours.get(0)));
		Region projectedRegion = projectRegion(currRegion, getColumnsIdx(groupkey));

		// if there is intersection, only then the new variables must be formed
		if (!projectedRegion.intersection(var.intersection).isEmpty()) {

			ProjectionVariable var1 = new ProjectionVariable();

			var1.positive.addAll(var.positive);
			var1.negative.addAll(var.negative);

			ProjectionVariable var2 = new ProjectionVariable();
			var2.positive.addAll(var.positive);
			var2.negative.addAll(var.negative);

			var1.addPositive(Integer.parseInt(neighbours.get(0)));
			// var1.intersection = projectedRegion;bug
			var1.intersection = projectedRegion.intersection(var.intersection);

			var2.addNegative(Integer.parseInt(neighbours.get(0)));
			var2.intersection = var.intersection;

			ret.addAll(getPowerSetOptimized(var1, neighbours.subList(1, neighbours.size()), groupkey, cliqueIndex));
			ret.addAll(getPowerSetOptimized(var2, neighbours.subList(1, neighbours.size()), groupkey, cliqueIndex));
		} else {
			ret.addAll(getPowerSetOptimized(var, neighbours.subList(1, neighbours.size()), groupkey, cliqueIndex));
		}
		return ret;
	}

	private List<ProjectionVariable> getProjectionRegions(List<Integer> aggregateRegionIdx,
			List<Integer> projectionColumnsIdx, int cliqueIdx) {
//		Uses Apriori algorithm for variable generation
		List<ProjectionVariable> projectionVariableList = new ArrayList<>();// stores the final list of
																			// projection
		// variables.
		List<ProjectionVariable> prevProjectionVariableList = new ArrayList<>();
		List<Region> regionList = cliqueIdxtoPList.get(cliqueIdx).getAll();
		for (Integer regionId : aggregateRegionIdx) {
			ProjectionVariable currVar = new ProjectionVariable();
			currVar.addPositive(regionId);
//			currVar.groupkey = projectionColumns;
			currVar.intersection = projectRegion(regionList.get(regionId), projectionColumnsIdx);
			projectionVariableList.add(currVar);
			prevProjectionVariableList.add(currVar);
		}
		System.out.println(projectionVariableList.size());
		int maxLength = aggregateRegionIdx.size(); // the maximum length is upper bounded by the no. of regions(when all
													// regions intersect)_
		for (int k = 2; k <= maxLength; k++) {
			// generates k-length projection regions
			List<ProjectionVariable> currProjectionVariableList = new ArrayList<>();
			for (int i = 0; i < prevProjectionVariableList.size(); i++) {
				for (int j = i + 1; j < prevProjectionVariableList.size(); j++) {
					ProjectionVariable newVariable = areCompatible(prevProjectionVariableList.get(i),
							prevProjectionVariableList.get(j), projectionColumnsIdx, k - 1, cliqueIdx);
					if (newVariable != null) {
						currProjectionVariableList.add(newVariable);
					}
				}
			}
			prevProjectionVariableList.clear();
			prevProjectionVariableList.addAll(currProjectionVariableList);
			projectionVariableList.addAll(currProjectionVariableList);
			if (currProjectionVariableList.size() == 0)
				break;
		}

		return projectionVariableList;

	}

	private ProjectionVariable areCompatible(ProjectionVariable projectionVariable1,
			ProjectionVariable projectionVariable2, List<Integer> projectionColumnsIdx, int len, int cliqueIdx) {
		// Makes projection regions of length len+1 using 2 PRs of length len. Two PRs
		// are compatible iff their regionlist till len-1 is identical.
		List<Integer> regionList1 = projectionVariable1.positive;
		List<Integer> regionList2 = projectionVariable2.positive;

		for (int i = 0; i < len - 1; i++) {
			if (!(regionList1.get(i) == regionList2.get(i))) {

				return null;
			}
		}
		Region intersection = projectionVariable1.intersection.intersection(projectionVariable2.intersection);// take
																												// intersection
																												// of
																												// both
																												// PRs
		if (intersection.isEmpty())
			return null;
		ProjectionVariable newProjectionVariable = new ProjectionVariable();
		newProjectionVariable.positive.addAll(regionList1);
		newProjectionVariable.positive.remove(len - 1);
		// System.out.println(regionList1.get(len-1)+regionList2.get(len-1) );
		newProjectionVariable.positive.add(Math.min(regionList1.get(len - 1), regionList2.get(len - 1)));
		newProjectionVariable.positive.add(Math.max(regionList1.get(len - 1), regionList2.get(len - 1)));
		newProjectionVariable.intersection = intersection;
		return newProjectionVariable;

	}

	private IntList getColumnsIdx(List<String> groupkey) {
//		List<Integer> projectionColumnsIdx = new ArrayList<>();
		IntList projectionColumnsIdx = new IntArrayList();

		// converting col names to index
		for (String projectionColumn : groupkey) {
			projectionColumnsIdx.add(sortedViewColumns.indexOf(projectionColumn));
		}
		return projectionColumnsIdx;
	}

	private boolean symmetryCheck(Region reg, List<Integer> projectionColumns) {
//		System.out.println("in here");
		// retruns true if the region is symetric along projectionColumns
		List<Integer> nonProjectionColumns = new ArrayList<>();
		int numCol = reg.at(0).size();
		for (int i = 0; i < numCol; i++) {
			if (!projectionColumns.contains(i))
				nonProjectionColumns.add(i);
		}

//		System.out.println(
//				getTruncatedRegion(reg, arasuCliquesAsColIndxs.get(0)) + "--------end check1");
		Region projectionRegion = projectRegion(reg, projectionColumns);
		Region nonProjectionRegion = projectRegion(reg, nonProjectionColumns);
		Region crossProduct = new Region();
//		System.out.println(
//				getTruncatedRegion(reg, arasuCliquesAsColIndxs.get(0)) + "--------end check2");
		// Do cross product between the two regions.
		for (BucketStructure bsProj : projectionRegion.getAll()) {
			for (BucketStructure bsNonProj : nonProjectionRegion.getAll()) {
				BucketStructure newBS = new BucketStructure();
				for (int i = 0; i < numCol; i++)
					newBS.add(new Bucket());
				for (int i = 0; i < projectionColumns.size(); i++) {
					int col = projectionColumns.get(i);
					newBS.set(bsProj.at(i), col);
				}
				for (int i = 0; i < nonProjectionColumns.size(); i++) {
					int col = nonProjectionColumns.get(i);
					newBS.set(bsNonProj.at(i), col);
				}
				crossProduct.add(newBS);
			}
		}
//		System.out.println(
//				getTruncatedRegion(reg, arasuCliquesAsColIndxs.get(0)) + "--------end check");
		if (crossProduct.areEqual(reg))
			return true;
		return false;

	}

	private List<Region> makeSymmetricNew(Region reg, List<Integer> projectionColumns) {
		List<Region> symmetricRegions = new ArrayList<>();
		int numCol = reg.at(0).size();
		Map<BucketStructure, Region> intervalToCompatibleRegion = new HashMap<BucketStructure, Region>();
		Map<Region, Region> symmetricMap = new HashMap<>();
		List<Integer> nonProjectionColumns = new ArrayList<>();
		for (int i = 0; i < numCol; i++) {
			if (!projectionColumns.contains(i))
				nonProjectionColumns.add(i);
		}

		for (BucketStructure bs : reg.getAll()) {
			BucketStructure bsProj = bs.projectBS(projectionColumns);
			List<Integer> positions = new ArrayList<>();
			for (int i = 0; i < projectionColumns.size(); i++) {
				positions.add(0);
			}
			List<BucketStructure> intervals = getProjectionIntervals(bsProj, positions);
			for (BucketStructure interval : intervals) {
				boolean foundBS = false;
				for (Entry<BucketStructure, Region> entry : intervalToCompatibleRegion.entrySet()) {
					BucketStructure currBS = entry.getKey();
					if (currBS.areEqual(interval)) {
						foundBS = true;
						intervalToCompatibleRegion.get(interval).add(bs.projectBS(nonProjectionColumns).getDeepCopy());
						break;
					}

				}
				if (!foundBS) {
					intervalToCompatibleRegion.put(interval, new Region());
					intervalToCompatibleRegion.get(interval).add(bs.projectBS(nonProjectionColumns).getDeepCopy());
				}
			}

		}
		for (Entry<BucketStructure, Region> entry : intervalToCompatibleRegion.entrySet()) {
			compressRegions(entry.getValue());
		}
		for (Entry<BucketStructure, Region> entry : intervalToCompatibleRegion.entrySet()) {

			Region regCurr = entry.getValue();
			boolean foundReg = false;
			for (Region regTemp : symmetricMap.keySet()) {
				if (regTemp.areEqual(regCurr)) {
					foundReg = true;
					symmetricMap.get(regTemp).add(entry.getKey());
					break;
				}
			}
			if (!foundReg) {
				symmetricMap.put(regCurr, new Region());
				symmetricMap.get(regCurr).add(entry.getKey());
			}
		}
//		symmetricMap maps a non-projection subspace region to a list of BS intervals stored as regions 
//		Need to add buckets cross-product
		for (Entry<Region, Region> entry3 : symmetricMap.entrySet()) {
//			compressRegions(entry3.getValue());
			Region newRegion = new Region();
			Region projRegion = entry3.getValue();
			Region nonProjRegion = entry3.getKey();
			// Do cross product between the two regions.
			for (BucketStructure bsProj : projRegion.getAll()) {
				for (BucketStructure bsNonProj : nonProjRegion.getAll()) {
					BucketStructure newBS = new BucketStructure();
					for (int i = 0; i < numCol; i++)
						newBS.add(new Bucket());
					for (int i = 0; i < projectionColumns.size(); i++) {
						int col = projectionColumns.get(i);
						newBS.set(bsProj.at(i), col);
					}
					for (int i = 0; i < nonProjectionColumns.size(); i++) {
						int col = nonProjectionColumns.get(i);
						newBS.set(bsNonProj.at(i), col);
					}
					newRegion.add(newBS);
				}
			}
			symmetricRegions.add(newRegion);

		}
		if (symmetricRegions.size() == 1) {
			if (!symmetricRegions.get(0).areEqual(reg))
				throw new RuntimeException("Wrong symmetry!");
		} else {
//			System.out.println("broken regions");
			Region tempRegion = reg.getDeepCopy();
			Region fullRegion = new Region();
			for (Region region : symmetricRegions) {
//				System.out.println(
//						"printing" + getTruncatedRegion(region, arasuCliquesAsColIndxs.get(0)) + "--------end");
				if (!symmetryCheck(region, projectionColumns))
					throw new RuntimeException("Not symmetric after refinement!");
				if (!tempRegion.contains(region))
					throw new RuntimeException("Not a part of the old region");
				if (!region.intersection(fullRegion).isEmpty())
					throw new RuntimeException("Split regions overlap!!");
				tempRegion = tempRegion.minus(region);
				fullRegion = fullRegion.union(region);
				compressRegions(fullRegion);
			}
			if (!tempRegion.isEmpty())
				throw new RuntimeException("Wrong implementation");
			if (!fullRegion.areEqual(reg))
				throw new RuntimeException("Wrong implementation");

		}
		return symmetricRegions;
	}

	private List<BucketStructure> getProjectionIntervals(BucketStructure bs, List<Integer> positions) {
		List<BucketStructure> result = new ArrayList<>();
		BucketStructure combination = getCombination(bs, positions);
		if (!incrementPos(bs, positions, positions.size() - 1)) {
			result.add(combination);
			return result;
		}
		result = getProjectionIntervals(bs, positions);
		result.add(combination);
		return result;
	}

	private BucketStructure getCombination(BucketStructure bs, List<Integer> positions) {
		BucketStructure result = new BucketStructure();

		for (int i = 0; i < positions.size(); i++) {
			Bucket b = new Bucket();
			Integer pos = positions.get(i);
			b.add(bs.at(i).at(pos));
			result.add(b);
		}
		return result;
	}

	private boolean incrementPos(BucketStructure bs, List<Integer> positions, int i) {
		if (positions.get(i) >= bs.at(i).size() - 1) {
			if (i == 0)
				return false;
			positions.set(i, 0);
			return incrementPos(bs, positions, i - 1);
		}
//		Integer inc=positions.get(i)+1;
		positions.set(i, positions.get(i) + 1);
		return true;
	}

	public void compressRegions(Region region) {
		// Code by Subhodeep
		// Eg :Two BS having all buckets exactly same except one will be merged into 1.

		Boolean change = true;

		while (change) {
			change = false;
			for (int i = 0; i < region.size(); i++) {
				for (int j = i + 1; j < region.size(); j++) {
					if ((region.at(i).minus(region.at(j))).isEmpty() && (region.at(j).minus(region.at(i))).isEmpty()) {
						region.remove(j);
						j--;
						continue;
					}
					int index = CheckBSmergeCompatibility(region.at(i), region.at(j));
					if (index != -1) {
						mergeBS(region.at(i), region.at(j), index);
						// region.set(i,mergeBS(region.at(i), region.at(j), index));
						region.remove(j);
						j--;
						change = true;
					}
				}
			}
		}
		// if(region.size()>1)
		// System.out.print(region);
	}

	static void mergeBS(BucketStructure BS1, BucketStructure BS2, int index) {
		// 0Bucket mergedB = new Bucket(BS1.at(index));
		Bucket temp = BS1.at(index).merge(BS2.at(index));
		BS1.set(temp, index);
		// BS1.at(index).addAll(BS2.at(index));

	}

	static int CheckBSmergeCompatibility(BucketStructure BS1, BucketStructure BS2) {

		int ans_index = -1;
		int diff_count = 0;
		for (int i = 0; i < BS1.size(); i++) {
			if (!BS1.at(i).isEqual(BS2.at(i))) {
				diff_count++;
				ans_index = i;
			}
			if (diff_count > 1) {
//				More than one dimension unaligned
				return -1;
			}
		}
		if (diff_count == 1)
			return ans_index;
		return -1;
	}

	private Region getIntervalRegion(Region reg, IntList common) {
		// TODO Auto-generated method stub
		Region interval = reg.getDeepCopy();
		for (BucketStructure bs : interval.getAll()) {
			for (int i = 0; i < allTrueBS.size(); i++) {
				if (common.contains(i))
					continue;
				Bucket b = new Bucket();
				for (int j = 0; j < allTrueBS.get(i).length; j++) {
					b.add(j);
				}
				bs.at(i).clear();
				bs.at(i).addAll(b);

			}

		}
		return interval;
	}

	private Region projectRegion(Region region1, List<Integer> projectionColumnsIdx) {
//		System.out.println("start project"+
//				getTruncatedRegion(region1, arasuCliquesAsColIndxs.get(0)));
		Region result = new Region();
		result.add(region1.at(0).projectBS(projectionColumnsIdx));
		for (int i = 1; i < region1.size(); i++) {
			BucketStructure projBS = region1.at(i).projectBS(projectionColumnsIdx);
			Region temp = new Region();
			temp.add(projBS);// project the BS and create a new region to use minus method.
			result.addAll(temp.minus(result).getAll());// doing union between the two regions. A U B = A + B\A
			compressRegions(result);
		}
//		System.out.println("end project"+
//				getTruncatedRegion(region1, arasuCliquesAsColIndxs.get(0)));
		return result;
	}

	private void isUniverseCheck(List<Region> regions, List<boolean[]> allTrueBS) {
		// checks if regions cover the universe. universe setminus all regions should
		// become empty
		Region universe = new Region();
		BucketStructure subConditionBS = new BucketStructure();
		for (int j = 0; j < allTrueBS.size(); j++) {
			Bucket bucket = new Bucket();
			for (int k = 0; k < allTrueBS.get(j).length; k++) {
				if (allTrueBS.get(j)[k]) {
					bucket.add(k);
				}
			}
			subConditionBS.add(bucket);
		}
		universe.add(subConditionBS);

		for (Region region : regions) {
			universe = universe.minus(region);
		}

		if (!universe.isEmpty())
			throw new RuntimeException("Expected empty region but found non-empty");
	}

	private static boolean isFullOverlap(IntList posInLHS, Region lhsRegion, IntList posInRHS, Region rhsRegion) {


		for (IntIterator iterLHS = posInLHS.iterator(), iterRHS = posInRHS.iterator(); iterLHS.hasNext();) {
			int posL = iterLHS.nextInt();
			int posR = iterRHS.nextInt();
			Bucket lB = new Bucket();
			Bucket rB = new Bucket();

			for (BucketStructure bs : lhsRegion.getAll())
				lB = Bucket.union(lB, bs.at(posL));
			// lhsUnion.add(lB);
			for (BucketStructure bs : rhsRegion.getAll())
				rB = Bucket.union(rB, bs.at(posR));
			// lhsUnion.add(rB);
			if (!lB.isEqual(rB))//
			{
				System.out.println("Not fully overlappping");
				return false;
			}
		}
		return true;
	}

	private Region getConditionRegion(FormalCondition condition, List<boolean[]> allTrueBS, List<String> sortedColumns,
			Map<String, IntList> bucketFloorsByColumns) {

		List<FormalCondition> subconditions = getSOPSubconditions(condition);
		Region conditionRegion = new Region();

		for (FormalCondition subcondition : subconditions) { // which buckets follow this particular subcondition
			List<boolean[]> bsCopy = deepCopyBS(allTrueBS);

			// Unmarking false buckets
			setFalseAppropriateBuckets(subcondition, sortedColumns, bsCopy, bucketFloorsByColumns);// assert: every
																									// element of
																									// bucketStructures
																									// has at least one
																									// true entry

			BucketStructure subConditionBS = new BucketStructure();
			for (int j = 0; j < bsCopy.size(); j++) {
				Bucket bucket = new Bucket();
				for (int k = 0; k < bsCopy.get(j).length; k++) {
					if (bsCopy.get(j)[k]) {
						bucket.add(k); // What split points of this dimension follow this sub constraint (Important
										// Note: index of split points in bucketFloorsByColumns is being added in bucket
										// instead of split point value)
					}
				}
				subConditionBS.add(bucket); // For particular dimension
			}
			conditionRegion.add(subConditionBS); // For every subcondition in condition
		}
		return conditionRegion;
	}

	private List<FormalCondition> getSOPSubconditions(FormalCondition condition) {
		FormalConditionSOP sopCondition = new FormalConditionSOP(condition);
		return sopCondition.getConditionList();
	}

	private static void setFalseAppropriateBuckets(FormalCondition condition, List<String> sortedColumns,
			List<boolean[]> bucketStructures, Map<String, IntList> bucketFloorsByColumns) {

		if (condition instanceof FormalConditionAnd) {
			setFalseAppropriateBuckets((FormalConditionAnd) condition, sortedColumns, bucketStructures,
					bucketFloorsByColumns);
			return;
		}
		if (condition instanceof FormalConditionSimpleInt) {
			setFalseAppropriateBuckets((FormalConditionSimpleInt) condition, sortedColumns, bucketStructures,
					bucketFloorsByColumns);
			return;
		}
		throw new RuntimeException("Unsupported FormalCondition of type" + condition.getClass() + " " + condition);
	}

	private static void setFalseAppropriateBuckets(FormalConditionAnd andCondition, List<String> sortedColumns,
			List<boolean[]> bucketStructures, Map<String, IntList> bucketFloorsByColumns) {
		for (FormalCondition condition : andCondition.getConditionList()) {
			setFalseAppropriateBuckets(condition, sortedColumns, bucketStructures, bucketFloorsByColumns);
		}
	}

	private static void setFalseAppropriateBuckets(FormalConditionSimpleInt simpleCondition, List<String> sortedColumns,
			List<boolean[]> bucketStructures, Map<String, IntList> bucketFloorsByColumns) {

		String columnname = simpleCondition.getColumnname();
		int columnIndex = sortedColumns.indexOf(columnname);
		boolean[] bucketStructure = bucketStructures.get(columnIndex);
		IntList bucketFloors = bucketFloorsByColumns.get(columnname);

		Symbol symbol = simpleCondition.getSymbol();
		long val = simpleCondition.getValue();

		switch (symbol) {
		case LT:
			for (int i = bucketFloors.size() - 1; i >= 0 && bucketFloors.getInt(i) >= val; i--) {
				bucketStructure[i] = false;
			}
			break;
		case LE:
			for (int i = bucketFloors.size() - 1; i >= 0 && bucketFloors.getInt(i) > val; i--) {
				bucketStructure[i] = false;
			}
			break;
		case GT:
			for (int i = 0; i < bucketFloors.size() && bucketFloors.getInt(i) <= val; i++) {
				bucketStructure[i] = false;
			}
			break;
		case GE:
			for (int i = 0; i < bucketFloors.size() && bucketFloors.getInt(i) < val; i++) {
				bucketStructure[i] = false;
			}
			break;
		case EQ:
			for (int i = 0; i < bucketFloors.size(); i++) {
				if (bucketFloors.getInt(i) != val) {
					bucketStructure[i] = false;
				}
			}
			break;
		default:
			throw new RuntimeException("Unrecognized Symbol " + symbol);
		}
	}

	private static List<boolean[]> deepCopyBS(List<boolean[]> bucketStructures) {
		List<boolean[]> bucketStructuresCopy = new ArrayList<>();
		for (boolean[] bucketStructure : bucketStructures) {
			boolean[] bucketStructureCopy = Arrays.copyOf(bucketStructure, bucketStructure.length);
			bucketStructuresCopy.add(bucketStructureCopy);
		}
		return bucketStructuresCopy;
	}

//	shadab methods end

	private boolean checkCCSatifyRegion(Region r, Set<String> appearingCols, FormalCondition condition) {
		// TODO Auto-generated method stub
		r = getReverseMappedRegion(r);
		r = getExpandedRegion(r);
		IntList columnValues = getFloorInstantiation(r);
		ValueCombination valueCombination = new ValueCombination(columnValues, 0);// if you wish to get the
																					// valuecombination too
		List<String> sortedColumns = this.sortedViewColumns;
		if (condition instanceof FormalConditionSimpleInt
				&& meetsSimple(valueCombination, (FormalConditionSimpleInt) condition, sortedColumns)) {
			return true;
		} else if (condition instanceof FormalConditionAnd
				&& meetsAnd(valueCombination, (FormalConditionAnd) condition, sortedColumns)) {
			return true;
		} else if (condition instanceof FormalConditionOr
				&& meetsOr(valueCombination, (FormalConditionOr) condition, sortedColumns)) {
			return true;
		} else if (!(condition instanceof FormalConditionSimpleInt || condition instanceof FormalConditionAnd
				|| condition instanceof FormalConditionOr))
			throw new RuntimeException("Unrecognized condition " + condition + " of type " + condition.getClass());

		return false;
	}

	private static boolean meetsSimple(ValueCombination valueCombination, FormalConditionSimpleInt simpleCondition,
			List<String> sortedColumns) {
		String colname = simpleCondition.getColumnname();
		// String colname = PostgresVConfig.COLUMN_ID_MAP.get(columnId).getColname();
		int condValue = simpleCondition.getValue();
		Symbol symbol = simpleCondition.getSymbol();

		int colIndx = sortedColumns.indexOf(colname);
		int tupleValue = valueCombination.getColValues().getInt(colIndx);
		String colType = PostgresVConfig.columnDataTypeMap.get(colname);

		switch (symbol) {
		case EQ:
			return tupleValue == condValue;
		case LT:
			return tupleValue < condValue;
		case LE:
			return tupleValue <= condValue;
		case GT:
			return tupleValue > condValue;
		case GE:
			return tupleValue >= condValue;
		}
		throw new RuntimeException("Should not be reaching here");
	}

	private static boolean meetsAnd(ValueCombination valueCombination, FormalConditionAnd andCondition,
			List<String> sortedColumns) {
		for (FormalCondition condition : andCondition.getConditionList()) {
			if (condition instanceof FormalConditionSimpleInt
					&& !meetsSimple(valueCombination, (FormalConditionSimpleInt) condition, sortedColumns))
				return false;
			else if (condition instanceof FormalConditionAnd
					&& !meetsAnd(valueCombination, (FormalConditionAnd) condition, sortedColumns))
				return false;
			else if (condition instanceof FormalConditionOr
					&& !meetsOr(valueCombination, (FormalConditionOr) condition, sortedColumns))
				return false;
			else if (!(condition instanceof FormalConditionSimpleInt || condition instanceof FormalConditionAnd
					|| condition instanceof FormalConditionOr))
				throw new RuntimeException("Unrecognized condition " + condition + " of type " + condition.getClass());
		}
		return true;
	}

	private static boolean meetsOr(ValueCombination valueCombination, FormalConditionOr orCondition,
			List<String> sortedColumns) {
		for (FormalCondition condition : orCondition.getConditionList()) {
			if (condition instanceof FormalConditionSimpleInt
					&& meetsSimple(valueCombination, (FormalConditionSimpleInt) condition, sortedColumns))
				return true;
			else if (condition instanceof FormalConditionAnd
					&& meetsAnd(valueCombination, (FormalConditionAnd) condition, sortedColumns))
				return true;
			else if (condition instanceof FormalConditionOr
					&& meetsOr(valueCombination, (FormalConditionOr) condition, sortedColumns))
				return true;
			else if (!(condition instanceof FormalConditionSimpleInt || condition instanceof FormalConditionAnd
					|| condition instanceof FormalConditionOr))
				throw new RuntimeException("Unrecognized condition " + condition + " of type " + condition.getClass());
		}
		return false;
	}

	public List<LinkedList<VariableValuePair>> formAndSolveLP(ConsistencyMakerType consistencyMakerType,
			FormalCondition[] consistencyConstraints, List<FormalCondition> conditions,
			List<Map<List<String>, List<Integer>>> cliqueToGroupkeyToRegionIdx,
			List<Map<List<String>, Map<FormalConditionAggregate, List<Integer>>>> cliqueToGroupkeyConditionToRegionIdx,
			List<Map<List<String>, Map<Integer, List<Integer>>>> cliqueToGroupkeyToRegionToProjectionVariablesOptimzed,
			List<Map<List<String>, List<ProjectionVariable>>> cliqueToGroupkeyToProjectionVariablesOptimized,
			HashMap<Set<String>, Set<String>> cliquesToFKeyCoverage) {

		// Map<String, String> contextmaptest = new HashMap<>();
		// contextmaptest.put("model", "true");
		// contextmaptest.put("unsat_core", "true");
		// Context ctxtest = new Context(contextmaptest);
		//
		// Optimize osolver = ctxtest.mkOptimize();
		// IntExpr x = ctxtest.mkIntConst("x");
		// IntExpr y = ctxtest.mkIntConst("y");
		// ArithExpr arithexpr = ctxtest.mkAdd(x, y);
		// osolver.Add(ctxtest.mkGt(arithexpr, ctxtest.mkInt(10)));
		// osolver.Add(ctxtest.mkLt(arithexpr, ctxtest.mkInt(20)));
		//
		// osolver.MkMaximize(arithexpr);
		//
		// osolver.Check();
		//
		// Model modeltest = osolver.getModel();
		// System.out.println(modeltest.evaluate(x, true) + " : " +
		// modeltest.evaluate(y, true));
		///////////////// End dk

		StopWatch onlyFormationSW = new StopWatch("LP-OnlyFormation" + viewname);

		Map<String, String> contextmap = new HashMap<>();
		contextmap.put("model", "true");
		contextmap.put("unsat_core", "true");
		Context ctx = new Context(contextmap);

		Optimize solver = ctx.mkOptimize();
		int projectionVarsIndex = 0;
		int type1 = 0, type2 = 0, type3 = 0, projectionCC = 0, filterCC = 0, consistencyCC = 0;
		List<List<List<IntExpr>>> solverConstraintsRequiredForConsistency = new ArrayList<>();
		// Create lp variables for cardinality constraints
		for (int cliqueIndex = 0; cliqueIndex < cliqueCount; cliqueIndex++) {

			LongList bvalues = cliqueIdxtoConditionBValuesList.get(cliqueIndex);
			Partition partition = cliqueIdxtoPList.get(cliqueIndex); // Partition is a list of regions corresponding to
																		// below labels
			List<IntList> conditionIdxsList = cliqueIdxtoPSimplifiedList.get(cliqueIndex); // Getting label

			HashMap<Integer, Integer> indexKeeper = null;
			int solverConstraintSize;

			if (consistencyMakerType == ConsistencyMakerType.CONSISTENCYFILTERS) {
				if (cliqueCount > 1) {
					indexKeeper = mappedIndexOfConsistencyConstraint.get(cliqueIndex);
					solverConstraintSize = bvalues.size() + indexKeeper.size();
				} else
					solverConstraintSize = bvalues.size();
			} else {
				indexKeeper = new HashMap<>();
				solverConstraintSize = bvalues.size() + cliqueWiseTotalSingleSplitPointRegions.get(cliqueIndex);
			}

			List<List<IntExpr>> solverConstraints = new ArrayList<>(solverConstraintSize);
			for (int j = 0; j < solverConstraintSize; j++) {
				solverConstraints.add(new ArrayList<>());
			}

			for (int blockIndex = 0; blockIndex < partition.size(); blockIndex++) {
				String varname = "var" + cliqueIndex + "_" + blockIndex;
				solverStats.solverVarCount++;

				// Adding non-negativity constraints
				solver.Add(ctx.mkGe(ctx.mkIntConst(varname), ctx.mkInt(0)));
				type1++;
				// Adds the region to all the constraints it belongs to
				for (IntIterator iter = conditionIdxsList.get(blockIndex).iterator(); iter.hasNext();) {
					int k = iter.nextInt();

					solverConstraints.get(k).add(ctx.mkIntConst(varname));
				}

			}
			// Adding filter constraints
			for (int conditionIndex = 0; conditionIndex < bvalues.size(); conditionIndex++) {
				long outputCardinality = bvalues.getLong(conditionIndex);
				List<IntExpr> addList = solverConstraints.get(conditionIndex);
				solver.Add(ctx.mkEq(ctx.mkAdd(addList.toArray(new ArithExpr[addList.size()])),
						ctx.mkInt(outputCardinality)));
				filterCC++;
				solverStats.solverConstraintCount++;
			}

//			---------------shadab----adding projection constraints-----------------------------

			Map<List<String>, List<ProjectionVariable>> groupkeyToProjectionVariablesOptimized = cliqueToGroupkeyToProjectionVariablesOptimized
					.get(cliqueIndex);

			for (List<String> groupkey : groupkeyToProjectionVariablesOptimized.keySet()) {
				String groupkeyStr = toStringFunc(groupkey);
				List<ProjectionVariable> projectionVariablesOptimized = groupkeyToProjectionVariablesOptimized
						.get(groupkey);
				for (int j = 0; j < projectionVariablesOptimized.size(); j++) {
					String varname = "y" + cliqueIndex + "_" + groupkeyStr + "_"
							+ projectionVariablesOptimized.get(j).toString();
					solver.Add(ctx.mkGe(ctx.mkIntConst(varname), ctx.mkInt(0)));
					type1++;

				}
			}

			Map<List<String>, Map<Integer, List<Integer>>> groupkeyToRegionToProjectionVariablesOptimzed = cliqueToGroupkeyToRegionToProjectionVariablesOptimzed
					.get(cliqueIndex);

			for (List<String> groupkey : groupkeyToRegionToProjectionVariablesOptimzed.keySet()) {
				String groupkeyStr = toStringFunc(groupkey);

				List<ProjectionVariable> projectionVariablesOptimized = groupkeyToProjectionVariablesOptimized
						.get(groupkey);
				Map<Integer, List<Integer>> regionToProjectionVariablesOptimized = groupkeyToRegionToProjectionVariablesOptimzed
						.get(groupkey);
				for (Integer regionIdx : regionToProjectionVariablesOptimized.keySet()) {
					String varname = "var" + cliqueIndex + "_" + regionIdx;
					List<IntExpr> projectionExpr = new ArrayList<>();
					for (Integer projVarIndx : regionToProjectionVariablesOptimized.get(regionIdx)) {
						projectionExpr.add(ctx.mkIntConst("y" + cliqueIndex + "_" + groupkeyStr + "_"
								+ projectionVariablesOptimized.get(projVarIndx).toString()));
					}

					if (!datasynthcomp) {
						solver.Add(
								ctx.mkGe(
										ctx.mkMul(ctx.mkInt(relationCardinality),
												ctx.mkAdd(
														projectionExpr.toArray(new ArithExpr[projectionExpr.size()]))),
										ctx.mkIntConst(varname)));
						type3++;
					}
					solver.Add(ctx.mkLe(ctx.mkAdd(projectionExpr.toArray(new ArithExpr[projectionExpr.size()])),
							ctx.mkIntConst(varname)));
					type2++;
				}
			}

			Map<List<String>, Map<FormalConditionAggregate, List<Integer>>> groupkeyConditionToRegionIdx = cliqueToGroupkeyConditionToRegionIdx
					.get(cliqueIndex);
			for (List<String> groupkey : groupkeyConditionToRegionIdx.keySet()) {
				String groupkeyStr = toStringFunc(groupkey);
				List<ProjectionVariable> projectionVariablesOptimized = groupkeyToProjectionVariablesOptimized
						.get(groupkey);

				Map<Integer, List<Integer>> regionsToProjectionVariables = cliqueToGroupkeyToRegionToProjectionVariablesOptimzed
						.get(cliqueIndex).get(groupkey);
				Map<FormalConditionAggregate, List<Integer>> conditionToRegionIdx = groupkeyConditionToRegionIdx
						.get(groupkey);
				for (FormalConditionAggregate condition : conditionToRegionIdx.keySet()) {
					List<IntExpr> projectionExpr = new ArrayList<>();
					List<Integer> regionsIdx = conditionToRegionIdx.get(condition);
					Set<Integer> projectionVariablesIdx = new HashSet<>();
					for (Integer regionIdx : regionsIdx) {
						projectionVariablesIdx.addAll(regionsToProjectionVariables.get(regionIdx));
					}

					// nonOverlappingSanityCheck(projectionVariablesIdx,projectionVariablesOptimized);

					for (Integer projectionVariableIdx : projectionVariablesIdx)
						projectionExpr.add(ctx.mkIntConst("y" + cliqueIndex + "_" + groupkeyStr + "_"
								+ projectionVariablesOptimized.get(projectionVariableIdx).toString()));
					solver.Add(ctx.mkEq(ctx.mkAdd(projectionExpr.toArray(new ArithExpr[projectionExpr.size()])),
							ctx.mkInt(condition.getProjectionCardinality())));
					projectionCC++;
				}
			}

			///////////////// Start dk
			if (cliqueCount > 1 && consistencyMakerType == ConsistencyMakerType.CONSISTENCYFILTERS) {
				List<List<IntExpr>> solverConstraintsToExport = new ArrayList<>(indexKeeper.size());
				for (int j = bvalues.size(); j < solverConstraintSize; j++) {
					solverConstraintsToExport.add(solverConstraints.get(j));
				}
				solverConstraintsToExport.add(solverConstraints.get(bvalues.size() - 1)); // Clique size
				solverConstraintsRequiredForConsistency.add(solverConstraintsToExport);
			}
		}

		// Consistency

		int countConsistencyConstraint = 0;
		if (cliqueCount > 1) {// TODO is necessary?
			if (consistencyMakerType == ConsistencyMakerType.CONSISTENCYFILTERS) {

				if (consistencyConstraints.length != 0) {
					for (int c1index = 0; c1index < cliqueCount; c1index++) {
						HashMap<Integer, Integer> c1indexKeeper = mappedIndexOfConsistencyConstraint.get(c1index);
						if (c1indexKeeper.isEmpty())
							continue;
						List<List<IntExpr>> c1solverConstraints = solverConstraintsRequiredForConsistency.get(c1index);
						for (int c2index = c1index + 1; c2index < cliqueCount; c2index++) {
							HashMap<Integer, Integer> c2indexKeeper = mappedIndexOfConsistencyConstraint.get(c2index);
							if (c2indexKeeper.isEmpty())
								continue;
							List<List<IntExpr>> c2solverConstraints = solverConstraintsRequiredForConsistency
									.get(c2index);
							Set<Integer> applicableConsistencyConstraints = new HashSet<>(c1indexKeeper.keySet());
							applicableConsistencyConstraints.retainAll(c2indexKeeper.keySet());
							if (applicableConsistencyConstraints.isEmpty())
								continue;
							List<List<IntExpr>> c1ApplicableSolverConstraints = new ArrayList<>();
							List<List<IntExpr>> c2ApplicableSolverConstraints = new ArrayList<>();
							for (Integer originalConsistencyConstraintIndex : applicableConsistencyConstraints) {
								c1ApplicableSolverConstraints.add(
										c1solverConstraints.get(c1indexKeeper.get(originalConsistencyConstraintIndex)));
								c2ApplicableSolverConstraints.add(
										c2solverConstraints.get(c2indexKeeper.get(originalConsistencyConstraintIndex)));
							}

							c1ApplicableSolverConstraints.add(c1solverConstraints.get(c1solverConstraints.size() - 1));
							c2ApplicableSolverConstraints.add(c2solverConstraints.get(c2solverConstraints.size() - 1));

							HashMap<IntList, MutablePair<List<IntExpr>, List<IntExpr>>> conditionListToPairOfVarList = new HashMap<>();
							addTo_ConditionListToPairOfVarList(c1ApplicableSolverConstraints,
									conditionListToPairOfVarList);
							addTo_ConditionListToPairOfVarList(c2ApplicableSolverConstraints,
									conditionListToPairOfVarList);

							// Set<String> commonCols = new HashSet<>(arasuCliques.get(c1index));
							// commonCols.retainAll(arasuCliques.get(c2index));

							for (MutablePair<List<IntExpr>, List<IntExpr>> pair : conditionListToPairOfVarList
									.values()) {
								List<IntExpr> c1Set = pair.getFirst();
								List<IntExpr> c2Set = pair.getSecond();
								ArithExpr set1expr = ctx.mkAdd(c1Set.toArray(new ArithExpr[c1Set.size()]));
								ArithExpr set2expr = ctx.mkAdd(c2Set.toArray(new ArithExpr[c2Set.size()]));
								solver.Add(ctx.mkEq(set1expr, set2expr));
								consistencyCC++;
								countConsistencyConstraint++;

								// 1-D projection
								// collectProjectionConsistencyData(solver,ctx, c1Set, c2Set, c1index, c2index,
								// commonCols, projectionConsistencyInfoPairs, cliqueWColumnWProjectionStuff);
							}
						}
					}
				}
			}
			///////////////// End dk

			else if (consistencyMakerType == ConsistencyMakerType.BRUTEFORCE) {
				for (CliqueIntersectionInfo cliqueIntersectionInfo : cliqueIntersectionInfos) { // Create lp variables
																								// for
																								// consistency
																								// constraints

					int i = cliqueIntersectionInfo.i;
					int j = cliqueIntersectionInfo.j;
					IntList intersectingColIndices = cliqueIntersectionInfo.intersectingColIndices;

					Partition partitionI = cliqueIdxtoPList.get(i);
					Partition partitionJ = cliqueIdxtoPList.get(j);

					// Recomputing SplitRegions for every pair of intersecting cliques
					// as the SplitRegions might have become more granular due to
					// some other pair of intersecting cliques having its intersectingColIndices
					// overlapping with this pair's intersectingColIndices
					List<Region> splitRegions = getSplitRegions(partitionI, partitionJ, intersectingColIndices);

					Set<String> commonCols = new HashSet<>(arasuCliques.get(i));
					commonCols.retainAll(arasuCliques.get(j));

					for (Region splitRegion : splitRegions) {
						List<IntExpr> consistencyLHS = new ArrayList<>();
						for (int k = 0; k < partitionI.size(); k++) {
							Region iVar = partitionI.at(k);

							Region truncRegion = getTruncatedRegion(iVar, intersectingColIndices);
							Region truncOverlap = truncRegion.intersection(splitRegion);
							if (!truncOverlap.isEmpty()) {
								String varname = "var" + i + "_" + k;
								consistencyLHS.add(ctx.mkIntConst(varname));
							}
						}

						List<IntExpr> consistencyRHS = new ArrayList<>();
						for (int k = 0; k < partitionJ.size(); k++) {
							Region jVar = partitionJ.at(k);

							Region truncRegion = getTruncatedRegion(jVar, intersectingColIndices);
							Region truncOverlap = truncRegion.intersection(splitRegion);
							if (!truncOverlap.isEmpty()) {
								String varname = "var" + j + "_" + k;
								consistencyRHS.add(ctx.mkIntConst(varname));
							}
						}

						// Adding consistency constraints
						solver.Add(ctx.mkEq(ctx.mkAdd(consistencyLHS.toArray(new ArithExpr[consistencyLHS.size()])),
								ctx.mkAdd(consistencyRHS.toArray(new ArithExpr[consistencyRHS.size()]))));
						solverStats.solverConstraintCount++;
						countConsistencyConstraint++;

					}
				}
			} else {
				ctx.close();
				throw new RuntimeException("Unknown consistency maker " + consistencyMakerType);
			}
		}
		DebugHelper.printInfo("countConsistencyConstraint for " + viewname + " = " + countConsistencyConstraint);

		List<String> allIntervalRegions = new ArrayList<>(); // List of all intervals
		List<String> allIntervalisedRegions = new ArrayList<>(); // List of all intervalised regions
		List<String> allDxValues = new ArrayList<>();

		if (PostgresVConfig.hydraVersions.contains(PostgresVConfig.HydraTypes.duplicationHydra)) {

			// New variables
			Map<String, List<String>> allIntervalRegionsVariables = new HashMap<>();
			Map<String, List<String>> allDxValuesVariables = new HashMap<>();
			Map<String, List<String>> allIntervalisedRegionsVariables = new HashMap<>();
			Map<String, HashMap<String, List<Integer>>> varToIntervalMapPerFKey = new HashMap<>();

			if (PostgresVConfig.fkeyToBorrowedAttr.containsKey(viewname)) {

				Map<String, Set<String>> fkeyToBorrowedAttr = PostgresVConfig.fkeyToBorrowedAttr.get(viewname);

				for (String fkey : fkeyToBorrowedAttr.keySet()) {

					allIntervalRegionsVariables.put(fkey, new ArrayList<>());
					allDxValuesVariables.put(fkey, new ArrayList<>());
					allIntervalisedRegionsVariables.put(fkey, new ArrayList<>());
					varToIntervalMapPerFKey.put(fkey, new HashMap<>());
					Set<String> currentClique = null;
					Integer currentCliqueIdx = null;

					for (int c = 0; c < this.arasuCliques.size(); c++) {
						Set<String> clique = this.arasuCliques.get(c);
						if (!cliquesToFKeyCoverage.containsKey(clique)) {
							continue;
						}
						Set<String> fkeysCovered = cliquesToFKeyCoverage.get(clique);
						if (fkeysCovered.contains(fkey)) {
							currentClique = clique;
							currentCliqueIdx = c;
							break;
						}

					}

					if (currentClique == null) {
						throw new RuntimeException("Something wrong can't be possible");
					}

					fkeyToCliqueIdx.put(fkey, currentCliqueIdx);

					Set<String> borrowedAttr = fkeyToBorrowedAttr.get(fkey);
					List<String> sortedBorrowedAttr = new ArrayList<>(borrowedAttr);
					List<Integer> borrowedAttrIdx = new ArrayList<>();
					Collections.sort(sortedBorrowedAttr);
					int c = 0;
					for (int i = 0; i < sortedViewColumns.size(); i++) {

						if (sortedBorrowedAttr.get(c).contentEquals(sortedViewColumns.get(i))) {

							borrowedAttrIdx.add(i);
							c = c + 1;
						}
						if (c == sortedBorrowedAttr.size()) {
							break;
						}

					}

					int noOfIntervalRegions = 1;
					List<List<Integer>> borrowedAttrIntervals = new ArrayList<>();
					Partition partition = cliqueIdxtoPList.get(currentCliqueIdx);
					for (int bucket : borrowedAttrIdx) {

						Set<Integer> intervals = new HashSet<>();
						for (Region r : partition.getAll()) {

							for (BucketStructure bs : r.getAll()) {

								intervals.addAll((bs.at(bucket).getAll()));

							}

						}
						noOfIntervalRegions *= intervals.size();
						ArrayList<Integer> intervalsList = new ArrayList<>(intervals);
						Collections.sort(intervalsList);
						borrowedAttrIntervals.add(intervalsList);

					}

					List<List<Integer>> intervalRegions = new ArrayList<>();
					for (int i = 0; i < noOfIntervalRegions; i++) {

						intervalRegions.add(new ArrayList<>());
					}

					int count = 0;
					int row = 0;
					while (count < noOfIntervalRegions) {

						int currentRowSize = borrowedAttrIntervals.get(row).size();

						if (count > 0) {

							int currentIndex = 0;
							List<List<Integer>> copyofIntervalRegionList = new ArrayList<>();
							for (int i = 0; i < intervalRegions.size(); i++) {
								List<Integer> temp = new ArrayList<Integer>();
								copyofIntervalRegionList.add(temp);
								for (int j = 0; j < intervalRegions.get(i).size(); j++) {
									temp.add(intervalRegions.get(i).get(j));
								}

							}
							for (int j = 0; j < currentRowSize; j++) {
								Integer val = borrowedAttrIntervals.get(row).get(j);
								for (int i = 0; i < count; i++) {
									List<Integer> w = new ArrayList<>(copyofIntervalRegionList.get(i));
									w.add(val);
									intervalRegions.set(currentIndex, w);
									currentIndex++;
								}
							}
							row = row + 1;
							count *= currentRowSize;

						} else {

							int currentIndex = 0;
							for (int j = 0; j < currentRowSize; j++) {

								Integer val = borrowedAttrIntervals.get(row).get(j);
								List<Integer> w = new ArrayList<>();
								w.add(val);

								intervalRegions.set(currentIndex, w);
								currentIndex++;

							}

							count = currentRowSize;
							row = row + 1;

						}

					}

					HashMap<Integer, String> Z3name = new HashMap<>();
					for (int i = 0; i < intervalRegions.size(); i++) {
						String intervalname = fkey + "_clique" + currentCliqueIdx + "interval" + i;
						allIntervalRegionsVariables.get(fkey).add(intervalname);
						Z3name.put(i, intervalname);
					}

					// Adding sum of all intervals to total tuple cout
					ArithExpr[] sumOfIntervalRegions = new ArithExpr[intervalRegions.size()];
					c = 0;
					allIntervalRegionsPerFKey.put(fkey, intervalRegions);
					for (Integer interval : Z3name.keySet()) {

						String intervalName = Z3name.get(interval);
						solver.Add(ctx.mkGe(ctx.mkIntConst(intervalName), ctx.mkInt(0)));
						allIntervalRegions.add(intervalName);
						sumOfIntervalRegions[c++] = ctx.mkIntConst(intervalName);

					}

					c = 0;
					ArithExpr[] sumOfPartitionedRegions = new ArithExpr[partition.size()];
					for (int r = 0; r < partition.size(); r++) {

						String varname = "var" + currentCliqueIdx + "_" + r;
						varToIntervalMapPerFKey.get(fkey).put(varname, new ArrayList<>());
						sumOfPartitionedRegions[c++] = ctx.mkIntConst(varname);

					}
					// adding all vars = all clique intervals
					solver.Add(ctx.mkEq(ctx.mkAdd(sumOfPartitionedRegions), ctx.mkAdd(sumOfIntervalRegions)));

					fkeyToActualInteervalisedRegMap.put(fkey, intervalisedRegionMap);
					Map<Integer, List<String>> intervalRegionToPartionedRegionsMap = new HashMap<>();
					for (int r = 0; r < partition.size(); r++) {

						Region region = partition.at(r);
						String regionName = "var" + currentCliqueIdx + "_" + r;
						List<String> regionPartitionList = new ArrayList<>();
						for (int i = 0; i < intervalRegions.size(); i++) {

							List<Integer> intervalRegion = intervalRegions.get(i);
							boolean flag = false;
							int bsIdx = 0;

							for (BucketStructure bs : region.getAll()) {

								c = 0;
								for (int bucketIdx : borrowedAttrIdx) {
									Bucket bucket = bs.at(bucketIdx);
									if (bucket.contains(intervalRegion.get(c))) {
										c = c + 1;
									} else {

										break;
									}

								}

								if (c == borrowedAttrIdx.size()) {
									flag = true;
									break;
								}
								bsIdx++;

							}

							if (flag) {
								String intervalisedRegionName = fkey + "_var" + currentCliqueIdx + "_" + r
										+ "_interval_" + i;
								BucketStructure bucketStructure = region.at(bsIdx);
								BucketStructure bsNew = new BucketStructure();

								int ci = 0;
								for (int bi = 0; bi < bucketStructure.size(); bi++) {

									Bucket bucket = new Bucket();
									if (bi == borrowedAttrIdx.get(ci)) {
										bucket.add(intervalRegion.get(ci));
									} else {
										bucket = bucketStructure.at(bi);
									}
									bsNew.add(bucket);

								}

								Region newR = new Region();
								newR.add(bsNew);

								intervalisedRegionMap.put(intervalisedRegionName, newR);
								regionPartitionList.add(intervalisedRegionName);
								allIntervalisedRegions.add(intervalisedRegionName);
								allIntervalisedRegionsVariables.get(fkey).add(intervalisedRegionName);
								varToIntervalMapPerFKey.get(fkey).get("var" + currentCliqueIdx + "_" + r).add(i);
								if (!intervalRegionToPartionedRegionsMap.containsKey(i)) {
									intervalRegionToPartionedRegionsMap.put(i, new ArrayList<>());
								}
								intervalRegionToPartionedRegionsMap.get(i).add(intervalisedRegionName);
								solver.Add(ctx.mkGe(ctx.mkIntConst(intervalisedRegionName), ctx.mkInt(0)));
							}

						}

						ArithExpr[] regionPartitionArray = new ArithExpr[regionPartitionList.size()];
						for (int i = 0; i < regionPartitionList.size(); i++) {

							regionPartitionArray[i] = ctx.mkIntConst(regionPartitionList.get(i));

						}

						// sum of intervalised regions = var
						solver.Add(ctx.mkEq(ctx.mkAdd(regionPartitionArray), ctx.mkIntConst(regionName)));

					}

					System.out.print("");

					for (int intervalIdx : intervalRegionToPartionedRegionsMap.keySet()) {

						List<String> regionNames = intervalRegionToPartionedRegionsMap.get(intervalIdx);

						ArithExpr[] regionArray = new ArithExpr[regionNames.size()];
						for (int i = 0; i < regionNames.size(); i++) {
							regionArray[i] = ctx.mkIntConst(regionNames.get(i));
						}

						solver.Add(ctx.mkEq(ctx.mkAdd(regionArray), ctx.mkIntConst(Z3name.get(intervalIdx))));

					}

					JSONArray dfVector = PostgresVConfig.fkeySkewVectors.getJSONObject(viewname).getJSONArray(fkey);
					JSONArray d = dfVector.getJSONArray(0);
					JSONArray f = dfVector.getJSONArray(1);

					for (Integer i = 0; i < intervalRegions.size(); i++) {
						ArithExpr[] dxSumm = new ArithExpr[d.length()];
						for (int d_i = 0; d_i < d.length(); d_i++) {

							String x = fkey + "_interval_" + i + "_d_" + d_i;
							solver.Add(ctx.mkGe(ctx.mkIntConst(x), ctx.mkInt(0)));
							allDxValuesVariables.get(fkey).add(x);
							allDxValues.add(x);
							ArithExpr xd = ctx.mkMul(ctx.mkIntConst(x), ctx.mkInt(d.getInt(d_i)));
							dxSumm[d_i] = xd;

						}
						String intervalname = Z3name.get(i);
						solver.Add(ctx.mkEq(ctx.mkAdd(dxSumm), ctx.mkIntConst(Z3name.get(i))));
					}

					for (int d_i = 0; d_i < d.length(); d_i++) {

						ArithExpr[] xfSumm = new ArithExpr[intervalRegions.size()];
						for (int i = 0; i < intervalRegions.size(); i++) {

							String x = fkey + "_interval_" + i + "_d_" + d_i;
							xfSumm[i] = ctx.mkIntConst(x);

						}

						solver.Add(ctx.mkEq(ctx.mkAdd(xfSumm), ctx.mkInt(f.getInt(d_i))));

					}

				}

				// Adding equations for CCs skew

				Map<String, Map<String, Set<String>>> fkeyToBR = PostgresVConfig.fkeyToBorrowedAttr;
				for (FormalCondition condition : conditions) {

					Integer counter = condition.getCounter();
					String queryname = condition.getQueryname();
					List<FormalCondition> conditionList = new ArrayList<>();
					conditionList.add(condition);
					String fkey = findFkey(conditionList);
					// CC having no foreign key column
					if (fkey == null) {
						continue;
					}
					// No borrowed attr for fkey
					if (!fkeyToBR.containsKey(fkey)) {
						continue;
					}
					String actualFKey = PostgresVConfig.reverseColumnAnonyMap.get(fkey);
					String dfVec = actualFKey + "___" + counter + "_" + queryname;

					DFvector dfvector = PostgresVConfig.ccsDFvectors.get(dfVec);
					List<Long> dValues = dfvector.getD();
					List<Long> fValues = dfvector.getF();
					List<List<Integer>> intervalRegions = this.allIntervalRegionsPerFKey.get(fkey);
					// String x = fkey + "_interval_" + i + "_d_" + d_i;

					// find CCs intersecting with intervals

					Map<String, Region> intervalisedRegions = this.fkeyToActualInteervalisedRegMap.get(fkey);
					Set<Integer> intersectingIntervals = findCCsIntersectingWithIntervals(condition,
							intervalisedRegions);

					JSONArray fkeyBaseSkewVectors = PostgresVConfig.fkeySkewVectors.getJSONObject(viewname)
							.getJSONArray(fkey);
					JSONArray baseDValues = fkeyBaseSkewVectors.getJSONArray(0);
					JSONArray baseFValues = fkeyBaseSkewVectors.getJSONArray(1);

					long fCount = 0;
					for (int di = 0; di < dValues.size(); di++) {

						Long fVal = fValues.get(di);
						Long dVal = dValues.get(di);
						ArithExpr[] dxArray = new ArithExpr[intersectingIntervals.size()];
						for (int bdi = 0; bdi < baseDValues.length(); bdi++) {
							long baseDval = baseDValues.getLong(bdi);
							if (baseDval < dVal) {
								break;
							} else {

								int c = 0;
								for (int intervalIdx : intersectingIntervals) {

									dxArray[c] = ctx.mkIntConst(fkey + "_interval_" + intervalIdx + "_d_" + di);
									c = c + 1;
								}

							}

						}

						solver.Add(ctx.mkGe(ctx.mkAdd(dxArray), ctx.mkInt(fVal - fCount)));
						fCount += fVal;

					}

					System.out.print("");

				}

			}

		}

		onlyFormationSW.displayTimeAndDispose();

		// Dumping LP into a file -- Anupam
		// start
		/*
		 * FileWriter fw; try { fw = new FileWriter("lpfile-" + viewname + ".txt");
		 * fw.write(solver.toString()); fw.close(); } catch (IOException e) { // TODO
		 * Auto-generated catch block e.printStackTrace(); }
		 */
		// System.err.println(solver.toString());
		// stop

		StopWatch onlySolvingSW = new StopWatch("LP-OnlySolving" + viewname);

		Status solverStatus = solver.Check();
		DebugHelper.printInfo("Solver Status: " + solverStatus);

		if (!Status.SATISFIABLE.equals(solverStatus)) {
			ctx.close();
			throw new RuntimeException("solverStatus is not SATISFIABLE");
		}

		Model model = solver.getModel();

		List<LinkedList<VariableValuePair>> cliqueIdxToVarValuesList = new ArrayList<>(cliqueCount);
		for (int i = 0; i < cliqueCount; i++) {

			IntList colIndxs = arasuCliquesAsColIndxs.get(i);
			Partition partition = cliqueIdxtoPList.get(i);
			LinkedList<VariableValuePair> varValuePairs = new LinkedList<>();
			for (int j = 0; j < partition.size(); j++) {
				String varname = "var" + i + "_" + j;

				// Variable to column indices mapping -- Anupam
				// start
//				FileWriter fw1;
//				try {
//					fw1 = new FileWriter(viewname + "-var-to-colindices.txt", true);
//					fw1.write(varname + " " + colIndxs.toString() + "\n");
//					fw1.close();
//				} catch (IOException e) {
//					// TODO Auto-generated catch block
//					e.printStackTrace();
//				}
				// stop
				// System.err.println(varname+colIndxs.toString());
				long rowcount = Long.parseLong(model.evaluate(ctx.mkIntConst(varname), true).toString());
				// Variable to value mapping -- Anupam
				// start
//				FileWriter fw2;
//				try {
//					fw2 = new FileWriter(viewname + "-var-to-value.txt", true);
//					fw2.write(varname + " " + rowcount + "\n");
//					fw2.close();
//				} catch (IOException e) {
//					// TODO Auto-generated catch block
//					e.printStackTrace();
//				}
				// stop
				if (rowcount != 0) {
					Region variable = getTruncatedRegion(partition.at(j), colIndxs);
					VariableValuePair varValuePair = new VariableValuePair(variable, rowcount);
					varValuePairs.add(varValuePair);
				}
			}
			cliqueIdxToVarValuesList.add(varValuePairs);

			Map<Integer, RegionSummaryProjection> regionsSummary = new HashMap<>();
			// int idx=0;

			for (int idx = 0; idx < cliqueIdxtoPList.get(i).size(); idx++) {
				Region reg = cliqueIdxtoPList.get(i).getAll().get(idx);
				String varname = "var" + i + "_" + idx;
				long rowcount = Long.parseLong(model.evaluate(ctx.mkIntConst(varname), true).toString());
				if (rowcount == 0)
					continue;
				RegionSummaryProjection regSum = new RegionSummaryProjection();
				regSum.region = getTruncatedRegion(reg, colIndxs);
				regSum.rowCount = rowcount;
				regionsSummary.put(idx, regSum);

			}

			Map<List<String>, Map<Integer, List<Integer>>> groupkeyToRegionToProjectionVariablesOptimzed = cliqueToGroupkeyToRegionToProjectionVariablesOptimzed
					.get(i);
			// int count=0;
			for (List<String> groupKey : groupkeyToRegionToProjectionVariablesOptimzed.keySet()) {

				List<ProjectionVariable> projectionVariables = cliqueToGroupkeyToProjectionVariablesOptimized.get(i)
						.get(groupKey);// all projection variables of the groupkey in the clique
				Map<Integer, List<Integer>> regionToProjectionVariablesOptimzed = groupkeyToRegionToProjectionVariablesOptimzed
						.get(groupKey);
				for (Integer regionIdx : regionToProjectionVariablesOptimzed.keySet()) {
					String varnameRegion = "var" + i + "_" + regionIdx;
					long rowcountR = Long.parseLong(model.evaluate(ctx.mkIntConst(varnameRegion), true).toString());
					if (rowcountR == 0)
						continue;
					regionsSummary.get(regionIdx).groupkeys.add(groupKey);// adding the groupkey for this region in
																			// the
																			// regionsSummary

					List<Integer> projectionRegionsIdx = regionToProjectionVariablesOptimzed.get(regionIdx);
					// regionsSummary.get(regionIdx).groupKeyToRegionF.add(new ArrayList<>());
					regionsSummary.get(regionIdx).groupKeyToRegionF.put(getColumnsIdx(groupKey), new ArrayList<>());
					for (Integer projectionRegionIdx : projectionRegionsIdx) {
						String groupkeyStr = toStringFunc(groupKey);
						String varnameP = "y" + i + "_" + groupkeyStr + "_"
								+ projectionVariables.get(projectionRegionIdx).toString();
						Long rowCountP = Long.parseLong(model.evaluate(ctx.mkIntConst(varnameP), true).toString());
						if (rowCountP == 0)
							continue;
						Pair<Long, Long> pTemp = new Pair<Long, Long>(rowCountP, 0L);// count and cut off
						// The cut off is initially 0 which may be changed when regions are divided
						RegionF interval = projectionVariables.get(projectionRegionIdx).interval;
						Pair<RegionF, Pair<Long, Long>> p = new Pair<RegionF, Pair<Long, Long>>(
								projectionVariables.get(projectionRegionIdx).interval, pTemp);
						regionsSummary.get(regionIdx).groupKeyToRegionF.get(getColumnsIdx(groupKey)).add(p);

						// adding the count to the split count
						int colIdx = getColumnsIdx(groupKey).get(0);

						double splitPoint = interval.at(0).at(0).at(0);// we plan to generate all distinct points
																		// using
																		// the first split point.
						// this split point will be only present in this regionF

						int splitPointIdx = bucketSplitPoints.get(colIdx).indexOf(splitPoint);
//							if(splitPointsCount.get(colIdx).get(splitPointIdx)!=0)
//								System.out.println();
//							if(colIdx==64)
//							System.out.println();
						splitPointsCount.get(colIdx).set(splitPointIdx, rowCountP);

						if (regionsSummary.get(regionIdx).groupKeyToRegionF.get(getColumnsIdx(groupKey)).isEmpty())
							System.out.println("What the ...!?");
					}
				}
				// count++;
			}
			// regions summary for every region in curr clique has been done.
			List<RegionSummaryProjection> regionsSummaryList = new ArrayList<>();
			regionsSummaryList.addAll(regionsSummary.values());// map to list. RegionIdx is lost but is no needed
																// here
																// on after
			cliqueToRegionsSummary.add(regionsSummaryList);

		}

		if (PostgresVConfig.hydraVersions.contains(PostgresVConfig.HydraTypes.duplicationHydra)) {
			long sumOfIntervalRegion = 0;
			for (int i = 0; i < allIntervalRegions.size(); i++) {

				// t17_c001_clique0interval8
				long val = Long.parseLong(model.evaluate(ctx.mkIntConst(allIntervalRegions.get(i)), true).toString());
				if (val == 0) {
					continue;
				}

				String interval = allIntervalRegions.get(i);
				String fkey = interval.split("_clique")[0];

				this.allIntervalRegionValueMap.put(allIntervalRegions.get(i), val);
				sumOfIntervalRegion += val;
				if (!this.fkeyToIntervalRegionMap.containsKey(fkey)) {
					this.fkeyToIntervalRegionMap.put(fkey, new ArrayList<>());
				}
				this.fkeyToIntervalRegionMap.get(fkey).add(interval);

			}

			long sumOfIntervalisedRegion = 0;

			for (int i = 0; i < allIntervalisedRegions.size(); i++) {

				long val = Long
						.parseLong(model.evaluate(ctx.mkIntConst(allIntervalisedRegions.get(i)), true).toString());
				if (val == 0) {
					continue;
				}

				String intervalisedRegion = allIntervalisedRegions.get(i);

				this.allIntervalisedRegionsMap.put(allIntervalisedRegions.get(i), val);
				sumOfIntervalisedRegion += val;

				String fkey = intervalisedRegion.split("_var")[0];
				String varname = intervalisedRegion.split("_")[2] + "_" + intervalisedRegion.split("_")[3];

				if (!varToIntervalisedRegionMapPerFkey.containsKey(fkey)) {
					varToIntervalisedRegionMapPerFkey.put(fkey, new HashMap<>());
				}
				if (!varToIntervalisedRegionMapPerFkey.get(fkey).containsKey(varname)) {
					varToIntervalisedRegionMapPerFkey.get(fkey).put(varname, new ArrayList<>());
				}
				varToIntervalisedRegionMapPerFkey.get(fkey).get(varname).add(intervalisedRegion);

			}

			for (int i = 0; i < allDxValues.size(); i++) {
				// t17_c018_interval_0_d_0
				long val = Long.parseLong(model.evaluate(ctx.mkIntConst(allDxValues.get(i)), true).toString());
				if (val == 0) {
					continue;
				}

				this.allDxValuesMap.put(allDxValues.get(i), val);
				String dxValue = allDxValues.get(i);
				String fkey = dxValue.split("_interval_")[0];
				int intervalIdx = Integer.parseInt(dxValue.split("_")[3]);
				if (!intervalToDxValuePerFkey.containsKey(fkey)) {
					intervalToDxValuePerFkey.put(fkey, new HashMap<>());
				}
				if (!intervalToDxValuePerFkey.get(fkey).containsKey(intervalIdx)) {
					intervalToDxValuePerFkey.get(fkey).put(intervalIdx, new ArrayList<>());
				}
				intervalToDxValuePerFkey.get(fkey).get(intervalIdx).add(dxValue);

			}
		}

		onlySolvingSW.displayTimeAndDispose();

		ctx.close();
		return cliqueIdxToVarValuesList;

	}

	//PKR: unified + varname 
	public HashMap<String, List<VariableValuePair>> unifiedformAndSolveLP(Context unifiedctx, Optimize unifiedsolver, 
			ConsistencyMakerType consistencyMakerType, FormalCondition[] consistencyConstraints, List<FormalCondition> conditions,
			List<Map<List<String>, List<Integer>>> cliqueToGroupkeyToRegionIdx,
			List<Map<List<String>, Map<FormalConditionAggregate, List<Integer>>>> cliqueToGroupkeyConditionToRegionIdx,
			List<Map<List<String>, Map<Integer, List<Integer>>>> cliqueToGroupkeyToRegionToProjectionVariablesOptimzed,
			List<Map<List<String>, List<ProjectionVariable>>> cliqueToGroupkeyToProjectionVariablesOptimized,
			HashMap<Set<String>, Set<String>> cliquesToFKeyCoverage, List<LongList> cliqueIdxtoConditionBValuesList, 
			List<Partition> cliqueIdxtoPList, List<List<IntList>> cliqueIdxtoPSimplifiedList) {

		// Map<String, String> contextmaptest = new HashMap<>();
		// contextmaptest.put("model", "true");
		// contextmaptest.put("unsat_core", "true");
		// Context ctxtest = new Context(contextmaptest);
		//
		// Optimize osolver = ctxtest.mkOptimize();
		// IntExpr x = ctxtest.mkIntConst("x");
		// IntExpr y = ctxtest.mkIntConst("y");
		// ArithExpr arithexpr = ctxtest.mkAdd(x, y);
		// osolver.Add(ctxtest.mkGt(arithexpr, ctxtest.mkInt(10)));
		// osolver.Add(ctxtest.mkLt(arithexpr, ctxtest.mkInt(20)));
		//
		// osolver.MkMaximize(arithexpr);
		//
		// osolver.Check();
		//
		// Model modeltest = osolver.getModel();
		// System.out.println(modeltest.evaluate(x, true) + " : " +
		// modeltest.evaluate(y, true));
		///////////////// End dk

		StopWatch onlyFormationSW = new StopWatch("LP-OnlyFormation" + viewname);

		//commented by PKR
//		Map<String, String> contextmap = new HashMap<>();
//		contextmap.put("model", "true");
//		contextmap.put("unsat_core", "true");
//		Context ctx = new Context(contextmap);
//
//		Optimize solver = ctx.mkOptimize();
		int projectionVarsIndex = 0;
		int type1 = 0, type2 = 0, type3 = 0, projectionCC = 0, filterCC = 0, consistencyCC = 0;
		List<List<List<IntExpr>>> solverConstraintsRequiredForConsistency = new ArrayList<>();
		// Create lp variables for cardinality constraints
		for (int cliqueIndex = 0; cliqueIndex < cliqueCount; cliqueIndex++) {

			LongList bvalues = cliqueIdxtoConditionBValuesList.get(cliqueIndex);
			Partition partition = cliqueIdxtoPList.get(cliqueIndex); // Partition is a list of regions corresponding to
																		// below labels
			List<IntList> conditionIdxsList = cliqueIdxtoPSimplifiedList.get(cliqueIndex); // Getting label

			HashMap<Integer, Integer> indexKeeper = null;
			int solverConstraintSize;

			if (consistencyMakerType == ConsistencyMakerType.CONSISTENCYFILTERS) {
				if (cliqueCount > 1) {
					indexKeeper = mappedIndexOfConsistencyConstraint.get(cliqueIndex);
					solverConstraintSize = bvalues.size() + indexKeeper.size();
				} else
					solverConstraintSize = bvalues.size();
			} else {
				indexKeeper = new HashMap<>();
				solverConstraintSize = bvalues.size() + cliqueWiseTotalSingleSplitPointRegions.get(cliqueIndex);
			}

			List<List<IntExpr>> solverConstraints = new ArrayList<>(solverConstraintSize);
			for (int j = 0; j < solverConstraintSize; j++) {
				solverConstraints.add(new ArrayList<>());
			}

			for (int blockIndex = 0; blockIndex < partition.size(); blockIndex++) {
				String varname = "var"  + viewname + "_" + cliqueIndex + "_" + blockIndex;
				solverStats.solverVarCount++;

				// Adding non-negativity constraints
				unifiedsolver.Add(unifiedctx.mkGe(unifiedctx.mkIntConst(varname), unifiedctx.mkInt(0)));
				type1++;
				// Adds the region to all the constraints it belongs to
				for (IntIterator iter = conditionIdxsList.get(blockIndex).iterator(); iter.hasNext();) {
					int k = iter.nextInt();

					solverConstraints.get(k).add(unifiedctx.mkIntConst(varname));
				}

			}
			// Adding filter constraints
			for (int conditionIndex = 0; conditionIndex < bvalues.size(); conditionIndex++) {
				long outputCardinality = bvalues.getLong(conditionIndex);
				List<IntExpr> addList = solverConstraints.get(conditionIndex);
				unifiedsolver.Add(unifiedctx.mkEq(unifiedctx.mkAdd(addList.toArray(new ArithExpr[addList.size()])),
						unifiedctx.mkInt(outputCardinality)));
				filterCC++;
				solverStats.solverConstraintCount++;
			}

//			---------------shadab----adding projection constraints-----------------------------

			Map<List<String>, List<ProjectionVariable>> groupkeyToProjectionVariablesOptimized = cliqueToGroupkeyToProjectionVariablesOptimized
					.get(cliqueIndex);

			for (List<String> groupkey : groupkeyToProjectionVariablesOptimized.keySet()) {
				String groupkeyStr = toStringFunc(groupkey);
				List<ProjectionVariable> projectionVariablesOptimized = groupkeyToProjectionVariablesOptimized
						.get(groupkey);
				for (int j = 0; j < projectionVariablesOptimized.size(); j++) {
					String varname = "y" + viewname + "_"  + cliqueIndex + "_" + groupkeyStr + "_"
							+ projectionVariablesOptimized.get(j).toString();
					unifiedsolver.Add(unifiedctx.mkGe(unifiedctx.mkIntConst(varname), unifiedctx.mkInt(0)));
					type1++;

				}
			}

			Map<List<String>, Map<Integer, List<Integer>>> groupkeyToRegionToProjectionVariablesOptimzed = cliqueToGroupkeyToRegionToProjectionVariablesOptimzed
					.get(cliqueIndex);

			for (List<String> groupkey : groupkeyToRegionToProjectionVariablesOptimzed.keySet()) {
				String groupkeyStr = toStringFunc(groupkey);

				List<ProjectionVariable> projectionVariablesOptimized = groupkeyToProjectionVariablesOptimized
						.get(groupkey);
				Map<Integer, List<Integer>> regionToProjectionVariablesOptimized = groupkeyToRegionToProjectionVariablesOptimzed
						.get(groupkey);
				for (Integer regionIdx : regionToProjectionVariablesOptimized.keySet()) {
					String varname = "var" + viewname + "_"  + cliqueIndex + "_" + regionIdx;
					List<IntExpr> projectionExpr = new ArrayList<>();
					for (Integer projVarIndx : regionToProjectionVariablesOptimized.get(regionIdx)) {
						projectionExpr.add(unifiedctx.mkIntConst("y" + cliqueIndex + "_" + groupkeyStr + "_"
								+ projectionVariablesOptimized.get(projVarIndx).toString()));
					}

					if (!datasynthcomp) {
						unifiedsolver.Add(
								unifiedctx.mkGe(
										unifiedctx.mkMul(unifiedctx.mkInt(relationCardinality),
												unifiedctx.mkAdd(
														projectionExpr.toArray(new ArithExpr[projectionExpr.size()]))),
										unifiedctx.mkIntConst(varname)));
						type3++;
					}
					unifiedsolver.Add(unifiedctx.mkLe(unifiedctx.mkAdd(projectionExpr.toArray(new ArithExpr[projectionExpr.size()])),
							unifiedctx.mkIntConst(varname)));
					type2++;
				}
			}

			Map<List<String>, Map<FormalConditionAggregate, List<Integer>>> groupkeyConditionToRegionIdx = cliqueToGroupkeyConditionToRegionIdx
					.get(cliqueIndex);
			for (List<String> groupkey : groupkeyConditionToRegionIdx.keySet()) {
				String groupkeyStr = toStringFunc(groupkey);
				List<ProjectionVariable> projectionVariablesOptimized = groupkeyToProjectionVariablesOptimized
						.get(groupkey);

				Map<Integer, List<Integer>> regionsToProjectionVariables = cliqueToGroupkeyToRegionToProjectionVariablesOptimzed
						.get(cliqueIndex).get(groupkey);
				Map<FormalConditionAggregate, List<Integer>> conditionToRegionIdx = groupkeyConditionToRegionIdx
						.get(groupkey);
				for (FormalConditionAggregate condition : conditionToRegionIdx.keySet()) {
					List<IntExpr> projectionExpr = new ArrayList<>();
					List<Integer> regionsIdx = conditionToRegionIdx.get(condition);
					Set<Integer> projectionVariablesIdx = new HashSet<>();
					for (Integer regionIdx : regionsIdx) {
						projectionVariablesIdx.addAll(regionsToProjectionVariables.get(regionIdx));
					}

					// nonOverlappingSanityCheck(projectionVariablesIdx,projectionVariablesOptimized);

					for (Integer projectionVariableIdx : projectionVariablesIdx)
						projectionExpr.add(unifiedctx.mkIntConst("y" + cliqueIndex + "_" + groupkeyStr + "_"
								+ projectionVariablesOptimized.get(projectionVariableIdx).toString()));
					unifiedsolver.Add(unifiedctx.mkEq(unifiedctx.mkAdd(projectionExpr.toArray(new ArithExpr[projectionExpr.size()])),
							unifiedctx.mkInt(condition.getProjectionCardinality())));
					projectionCC++;
				}
			}

			///////////////// Start dk
			if (cliqueCount > 1 && consistencyMakerType == ConsistencyMakerType.CONSISTENCYFILTERS) {
				List<List<IntExpr>> solverConstraintsToExport = new ArrayList<>(indexKeeper.size());
				for (int j = bvalues.size(); j < solverConstraintSize; j++) {
					solverConstraintsToExport.add(solverConstraints.get(j));
				}
				solverConstraintsToExport.add(solverConstraints.get(bvalues.size() - 1)); // Clique size
				solverConstraintsRequiredForConsistency.add(solverConstraintsToExport);
			}
		}

		// Consistency

		int countConsistencyConstraint = 0;
		if (cliqueCount > 1) {// TODO is necessary?
			if (consistencyMakerType == ConsistencyMakerType.CONSISTENCYFILTERS) {

				if (consistencyConstraints.length != 0) {
					for (int c1index = 0; c1index < cliqueCount; c1index++) {
						HashMap<Integer, Integer> c1indexKeeper = mappedIndexOfConsistencyConstraint.get(c1index);
						if (c1indexKeeper.isEmpty())
							continue;
						List<List<IntExpr>> c1solverConstraints = solverConstraintsRequiredForConsistency.get(c1index);
						for (int c2index = c1index + 1; c2index < cliqueCount; c2index++) {
							HashMap<Integer, Integer> c2indexKeeper = mappedIndexOfConsistencyConstraint.get(c2index);
							if (c2indexKeeper.isEmpty())
								continue;
							List<List<IntExpr>> c2solverConstraints = solverConstraintsRequiredForConsistency
									.get(c2index);
							Set<Integer> applicableConsistencyConstraints = new HashSet<>(c1indexKeeper.keySet());
							applicableConsistencyConstraints.retainAll(c2indexKeeper.keySet());
							if (applicableConsistencyConstraints.isEmpty())
								continue;
							List<List<IntExpr>> c1ApplicableSolverConstraints = new ArrayList<>();
							List<List<IntExpr>> c2ApplicableSolverConstraints = new ArrayList<>();
							for (Integer originalConsistencyConstraintIndex : applicableConsistencyConstraints) {
								c1ApplicableSolverConstraints.add(
										c1solverConstraints.get(c1indexKeeper.get(originalConsistencyConstraintIndex)));
								c2ApplicableSolverConstraints.add(
										c2solverConstraints.get(c2indexKeeper.get(originalConsistencyConstraintIndex)));
							}

							c1ApplicableSolverConstraints.add(c1solverConstraints.get(c1solverConstraints.size() - 1));
							c2ApplicableSolverConstraints.add(c2solverConstraints.get(c2solverConstraints.size() - 1));

							HashMap<IntList, MutablePair<List<IntExpr>, List<IntExpr>>> conditionListToPairOfVarList = new HashMap<>();
							addTo_ConditionListToPairOfVarList(c1ApplicableSolverConstraints,
									conditionListToPairOfVarList);
							addTo_ConditionListToPairOfVarList(c2ApplicableSolverConstraints,
									conditionListToPairOfVarList);

							// Set<String> commonCols = new HashSet<>(arasuCliques.get(c1index));
							// commonCols.retainAll(arasuCliques.get(c2index));

							for (MutablePair<List<IntExpr>, List<IntExpr>> pair : conditionListToPairOfVarList
									.values()) {
								List<IntExpr> c1Set = pair.getFirst();
								List<IntExpr> c2Set = pair.getSecond();
								ArithExpr set1expr = unifiedctx.mkAdd(c1Set.toArray(new ArithExpr[c1Set.size()]));
								ArithExpr set2expr = unifiedctx.mkAdd(c2Set.toArray(new ArithExpr[c2Set.size()]));
								unifiedsolver.Add(unifiedctx.mkEq(set1expr, set2expr));
								consistencyCC++;
								countConsistencyConstraint++;

								// 1-D projection
								// collectProjectionConsistencyData(solver,ctx, c1Set, c2Set, c1index, c2index,
								// commonCols, projectionConsistencyInfoPairs, cliqueWColumnWProjectionStuff);
							}
						}
					}
				}
			}
			///////////////// End dk

			else if (consistencyMakerType == ConsistencyMakerType.BRUTEFORCE) {
				for (CliqueIntersectionInfo cliqueIntersectionInfo : cliqueIntersectionInfos) { // Create lp variables
																								// for
																								// consistency
																								// constraints

					int i = cliqueIntersectionInfo.i;
					int j = cliqueIntersectionInfo.j;
					IntList intersectingColIndices = cliqueIntersectionInfo.intersectingColIndices;

					Partition partitionI = cliqueIdxtoPList.get(i);
					Partition partitionJ = cliqueIdxtoPList.get(j);

					// Recomputing SplitRegions for every pair of intersecting cliques
					// as the SplitRegions might have become more granular due to
					// some other pair of intersecting cliques having its intersectingColIndices
					// overlapping with this pair's intersectingColIndices
					List<Region> splitRegions = getSplitRegions(partitionI, partitionJ, intersectingColIndices);

					Set<String> commonCols = new HashSet<>(arasuCliques.get(i));
					commonCols.retainAll(arasuCliques.get(j));

					for (Region splitRegion : splitRegions) {
						List<IntExpr> consistencyLHS = new ArrayList<>();
						for (int k = 0; k < partitionI.size(); k++) {
							Region iVar = partitionI.at(k);

							Region truncRegion = getTruncatedRegion(iVar, intersectingColIndices);
							Region truncOverlap = truncRegion.intersection(splitRegion);
							if (!truncOverlap.isEmpty()) {
								String varname = "var" + viewname + "_"  + i + "_" + k;
								consistencyLHS.add(unifiedctx.mkIntConst(varname));
							}
						}

						List<IntExpr> consistencyRHS = new ArrayList<>();
						for (int k = 0; k < partitionJ.size(); k++) {
							Region jVar = partitionJ.at(k);

							Region truncRegion = getTruncatedRegion(jVar, intersectingColIndices);
							Region truncOverlap = truncRegion.intersection(splitRegion);
							if (!truncOverlap.isEmpty()) {
								String varname = "var" + viewname + "_"  + j + "_" + k;
								consistencyRHS.add(unifiedctx.mkIntConst(varname));
							}
						}

						// Adding consistency constraints
						unifiedsolver.Add(unifiedctx.mkEq(unifiedctx.mkAdd(consistencyLHS.toArray(new ArithExpr[consistencyLHS.size()])),
								unifiedctx.mkAdd(consistencyRHS.toArray(new ArithExpr[consistencyRHS.size()]))));
						solverStats.solverConstraintCount++;
						countConsistencyConstraint++;

					}
				}
			} else {
				unifiedctx.close();
				throw new RuntimeException("Unknown consistency maker " + consistencyMakerType);
			}
		}
		DebugHelper.printInfo("countConsistencyConstraint for " + viewname + " = " + countConsistencyConstraint);

		List<String> allIntervalRegions = new ArrayList<>(); // List of all intervals
		List<String> allIntervalisedRegions = new ArrayList<>(); // List of all intervalised regions
		List<String> allDxValues = new ArrayList<>();

		if (PostgresVConfig.hydraVersions.contains(PostgresVConfig.HydraTypes.duplicationHydra)) {

			// New variables
			Map<String, List<String>> allIntervalRegionsVariables = new HashMap<>();
			Map<String, List<String>> allDxValuesVariables = new HashMap<>();
			Map<String, List<String>> allIntervalisedRegionsVariables = new HashMap<>();
			Map<String, HashMap<String, List<Integer>>> varToIntervalMapPerFKey = new HashMap<>();

			if (PostgresVConfig.fkeyToBorrowedAttr.containsKey(viewname)) {

				Map<String, Set<String>> fkeyToBorrowedAttr = PostgresVConfig.fkeyToBorrowedAttr.get(viewname);

				for (String fkey : fkeyToBorrowedAttr.keySet()) {

					allIntervalRegionsVariables.put(fkey, new ArrayList<>());
					allDxValuesVariables.put(fkey, new ArrayList<>());
					allIntervalisedRegionsVariables.put(fkey, new ArrayList<>());
					varToIntervalMapPerFKey.put(fkey, new HashMap<>());
					Set<String> currentClique = null;
					Integer currentCliqueIdx = null;

					for (int c = 0; c < this.arasuCliques.size(); c++) {
						Set<String> clique = this.arasuCliques.get(c);
						if (!cliquesToFKeyCoverage.containsKey(clique)) {
							continue;
						}
						Set<String> fkeysCovered = cliquesToFKeyCoverage.get(clique);
						if (fkeysCovered.contains(fkey)) {
							currentClique = clique;
							currentCliqueIdx = c;
							break;
						}

					}

					if (currentClique == null) {
						throw new RuntimeException("Something wrong can't be possible");
					}

					fkeyToCliqueIdx.put(fkey, currentCliqueIdx);

					Set<String> borrowedAttr = fkeyToBorrowedAttr.get(fkey);
					List<String> sortedBorrowedAttr = new ArrayList<>(borrowedAttr);
					List<Integer> borrowedAttrIdx = new ArrayList<>();
					Collections.sort(sortedBorrowedAttr);
					int c = 0;
					for (int i = 0; i < sortedViewColumns.size(); i++) {

						if (sortedBorrowedAttr.get(c).contentEquals(sortedViewColumns.get(i))) {

							borrowedAttrIdx.add(i);
							c = c + 1;
						}
						if (c == sortedBorrowedAttr.size()) {
							break;
						}

					}

					int noOfIntervalRegions = 1;
					List<List<Integer>> borrowedAttrIntervals = new ArrayList<>();
					Partition partition = cliqueIdxtoPList.get(currentCliqueIdx);
					for (int bucket : borrowedAttrIdx) {

						Set<Integer> intervals = new HashSet<>();
						for (Region r : partition.getAll()) {

							for (BucketStructure bs : r.getAll()) {

								intervals.addAll((bs.at(bucket).getAll()));

							}

						}
						noOfIntervalRegions *= intervals.size();
						ArrayList<Integer> intervalsList = new ArrayList<>(intervals);
						Collections.sort(intervalsList);
						borrowedAttrIntervals.add(intervalsList);

					}

					List<List<Integer>> intervalRegions = new ArrayList<>();
					for (int i = 0; i < noOfIntervalRegions; i++) {

						intervalRegions.add(new ArrayList<>());
					}

					int count = 0;
					int row = 0;
					while (count < noOfIntervalRegions) {

						int currentRowSize = borrowedAttrIntervals.get(row).size();

						if (count > 0) {

							int currentIndex = 0;
							List<List<Integer>> copyofIntervalRegionList = new ArrayList<>();
							for (int i = 0; i < intervalRegions.size(); i++) {
								List<Integer> temp = new ArrayList<Integer>();
								copyofIntervalRegionList.add(temp);
								for (int j = 0; j < intervalRegions.get(i).size(); j++) {
									temp.add(intervalRegions.get(i).get(j));
								}

							}
							for (int j = 0; j < currentRowSize; j++) {
								Integer val = borrowedAttrIntervals.get(row).get(j);
								for (int i = 0; i < count; i++) {
									List<Integer> w = new ArrayList<>(copyofIntervalRegionList.get(i));
									w.add(val);
									intervalRegions.set(currentIndex, w);
									currentIndex++;
								}
							}
							row = row + 1;
							count *= currentRowSize;

						} else {

							int currentIndex = 0;
							for (int j = 0; j < currentRowSize; j++) {

								Integer val = borrowedAttrIntervals.get(row).get(j);
								List<Integer> w = new ArrayList<>();
								w.add(val);

								intervalRegions.set(currentIndex, w);
								currentIndex++;

							}

							count = currentRowSize;
							row = row + 1;

						}

					}

					HashMap<Integer, String> Z3name = new HashMap<>();
					for (int i = 0; i < intervalRegions.size(); i++) {
						String intervalname = fkey + "_clique" + currentCliqueIdx + "interval" + i;
						allIntervalRegionsVariables.get(fkey).add(intervalname);
						Z3name.put(i, intervalname);
					}

					// Adding sum of all intervals to total tuple cout
					ArithExpr[] sumOfIntervalRegions = new ArithExpr[intervalRegions.size()];
					c = 0;
					allIntervalRegionsPerFKey.put(fkey, intervalRegions);
					for (Integer interval : Z3name.keySet()) {

						String intervalName = Z3name.get(interval);
						unifiedsolver.Add(unifiedctx.mkGe(unifiedctx.mkIntConst(intervalName), unifiedctx.mkInt(0)));
						allIntervalRegions.add(intervalName);
						sumOfIntervalRegions[c++] = unifiedctx.mkIntConst(intervalName);

					}

					c = 0;
					ArithExpr[] sumOfPartitionedRegions = new ArithExpr[partition.size()];
					for (int r = 0; r < partition.size(); r++) {

						String varname = "var" + currentCliqueIdx + "_" + r;
						varToIntervalMapPerFKey.get(fkey).put(varname, new ArrayList<>());
						sumOfPartitionedRegions[c++] = unifiedctx.mkIntConst(varname);

					}
					// adding all vars = all clique intervals
					unifiedsolver.Add(unifiedctx.mkEq(unifiedctx.mkAdd(sumOfPartitionedRegions), unifiedctx.mkAdd(sumOfIntervalRegions)));

					fkeyToActualInteervalisedRegMap.put(fkey, intervalisedRegionMap);
					Map<Integer, List<String>> intervalRegionToPartionedRegionsMap = new HashMap<>();
					for (int r = 0; r < partition.size(); r++) {

						Region region = partition.at(r);
						String regionName = "var" + currentCliqueIdx + "_" + r;
						List<String> regionPartitionList = new ArrayList<>();
						for (int i = 0; i < intervalRegions.size(); i++) {

							List<Integer> intervalRegion = intervalRegions.get(i);
							boolean flag = false;
							int bsIdx = 0;

							for (BucketStructure bs : region.getAll()) {

								c = 0;
								for (int bucketIdx : borrowedAttrIdx) {
									Bucket bucket = bs.at(bucketIdx);
									if (bucket.contains(intervalRegion.get(c))) {
										c = c + 1;
									} else {

										break;
									}

								}

								if (c == borrowedAttrIdx.size()) {
									flag = true;
									break;
								}
								bsIdx++;

							}

							if (flag) {
								String intervalisedRegionName = fkey + "_var" + currentCliqueIdx + "_" + r
										+ "_interval_" + i;
								BucketStructure bucketStructure = region.at(bsIdx);
								BucketStructure bsNew = new BucketStructure();

								int ci = 0;
								for (int bi = 0; bi < bucketStructure.size(); bi++) {

									Bucket bucket = new Bucket();
									if (bi == borrowedAttrIdx.get(ci)) {
										bucket.add(intervalRegion.get(ci));
									} else {
										bucket = bucketStructure.at(bi);
									}
									bsNew.add(bucket);

								}

								Region newR = new Region();
								newR.add(bsNew);

								intervalisedRegionMap.put(intervalisedRegionName, newR);
								regionPartitionList.add(intervalisedRegionName);
								allIntervalisedRegions.add(intervalisedRegionName);
								allIntervalisedRegionsVariables.get(fkey).add(intervalisedRegionName);
								varToIntervalMapPerFKey.get(fkey).get("var" + currentCliqueIdx + "_" + r).add(i);
								if (!intervalRegionToPartionedRegionsMap.containsKey(i)) {
									intervalRegionToPartionedRegionsMap.put(i, new ArrayList<>());
								}
								intervalRegionToPartionedRegionsMap.get(i).add(intervalisedRegionName);
								unifiedsolver.Add(unifiedctx.mkGe(unifiedctx.mkIntConst(intervalisedRegionName), unifiedctx.mkInt(0)));
							}

						}

						ArithExpr[] regionPartitionArray = new ArithExpr[regionPartitionList.size()];
						for (int i = 0; i < regionPartitionList.size(); i++) {

							regionPartitionArray[i] = unifiedctx.mkIntConst(regionPartitionList.get(i));

						}

						// sum of intervalised regions = var
						unifiedsolver.Add(unifiedctx.mkEq(unifiedctx.mkAdd(regionPartitionArray), unifiedctx.mkIntConst(regionName)));

					}

					System.out.print("");

					for (int intervalIdx : intervalRegionToPartionedRegionsMap.keySet()) {

						List<String> regionNames = intervalRegionToPartionedRegionsMap.get(intervalIdx);

						ArithExpr[] regionArray = new ArithExpr[regionNames.size()];
						for (int i = 0; i < regionNames.size(); i++) {
							regionArray[i] = unifiedctx.mkIntConst(regionNames.get(i));
						}

						unifiedsolver.Add(unifiedctx.mkEq(unifiedctx.mkAdd(regionArray), unifiedctx.mkIntConst(Z3name.get(intervalIdx))));

					}

					JSONArray dfVector = PostgresVConfig.fkeySkewVectors.getJSONObject(viewname).getJSONArray(fkey);
					JSONArray d = dfVector.getJSONArray(0);
					JSONArray f = dfVector.getJSONArray(1);

					for (Integer i = 0; i < intervalRegions.size(); i++) {
						ArithExpr[] dxSumm = new ArithExpr[d.length()];
						for (int d_i = 0; d_i < d.length(); d_i++) {

							String x = fkey + "_interval_" + i + "_d_" + d_i;
							unifiedsolver.Add(unifiedctx.mkGe(unifiedctx.mkIntConst(x), unifiedctx.mkInt(0)));
							allDxValuesVariables.get(fkey).add(x);
							allDxValues.add(x);
							ArithExpr xd = unifiedctx.mkMul(unifiedctx.mkIntConst(x), unifiedctx.mkInt(d.getInt(d_i)));
							dxSumm[d_i] = xd;

						}
						String intervalname = Z3name.get(i);
						unifiedsolver.Add(unifiedctx.mkEq(unifiedctx.mkAdd(dxSumm), unifiedctx.mkIntConst(Z3name.get(i))));
					}

					for (int d_i = 0; d_i < d.length(); d_i++) {

						ArithExpr[] xfSumm = new ArithExpr[intervalRegions.size()];
						for (int i = 0; i < intervalRegions.size(); i++) {

							String x = fkey + "_interval_" + i + "_d_" + d_i;
							xfSumm[i] = unifiedctx.mkIntConst(x);

						}

						unifiedsolver.Add(unifiedctx.mkEq(unifiedctx.mkAdd(xfSumm), unifiedctx.mkInt(f.getInt(d_i))));

					}

				}

				// Adding equations for CCs skew

				Map<String, Map<String, Set<String>>> fkeyToBR = PostgresVConfig.fkeyToBorrowedAttr;
				for (FormalCondition condition : conditions) {

					Integer counter = condition.getCounter();
					String queryname = condition.getQueryname();
					List<FormalCondition> conditionList = new ArrayList<>();
					conditionList.add(condition);
					String fkey = findFkey(conditionList);
					// CC having no foreign key column
					if (fkey == null) {
						continue;
					}
					// No borrowed attr for fkey
					if (!fkeyToBR.containsKey(fkey)) {
						continue;
					}
					String actualFKey = PostgresVConfig.reverseColumnAnonyMap.get(fkey);
					String dfVec = actualFKey + "___" + counter + "_" + queryname;

					DFvector dfvector = PostgresVConfig.ccsDFvectors.get(dfVec);
					List<Long> dValues = dfvector.getD();
					List<Long> fValues = dfvector.getF();
					List<List<Integer>> intervalRegions = this.allIntervalRegionsPerFKey.get(fkey);
					// String x = fkey + "_interval_" + i + "_d_" + d_i;

					// find CCs intersecting with intervals

					Map<String, Region> intervalisedRegions = this.fkeyToActualInteervalisedRegMap.get(fkey);
					Set<Integer> intersectingIntervals = findCCsIntersectingWithIntervals(condition,
							intervalisedRegions);

					JSONArray fkeyBaseSkewVectors = PostgresVConfig.fkeySkewVectors.getJSONObject(viewname)
							.getJSONArray(fkey);
					JSONArray baseDValues = fkeyBaseSkewVectors.getJSONArray(0);
					JSONArray baseFValues = fkeyBaseSkewVectors.getJSONArray(1);

					long fCount = 0;
					for (int di = 0; di < dValues.size(); di++) {

						Long fVal = fValues.get(di);
						Long dVal = dValues.get(di);
						ArithExpr[] dxArray = new ArithExpr[intersectingIntervals.size()];
						for (int bdi = 0; bdi < baseDValues.length(); bdi++) {
							long baseDval = baseDValues.getLong(bdi);
							if (baseDval < dVal) {
								break;
							} else {

								int c = 0;
								for (int intervalIdx : intersectingIntervals) {

									dxArray[c] = unifiedctx.mkIntConst(fkey + "_interval_" + intervalIdx + "_d_" + di);
									c = c + 1;
								}

							}

						}

						unifiedsolver.Add(unifiedctx.mkGe(unifiedctx.mkAdd(dxArray), unifiedctx.mkInt(fVal - fCount)));
						fCount += fVal;

					}

					System.out.print("");

				}

			}

		}

		onlyFormationSW.displayTimeAndDispose();

		// Dumping LP into a file -- Anupam
		// start
		/*
		 * FileWriter fw; try { fw = new FileWriter("lpfile-" + viewname + ".txt");
		 * fw.write(solver.toString()); fw.close(); } catch (IOException e) { // TODO
		 * Auto-generated catch block e.printStackTrace(); }
		 */
		// System.err.println(solver.toString());
		// stop

		//commented by PKR
//		StopWatch onlySolvingSW = new StopWatch("LP-OnlySolving" + viewname);
//
//		Status solverStatus = unifiedsolver.Check();
//		DebugHelper.printInfo("Solver Status: " + solverStatus);
//
//		if (!Status.SATISFIABLE.equals(solverStatus)) {
//			unifiedctx.close();
//			throw new RuntimeException("solverStatus is not SATISFIABLE");
//		}
//
//		Model model = unifiedsolver.getModel();
//
		List<VariableValuePair> unifiedcliqueIdxToVarValuesList = new ArrayList<>(cliqueCount);
		HashMap<String, List<VariableValuePair>> viewtoCCMap = new HashMap<>();

		List<LinkedList<VariableValuePair>> cliqueIdxToVarValuesList = new ArrayList<>(cliqueCount);
		for (int i = 0; i < cliqueCount; i++) {

			IntList colIndxs = arasuCliquesAsColIndxs.get(i);
			Partition partition = cliqueIdxtoPList.get(i);
			LinkedList<VariableValuePair> varValuePairs = new LinkedList<>();
			List<VariableValuePair> unifiedvarValuePairs = new ArrayList<>();
			for (int j = 0; j < partition.size(); j++) {
//				String varname = "var" + i + "_" + j;
//
//				// Variable to column indices mapping -- Anupam
//				// start
//				FileWriter fw1;
//				try {
//					fw1 = new FileWriter(viewname + "-var-to-colindices.txt", true);
//					fw1.write(varname + " " + colIndxs.toString() + "\n");
//					fw1.close();
//				} catch (IOException e) {
//					// TODO Auto-generated catch block
//					e.printStackTrace();
//				}
//				// stop
//				// System.err.println(varname+colIndxs.toString());
//				long rowcount = Long.parseLong(model.evaluate(unifiedctx.mkIntConst(varname), true).toString());
//				// Variable to value mapping -- Anupam
//				// start
//				FileWriter fw2;
//				try {
//					fw2 = new FileWriter(viewname + "-var-to-value.txt", true);
//					fw2.write(varname + " " + rowcount + "\n");
//					fw2.close();
//				} catch (IOException e) {
//					// TODO Auto-generated catch block
//					e.printStackTrace();
//				}
				// stop
				
				//PKR: commented "if" condition
//				if (rowcount != 0) {
					Region variable = getTruncatedRegion(partition.at(j), colIndxs);
					VariableValuePair varValuePair = new VariableValuePair(variable, 0);
					varValuePairs.add(varValuePair);
					unifiedvarValuePairs.add(varValuePair);
//				}
			}
			cliqueIdxToVarValuesList.add(varValuePairs);
			//PKR: will only work when we have only one clique
			viewtoCCMap.put(viewname, unifiedvarValuePairs);
//
//			Map<Integer, RegionSummaryProjection> regionsSummary = new HashMap<>();
//			// int idx=0;
//
//			for (int idx = 0; idx < cliqueIdxtoPList.get(i).size(); idx++) {
//				Region reg = cliqueIdxtoPList.get(i).getAll().get(idx);
//				String varname = "var" + i + "_" + idx;
//				long rowcount = Long.parseLong(model.evaluate(unifiedctx.mkIntConst(varname), true).toString());
//				if (rowcount == 0)
//					continue;
//				RegionSummaryProjection regSum = new RegionSummaryProjection();
//				regSum.region = getTruncatedRegion(reg, colIndxs);
//				regSum.rowCount = rowcount;
//				regionsSummary.put(idx, regSum);
//
//			}
//
//			Map<List<String>, Map<Integer, List<Integer>>> groupkeyToRegionToProjectionVariablesOptimzed = cliqueToGroupkeyToRegionToProjectionVariablesOptimzed
//					.get(i);
//			// int count=0;
//			for (List<String> groupKey : groupkeyToRegionToProjectionVariablesOptimzed.keySet()) {
//
//				List<ProjectionVariable> projectionVariables = cliqueToGroupkeyToProjectionVariablesOptimized.get(i)
//						.get(groupKey);// all projection variables of the groupkey in the clique
//				Map<Integer, List<Integer>> regionToProjectionVariablesOptimzed = groupkeyToRegionToProjectionVariablesOptimzed
//						.get(groupKey);
//				for (Integer regionIdx : regionToProjectionVariablesOptimzed.keySet()) {
//					String varnameRegion = "var" + i + "_" + regionIdx;
//					long rowcountR = Long.parseLong(model.evaluate(unifiedctx.mkIntConst(varnameRegion), true).toString());
//					if (rowcountR == 0)
//						continue;
//					regionsSummary.get(regionIdx).groupkeys.add(groupKey);// adding the groupkey for this region in
//																			// the
//																			// regionsSummary
//
//					List<Integer> projectionRegionsIdx = regionToProjectionVariablesOptimzed.get(regionIdx);
//					// regionsSummary.get(regionIdx).groupKeyToRegionF.add(new ArrayList<>());
//					regionsSummary.get(regionIdx).groupKeyToRegionF.put(getColumnsIdx(groupKey), new ArrayList<>());
//					for (Integer projectionRegionIdx : projectionRegionsIdx) {
//						String groupkeyStr = toStringFunc(groupKey);
//						String varnameP = "y" + i + "_" + groupkeyStr + "_"
//								+ projectionVariables.get(projectionRegionIdx).toString();
//						Long rowCountP = Long.parseLong(model.evaluate(unifiedctx.mkIntConst(varnameP), true).toString());
//						if (rowCountP == 0)
//							continue;
//						Pair<Long, Long> pTemp = new Pair<Long, Long>(rowCountP, 0L);// count and cut off
//						// The cut off is initially 0 which may be changed when regions are divided
//						RegionF interval = projectionVariables.get(projectionRegionIdx).interval;
//						Pair<RegionF, Pair<Long, Long>> p = new Pair<RegionF, Pair<Long, Long>>(
//								projectionVariables.get(projectionRegionIdx).interval, pTemp);
//						regionsSummary.get(regionIdx).groupKeyToRegionF.get(getColumnsIdx(groupKey)).add(p);
//
//						// adding the count to the split count
//						int colIdx = getColumnsIdx(groupKey).get(0);
//
//						double splitPoint = interval.at(0).at(0).at(0);// we plan to generate all distinct points
//																		// using
//																		// the first split point.
//						// this split point will be only present in this regionF
//
//						int splitPointIdx = bucketSplitPoints.get(colIdx).indexOf(splitPoint);
////							if(splitPointsCount.get(colIdx).get(splitPointIdx)!=0)
////								System.out.println();
////							if(colIdx==64)
////							System.out.println();
//						splitPointsCount.get(colIdx).set(splitPointIdx, rowCountP);
//
//						if (regionsSummary.get(regionIdx).groupKeyToRegionF.get(getColumnsIdx(groupKey)).isEmpty())
//							System.out.println("What the ...!?");
//					}
//				}
//				// count++;
//			}
//			// regions summary for every region in curr clique has been done.
//			List<RegionSummaryProjection> regionsSummaryList = new ArrayList<>();
//			regionsSummaryList.addAll(regionsSummary.values());// map to list. RegionIdx is lost but is no needed
//																// here
//																// on after
//			cliqueToRegionsSummary.add(regionsSummaryList);
//
//		}

//		if (PostgresVConfig.hydraVersions.contains(PostgresVConfig.HydraTypes.duplicationHydra)) {
//			long sumOfIntervalRegion = 0;
//			for (int i = 0; i < allIntervalRegions.size(); i++) {
//
//				// t17_c001_clique0interval8
//				long val = Long.parseLong(model.evaluate(unifiedctx.mkIntConst(allIntervalRegions.get(i)), true).toString());
//				if (val == 0) {
//					continue;
//				}
//
//				String interval = allIntervalRegions.get(i);
//				String fkey = interval.split("_clique")[0];
//
//				this.allIntervalRegionValueMap.put(allIntervalRegions.get(i), val);
//				sumOfIntervalRegion += val;
//				if (!this.fkeyToIntervalRegionMap.containsKey(fkey)) {
//					this.fkeyToIntervalRegionMap.put(fkey, new ArrayList<>());
//				}
//				this.fkeyToIntervalRegionMap.get(fkey).add(interval);
//
//			}
//
//			long sumOfIntervalisedRegion = 0;
//
//			for (int i = 0; i < allIntervalisedRegions.size(); i++) {
//
//				long val = Long
//						.parseLong(model.evaluate(unifiedctx.mkIntConst(allIntervalisedRegions.get(i)), true).toString());
//				if (val == 0) {
//					continue;
//				}
//
//				String intervalisedRegion = allIntervalisedRegions.get(i);
//
//				this.allIntervalisedRegionsMap.put(allIntervalisedRegions.get(i), val);
//				sumOfIntervalisedRegion += val;
//
//				String fkey = intervalisedRegion.split("_var")[0];
//				String varname = intervalisedRegion.split("_")[2] + "_" + intervalisedRegion.split("_")[3];
//
//				if (!varToIntervalisedRegionMapPerFkey.containsKey(fkey)) {
//					varToIntervalisedRegionMapPerFkey.put(fkey, new HashMap<>());
//				}
//				if (!varToIntervalisedRegionMapPerFkey.get(fkey).containsKey(varname)) {
//					varToIntervalisedRegionMapPerFkey.get(fkey).put(varname, new ArrayList<>());
//				}
//				varToIntervalisedRegionMapPerFkey.get(fkey).get(varname).add(intervalisedRegion);
//
//			}
//
//			for (int i = 0; i < allDxValues.size(); i++) {
//				// t17_c018_interval_0_d_0
//				long val = Long.parseLong(model.evaluate(unifiedctx.mkIntConst(allDxValues.get(i)), true).toString());
//				if (val == 0) {
//					continue;
//				}
//
//				this.allDxValuesMap.put(allDxValues.get(i), val);
//				String dxValue = allDxValues.get(i);
//				String fkey = dxValue.split("_interval_")[0];
//				int intervalIdx = Integer.parseInt(dxValue.split("_")[3]);
//				if (!intervalToDxValuePerFkey.containsKey(fkey)) {
//					intervalToDxValuePerFkey.put(fkey, new HashMap<>());
//				}
//				if (!intervalToDxValuePerFkey.get(fkey).containsKey(intervalIdx)) {
//					intervalToDxValuePerFkey.get(fkey).put(intervalIdx, new ArrayList<>());
//				}
//				intervalToDxValuePerFkey.get(fkey).get(intervalIdx).add(dxValue);
//
//			}
		}
//
//		onlySolvingSW.displayTimeAndDispose();

//		unifiedctx.close();
		return viewtoCCMap;

	}
	
	
	
	//PKR: varname change wala
	public List<LinkedList<VariableValuePair>> formAndSolveLPUnified(ConsistencyMakerType consistencyMakerType,
			FormalCondition[] consistencyConstraints, List<FormalCondition> conditions,
			List<Map<List<String>, List<Integer>>> cliqueToGroupkeyToRegionIdx,
			List<Map<List<String>, Map<FormalConditionAggregate, List<Integer>>>> cliqueToGroupkeyConditionToRegionIdx,
			List<Map<List<String>, Map<Integer, List<Integer>>>> cliqueToGroupkeyToRegionToProjectionVariablesOptimzed,
			List<Map<List<String>, List<ProjectionVariable>>> cliqueToGroupkeyToProjectionVariablesOptimized,
			HashMap<Set<String>, Set<String>> cliquesToFKeyCoverage) {

		// Map<String, String> contextmaptest = new HashMap<>();
		// contextmaptest.put("model", "true");
		// contextmaptest.put("unsat_core", "true");
		// Context ctxtest = new Context(contextmaptest);
		//
		// Optimize osolver = ctxtest.mkOptimize();
		// IntExpr x = ctxtest.mkIntConst("x");
		// IntExpr y = ctxtest.mkIntConst("y");
		// ArithExpr arithexpr = ctxtest.mkAdd(x, y);
		// osolver.Add(ctxtest.mkGt(arithexpr, ctxtest.mkInt(10)));
		// osolver.Add(ctxtest.mkLt(arithexpr, ctxtest.mkInt(20)));
		//
		// osolver.MkMaximize(arithexpr);
		//
		// osolver.Check();
		//
		// Model modeltest = osolver.getModel();
		// System.out.println(modeltest.evaluate(x, true) + " : " +
		// modeltest.evaluate(y, true));
		///////////////// End dk

		StopWatch onlyFormationSW = new StopWatch("LP-OnlyFormation" + viewname);

		Map<String, String> contextmap = new HashMap<>();
		contextmap.put("model", "true");
		contextmap.put("unsat_core", "true");
		Context ctx = new Context(contextmap);

		Optimize solver = ctx.mkOptimize();
		int projectionVarsIndex = 0;
		int type1 = 0, type2 = 0, type3 = 0, projectionCC = 0, filterCC = 0, consistencyCC = 0;
		List<List<List<IntExpr>>> solverConstraintsRequiredForConsistency = new ArrayList<>();
		// Create lp variables for cardinality constraints
		for (int cliqueIndex = 0; cliqueIndex < cliqueCount; cliqueIndex++) {

			LongList bvalues = cliqueIdxtoConditionBValuesList.get(cliqueIndex);
			Partition partition = cliqueIdxtoPList.get(cliqueIndex); // Partition is a list of regions corresponding to
																		// below labels
			List<IntList> conditionIdxsList = cliqueIdxtoPSimplifiedList.get(cliqueIndex); // Getting label

			HashMap<Integer, Integer> indexKeeper = null;
			int solverConstraintSize;

			if (consistencyMakerType == ConsistencyMakerType.CONSISTENCYFILTERS) {
				if (cliqueCount > 1) {
					indexKeeper = mappedIndexOfConsistencyConstraint.get(cliqueIndex);
					solverConstraintSize = bvalues.size() + indexKeeper.size();
				} else
					solverConstraintSize = bvalues.size();
			} else {
				indexKeeper = new HashMap<>();
				solverConstraintSize = bvalues.size() + cliqueWiseTotalSingleSplitPointRegions.get(cliqueIndex);
			}

			List<List<IntExpr>> solverConstraints = new ArrayList<>(solverConstraintSize);
			for (int j = 0; j < solverConstraintSize; j++) {
				solverConstraints.add(new ArrayList<>());
			}

			for (int blockIndex = 0; blockIndex < partition.size(); blockIndex++) {
				String varname = "var" + viewname + "_" + cliqueIndex + "_" + blockIndex;
				solverStats.solverVarCount++;

				// Adding non-negativity constraints
				solver.Add(ctx.mkGe(ctx.mkIntConst(varname), ctx.mkInt(0)));
				type1++;
				// Adds the region to all the constraints it belongs to
				for (IntIterator iter = conditionIdxsList.get(blockIndex).iterator(); iter.hasNext();) {
					int k = iter.nextInt();

					solverConstraints.get(k).add(ctx.mkIntConst(varname));
				}

			}
			// Adding filter constraints
			for (int conditionIndex = 0; conditionIndex < bvalues.size(); conditionIndex++) {
				long outputCardinality = bvalues.getLong(conditionIndex);
				List<IntExpr> addList = solverConstraints.get(conditionIndex);
				solver.Add(ctx.mkEq(ctx.mkAdd(addList.toArray(new ArithExpr[addList.size()])),
						ctx.mkInt(outputCardinality)));
				filterCC++;
				solverStats.solverConstraintCount++;
			}

//			---------------shadab----adding projection constraints-----------------------------

			Map<List<String>, List<ProjectionVariable>> groupkeyToProjectionVariablesOptimized = cliqueToGroupkeyToProjectionVariablesOptimized
					.get(cliqueIndex);

			for (List<String> groupkey : groupkeyToProjectionVariablesOptimized.keySet()) {
				String groupkeyStr = toStringFunc(groupkey);
				List<ProjectionVariable> projectionVariablesOptimized = groupkeyToProjectionVariablesOptimized
						.get(groupkey);
				for (int j = 0; j < projectionVariablesOptimized.size(); j++) {
					String varname = "y" + viewname + "_"+ cliqueIndex + "_" + groupkeyStr + "_"
							+ projectionVariablesOptimized.get(j).toString();
					solver.Add(ctx.mkGe(ctx.mkIntConst(varname), ctx.mkInt(0)));
					type1++;

				}
			}

			Map<List<String>, Map<Integer, List<Integer>>> groupkeyToRegionToProjectionVariablesOptimzed = cliqueToGroupkeyToRegionToProjectionVariablesOptimzed
					.get(cliqueIndex);

			for (List<String> groupkey : groupkeyToRegionToProjectionVariablesOptimzed.keySet()) {
				String groupkeyStr = toStringFunc(groupkey);

				List<ProjectionVariable> projectionVariablesOptimized = groupkeyToProjectionVariablesOptimized
						.get(groupkey);
				Map<Integer, List<Integer>> regionToProjectionVariablesOptimized = groupkeyToRegionToProjectionVariablesOptimzed
						.get(groupkey);
				for (Integer regionIdx : regionToProjectionVariablesOptimized.keySet()) {
					String varname = "var"+ viewname + "_" + cliqueIndex + "_" + regionIdx;
					List<IntExpr> projectionExpr = new ArrayList<>();
					for (Integer projVarIndx : regionToProjectionVariablesOptimized.get(regionIdx)) {
						projectionExpr.add(ctx.mkIntConst("y" + cliqueIndex + "_" + groupkeyStr + "_"
								+ projectionVariablesOptimized.get(projVarIndx).toString()));
					}

					if (!datasynthcomp) {
						solver.Add(
								ctx.mkGe(
										ctx.mkMul(ctx.mkInt(relationCardinality),
												ctx.mkAdd(
														projectionExpr.toArray(new ArithExpr[projectionExpr.size()]))),
										ctx.mkIntConst(varname)));
						type3++;
					}
					solver.Add(ctx.mkLe(ctx.mkAdd(projectionExpr.toArray(new ArithExpr[projectionExpr.size()])),
							ctx.mkIntConst(varname)));
					type2++;
				}
			}

			Map<List<String>, Map<FormalConditionAggregate, List<Integer>>> groupkeyConditionToRegionIdx = cliqueToGroupkeyConditionToRegionIdx
					.get(cliqueIndex);
			for (List<String> groupkey : groupkeyConditionToRegionIdx.keySet()) {
				String groupkeyStr = toStringFunc(groupkey);
				List<ProjectionVariable> projectionVariablesOptimized = groupkeyToProjectionVariablesOptimized
						.get(groupkey);

				Map<Integer, List<Integer>> regionsToProjectionVariables = cliqueToGroupkeyToRegionToProjectionVariablesOptimzed
						.get(cliqueIndex).get(groupkey);
				Map<FormalConditionAggregate, List<Integer>> conditionToRegionIdx = groupkeyConditionToRegionIdx
						.get(groupkey);
				for (FormalConditionAggregate condition : conditionToRegionIdx.keySet()) {
					List<IntExpr> projectionExpr = new ArrayList<>();
					List<Integer> regionsIdx = conditionToRegionIdx.get(condition);
					Set<Integer> projectionVariablesIdx = new HashSet<>();
					for (Integer regionIdx : regionsIdx) {
						projectionVariablesIdx.addAll(regionsToProjectionVariables.get(regionIdx));
					}

					// nonOverlappingSanityCheck(projectionVariablesIdx,projectionVariablesOptimized);

					for (Integer projectionVariableIdx : projectionVariablesIdx)
						projectionExpr.add(ctx.mkIntConst("y" + cliqueIndex + "_" + groupkeyStr + "_"
								+ projectionVariablesOptimized.get(projectionVariableIdx).toString()));
					solver.Add(ctx.mkEq(ctx.mkAdd(projectionExpr.toArray(new ArithExpr[projectionExpr.size()])),
							ctx.mkInt(condition.getProjectionCardinality())));
					projectionCC++;
				}
			}

			///////////////// Start dk
			if (cliqueCount > 1 && consistencyMakerType == ConsistencyMakerType.CONSISTENCYFILTERS) {
				List<List<IntExpr>> solverConstraintsToExport = new ArrayList<>(indexKeeper.size());
				for (int j = bvalues.size(); j < solverConstraintSize; j++) {
					solverConstraintsToExport.add(solverConstraints.get(j));
				}
				solverConstraintsToExport.add(solverConstraints.get(bvalues.size() - 1)); // Clique size
				solverConstraintsRequiredForConsistency.add(solverConstraintsToExport);
			}
		}

		// Consistency

		int countConsistencyConstraint = 0;
		if (cliqueCount > 1) {// TODO is necessary?
			if (consistencyMakerType == ConsistencyMakerType.CONSISTENCYFILTERS) {

				if (consistencyConstraints.length != 0) {
					for (int c1index = 0; c1index < cliqueCount; c1index++) {
						HashMap<Integer, Integer> c1indexKeeper = mappedIndexOfConsistencyConstraint.get(c1index);
						if (c1indexKeeper.isEmpty())
							continue;
						List<List<IntExpr>> c1solverConstraints = solverConstraintsRequiredForConsistency.get(c1index);
						for (int c2index = c1index + 1; c2index < cliqueCount; c2index++) {
							HashMap<Integer, Integer> c2indexKeeper = mappedIndexOfConsistencyConstraint.get(c2index);
							if (c2indexKeeper.isEmpty())
								continue;
							List<List<IntExpr>> c2solverConstraints = solverConstraintsRequiredForConsistency
									.get(c2index);
							Set<Integer> applicableConsistencyConstraints = new HashSet<>(c1indexKeeper.keySet());
							applicableConsistencyConstraints.retainAll(c2indexKeeper.keySet());
							if (applicableConsistencyConstraints.isEmpty())
								continue;
							List<List<IntExpr>> c1ApplicableSolverConstraints = new ArrayList<>();
							List<List<IntExpr>> c2ApplicableSolverConstraints = new ArrayList<>();
							for (Integer originalConsistencyConstraintIndex : applicableConsistencyConstraints) {
								c1ApplicableSolverConstraints.add(
										c1solverConstraints.get(c1indexKeeper.get(originalConsistencyConstraintIndex)));
								c2ApplicableSolverConstraints.add(
										c2solverConstraints.get(c2indexKeeper.get(originalConsistencyConstraintIndex)));
							}

							c1ApplicableSolverConstraints.add(c1solverConstraints.get(c1solverConstraints.size() - 1));
							c2ApplicableSolverConstraints.add(c2solverConstraints.get(c2solverConstraints.size() - 1));

							HashMap<IntList, MutablePair<List<IntExpr>, List<IntExpr>>> conditionListToPairOfVarList = new HashMap<>();
							addTo_ConditionListToPairOfVarList(c1ApplicableSolverConstraints,
									conditionListToPairOfVarList);
							addTo_ConditionListToPairOfVarList(c2ApplicableSolverConstraints,
									conditionListToPairOfVarList);

							// Set<String> commonCols = new HashSet<>(arasuCliques.get(c1index));
							// commonCols.retainAll(arasuCliques.get(c2index));

							for (MutablePair<List<IntExpr>, List<IntExpr>> pair : conditionListToPairOfVarList
									.values()) {
								List<IntExpr> c1Set = pair.getFirst();
								List<IntExpr> c2Set = pair.getSecond();
								ArithExpr set1expr = ctx.mkAdd(c1Set.toArray(new ArithExpr[c1Set.size()]));
								ArithExpr set2expr = ctx.mkAdd(c2Set.toArray(new ArithExpr[c2Set.size()]));
								solver.Add(ctx.mkEq(set1expr, set2expr));
								consistencyCC++;
								countConsistencyConstraint++;

								// 1-D projection
								// collectProjectionConsistencyData(solver,ctx, c1Set, c2Set, c1index, c2index,
								// commonCols, projectionConsistencyInfoPairs, cliqueWColumnWProjectionStuff);
							}
						}
					}
				}
			}
			///////////////// End dk

			else if (consistencyMakerType == ConsistencyMakerType.BRUTEFORCE) {
				for (CliqueIntersectionInfo cliqueIntersectionInfo : cliqueIntersectionInfos) { // Create lp variables
																								// for
																								// consistency
																								// constraints

					int i = cliqueIntersectionInfo.i;
					int j = cliqueIntersectionInfo.j;
					IntList intersectingColIndices = cliqueIntersectionInfo.intersectingColIndices;

					Partition partitionI = cliqueIdxtoPList.get(i);
					Partition partitionJ = cliqueIdxtoPList.get(j);

					// Recomputing SplitRegions for every pair of intersecting cliques
					// as the SplitRegions might have become more granular due to
					// some other pair of intersecting cliques having its intersectingColIndices
					// overlapping with this pair's intersectingColIndices
					List<Region> splitRegions = getSplitRegions(partitionI, partitionJ, intersectingColIndices);

					Set<String> commonCols = new HashSet<>(arasuCliques.get(i));
					commonCols.retainAll(arasuCliques.get(j));

					for (Region splitRegion : splitRegions) {
						List<IntExpr> consistencyLHS = new ArrayList<>();
						for (int k = 0; k < partitionI.size(); k++) {
							Region iVar = partitionI.at(k);

							Region truncRegion = getTruncatedRegion(iVar, intersectingColIndices);
							Region truncOverlap = truncRegion.intersection(splitRegion);
							if (!truncOverlap.isEmpty()) {
								String varname = "var" + viewname + "_"+ i + "_" + k;
								consistencyLHS.add(ctx.mkIntConst(varname));
							}
						}

						List<IntExpr> consistencyRHS = new ArrayList<>();
						for (int k = 0; k < partitionJ.size(); k++) {
							Region jVar = partitionJ.at(k);

							Region truncRegion = getTruncatedRegion(jVar, intersectingColIndices);
							Region truncOverlap = truncRegion.intersection(splitRegion);
							if (!truncOverlap.isEmpty()) {
								String varname = "var" + viewname + "_"+ j + "_" + k;
								consistencyRHS.add(ctx.mkIntConst(varname));
							}
						}

						// Adding consistency constraints
						solver.Add(ctx.mkEq(ctx.mkAdd(consistencyLHS.toArray(new ArithExpr[consistencyLHS.size()])),
								ctx.mkAdd(consistencyRHS.toArray(new ArithExpr[consistencyRHS.size()]))));
						solverStats.solverConstraintCount++;
						countConsistencyConstraint++;

					}
				}
			} else {
				ctx.close();
				throw new RuntimeException("Unknown consistency maker " + consistencyMakerType);
			}
		}
		DebugHelper.printInfo("countConsistencyConstraint for " + viewname + " = " + countConsistencyConstraint);

		List<String> allIntervalRegions = new ArrayList<>(); // List of all intervals
		List<String> allIntervalisedRegions = new ArrayList<>(); // List of all intervalised regions
		List<String> allDxValues = new ArrayList<>();

		if (PostgresVConfig.hydraVersions.contains(PostgresVConfig.HydraTypes.duplicationHydra)) {

			// New variables
			Map<String, List<String>> allIntervalRegionsVariables = new HashMap<>();
			Map<String, List<String>> allDxValuesVariables = new HashMap<>();
			Map<String, List<String>> allIntervalisedRegionsVariables = new HashMap<>();
			Map<String, HashMap<String, List<Integer>>> varToIntervalMapPerFKey = new HashMap<>();

			if (PostgresVConfig.fkeyToBorrowedAttr.containsKey(viewname)) {

				Map<String, Set<String>> fkeyToBorrowedAttr = PostgresVConfig.fkeyToBorrowedAttr.get(viewname);

				for (String fkey : fkeyToBorrowedAttr.keySet()) {

					allIntervalRegionsVariables.put(fkey, new ArrayList<>());
					allDxValuesVariables.put(fkey, new ArrayList<>());
					allIntervalisedRegionsVariables.put(fkey, new ArrayList<>());
					varToIntervalMapPerFKey.put(fkey, new HashMap<>());
					Set<String> currentClique = null;
					Integer currentCliqueIdx = null;

					for (int c = 0; c < this.arasuCliques.size(); c++) {
						Set<String> clique = this.arasuCliques.get(c);
						if (!cliquesToFKeyCoverage.containsKey(clique)) {
							continue;
						}
						Set<String> fkeysCovered = cliquesToFKeyCoverage.get(clique);
						if (fkeysCovered.contains(fkey)) {
							currentClique = clique;
							currentCliqueIdx = c;
							break;
						}

					}

					if (currentClique == null) {
						throw new RuntimeException("Something wrong can't be possible");
					}

					fkeyToCliqueIdx.put(fkey, currentCliqueIdx);

					Set<String> borrowedAttr = fkeyToBorrowedAttr.get(fkey);
					List<String> sortedBorrowedAttr = new ArrayList<>(borrowedAttr);
					List<Integer> borrowedAttrIdx = new ArrayList<>();
					Collections.sort(sortedBorrowedAttr);
					int c = 0;
					for (int i = 0; i < sortedViewColumns.size(); i++) {

						if (sortedBorrowedAttr.get(c).contentEquals(sortedViewColumns.get(i))) {

							borrowedAttrIdx.add(i);
							c = c + 1;
						}
						if (c == sortedBorrowedAttr.size()) {
							break;
						}

					}

					int noOfIntervalRegions = 1;
					List<List<Integer>> borrowedAttrIntervals = new ArrayList<>();
					Partition partition = cliqueIdxtoPList.get(currentCliqueIdx);
					for (int bucket : borrowedAttrIdx) {

						Set<Integer> intervals = new HashSet<>();
						for (Region r : partition.getAll()) {

							for (BucketStructure bs : r.getAll()) {

								intervals.addAll((bs.at(bucket).getAll()));

							}

						}
						noOfIntervalRegions *= intervals.size();
						ArrayList<Integer> intervalsList = new ArrayList<>(intervals);
						Collections.sort(intervalsList);
						borrowedAttrIntervals.add(intervalsList);

					}

					List<List<Integer>> intervalRegions = new ArrayList<>();
					for (int i = 0; i < noOfIntervalRegions; i++) {

						intervalRegions.add(new ArrayList<>());
					}

					int count = 0;
					int row = 0;
					while (count < noOfIntervalRegions) {

						int currentRowSize = borrowedAttrIntervals.get(row).size();

						if (count > 0) {

							int currentIndex = 0;
							List<List<Integer>> copyofIntervalRegionList = new ArrayList<>();
							for (int i = 0; i < intervalRegions.size(); i++) {
								List<Integer> temp = new ArrayList<Integer>();
								copyofIntervalRegionList.add(temp);
								for (int j = 0; j < intervalRegions.get(i).size(); j++) {
									temp.add(intervalRegions.get(i).get(j));
								}

							}
							for (int j = 0; j < currentRowSize; j++) {
								Integer val = borrowedAttrIntervals.get(row).get(j);
								for (int i = 0; i < count; i++) {
									List<Integer> w = new ArrayList<>(copyofIntervalRegionList.get(i));
									w.add(val);
									intervalRegions.set(currentIndex, w);
									currentIndex++;
								}
							}
							row = row + 1;
							count *= currentRowSize;

						} else {

							int currentIndex = 0;
							for (int j = 0; j < currentRowSize; j++) {

								Integer val = borrowedAttrIntervals.get(row).get(j);
								List<Integer> w = new ArrayList<>();
								w.add(val);

								intervalRegions.set(currentIndex, w);
								currentIndex++;

							}

							count = currentRowSize;
							row = row + 1;

						}

					}

					HashMap<Integer, String> Z3name = new HashMap<>();
					for (int i = 0; i < intervalRegions.size(); i++) {
						String intervalname = fkey + "_clique" + currentCliqueIdx + "interval" + i;
						allIntervalRegionsVariables.get(fkey).add(intervalname);
						Z3name.put(i, intervalname);
					}

					// Adding sum of all intervals to total tuple cout
					ArithExpr[] sumOfIntervalRegions = new ArithExpr[intervalRegions.size()];
					c = 0;
					allIntervalRegionsPerFKey.put(fkey, intervalRegions);
					for (Integer interval : Z3name.keySet()) {

						String intervalName = Z3name.get(interval);
						solver.Add(ctx.mkGe(ctx.mkIntConst(intervalName), ctx.mkInt(0)));
						allIntervalRegions.add(intervalName);
						sumOfIntervalRegions[c++] = ctx.mkIntConst(intervalName);

					}

					c = 0;
					ArithExpr[] sumOfPartitionedRegions = new ArithExpr[partition.size()];
					for (int r = 0; r < partition.size(); r++) {

						String varname = "var" + currentCliqueIdx + "_" + r;
						varToIntervalMapPerFKey.get(fkey).put(varname, new ArrayList<>());
						sumOfPartitionedRegions[c++] = ctx.mkIntConst(varname);

					}
					// adding all vars = all clique intervals
					solver.Add(ctx.mkEq(ctx.mkAdd(sumOfPartitionedRegions), ctx.mkAdd(sumOfIntervalRegions)));

					fkeyToActualInteervalisedRegMap.put(fkey, intervalisedRegionMap);
					Map<Integer, List<String>> intervalRegionToPartionedRegionsMap = new HashMap<>();
					for (int r = 0; r < partition.size(); r++) {

						Region region = partition.at(r);
						String regionName = "var" + currentCliqueIdx + "_" + r;
						List<String> regionPartitionList = new ArrayList<>();
						for (int i = 0; i < intervalRegions.size(); i++) {

							List<Integer> intervalRegion = intervalRegions.get(i);
							boolean flag = false;
							int bsIdx = 0;

							for (BucketStructure bs : region.getAll()) {

								c = 0;
								for (int bucketIdx : borrowedAttrIdx) {
									Bucket bucket = bs.at(bucketIdx);
									if (bucket.contains(intervalRegion.get(c))) {
										c = c + 1;
									} else {

										break;
									}

								}

								if (c == borrowedAttrIdx.size()) {
									flag = true;
									break;
								}
								bsIdx++;

							}

							if (flag) {
								String intervalisedRegionName = fkey + "_var" + currentCliqueIdx + "_" + r
										+ "_interval_" + i;
								BucketStructure bucketStructure = region.at(bsIdx);
								BucketStructure bsNew = new BucketStructure();

								int ci = 0;
								for (int bi = 0; bi < bucketStructure.size(); bi++) {

									Bucket bucket = new Bucket();
									if (bi == borrowedAttrIdx.get(ci)) {
										bucket.add(intervalRegion.get(ci));
									} else {
										bucket = bucketStructure.at(bi);
									}
									bsNew.add(bucket);

								}

								Region newR = new Region();
								newR.add(bsNew);

								intervalisedRegionMap.put(intervalisedRegionName, newR);
								regionPartitionList.add(intervalisedRegionName);
								allIntervalisedRegions.add(intervalisedRegionName);
								allIntervalisedRegionsVariables.get(fkey).add(intervalisedRegionName);
								varToIntervalMapPerFKey.get(fkey).get("var" + currentCliqueIdx + "_" + r).add(i);
								if (!intervalRegionToPartionedRegionsMap.containsKey(i)) {
									intervalRegionToPartionedRegionsMap.put(i, new ArrayList<>());
								}
								intervalRegionToPartionedRegionsMap.get(i).add(intervalisedRegionName);
								solver.Add(ctx.mkGe(ctx.mkIntConst(intervalisedRegionName), ctx.mkInt(0)));
							}

						}

						ArithExpr[] regionPartitionArray = new ArithExpr[regionPartitionList.size()];
						for (int i = 0; i < regionPartitionList.size(); i++) {

							regionPartitionArray[i] = ctx.mkIntConst(regionPartitionList.get(i));

						}

						// sum of intervalised regions = var
						solver.Add(ctx.mkEq(ctx.mkAdd(regionPartitionArray), ctx.mkIntConst(regionName)));

					}

					System.out.print("");

					for (int intervalIdx : intervalRegionToPartionedRegionsMap.keySet()) {

						List<String> regionNames = intervalRegionToPartionedRegionsMap.get(intervalIdx);

						ArithExpr[] regionArray = new ArithExpr[regionNames.size()];
						for (int i = 0; i < regionNames.size(); i++) {
							regionArray[i] = ctx.mkIntConst(regionNames.get(i));
						}

						solver.Add(ctx.mkEq(ctx.mkAdd(regionArray), ctx.mkIntConst(Z3name.get(intervalIdx))));

					}

					JSONArray dfVector = PostgresVConfig.fkeySkewVectors.getJSONObject(viewname).getJSONArray(fkey);
					JSONArray d = dfVector.getJSONArray(0);
					JSONArray f = dfVector.getJSONArray(1);

					for (Integer i = 0; i < intervalRegions.size(); i++) {
						ArithExpr[] dxSumm = new ArithExpr[d.length()];
						for (int d_i = 0; d_i < d.length(); d_i++) {

							String x = fkey + "_interval_" + i + "_d_" + d_i;
							solver.Add(ctx.mkGe(ctx.mkIntConst(x), ctx.mkInt(0)));
							allDxValuesVariables.get(fkey).add(x);
							allDxValues.add(x);
							ArithExpr xd = ctx.mkMul(ctx.mkIntConst(x), ctx.mkInt(d.getInt(d_i)));
							dxSumm[d_i] = xd;

						}
						String intervalname = Z3name.get(i);
						solver.Add(ctx.mkEq(ctx.mkAdd(dxSumm), ctx.mkIntConst(Z3name.get(i))));
					}

					for (int d_i = 0; d_i < d.length(); d_i++) {

						ArithExpr[] xfSumm = new ArithExpr[intervalRegions.size()];
						for (int i = 0; i < intervalRegions.size(); i++) {

							String x = fkey + "_interval_" + i + "_d_" + d_i;
							xfSumm[i] = ctx.mkIntConst(x);

						}

						solver.Add(ctx.mkEq(ctx.mkAdd(xfSumm), ctx.mkInt(f.getInt(d_i))));

					}

				}

				// Adding equations for CCs skew

				Map<String, Map<String, Set<String>>> fkeyToBR = PostgresVConfig.fkeyToBorrowedAttr;
				for (FormalCondition condition : conditions) {

					Integer counter = condition.getCounter();
					String queryname = condition.getQueryname();
					List<FormalCondition> conditionList = new ArrayList<>();
					conditionList.add(condition);
					String fkey = findFkey(conditionList);
					// CC having no foreign key column
					if (fkey == null) {
						continue;
					}
					// No borrowed attr for fkey
					if (!fkeyToBR.containsKey(fkey)) {
						continue;
					}
					String actualFKey = PostgresVConfig.reverseColumnAnonyMap.get(fkey);
					String dfVec = actualFKey + "___" + counter + "_" + queryname;

					DFvector dfvector = PostgresVConfig.ccsDFvectors.get(dfVec);
					List<Long> dValues = dfvector.getD();
					List<Long> fValues = dfvector.getF();
					List<List<Integer>> intervalRegions = this.allIntervalRegionsPerFKey.get(fkey);
					// String x = fkey + "_interval_" + i + "_d_" + d_i;

					// find CCs intersecting with intervals

					Map<String, Region> intervalisedRegions = this.fkeyToActualInteervalisedRegMap.get(fkey);
					Set<Integer> intersectingIntervals = findCCsIntersectingWithIntervals(condition,
							intervalisedRegions);

					JSONArray fkeyBaseSkewVectors = PostgresVConfig.fkeySkewVectors.getJSONObject(viewname)
							.getJSONArray(fkey);
					JSONArray baseDValues = fkeyBaseSkewVectors.getJSONArray(0);
					JSONArray baseFValues = fkeyBaseSkewVectors.getJSONArray(1);

					long fCount = 0;
					for (int di = 0; di < dValues.size(); di++) {

						Long fVal = fValues.get(di);
						Long dVal = dValues.get(di);
						ArithExpr[] dxArray = new ArithExpr[intersectingIntervals.size()];
						for (int bdi = 0; bdi < baseDValues.length(); bdi++) {
							long baseDval = baseDValues.getLong(bdi);
							if (baseDval < dVal) {
								break;
							} else {

								int c = 0;
								for (int intervalIdx : intersectingIntervals) {

									dxArray[c] = ctx.mkIntConst(fkey + "_interval_" + intervalIdx + "_d_" + di);
									c = c + 1;
								}

							}

						}

						solver.Add(ctx.mkGe(ctx.mkAdd(dxArray), ctx.mkInt(fVal - fCount)));
						fCount += fVal;

					}

					System.out.print("");

				}

			}

		}

		onlyFormationSW.displayTimeAndDispose();

		// Dumping LP into a file -- Anupam
		// start
		/*
		 * FileWriter fw; try { fw = new FileWriter("lpfile-" + viewname + ".txt");
		 * fw.write(solver.toString()); fw.close(); } catch (IOException e) { // TODO
		 * Auto-generated catch block e.printStackTrace(); }
		 */
		// System.err.println(solver.toString());
		// stop

		StopWatch onlySolvingSW = new StopWatch("LP-OnlySolving" + viewname);

		Status solverStatus = solver.Check();
		DebugHelper.printInfo("Solver Status: " + solverStatus);

		if (!Status.SATISFIABLE.equals(solverStatus)) {
			ctx.close();
			throw new RuntimeException("solverStatus is not SATISFIABLE");
		}

		Model model = solver.getModel();

		List<LinkedList<VariableValuePair>> cliqueIdxToVarValuesList = new ArrayList<>(cliqueCount);
		for (int i = 0; i < cliqueCount; i++) {

			IntList colIndxs = arasuCliquesAsColIndxs.get(i);
			Partition partition = cliqueIdxtoPList.get(i);
			LinkedList<VariableValuePair> varValuePairs = new LinkedList<>();
			for (int j = 0; j < partition.size(); j++) {
				String varname = "var" + i + "_" + j;

				// Variable to column indices mapping -- Anupam
				// start
				FileWriter fw1;
				try {
					fw1 = new FileWriter(viewname + "-var-to-colindices.txt", true);
					fw1.write(varname + " " + colIndxs.toString() + "\n");
					fw1.close();
				} catch (IOException e) {
					// TODO Auto-generated catch block
					e.printStackTrace();
				}
				// stop
				// System.err.println(varname+colIndxs.toString());
				long rowcount = Long.parseLong(model.evaluate(ctx.mkIntConst(varname), true).toString());
				// Variable to value mapping -- Anupam
				// start
				FileWriter fw2;
				try {
					fw2 = new FileWriter(viewname + "-var-to-value.txt", true);
					fw2.write(varname + " " + rowcount + "\n");
					fw2.close();
				} catch (IOException e) {
					// TODO Auto-generated catch block
					e.printStackTrace();
				}
				// stop
				if (rowcount != 0) {
					Region variable = getTruncatedRegion(partition.at(j), colIndxs);
					VariableValuePair varValuePair = new VariableValuePair(variable, rowcount);
					varValuePairs.add(varValuePair);
				}
			}
			cliqueIdxToVarValuesList.add(varValuePairs);

			Map<Integer, RegionSummaryProjection> regionsSummary = new HashMap<>();
			// int idx=0;

			for (int idx = 0; idx < cliqueIdxtoPList.get(i).size(); idx++) {
				Region reg = cliqueIdxtoPList.get(i).getAll().get(idx);
				String varname = "var" + i + "_" + idx;
				long rowcount = Long.parseLong(model.evaluate(ctx.mkIntConst(varname), true).toString());
				if (rowcount == 0)
					continue;
				RegionSummaryProjection regSum = new RegionSummaryProjection();
				regSum.region = getTruncatedRegion(reg, colIndxs);
				regSum.rowCount = rowcount;
				regionsSummary.put(idx, regSum);

			}

			Map<List<String>, Map<Integer, List<Integer>>> groupkeyToRegionToProjectionVariablesOptimzed = cliqueToGroupkeyToRegionToProjectionVariablesOptimzed
					.get(i);
			// int count=0;
			for (List<String> groupKey : groupkeyToRegionToProjectionVariablesOptimzed.keySet()) {

				List<ProjectionVariable> projectionVariables = cliqueToGroupkeyToProjectionVariablesOptimized.get(i)
						.get(groupKey);// all projection variables of the groupkey in the clique
				Map<Integer, List<Integer>> regionToProjectionVariablesOptimzed = groupkeyToRegionToProjectionVariablesOptimzed
						.get(groupKey);
				for (Integer regionIdx : regionToProjectionVariablesOptimzed.keySet()) {
					String varnameRegion = "var" + i + "_" + regionIdx;
					long rowcountR = Long.parseLong(model.evaluate(ctx.mkIntConst(varnameRegion), true).toString());
					if (rowcountR == 0)
						continue;
					regionsSummary.get(regionIdx).groupkeys.add(groupKey);// adding the groupkey for this region in
																			// the
																			// regionsSummary

					List<Integer> projectionRegionsIdx = regionToProjectionVariablesOptimzed.get(regionIdx);
					// regionsSummary.get(regionIdx).groupKeyToRegionF.add(new ArrayList<>());
					regionsSummary.get(regionIdx).groupKeyToRegionF.put(getColumnsIdx(groupKey), new ArrayList<>());
					for (Integer projectionRegionIdx : projectionRegionsIdx) {
						String groupkeyStr = toStringFunc(groupKey);
						String varnameP = "y" + i + "_" + groupkeyStr + "_"
								+ projectionVariables.get(projectionRegionIdx).toString();
						Long rowCountP = Long.parseLong(model.evaluate(ctx.mkIntConst(varnameP), true).toString());
						if (rowCountP == 0)
							continue;
						Pair<Long, Long> pTemp = new Pair<Long, Long>(rowCountP, 0L);// count and cut off
						// The cut off is initially 0 which may be changed when regions are divided
						RegionF interval = projectionVariables.get(projectionRegionIdx).interval;
						Pair<RegionF, Pair<Long, Long>> p = new Pair<RegionF, Pair<Long, Long>>(
								projectionVariables.get(projectionRegionIdx).interval, pTemp);
						regionsSummary.get(regionIdx).groupKeyToRegionF.get(getColumnsIdx(groupKey)).add(p);

						// adding the count to the split count
						int colIdx = getColumnsIdx(groupKey).get(0);

						double splitPoint = interval.at(0).at(0).at(0);// we plan to generate all distinct points
																		// using
																		// the first split point.
						// this split point will be only present in this regionF

						int splitPointIdx = bucketSplitPoints.get(colIdx).indexOf(splitPoint);
//							if(splitPointsCount.get(colIdx).get(splitPointIdx)!=0)
//								System.out.println();
//							if(colIdx==64)
//							System.out.println();
						splitPointsCount.get(colIdx).set(splitPointIdx, rowCountP);

						if (regionsSummary.get(regionIdx).groupKeyToRegionF.get(getColumnsIdx(groupKey)).isEmpty())
							System.out.println("What the ...!?");
					}
				}
				// count++;
			}
			// regions summary for every region in curr clique has been done.
			List<RegionSummaryProjection> regionsSummaryList = new ArrayList<>();
			regionsSummaryList.addAll(regionsSummary.values());// map to list. RegionIdx is lost but is no needed
																// here
																// on after
			cliqueToRegionsSummary.add(regionsSummaryList);

		}

		if (PostgresVConfig.hydraVersions.contains(PostgresVConfig.HydraTypes.duplicationHydra)) {
			long sumOfIntervalRegion = 0;
			for (int i = 0; i < allIntervalRegions.size(); i++) {

				// t17_c001_clique0interval8
				long val = Long.parseLong(model.evaluate(ctx.mkIntConst(allIntervalRegions.get(i)), true).toString());
				if (val == 0) {
					continue;
				}

				String interval = allIntervalRegions.get(i);
				String fkey = interval.split("_clique")[0];

				this.allIntervalRegionValueMap.put(allIntervalRegions.get(i), val);
				sumOfIntervalRegion += val;
				if (!this.fkeyToIntervalRegionMap.containsKey(fkey)) {
					this.fkeyToIntervalRegionMap.put(fkey, new ArrayList<>());
				}
				this.fkeyToIntervalRegionMap.get(fkey).add(interval);

			}

			long sumOfIntervalisedRegion = 0;

			for (int i = 0; i < allIntervalisedRegions.size(); i++) {

				long val = Long
						.parseLong(model.evaluate(ctx.mkIntConst(allIntervalisedRegions.get(i)), true).toString());
				if (val == 0) {
					continue;
				}

				String intervalisedRegion = allIntervalisedRegions.get(i);

				this.allIntervalisedRegionsMap.put(allIntervalisedRegions.get(i), val);
				sumOfIntervalisedRegion += val;

				String fkey = intervalisedRegion.split("_var")[0];
				String varname = intervalisedRegion.split("_")[2] + "_" + intervalisedRegion.split("_")[3];

				if (!varToIntervalisedRegionMapPerFkey.containsKey(fkey)) {
					varToIntervalisedRegionMapPerFkey.put(fkey, new HashMap<>());
				}
				if (!varToIntervalisedRegionMapPerFkey.get(fkey).containsKey(varname)) {
					varToIntervalisedRegionMapPerFkey.get(fkey).put(varname, new ArrayList<>());
				}
				varToIntervalisedRegionMapPerFkey.get(fkey).get(varname).add(intervalisedRegion);

			}

			for (int i = 0; i < allDxValues.size(); i++) {
				// t17_c018_interval_0_d_0
				long val = Long.parseLong(model.evaluate(ctx.mkIntConst(allDxValues.get(i)), true).toString());
				if (val == 0) {
					continue;
				}

				this.allDxValuesMap.put(allDxValues.get(i), val);
				String dxValue = allDxValues.get(i);
				String fkey = dxValue.split("_interval_")[0];
				int intervalIdx = Integer.parseInt(dxValue.split("_")[3]);
				if (!intervalToDxValuePerFkey.containsKey(fkey)) {
					intervalToDxValuePerFkey.put(fkey, new HashMap<>());
				}
				if (!intervalToDxValuePerFkey.get(fkey).containsKey(intervalIdx)) {
					intervalToDxValuePerFkey.get(fkey).put(intervalIdx, new ArrayList<>());
				}
				intervalToDxValuePerFkey.get(fkey).get(intervalIdx).add(dxValue);

			}
		}

		onlySolvingSW.displayTimeAndDispose();

		ctx.close();
		return cliqueIdxToVarValuesList;

	}

	
	//merge align methods start

	private ViewSolutionRegion mergeCliqueSolutionsRegionwiseProjection(List<FormalCondition> conditions,
			List<Region> conditionRegions) {
		Set<String> columns = new HashSet<>();
		for (Set<String> clique : arasuCliques) {
			columns.addAll(clique);
		}

		StopWatch postLPsolutionSW = new StopWatch("merging " + viewname);
		IntList mergedColIndxs = new IntArrayList();
		List<RegionSummaryProjection> finalRegionSummary = new ArrayList<>();
		mergedColIndxs.addAll(arasuCliquesAsColIndxs.get(0));

		// Instantiating variables of first clique

		for (RegionSummaryProjection regSum : cliqueToRegionsSummary.get(0)) {
			finalRegionSummary.add(regSum);
		}

		// Shadab, mergeWithAlignmentRegionwise deletes the regions from
		// arasuCliquesAsColIndxs. So if regions are needed post merging too, then make
		// a deep copy in the function.
		for (int i = 1; i < cliqueCount; i++) {
//			System.out.println(i);
			mergeWithAlignmentRegionwiseProjection(mergedColIndxs, finalRegionSummary, arasuCliquesAsColIndxs.get(i),
					cliqueToRegionsSummary.get(i));
		}

//		Uncomment to write summary
//		
//		
//		DatabaseSummaryProjection summ = new DatabaseSummaryProjection(finalRegionSummary);
//		try {
//			FileOutputStream f = new FileOutputStream("ProjectionSummary.txt", true);
//			ObjectOutputStream o = new ObjectOutputStream(f);
//
//			// Write objects to file
//			o.writeObject(summ);
//			// o.writeObject(p2);
//			System.out.println("Summary written for view" + viewname);
//			o.close();
//			f.close();
//
//		} catch (FileNotFoundException e) {
//			throw new RuntimeException("file not found");
//		} catch (IOException e) {
//			throw new RuntimeException("Error initializing stream");
//		}
		finalRegionSummaryGlobal = finalRegionSummary;

		if (wantAccuracy) {
			for (RegionSummaryProjection regSum : finalRegionSummary) {
				getRegionValueCombination(regSum, mergedColIndxs);

			}
			for (int j = 0; j < conditions.size(); j++) {

				Region currCRegion = conditionRegions.get(j);

				FormalCondition condition = conditions.get(j);
				checkAccuracy(condition, currCRegion, finalRegionSummary, mergedColIndxs);
			}
		}
		postLPsolutionSW.displayTimeAndDispose();
		// On the fly tuple generation begins.

		StopWatch onTheFlySW = new StopWatch("On-the fly time " + viewname);
		// initializing each region summary with a corner tuple
		for (RegionSummaryProjection regSum : finalRegionSummaryGlobal) {
			regSum.intialize(mergedColIndxs, bucketSplitPoints, splitPointsCount, getExpandedRegion(regSum.region),
					allTrueBS.size());
		}

		summIter = finalRegionSummaryGlobal.listIterator();
		regSum = summIter.next();
		
		ArrayList<List<Double> > table = new ArrayList<List<Double> >();
//		List<Double> list1 = new ArrayList<Double>();
		
		String tn = "t07";

		if (tupleGen) {
			if (viewname.equals(tn) ) {
			for (long i = 0; i < relationCardinality; i++) {
//				getNextRec();
				List<Double> list1 = getNextRec();
				if (list1.size()!=0)
					table.add(list1);
			}
//			int count=0;
//			for (int i = 0; i < table.size(); i++) {
//				if (table.get(i).get(6)<=1207)
//					count++;
//			}
//			System.out.print(count);
		}
		}
		
		JSONObject obj = new JSONObject();
		obj.put("columns", sortedViewColumns);
		obj.put(viewname,table);
//		FileUtils.writeStringToFile(viewname+".txt", obj.toString());
		
		onTheFlySW.displayTimeAndDispose();
		return null;
		
	
	}

	private void mergeWithAlignmentRegionwiseProjection(IntList lhsColIndxs, List<RegionSummaryProjection> finalRegionSummay,
			IntList rhsColIndxs, List<RegionSummaryProjection> rhsRegionSummary) {

		// Shadab-"snitches get stiches"
		// System.out.println("Shadab has reached here");
		IntList tempColIndxs = new IntArrayList(rhsColIndxs);
		tempColIndxs.removeAll(lhsColIndxs);
		IntList sharedColIndxs = new IntArrayList(rhsColIndxs);
		sharedColIndxs.removeAll(tempColIndxs);
		IntList posInLHS = new IntArrayList(sharedColIndxs.size());
		IntList posInRHS = new IntArrayList(sharedColIndxs.size());
		for (IntIterator iter = sharedColIndxs.iterator(); iter.hasNext();) {
			int sharedColIndx = iter.nextInt();
			posInLHS.add(lhsColIndxs.indexOf(sharedColIndx));
			posInRHS.add(rhsColIndxs.indexOf(sharedColIndx));
		}

		IntList mergedColIndxsList = new IntArrayList(lhsColIndxs);
		mergedColIndxsList.addAll(rhsColIndxs);
		mergedColIndxsList = new IntArrayList(new IntOpenHashSet(mergedColIndxsList));
		Collections.sort(mergedColIndxsList);

		boolean[] fromLHS = new boolean[mergedColIndxsList.size()];
		int[] correspOriginalIndx = new int[mergedColIndxsList.size()];
		for (int i = 0; i < mergedColIndxsList.size(); i++) {
			fromLHS[i] = lhsColIndxs.contains(mergedColIndxsList.get(i));
			if (fromLHS[i]) {
				correspOriginalIndx[i] = lhsColIndxs.indexOf(mergedColIndxsList.get(i));
			} else {
				correspOriginalIndx[i] = rhsColIndxs.indexOf(mergedColIndxsList.get(i));
			}
		}
		// adds the index of merged columns(from rhs or lhs)
		int count = 0;
		List<VariableValuePair> mergedVarValuePairs = new ArrayList<>();// new table after merging
		List<RegionSummaryProjection> mergedSummary = new ArrayList<>();
//		for (RegionSummaryProjection lhsSum : finalRegionSummay) {
		for (int idx = 0; idx < finalRegionSummay.size(); idx++) {
			RegionSummaryProjection lhsSum = finalRegionSummay.get(idx);
//			Region lhsRegion = lhsVarValue.variable;
			Region lhsRegion = lhsSum.region;
			long lhsRowcount = lhsSum.rowCount;
			boolean check = false;
			count++;
			// int ind = 0;
			for (ListIterator<RegionSummaryProjection> rhsIter = rhsRegionSummary.listIterator(); rhsIter.hasNext();) {
				RegionSummaryProjection rhsSum = rhsIter.next();
				Region rhsVariable = rhsSum.region;
				long rhsRowcount = rhsSum.rowCount;
				// ind++;
				// if (checkCompatibleRegions(posInLHS, lhsRegion, posInRHS, rhsVariable)) {//
				// if rhsregion is compatible
				// check = true;

				Region mergedTemp = new Region();// contains the region for the intersection of the two regions
				// int totBS = 0;

				for (int i = 0; i < lhsRegion.size(); i++) {// iterate over each clause
					BucketStructure lhsBS = lhsRegion.at(i);
					// int totmatch = 0;
					for (int j = 0; j < rhsVariable.size(); j++) {
						BucketStructure rhsBS = rhsVariable.at(j);
						BucketStructure mergedBS = new BucketStructure();// chceck -----------------contains the new
																			// clause
						if (isCompatibleBS(posInLHS, lhsBS, posInRHS, rhsBS)) {
							// totmatch++;
							// totBS++;
							int counter = 0;
							for (int k = 0; k < mergedColIndxsList.size(); k++) {
								if (sharedColIndxs.size() > counter
										&& mergedColIndxsList.get(k) == sharedColIndxs.get(counter)) {
									int lhsInd = posInLHS.get(counter);
									int rhsInd = posInRHS.get(counter);
									counter++;
									Bucket inter = Bucket.getIntersection(lhsBS.at(lhsInd), rhsBS.at(rhsInd));

									mergedBS.add(inter);
								} else if (fromLHS[k]) {
									mergedBS.add(lhsBS.at(correspOriginalIndx[k]));
									// mergedColValues.add(lhsColValues.getInt(correspOriginalIndx[j]));
								} else {
									mergedBS.add(rhsBS.at(correspOriginalIndx[k]));
								}
							}
							mergedTemp.add(mergedBS);
						}

					}
				}
				if (mergedTemp.isEmpty())
					continue;
				else {
					check = true;
					sanityCheckFullOverlap(posInLHS, lhsRegion, posInRHS, rhsVariable);
				}
				// do the rowcount
				if (lhsRowcount <= rhsRowcount) {
					RegionSummaryProjection mergedRegionSummary = new RegionSummaryProjection();
					mergedRegionSummary.region = mergedTemp;
					mergedRegionSummary.rowCount = lhsRowcount;
					mergedRegionSummary.groupkeys = new HashSet<>(lhsSum.groupkeys);
					mergedRegionSummary.groupkeys.addAll(rhsSum.groupkeys);// checked till here
					mergedRegionSummary.groupKeyToRegionF = lhsSum.groupKeyToRegionF;
					// VariableValuePair mergedVariable = new VariableValuePair(mergedTemp,
					// lhsRowcount);
					// mergedVarValuePairs.add(mergedVariable);
					mergedSummary.add(mergedRegionSummary);
					// lhsValueCombination.reduceRowcount(lhsRowcount);
					lhsSum.rowCount = 0L;

					if (rhsSum.rowCount == lhsRowcount) {
						mergedRegionSummary.groupKeyToRegionF.putAll(rhsSum.groupKeyToRegionF);
						rhsIter.remove();// removes this region from RHSvar
						rhsSum.rowCount -= lhsRowcount;// why needed?
					} else {
						RegionSummaryProjection brokenNew = rhsSum.divide(lhsRowcount);// rhs retains lhsrowcount tuples andbroken
																				// gets rest
						mergedRegionSummary.groupKeyToRegionF.putAll(rhsSum.groupKeyToRegionF);
						rhsIter.remove();
						// rhsIter.
						rhsRegionSummary.add(brokenNew);
					}
//				rhsSum.rowCount -= lhsRowcount;
					break;
				} else {
//						VariableValuePair mergedVariable = new VariableValuePair(mergedTemp, rhsRowcount);
					RegionSummaryProjection mergedRegionSummary = new RegionSummaryProjection();
					mergedRegionSummary.region = mergedTemp;
					mergedRegionSummary.rowCount = rhsRowcount;
					mergedSummary.add(mergedRegionSummary);
					mergedRegionSummary.groupkeys = lhsSum.groupkeys;
					mergedRegionSummary.groupkeys.addAll(rhsSum.groupkeys);
					mergedRegionSummary.groupKeyToRegionF = rhsSum.groupKeyToRegionF;
					RegionSummaryProjection brokenNew = lhsSum.divide(rhsRowcount);
					mergedRegionSummary.groupKeyToRegionF.putAll(lhsSum.groupKeyToRegionF);// added
					// lhsSum.rowCount -= rhsRowcount;
					finalRegionSummay.set(idx, brokenNew);
					lhsSum = brokenNew;
					lhsRowcount = lhsSum.rowCount;
					rhsSum.rowCount = 0L;
					rhsIter.remove();
				}

				// }

			}
			if (!check) {
				// System.out.println("failed");
				throw new RuntimeException("You Failed!!!!!Couldn't find a region in rhs for lhs region:" + lhsRegion);
			}

		}
		for (RegionSummaryProjection lhsSum : finalRegionSummay) {
			if (lhsSum.rowCount != 0)
				throw new RuntimeException("Found while merge Region " + lhsSum.region + " in LHS with unmet rowcount");
		}
		if (!rhsRegionSummary.isEmpty())
			throw new RuntimeException("Found while merge RHS variables not getting exhausted");

		// Updating targetColIndxs
		lhsColIndxs.clear();
		lhsColIndxs.addAll(mergedColIndxsList);

		finalRegionSummay.clear();
		finalRegionSummay.addAll(mergedSummary);

	}

	private static void sanityCheckFullOverlap(IntList posInLHS, Region lhsRegion, IntList posInRHS, Region rhsRegion) {
		// returns true if two regions are consistent.

		for (IntIterator iterLHS = posInLHS.iterator(), iterRHS = posInRHS.iterator(); iterLHS.hasNext();) {
			int posL = iterLHS.nextInt();
			int posR = iterRHS.nextInt();
			Bucket lB = new Bucket();
			Bucket rB = new Bucket();

			for (BucketStructure bs : lhsRegion.getAll())
				lB = Bucket.union(lB, bs.at(posL));
			for (BucketStructure bs : rhsRegion.getAll())
				rB = Bucket.union(rB, bs.at(posR));
			if (!lB.isEqual(rB))//
			{
				throw new RuntimeException("Not fully overlappping");
			}
		}
	}

	private void getRegionValueCombination(RegionSummaryProjection regSum, IntList mergedColIndxs) {
		// TODO Auto-generated method stub
		List<ValueCombinationF> ret = new ArrayList<>();
		Long numTuples = getNumTuples(regSum);// finds the maximum no. of distict tuples to be generated. Except this
												// all must be round0-robin-ed to produce numtuples
		List<List<Double>> columnList = new ArrayList<>();// a;; columns stiched together
		// for every column in the mergedidx, we create a list
		for (int i = 0; i < mergedColIndxs.size(); i++) {
			columnList.add(new ArrayList<>());
		}

		Map<List<Integer>, List<Pair<RegionF, Pair<Long, Long>>>> groupKeyToRegionF = regSum.groupKeyToRegionF;
		// Long numTuples=0L;
		for (List<Integer> groupkeyIdx : groupKeyToRegionF.keySet()) {
			List<Pair<RegionF, Pair<Long, Long>>> regionsFList = groupKeyToRegionF.get(groupkeyIdx);

			for (Pair<RegionF, Pair<Long, Long>> regionFCur : regionsFList) {
				RegionF regionF = regionFCur.getFirst();
				Long rowCount = regionFCur.getSecond().getFirst();
				Long cutOff = regionFCur.getSecond().getSecond();
				Double splitPoint = regionF.at(0).at(0).at(0);// first bs, first bucket, first interval
				int splitPointIdx = bucketSplitPoints.get(groupkeyIdx.get(0)).indexOf(splitPoint);
				Double nextSplitPoint;
				if (splitPointIdx + 1 < bucketSplitPoints.get(groupkeyIdx.get(0)).size())
					nextSplitPoint = bucketSplitPoints.get(groupkeyIdx.get(0)).get(splitPointIdx + 1);// what if no next
																										// split point
				else
					nextSplitPoint = (double) Math.floor(splitPoint + 1);// if the split point is the last split point
																			// then we will generate tuples between this
																			// point and the next integer
				Long splitCount = splitPointsCount.get(groupkeyIdx.get(0)).get(splitPointIdx);// the number of tuples
																								// that are to be
																								// generated from this
																								// interval(may not be
																								// only due to the
																								// current region)
				List<Double> colValues = generateColumnValues(splitPoint, nextSplitPoint, splitCount, rowCount, cutOff);

				columnList.get(mergedColIndxs.indexOf(groupkeyIdx.get(0))).addAll(colValues);
				// generate all other col in th egroup keys as they are coupled together( have
				// to be fromm the same regionF)
				for (int i = 1; i < groupkeyIdx.size(); i++) {
					int idx = groupkeyIdx.get(i);
					List<Double> list = new ArrayList<Double>();
					Double point = regionF.at(0).at(i).at(0);
					;
					list = generateOtherGroupkeysColumns(point, rowCount);
					columnList.get(mergedColIndxs.indexOf(idx)).addAll(list);
				}
			}
		}
		// generating single points for all the non groupkeycolumns.
		for (int i = 0; i < mergedColIndxs.size(); i++) {
			if (columnList.get(i).isEmpty()) {
				columnList.get(i).add((double) regSum.region.at(0).at(i).at(0));
			}
		}
		if (!numTuples.equals(0L)) {
			for (int i = 0; i < mergedColIndxs.size(); i++) {
				columnList.set(i, generateColumnRoundRobin(columnList.get(i), numTuples));
			}

			for (int i = 0; i < numTuples; i++) {
				ValueCombinationF valComb = new ValueCombinationF();
				for (int j = 0; j < columnList.size(); j++) {
					valComb.colValues.add(columnList.get(j).get(i));
				}
				valComb.rowcount = 1;
				ret.add(valComb);
			}
		} else {
			ValueCombinationF valComb = new ValueCombinationF();
			for (int j = 0; j < columnList.size(); j++) {
				valComb.colValues.add(columnList.get(j).get(0));
			}
			valComb.rowcount = 1;
			ret.add(valComb);
			numTuples++;
		}
		ret.get(0).rowcount += regSum.rowCount - numTuples;// getting extra for no groupkey region
		regSum.valComb = ret;
		sanityCheckForValComb(ret, regSum.region);
		// return ret;
	}

	private void sanityCheckForValComb(List<ValueCombinationF> ret, Region region) {
		// TODO Auto-generated method stub
		for (ValueCombinationF valComb : ret) {
			if (!valComb.isPartOf(region))
				System.out.println("wrong");
			// throw new RuntimeException("generated tuple not a part of region");
		}
	}

	private List<Double> generateColumnRoundRobin(List<Double> list, Long numTuples) {
		Long count = 0L;
		int count2 = 0;
		List<Double> fullColumn = new ArrayList<>();
		while (true) {
			for (double val : list) {
				fullColumn.add(val);
				count++;

				if (count.equals(numTuples))
					return fullColumn;
			}
		}
	}

	private List<Double> generateOtherGroupkeysColumns(double point, Long rowCount) {
		List<Double> col = new ArrayList<>();
		for (int i = 0; i < rowCount; i++)
			col.add(point);
		return col;
	}

	private List<Double> generateColumnValues(Double splitPoint, Double nextSplitPoint, Long splitCount, Long rowCount,
			Long cutOff) {
		Double intervalSize = nextSplitPoint - splitPoint;
		List<Double> fullColumn = new ArrayList<>();
		for (long i = 0; i < rowCount; i++) {
			fullColumn.add(splitPoint + (double) (i + cutOff) * (intervalSize / splitCount));
		}
		Set<Double> temp = new HashSet<>();
		temp.addAll(fullColumn);
		if (temp.size() != fullColumn.size())
			throw new RuntimeException("same value generated; sizes" + fullColumn.size() + "\t" + temp.size());
		return fullColumn;
	}

	private Long getNumTuples(RegionSummaryProjection regSum) {
		Map<List<Integer>, List<Pair<RegionF, Pair<Long, Long>>>> groupKeyToRegionF = regSum.groupKeyToRegionF;
		Long numTuples = 0L;
		for (List<Integer> groupkeyIdx : groupKeyToRegionF.keySet()) {

			List<Pair<RegionF, Pair<Long, Long>>> regionsFList = groupKeyToRegionF.get(groupkeyIdx);
			Long curNumTuples = 0L;
			for (Pair<RegionF, Pair<Long, Long>> regionFCur : regionsFList) {
				curNumTuples += regionFCur.getSecond().getFirst();
			}
			numTuples = Math.max(curNumTuples, numTuples);
		}
		if (numTuples == 0L)
			System.out.println("here1");
		return numTuples;
	}

	private void checkAccuracy(FormalCondition condition, Region currCRegion, List<RegionSummaryProjection> finalRegionSummary,
			IntList mergedColIndxs) {
		Region compressedCRegion = new Region();
		for (BucketStructure bs : currCRegion.getAll()) {
			BucketStructure bsNew = new BucketStructure();
			for (int i = 0; i < bs.size(); i++) {
				if (mergedColIndxs.contains(i))
					bsNew.add(bs.at(i));
			}
			compressedCRegion.add(bsNew);
		}
		Long totTuples = 0L;
		if (!(condition instanceof FormalConditionAggregate)) {
			for (RegionSummaryProjection regSum : finalRegionSummary) {
				if (compressedCRegion.contains(regSum.region)) {
					// region satisfies curr condition
					for (ValueCombinationF valComb : regSum.valComb) {
						
						totTuples += valComb.rowcount;
					}
				}
			}
			Long accuracyTot = condition.getOutputCardinality() - totTuples;
			System.out.println("Query " + condition.getQueryname());
			System.out.println("Output cardinality error = " + accuracyTot);
		} else {
			List<String> groupkey = ((FormalConditionAggregate) condition).getGroupKey();
			List<Integer> groupkeyIdx = getColumnsIdx(groupkey);
			List<Integer> groupkeyIdxInValComb = new ArrayList<>();

			for (Integer idx : groupkeyIdx) {
				groupkeyIdxInValComb.add(mergedColIndxs.indexOf(idx));
			}

			Set<List<Double>> extractedColumns = new HashSet<>();
			for (RegionSummaryProjection regSum : finalRegionSummary) {
				if (compressedCRegion.contains(regSum.region)) {
					// region satisfies curr condition
					for (ValueCombinationF valComb : regSum.valComb) {
						List<Double> projectionColumnValues = extractColumnValues(valComb.colValues,
								groupkeyIdxInValComb);// gets
														// the
														// columns
														// for
														// which
														// disticnt
														// has
														// to
														// be
														// checked.
						totTuples += valComb.rowcount;
						extractedColumns.add(projectionColumnValues);// check if duplicates removed
					}
				}
			}
			Long accuracyDistinct = ((FormalConditionAggregate) condition).getProjectionCardinality()
					- extractedColumns.size();

			Long accuracyTot = condition.getOutputCardinality() - totTuples;

//		System.out.println("Query " + condition.getQueryName());
			System.out.println("Query " + condition.getQueryname());
			System.out.println("Output cardinality error = " + accuracyTot);
			System.out.println("Projection cardinality error = " + accuracyDistinct);
			if (!accuracyDistinct.equals(0L) || !accuracyTot.equals(0L))
				throw new RuntimeException("Accuracy error");
		}
	}

	private List<Double> extractColumnValues(List<Double> colValues, List<Integer> groupkeyIdxInValComb) {
		// TODO Auto-generated method stub
		List<Double> ret = new ArrayList<>();
		for (Integer idx : groupkeyIdxInValComb) {
			ret.add(colValues.get(idx));
		}
		return ret;
	}

	private List<Double> getNextRec() {
		List<Double> tuple = regSum.getNextRec();
		List<Double> list2 = new ArrayList<Double>();
//		System.out.print(tuple.get(2));
		if (tuple == null) {

			regSum = summIter.next();// move on the next region.
		} else {
			for (Double value : tuple) {
//				System.out.print(value + ", ");
				list2.add(value);
				
			}
//			System.out.println();
		}
		return list2;

	}
// mere-align methods end

	// ------------shadab functions-----------------------
	private String toStringFunc(List<String> groupkey) {
		// returns a single concatenated string.
		String ans = "";
		for (String group : groupkey.subList(0, groupkey.size() - 1)) {
			ans = ans + "," + group;
		}
		return ans + groupkey.get(groupkey.size() - 1);
	}

	private Set<Integer> findCCsIntersectingWithIntervals(FormalCondition curCondition,
			Map<String, Region> intervalisedRegions) {
		// TODO Auto-generated method stub
		Set<Integer> intersectingIntervals = new HashSet<>();
		for (String regionName : intervalisedRegions.keySet()) {

			Region region = intervalisedRegions.get(regionName);
			int currentCliqueIdx = Integer.parseInt(regionName.split("var")[1].split("_")[0]);
			Set<String> currentClique = this.arasuCliques.get(currentCliqueIdx);
			Set<String> appearingCols = new HashSet<>();
			getAppearingCols(appearingCols, curCondition);

			if (currentClique.containsAll(appearingCols)) {

				if (checkCCSatifyRegion(region, appearingCols, curCondition)) {
					intersectingIntervals.add(Integer.parseInt(regionName.split("_")[5]));
				}
			}

		}
		return intersectingIntervals;
	}

	private String findFkey(List<FormalCondition> conditions) {

		for (FormalCondition condition : conditions) {

			Set<String> attrFound = new HashSet<>();
			String viewname = condition.getViewname();
			getAppearingCols(attrFound, condition);
			int count = 0;
			for (String attr : attrFound) {
				if (!attr.contains(viewname)) {
					break;
				} else {
					count++;
				}
			}
			if (count == attrFound.size()) {
				return null;
			}

			if (condition instanceof FormalConditionComposite) {
				return findFkey(((FormalConditionComposite) condition).getConditionList());
			} else if (condition instanceof FormalConditionSimpleInt) {

				FormalConditionSimpleInt conditionInt = (FormalConditionSimpleInt) condition;
				List<String> fkColumns = conditionInt.getFkColumnNames();
				return fkColumns.get(fkColumns.size() - 1);
			} else {

				throw new RuntimeException("Not expecting");
			}
		}

		throw new RuntimeException("Not expecting");

	}

	void areDisjointCheck(List<VariableValuePair> regions) {
		// every pair of Regions are disjoint

		// List<Region> regionList = new ArrayList<>(regions);
		int n = regions.size();
		for (int i = 0; i < n; i++) {
			Region regi = regions.get(i).variable;
			for (int j = i + 1; j < n; j++) {

				Region regj = regions.get(j).variable;
				if (!regi.intersection(regj).isEmpty())
					throw new RuntimeException("Expected disjoint region but found overlapping regions");
			}
		}
	}


	private ViewSolution mergeCliqueSolutions(List<LinkedList<VariableValuePair>> cliqueIdxToVarValuesList) {

		IntList mergedColIndxs = new IntArrayList();
		List<ValueCombination> mergedValueCombinations = new ArrayList<>();

		mergedColIndxs.addAll(arasuCliquesAsColIndxs.get(0));
		// Instantiating variables of first clique
		for (VariableValuePair varValuePair : cliqueIdxToVarValuesList.get(0)) {
			IntList columnValues = getFloorInstantiation(varValuePair.variable);
			ValueCombination valueCombination = new ValueCombination(columnValues, varValuePair.rowcount);
			mergedValueCombinations.add(valueCombination);
		}

		for (int i = 1; i < cliqueCount; i++) { // merging with other cliques
			mergeWithAlignment(mergedColIndxs, mergedValueCombinations, arasuCliquesAsColIndxs.get(i),
					cliqueIdxToVarValuesList.get(i));
		}

		for (ListIterator<ValueCombination> iter = mergedValueCombinations.listIterator(); iter.hasNext();) {
			ValueCombination valueCombination = iter.next();
			valueCombination = getReverseMappedValueCombination(valueCombination);
			valueCombination = getExpandedValueCombination(valueCombination);
			iter.set(valueCombination);
		}

		ViewSolutionInMemory viewSolutionInMemory = new ViewSolutionInMemory(mergedValueCombinations.size());
		for (ValueCombination mergedValueCombination : mergedValueCombinations) {
			viewSolutionInMemory.addValueCombination(mergedValueCombination);
		}
		return viewSolutionInMemory;
	}

	private IntList getFloorInstantiation(Region variable) {
		// choose BS with min bucket floors
		BucketStructure leadingBS = variable.getLeadingBS();
		IntList columnValues = new IntArrayList(leadingBS.getAll().size());
		for (Bucket b : leadingBS.getAll()) {
			columnValues.add(b.min());
		}
		return columnValues;
	}

	/**
	 * lhs has instantiated ValueCombinations. Each lhs ValueCombination is extended
	 * by widthwise appending instantiated tuples from appropriate BucketStructure
	 * of compatible rhs variable(s). lhsColIndxs and lhsValueCombinations get side
	 * effects. rhsColIndxs gets NO side effects. rhsVarValuePairs gets exhausted
	 * and becomes empty. TODO: Could have been some smart alignment which prevents
	 * extra tuples to be added to primary view
	 * 
	 * @param lhsColIndxs
	 * @param lhsValueCombinations
	 * @param rhsColIndxs
	 * @param sourceValueCombinations
	 */
	private void mergeWithAlignment(IntList lhsColIndxs, List<ValueCombination> lhsValueCombinations,
			IntList rhsColIndxs, LinkedList<VariableValuePair> rhsVarValuePairs) {

		IntList tempColIndxs = new IntArrayList(rhsColIndxs);
		tempColIndxs.removeAll(lhsColIndxs);
		IntList sharedColIndxs = new IntArrayList(rhsColIndxs);
		sharedColIndxs.removeAll(tempColIndxs);

		IntList posInLHS = new IntArrayList(sharedColIndxs.size());
		IntList posInRHS = new IntArrayList(sharedColIndxs.size());
		for (IntIterator iter = sharedColIndxs.iterator(); iter.hasNext();) {
			int sharedColIndx = iter.nextInt();
			posInLHS.add(lhsColIndxs.indexOf(sharedColIndx));
			posInRHS.add(rhsColIndxs.indexOf(sharedColIndx));
		}

		IntList mergedColIndxsList = new IntArrayList(lhsColIndxs);
		mergedColIndxsList.addAll(rhsColIndxs);
		mergedColIndxsList = new IntArrayList(new IntOpenHashSet(mergedColIndxsList));
		Collections.sort(mergedColIndxsList);

		boolean[] fromLHS = new boolean[mergedColIndxsList.size()];
		int[] correspOriginalIndx = new int[mergedColIndxsList.size()];

		for (int i = 0; i < mergedColIndxsList.size(); i++) {
			fromLHS[i] = lhsColIndxs.contains(mergedColIndxsList.get(i));
			if (fromLHS[i]) {
				correspOriginalIndx[i] = lhsColIndxs.indexOf(mergedColIndxsList.get(i));
			} else {
				correspOriginalIndx[i] = rhsColIndxs.indexOf(mergedColIndxsList.get(i));
			}
		}

		List<ValueCombination> mergedValueCombinations = new ArrayList<>();
		for (ValueCombination lhsValueCombination : lhsValueCombinations) {
			IntList lhsColValues = lhsValueCombination.getColValues();
			long lhsRowcount = lhsValueCombination.getRowcount();

			for (ListIterator<VariableValuePair> rhsIter = rhsVarValuePairs.listIterator(); rhsIter.hasNext();) {
				VariableValuePair rhsVarValuePair = rhsIter.next();
				Region rhsVariable = rhsVarValuePair.variable;
				long rhsRowcount = rhsVarValuePair.rowcount;

				BucketStructure rhsCompatibleBS = getCompatibleBS(posInLHS, lhsColValues, posInRHS, rhsVariable);
				if (rhsCompatibleBS != null) {
					IntList mergedColValues = new IntArrayList(mergedColIndxsList.size());
					for (int j = 0; j < mergedColIndxsList.size(); j++) {
						if (fromLHS[j]) {
							mergedColValues.add(lhsColValues.getInt(correspOriginalIndx[j]));
						} else {
							mergedColValues.add(rhsCompatibleBS.at(correspOriginalIndx[j]).at(0));
						}
					}

					if (lhsRowcount <= rhsRowcount) {
						ValueCombination mergedValueCombination = new ValueCombination(mergedColValues, lhsRowcount);
						mergedValueCombinations.add(mergedValueCombination);
						lhsValueCombination.reduceRowcount(lhsRowcount);
						rhsVarValuePair.rowcount -= lhsRowcount;
						if (rhsVarValuePair.rowcount == 0) {
							rhsIter.remove();
						}
						break;
					} else {
						ValueCombination mergedValueCombination = new ValueCombination(mergedColValues, rhsRowcount);
						mergedValueCombinations.add(mergedValueCombination);
						lhsValueCombination.reduceRowcount(rhsRowcount);
						lhsRowcount = lhsValueCombination.getRowcount();
						rhsVarValuePair.rowcount = 0;
						rhsIter.remove();
					}
				}
			}
		}

		// if (DebugHelper.sanityChecksNeeded()) {
		for (ValueCombination lhsValueCombination : lhsValueCombinations) {
			if (lhsValueCombination.getRowcount() != 0)
				throw new RuntimeException(
						"Found while merge ValueCombination " + lhsValueCombination + " in LHS with unmet rowcount");
		}
		if (!rhsVarValuePairs.isEmpty())
			throw new RuntimeException("Found while merge RHS variables not getting exhausted");

		// Updating targetColIndxs
		lhsColIndxs.clear();
		lhsColIndxs.addAll(mergedColIndxsList);

		// Updating targetValueCombinations
		lhsValueCombinations.clear();
		lhsValueCombinations.addAll(mergedValueCombinations);
	}

	private static BucketStructure getCompatibleBS(IntList posInLHS, IntList lhsColValues, IntList posInRHS,
			Region var) {
		for (BucketStructure bs : var.getAll()) {
			if (isCompatible(posInLHS, lhsColValues, posInRHS, bs))
				return bs;
		}
		return null;
	}

	private static boolean isCompatible(IntList posInLHS, IntList lhsColValues, IntList posInRHS, BucketStructure bs) {
		for (IntIterator iterLHS = posInLHS.iterator(), iterRHS = posInRHS.iterator(); iterLHS.hasNext();) {
			int posL = iterLHS.nextInt();
			int posR = iterRHS.nextInt();

			if (!bs.at(posR).contains(lhsColValues.getInt(posL)))
				return false;
		}
		return true;
	}

	private HashMap<String, ProjectionStuffInColumn> getColumnWiseAggAndNonAggVarsInSingleSplitPointRegion(
			Set<String> clique, List<List<IntExpr>> solverConstraints,
			HashMap<String, Set<IntExpr>> columnWiseVarsInAllAggregateConditions,
			Map<String, List<Region>> aggregateColumnsToSingleSplitPointRegions, int offsetForSingleSplitPointRegions,
			ArrayList<String> sortedAggCols) {
		HashMap<String, ProjectionStuffInColumn> result = new HashMap<>();
		int tempIndex = 0;
		for (String columnname : sortedAggCols) {
			if (clique.contains(columnname)) {
				ProjectionStuffInColumn projectionStuffInColumn = new ProjectionStuffInColumn();

				Set<IntExpr> blocksInAllAggregateConditions = columnWiseVarsInAllAggregateConditions
						.getOrDefault(columnname, new HashSet<>()); // This clique might not have any aggregate
																	// condition on this column, hence getOrDefault
				List<Region> splitPointRegions = aggregateColumnsToSingleSplitPointRegions.get(columnname);
				for (int splitPointIndex = 0; splitPointIndex < splitPointRegions.size(); ++splitPointIndex) {
					// offsetForSingleSplitPointRegions + tempIndex is correct index because of
					// consistent
					// ordering during multiple iterations of
					// aggregateColumnsToSingleSplitPointRegions
					Set<IntExpr> aggBlocks = new HashSet<>(
							solverConstraints.get(offsetForSingleSplitPointRegions + tempIndex));
					Set<IntExpr> nonAggBlocks = new HashSet<>(aggBlocks);

					aggBlocks.retainAll(blocksInAllAggregateConditions); // Only retain those blocks which are also in
																			// aggregate conditions
					nonAggBlocks.removeAll(aggBlocks); // Remove those blocks which are in aggregate conditions

					projectionStuffInColumn.putProjectionStuffInSSPRegion(splitPointRegions.get(splitPointIndex),
							new ProjectionStuffInSSPRegion(aggBlocks, nonAggBlocks));
					tempIndex++;
				}
				result.put(columnname, projectionStuffInColumn);
			}
		}
		return result;
	}

	private HashMap<String, Set<IntExpr>> getColumnWiseAggVarsInAllAggregateConditions(List<FormalCondition> conditions,
			List<List<IntExpr>> solverConstraints, List<Pair<Integer, Boolean>> applicableConditions) {

		HashMap<String, Set<IntExpr>> result = new HashMap<>();
		for (int i = 0; i < applicableConditions.size(); ++i) {
			Pair<Integer, Boolean> applicableConditionInfo = applicableConditions.get(i);
			if (applicableConditionInfo.getSecond()) { // Is the condition applied with projection or without projection
				FormalCondition formalCondition = conditions.get(applicableConditionInfo.getFirst());
				List<String> completeGroupKey = ((FormalConditionAggregate) formalCondition).getGroupKey();
				if (completeGroupKey.size() != 1)
					throw new RuntimeException("Only 1-D projection supported!");
				String groupKey = completeGroupKey.get(0);
				if (!result.containsKey(groupKey)) {
					result.put(groupKey, new HashSet<>());
				}
				result.get(groupKey).addAll(solverConstraints.get(i));
			}
		}
		return result;
	}

	/**
	 * @cite https://www.geeksforgeeks.org/finding-all-subsets-of-a-given-set-in-java/
	 */
	private Set<List<IntExpr>> getPowerSet(List<IntExpr> elements) {
		System.out.println("Power Set of : " + elements.size());
		Set<List<IntExpr>> powerSet = new HashSet<>();
		int size = elements.size();
		if (size > 62)
			throw new RuntimeException(
					"one << 63 will overflow and won't work correctly because long is used. Change type of 'one' to BigInt or something like that!");
		long one = 1;
		for (int i = 0; i < (one << size); i++) {
			List<IntExpr> newSet = new ArrayList<>(); // using list to save on memory because set properties are not
														// required
			for (int j = 0; j < size; j++)
				// (1<<j) is a number with jth bit 1
				// so when we 'and' them with the
				// subset number we get which numbers
				// are present in the subset and which
				// are not
				if ((i & (1 << j)) > 0)
					newSet.add(elements.get(j));
			powerSet.add(newSet);
		}
		powerSet.remove(new ArrayList<>()); // removing empty set
		return powerSet;
	}

	private IntList getIntersectionColIndices(Set<String> cliqueI, Set<String> cliqueJ) {
		Set<String> temp = new HashSet<>(cliqueI);
		temp.removeAll(cliqueJ);
		Set<String> intersectingCols = new HashSet<>(cliqueI);
		intersectingCols.removeAll(temp);
		IntList intersectingColIndices = getSortedIndxs(intersectingCols);
		return intersectingColIndices;
	}

	/**
	 * cliqueIndextoPList stores current partition (set of variables) of every
	 * clique. This method takes two (intersecting) cliques i and j as input and
	 * replaces cliqueIndextoPList[i] with a newer partition (a fresh set of
	 * variables) cliqueIndextoPList[j] with a newer partition (a fresh set of
	 * variables) such that these newer variables of the two cliques can be used to
	 * frame consistency conditions later.
	 *
	 * @param cliqueIdxtoPList
	 * @param cliqueIdxtoPSimplifiedList
	 * @param i
	 * @param j
	 * @param intersectingColIndices
	 * @return
	 */
	private CliqueIntersectionInfo replaceWithFreshVariablesToEnsureConsistency(List<Partition> cliqueIdxtoPList,
			List<List<IntList>> cliqueIdxtoPSimplifiedList, int i, int j, IntList intersectingColIndices) {
		Partition partitionI = cliqueIdxtoPList.get(i);
		Partition partitionJ = cliqueIdxtoPList.get(j);

		List<Region> splitRegions = getSplitRegions(partitionI, partitionJ, intersectingColIndices);

		IntList parentOldVarIdsI = new IntArrayList();
		Partition freshPartitionI = getFreshVariables(parentOldVarIdsI, partitionI, splitRegions,
				intersectingColIndices);
		cliqueIdxtoPList.set(i, freshPartitionI);
		List<IntList> sourceListI = cliqueIdxtoPSimplifiedList.get(i);
		List<IntList> freshListI = new ArrayList<>(freshPartitionI.size());
		for (int a = 0; a < freshPartitionI.size(); a++) {
			freshListI.add(sourceListI.get(parentOldVarIdsI.getInt(a)));
		}
		cliqueIdxtoPSimplifiedList.set(i, freshListI);

		IntArrayList parentOldVarIdsJ = new IntArrayList();
		Partition freshPartitionJ = getFreshVariables(parentOldVarIdsJ, partitionJ, splitRegions,
				intersectingColIndices);
		cliqueIdxtoPList.set(j, freshPartitionJ);
		List<IntList> sourceListJ = cliqueIdxtoPSimplifiedList.get(j);
		List<IntList> freshListJ = new ArrayList<>(freshPartitionJ.size());
		for (int a = 0; a < freshPartitionJ.size(); a++) {
			freshListJ.add(sourceListJ.get(parentOldVarIdsJ.getInt(a)));
		}
		cliqueIdxtoPSimplifiedList.set(j, freshListJ);

		CliqueIntersectionInfo cliqueIntersectionInfo = new CliqueIntersectionInfo(i, j, intersectingColIndices);
		// cliqueIntersectionInfo.splitRegions = splitRegions;
		return cliqueIntersectionInfo;
	}

	private List<Region> getSplitRegions(Partition partitionI, Partition partitionJ, IntList intersectingColIndices) {
		List<Region> bothRegions = new ArrayList<>();
		bothRegions.addAll(partitionI.getAll());
		bothRegions.addAll(partitionJ.getAll());

		List<boolean[]> truncAllTrueBS = getTruncatedAllTrueBS(intersectingColIndices);
		List<Region> truncRegions = getTruncatedRegions(bothRegions, intersectingColIndices);

		Reducer reducer = new Reducer(truncAllTrueBS, truncRegions);
		Map<IntList, Region> P = reducer.getMinPartition();
		List<Region> splitRegions = new ArrayList<>(P.values());
		return splitRegions;
	}

	/**
	 * Returns a Partition with freshVariables and also populated parentOldVarIds of
	 * same length storing which oldVarId it came from
	 * 
	 * @param parentOldVarIds
	 * @param oldPartition
	 * @param splitRegions
	 * @param intersectingColIndices
	 * @return
	 */
	private Partition getFreshVariables(IntList parentOldVarIds, Partition oldPartition, List<Region> splitRegions,
			IntList intersectingColIndices) {

		List<Region> freshRegions = new ArrayList<>();
		List<Region> oldRegions = oldPartition.getAll();

		IntList oldRegionIds = new IntArrayList(oldRegions.size());
		for (int i = 0; i < oldRegions.size(); i++) {
			oldRegionIds.add(i);
		}

		for (Region splitRegion : splitRegions) {
			List<Region> tempOldRegions = new ArrayList<>();
			IntList tempOldRegionIds = new IntArrayList();

			for (int i = 0; i < oldRegions.size(); i++) {
				Region oldRegion = oldRegions.get(i);
				Integer oldRegionId = oldRegionIds.get(i);

				Region freshRegion = new Region(); // stores list of untruncated bs which come from intersection of
													// oldRegion and splitRegion
				Region remainRegion = new Region(); // stores list of untruncated bs which come from oldRegion minus
													// splitRegion
				for (BucketStructure oldBS : oldRegion.getAll()) { // need to do bs by bs so that untruncing is possible
					Region oldSingleBSRegion = new Region();
					oldSingleBSRegion.add(oldBS);
					Region truncOldSingleBSRegion = getTruncatedRegion(oldSingleBSRegion, intersectingColIndices);
					Region truncOverlap = truncOldSingleBSRegion.intersection(splitRegion);
					if (truncOverlap.isEmpty()) {
						remainRegion.add(oldBS);
					} else {
						Region untruncOverlap = getUntruncatedRegion(truncOverlap, oldSingleBSRegion,
								intersectingColIndices);
						freshRegion.addAll(untruncOverlap.getAll());

						Region remainTruncRegion = truncOldSingleBSRegion.minus(truncOverlap);
						if (!remainTruncRegion.isEmpty()) {
							Region remainUntruncRegion = getUntruncatedRegion(remainTruncRegion, oldSingleBSRegion,
									intersectingColIndices);
							remainRegion.addAll(remainUntruncRegion.getAll());
						}
					}
				}
				if (!freshRegion.isEmpty()) {
					freshRegions.add(freshRegion);
					parentOldVarIds.add(oldRegionId);
				}
				if (!remainRegion.isEmpty()) {
					tempOldRegions.add(remainRegion);
					tempOldRegionIds.add(oldRegionId);
				}

			}
			oldRegions = tempOldRegions;
			oldRegionIds = tempOldRegionIds;
		}

		if (!oldRegions.isEmpty() || !oldRegionIds.isEmpty())
			throw new RuntimeException("Expected oldRegions to be empty here. oldRegions " + oldRegions.size()
					+ " and oldRegionIds " + oldRegionIds.size());

		Partition freshVariables = new Partition(freshRegions);
		return freshVariables;
	}

	private List<boolean[]> getTruncatedAllTrueBS(IntList intersectingColIndices) {
		List<boolean[]> truncatedAllTrueBS = new ArrayList<>();
		for (int i = 0; i < allTrueBS.size(); i++) {
			if (intersectingColIndices.contains(i)) {
				truncatedAllTrueBS.add(allTrueBS.get(i));
			}
		}
		return truncatedAllTrueBS;
	}

	private List<Region> getTruncatedRegions(List<Region> regions, IntList intersectingColIndices) {
		List<Region> truncatedRegions = new ArrayList<>(regions.size());
		for (Region region : regions) {
			Region truncatedRegion = getTruncatedRegion(region, intersectingColIndices);
			truncatedRegions.add(truncatedRegion);
		}
		return truncatedRegions;
	}

	private Region getTruncatedRegion(Region region, IntList intersectingColIndices) {
		Region truncatedRegion = new Region();
		for (BucketStructure bs : region.getAll()) {
			BucketStructure truncatedBS = new BucketStructure();
			List<Bucket> buckets = bs.getAll();
			for (int i = 0; i < buckets.size(); i++) {
				if (intersectingColIndices.contains(i)) {
					truncatedBS.add(buckets.get(i));
				}
			}
			truncatedRegion.add(truncatedBS);
		}
		return truncatedRegion;
	}

	private Region getUntruncatedRegion(Region truncatedRegion, Region donorRegion, IntList intersectingColIndices) {

		if (donorRegion.getAll().size() != 1)
			throw new RuntimeException("Can only untruncate Regions with single BucketStructure in donor but found "
					+ donorRegion.getAll().size());

		BucketStructure donorBS = donorRegion.getAll().get(0);
		Region untruncatedRegion = new Region();
		for (BucketStructure truncatedBS : truncatedRegion.getAll()) {

			BucketStructure untruncatedBS = new BucketStructure();
			int k = -1;
			for (int i = 0; i < donorBS.size(); i++) {
				if (intersectingColIndices.contains(i)) {
					untruncatedBS.add(truncatedBS.at(++k));
				} else {
					untruncatedBS.add(donorBS.at(i));
				}
			}
			untruncatedRegion.add(untruncatedBS);
		}
		return untruncatedRegion;
	}

	private void addTo_ConditionListToPairOfVarList(List<List<IntExpr>> applicableSolverConstraints,
			HashMap<IntList, MutablePair<List<IntExpr>, List<IntExpr>>> conditionListToSetOfVarList) {
		HashMap<IntExpr, IntList> varToConditionList = new HashMap<>();
		for (int i = 0; i < applicableSolverConstraints.size(); i++) {
			for (IntExpr var : applicableSolverConstraints.get(i)) { // For every region which satisfy i'th condition
				if (!varToConditionList.containsKey(var))
					varToConditionList.put(var, new IntArrayList());
				varToConditionList.get(var).add(i);
			}
		}
		HashMap<IntList, List<IntExpr>> conditionListToVarList = new HashMap<>();
		for (Entry<IntExpr, IntList> entry : varToConditionList.entrySet()) {
			IntExpr var = entry.getKey();
			IntList conditionsList = entry.getValue();
			if (!conditionListToVarList.containsKey(conditionsList)) {
				conditionListToVarList.put(conditionsList, new ArrayList<>());
			}
			conditionListToVarList.get(conditionsList).add(var);
		}

		for (Entry<IntList, List<IntExpr>> entry : conditionListToVarList.entrySet()) {
			MutablePair<List<IntExpr>, List<IntExpr>> mutablePair = conditionListToSetOfVarList.get(entry.getKey());
			if (mutablePair == null) {
				mutablePair = new MutablePair<List<IntExpr>, List<IntExpr>>(entry.getValue(), null);
				conditionListToSetOfVarList.put(entry.getKey(), mutablePair);
			} else {
				mutablePair.setSecond(entry.getValue());
			}

		}
	}

}

