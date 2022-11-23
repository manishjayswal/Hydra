package in.ac.iisc.cds.dsl.cdgvendor.solver;

/*
 * How to read code by dk:
 * Before every chunk of code a variable is defined. The value of that variable is found out in the corresponding code. The name of variable tells what the code is doing
 */
//added by manish starts
import gurobi.*;
//added by manish ends

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.ListIterator;
import java.util.Map;
import java.util.Scanner;
import java.util.Map.Entry;
import java.util.Set;
import java.util.Stack;
import java.io.BufferedWriter;
import java.io.FileWriter;
import java.io.IOException;
import org.jgrapht.alg.ConnectivityInspector;
import org.jgrapht.graph.DefaultEdge;
import org.jgrapht.graph.SimpleGraph;
import org.json.JSONArray;
import org.json.JSONObject;

import com.microsoft.z3.ArithExpr;
import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.Context;
import com.microsoft.z3.Expr;
import com.microsoft.z3.IntExpr;
import com.microsoft.z3.IntNum;
import com.microsoft.z3.Model;
import com.microsoft.z3.Optimize;
import com.microsoft.z3.Solver;
import com.microsoft.z3.Status;

import in.ac.iisc.cds.dsl.cdgclient.constants.PostgresCConfig;
import in.ac.iisc.cds.dsl.cdgvendor.constants.PostgresVConfig;
import in.ac.iisc.cds.dsl.cdgvendor.constants.PostgresVConfig.HydraTypes;
import in.ac.iisc.cds.dsl.cdgvendor.constants.PostgresVConfig.Key;
import in.ac.iisc.cds.dsl.cdgvendor.lpSolver.LPSolver;
import in.ac.iisc.cds.dsl.cdgvendor.model.ProjectionStuffInColumn;
import in.ac.iisc.cds.dsl.cdgvendor.model.ProjectionStuffInSSPRegion;
import in.ac.iisc.cds.dsl.cdgvendor.model.SkewRegion;
import in.ac.iisc.cds.dsl.cdgvendor.model.SolverViewStats;
import in.ac.iisc.cds.dsl.cdgvendor.model.ValueCombination;
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
import in.ac.iisc.cds.dsl.cdgvendor.model.formal.FormalConditionSimpleInt;
import in.ac.iisc.cds.dsl.cdgvendor.model.formal.Symbol;
import in.ac.iisc.cds.dsl.cdgvendor.reducer.Bucket;
import in.ac.iisc.cds.dsl.cdgvendor.reducer.BucketStructure;
import in.ac.iisc.cds.dsl.cdgvendor.reducer.Partition;
import in.ac.iisc.cds.dsl.cdgvendor.reducer.Reducer;
import in.ac.iisc.cds.dsl.cdgvendor.reducer.Region;
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


public class DoubleReductionBasedViewSolver extends AbstractCliqueFinder {

	public static int fileCount=-1;
	private final SolverViewStats solverStats;
    
    private final String slackVarNamePrefix = "slack_";
    
    // added by tarun 
    List<LongList> cliqueIdxtoConditionBValuesList;
    List<Partition> cliqueIdxtoPList;
    List<List<IntList>> cliqueIdxtoPSimplifiedList;
    
    List<HashMap<Integer, Integer>> mappedIndexOfConsistencyConstraint;	// Required by CONSISTENCYFILTERS type of consistency maker
    List<Integer> cliqueWiseTotalSingleSplitPointRegions;	// per clique
    List<List<Pair<Integer, Boolean>>> applicableConditionsOnClique;
    List<CliqueIntersectionInfo> cliqueIntersectionInfos; // Required by BRUTEFORCE type of consistency make
    
    HashMap<String,Long> allIntervalRegionValueMap = new HashMap<>();
    HashMap<String,Long> allIntervalisedRegionsMap = new HashMap<>();
    HashMap<String,Long> allDxValuesMap = new HashMap<>();
    
    Map<Set<String>,List<List<Integer>>> cliqueToIntervalMap = new HashMap<>();
    
    List<Set<String>> orderedCliques = new ArrayList<>();
    List<List<String>> borrowedAttrPerClique = new ArrayList<>();
    
    //dividing skew
    Map<String,Integer> fkeyToCliqueIdx = new HashMap<>();
    
    
    
    // Skew Variables came from clique 0
    // List of fkeys
    // Corresponding pk Columns of fkeys
    // Correspondng intervalised region
    // Corresponding df vector of intervalised region
    Map<String,List<String>> fkeyToPkColumnsMap = new HashMap<>();
    Map<String,List<String>> fkeyToIntervalRegionMap = new HashMap<>();    
    Map<String, List<List<Integer>>> allIntervalRegionsPerFKey = new HashMap<>();
    Map<String, Map<String,List<String>>> varToIntervalisedRegionMapPerFkey = new HashMap<>();
	Map<String, HashMap<Integer,List<String>>> intervalToDxValuePerFkey =  new HashMap<>();
    Map<String, Map<String, Region>> fkeyToActualInteervalisedRegMap = new HashMap<>();
    
    Map<String, Map<Long, List<Long>>> varPKValDistribution = new HashMap<>();
    
    Map<String, Region> intervalisedRegionMap = new HashMap<>();
    
    private List<String> bucketsToColumnNameMapping;
    
    public DoubleReductionBasedViewSolver(String viewname, ViewInfo viewInfo, List<boolean[]> allTrueBS, List<Set<String>> arasuCliques,
            Map<String, IntList> bucketFloorsByColumns) {
        super(viewname, viewInfo, allTrueBS, arasuCliques, bucketFloorsByColumns);
        solverStats = new SolverViewStats();
        solverStats.relRowCount = viewInfo.getRowcount();
        
        // variables added here by tarun  -- starts
        cliqueIdxtoConditionBValuesList = new ArrayList<>(cliqueCount);
        cliqueIdxtoPList = new ArrayList<>(cliqueCount);
        cliqueIdxtoPSimplifiedList = new ArrayList<>(cliqueCount);
        
        mappedIndexOfConsistencyConstraint = new ArrayList<>();	// Required by CONSISTENCYFILTERS type of consistency maker
        cliqueWiseTotalSingleSplitPointRegions = new ArrayList<>();	// per clique
        applicableConditionsOnClique = new ArrayList<>();
        cliqueIntersectionInfos = new ArrayList<>();	// Required by BRUTEFORCE type of consistency make
        // variables added here by tarun ends --
        
        bucketsToColumnNameMapping = new ArrayList<String>(viewInfo.getViewNonkeys());
    	
    }

//    @Override
    public ViewSolutionWithSolverStats solveView(List<FormalCondition> conditions, List<Region> conditionRegions, FormalCondition consistencyConstraints[], ConsistencyMakerType consistencyMakerType) {

    	
        StopWatch formulationPlusSolvingSW = new StopWatch("LP-SolvingPlusPostSolving-" + viewname);
        beginLPFormulation();
        List<LinkedList<VariableValuePair>> cliqueIdxToVarValuesList;
        if(PostgresVConfig.hydraVersions.contains(PostgresVConfig.HydraTypes.scalableHydra)) {
        	cliqueIdxToVarValuesList = subhoFormulateAndSolve(conditions, conditionRegions, consistencyConstraints, consistencyMakerType);
        }else if(PostgresVConfig.hydraVersions.contains(PostgresVConfig.HydraTypes.robustHydra)) {
        	cliqueIdxToVarValuesList = robustFormulateAndSolve(conditions, conditionRegions, consistencyConstraints, consistencyMakerType);
            
        }
        else {
        	cliqueIdxToVarValuesList = formulateAndSolve(conditions, conditionRegions, consistencyConstraints, consistencyMakerType);
        }
        
        finishSolving();
        
        if(PostgresVConfig.hydraVersions.contains(PostgresVConfig.HydraTypes.duplicationHydra)) {
        	dividingSkew(conditions);
        }
        
        
        
        
        //ViewSolution viewSolution = mergeCliqueSolutions(cliqueIdxToVarValuesList); //commented for shadab code
        ViewSolution viewSolution = mergeCliqueSolutionsRegionwise(cliqueIdxToVarValuesList); // to be used for region merging
        finishPostSolving();
        solverStats.millisToSolve = formulationPlusSolvingSW.getTimeAndDispose();
        //return new ViewSolutionWithSolverStats(viewSolution,solverStats);
        return new ViewSolutionWithSolverStats(viewSolution, viewSolution.getVariableValuePairs() ,solverStats,fkeyToPkColumnsMap,allIntervalRegionValueMap,allIntervalisedRegionsMap,allDxValuesMap,cliqueToIntervalMap,orderedCliques,borrowedAttrPerClique);
    }
    
    
    
    private List<LinkedList<VariableValuePair>> robustFormulateAndSolve(List<FormalCondition> conditions, List<Region> conditionRegions, FormalCondition[] consistencyConstraints, ConsistencyMakerType consistencyMakerType) {
		// TODO Auto-generated method stub
    	//Map<String, String> viewNameAndAnonymizedViewNameMap = getAllViewNameAndAnonymizedViewNameMap();

   		
    	StopWatch onlyReductionSW = new StopWatch("LP-OnlyReduction" + viewname);
    	
    	fileCount = fileCount + 1;
    	

    	//if(viewname.equals("t15")) {
        // 	 List<LinkedList<VariableValuePair>> cliqueIdxToVarValuesList = new ArrayList<>(cliqueCount);
        //      return cliqueIdxToVarValuesList;
        // 	}
    	
    	
    	//if((viewname.equals("t03") || viewname.equals("t17") || viewname.equals("t22")  || viewname.equals("t11"))) {// && !viewname.equals("t18") ) {
        //	 List<LinkedList<VariableValuePair>> cliqueIdxToVarValuesList = new ArrayList<>(cliqueCount);
        //     return cliqueIdxToVarValuesList;
    	//}
    	  
    	
    	//if(viewname.equals("t03")) {
        // 	 List<LinkedList<VariableValuePair>> cliqueIdxToVarValuesList = new ArrayList<>(cliqueCount);
        //      return cliqueIdxToVarValuesList;
        // 	}
    	Partition newPartition = new Partition();
    	
    	//for(Region c : conditionRegions) {
    	//	newPartition.add(c.getDeepCopy());
    	//}
    	
    	//System.out.println("NEW PARTITION CONDITION REGION SIZE : " + newPartition.size());
    	
    	
        //STEP 1: For each clique find set of applicable conditions and call variable reduction
        List<LongList> cliqueIdxtoConditionBValuesList = new ArrayList<>(cliqueCount);
        //sumang
        List<LongList> cliqueIdxtoConditionMValuesList = new ArrayList<>(cliqueCount);
        List<Partition> cliqueIdxtoPList = new ArrayList<>(cliqueCount);
        List<List<IntList>> cliqueIdxtoPSimplifiedList = new ArrayList<>(cliqueCount);
        List<String> meta_list=new ArrayList<String>();
        List<HashMap<Integer, Integer>> mappedIndexOfConsistencyConstraint = new ArrayList<>();

        
        Set<String> allColumnsFromAllCliques = new HashSet<String>();
        
        //IN Z3 SOLVER FILE, CONDITION REGIONS CONSIST OF CONSISTENCY CONSTRAINT AS WELL, COMMENT THAT FOR GENERATING CONDITION REGION QUERUES
        //for (int i = 0; i < cliqueCount; i++) {
        	
        //	Set<String> clique = arasuCliques.get(i);
        //	System.out.println("Cliques here : " + clique + cliqueCount);
        //    allColumnsFromAllCliques.addAll(clique);
        //}
        //UNCOMMENT THE FOLLOWING LOOP WHEN DOING NORMAL INSTEAD OF GENERATING CC FOR CONDITIONREGIONS
        //BUT COMMENT THE ABOVE LOOP
        
        for (int i = 0; i < cliqueCount; i++) {

            LongList bvalues = new LongArrayList();
            //sumang
            LongList mvalues = new LongArrayList();
            Set<String> clique = arasuCliques.get(i);
            
            System.out.println("Cliques here : " + clique + cliqueCount);
            
            allColumnsFromAllCliques.addAll(clique);
            
            List<Region> cRegions = new ArrayList<>();
            for (int j = 0; j < conditions.size(); j++) {
                Set<String> appearingCols = new HashSet<>();
                getAppearingCols(appearingCols, conditions.get(j));

                if (clique.containsAll(appearingCols)) {
                    cRegions.add(conditionRegions.get(j));
                    
                    if(conditions.get(j).getSource()==1) {
                    	meta_list.add(Integer.toString(i)+Integer.toString(bvalues.size()));
                    	//System.out.println(meta_list);
                    }
                    bvalues.add(conditions.get(j).getOutputCardinality());
                }
            }

            //Adding extra cRegion for all 1's condition
            Region allOnesCRegion = new Region();
            BucketStructure subConditionBS = new BucketStructure();
            for (int j = 0; j < allTrueBS.size(); j++) {
                Bucket bucket = new Bucket();
                for (int k = 0; k < allTrueBS.get(j).length; k++) {
                    if (allTrueBS.get(j)[k]) {		// TODO : Is this check needed?
                        bucket.add(k);
                    }
                }
                subConditionBS.add(bucket);
            }
            allOnesCRegion.add(subConditionBS);
            cRegions.add(allOnesCRegion);
            bvalues.add(relationCardinality);
            cliqueIdxtoConditionBValuesList.add(bvalues);
            cliqueIdxtoConditionMValuesList.add(mvalues);
            
            ///////////////// Start dk
            HashMap<Integer, Integer> indexKeeper = new HashMap<>();
            int tempIndex = 0;
            for (int j = 0; j < consistencyConstraints.length; j++) {
				FormalCondition condition = consistencyConstraints[j];
            	Set<String> appearingCols = new HashSet<>();
                getAppearingCols(appearingCols, condition);

                if (clique.containsAll(appearingCols)) {
                	indexKeeper.put(j, tempIndex++);
                    cRegions.add(conditionRegions.get(conditions.size() + j));
                }
			}
            mappedIndexOfConsistencyConstraint.add(indexKeeper);
            ///////////////// End dk
            
            Reducer reducer = new Reducer(allTrueBS, cRegions);
            //Map<IntList, Region> P = reducer.getMinPartition();

            //Using varIds instead of old variable regions
            List<Region> oldVarList = new ArrayList<>();	// List of regions corresponding to below labels
            List<IntList> conditionIdxsList = new ArrayList<>();	// List of labels
            reducer.getVarsAndConditionsSimplified(oldVarList, conditionIdxsList);

            Partition cliqueP = new Partition(new ArrayList<>(oldVarList));
            cliqueIdxtoPList.add(cliqueP);

            cliqueIdxtoPSimplifiedList.add(conditionIdxsList);
        }
        
        onlyReductionSW.displayTimeAndDispose();

        long varcountDR = 0;
        for (int i = 0; i < cliqueCount; i++) {
        	//COMMENT THIS LINE FOR GENERATING CONDITION REGION CCS, as they ll give exception otherwise since cliqueIdxtoPList are empty when a previous bigger loop doing region partitioning is commented 
        	varcountDR += cliqueIdxtoPList.get(i).getAll().size();
        }
        DebugHelper.printInfo("Number of variables after double reduction " + varcountDR);

        
        StopWatch onlyFormationSW = new StopWatch("LP-OnlyFormation" + viewname);
        
        Map<String, String> contextmap = new HashMap<>();
        contextmap.put("model", "true");
        contextmap.put("unsat_core", "true");
        Context ctx = new Context(contextmap);
        
        
        List<Integer> allEstimateList = new ArrayList<Integer>();
        int estimateListCounter = 0;
        int estimateVariableNameCounter = 0;

        System.out.println("cliqueCount :  " + cliqueCount);
        

        BufferedWriter writer = null;
  	    try {
  			writer = new BufferedWriter(new FileWriter(PostgresVConfig.getProp(PostgresVConfig.Key.QUERYGENMODULE_QUERYFILE) + "_" +  viewname + ".txt"));
  	  	} catch (IOException e) {
  			e.printStackTrace();
  		}
        
        for (int cliqueIndex = 0; cliqueIndex < cliqueCount; cliqueIndex++) {
            
        	//These	three lines call is to get the queries corresponding to the condition Regions - ie Used to get the queries for each edge of the CCs
            //Keep the first two lines commented, as they ll give exception otherwise since cliqueIdxtoConditionBValuesList and cliqueIdxtoPList are empty when a previous bigger loop doing region partitioning is commented 
        	//LongList bvalues = cliqueIdxtoConditionBValuesList.get(cliqueIndex);
            //Partition partition = cliqueIdxtoPList.get(cliqueIndex);		// Partition							+.025is a list of regions corresponding to below labels
            //List<IntList> conditionIdxsList = new ArrayList<IntList>();//cliqueIdxtoPSimplifiedList.get(cliqueIndex);	// Getting label list for this clique

            Partition partition = cliqueIdxtoPList.get(cliqueIndex);		// Partition							+.025is a list of regions corresponding to below labels
            
            if(PostgresVConfig.addCardinalityEstimateFlag) {              
                List<Integer> estimateListForThisPartition = GenerateQueryForRegions.getQueriesCorrespondingToDisjointRegions(viewname, allColumnsFromAllCliques, bucketsToColumnNameMapping, bucketFloorsByColumns, partition, writer);
                allEstimateList.addAll(estimateListForThisPartition);  
            }
        }
        
        try {
			writer.close();
		} catch (IOException e) {
			e.printStackTrace();
		}
	 


        //allEstimateList = null;
        //System.err.println("allEstimateList " + allEstimateList);
        
        
        //Solver solver = ctx.mkSolver();
        Optimize solver = ctx.mkOptimize();
        // System.err.println("Solver to String 1" + solver.toString());
        
  
        int global_meta_count=0;
        ArithExpr exp_final = ctx.mkInt(0);//ctx.mkSub(ctx.mkInt(0),ctx.mkInt(0));//sumang

        List<List<List<IntExpr>>> allSolverConstraints = new ArrayList<>();
        for (int i = 0; i < cliqueCount; i++) {					// Create lp variables for cardinality constraints
            LongList bvalues = cliqueIdxtoConditionBValuesList.get(i);
            LongList mvalues = cliqueIdxtoConditionMValuesList.get(i); //sumang
            Partition partition = cliqueIdxtoPList.get(i);		// Partition is a list of regions corresponding to below labels
            List<IntList> conditionIdxsList = cliqueIdxtoPSimplifiedList.get(i);	// Getting label list for this clique

            HashMap<Integer, Integer> indexKeeper = mappedIndexOfConsistencyConstraint.get(i);
            List<List<IntExpr>> solverConstraints = new ArrayList<>(bvalues.size() + indexKeeper.size());
            //List<List<IntExpr>> metaConstraints = new ArrayList<>(mvalues.size()); //sumang
            for (int j = 0; j < bvalues.size() + indexKeeper.size(); j++) {
                solverConstraints.add(new ArrayList<>());
            }
            //for (int j = 0; j < bvalues.size(); j++) {
             //   metaConstraints.add(new ArrayList<>());
            //}
            for (int j = 0; j < partition.size(); j++) {
                String varname = "var" + i + "_" + j;
                solverStats.solverVarCount++;
                

                if(PostgresVConfig.addCardinalityEstimateFlag) {              
                
	                String estimateVariableName = "estVar_" + estimateVariableNameCounter;
	                solver.Add(ctx.mkGe(ctx.mkIntConst(estimateVariableName), ctx.mkInt(0)));
	               
	                solver.Add(ctx.mkLe(ctx.mkSub(ctx.mkInt(0),ctx.mkIntConst(estimateVariableName)), ctx.mkSub(ctx.mkIntConst(varname), ctx.mkInt(allEstimateList.get(estimateListCounter)))));
	                solver.Add(ctx.mkLe(ctx.mkSub(ctx.mkIntConst(varname), ctx.mkInt(allEstimateList.get(estimateListCounter))), ctx.mkIntConst(estimateVariableName)));
	                exp_final=ctx.mkAdd(exp_final,ctx.mkIntConst(estimateVariableName));
	            	
	                estimateVariableNameCounter = estimateVariableNameCounter + 1;
	                estimateListCounter = estimateListCounter + 1;
                                
                }
                
                solver.Add(ctx.mkGe(ctx.mkIntConst(varname), ctx.mkInt(0)));

                for (IntIterator iter = conditionIdxsList.get(j).iterator(); iter.hasNext();) {
                    int k = iter.nextInt();
                    solverConstraints.get(k).add(ctx.mkIntConst(varname));
                }
            }
            
            //Adding normal constraints
            for (int j = 0; j < bvalues.size(); j++) {
                long outputCardinality = bvalues.getLong(j);
                long zz=(long) (0.3*outputCardinality);
                String test=Integer.toString(i)+Integer.toString(j);
                List<IntExpr> addList = solverConstraints.get(j);
                
                
                if(PostgresVConfig.addMetadataBucketsFlag) {//if(meta_list.contains(test)) {
                	//System.out.println("Do something here");
                    String meta_var="z"+global_meta_count;
                    global_meta_count+=1;
                                        
                   solver.Add(ctx.mkGe(ctx.mkAdd(ctx.mkAdd(addList.toArray(new ArithExpr[addList.size()])),ctx.mkIntConst(meta_var)), ctx.mkInt(outputCardinality)));
                   solver.Add(ctx.mkLe(ctx.mkSub(ctx.mkAdd(addList.toArray(new ArithExpr[addList.size()])),ctx.mkIntConst(meta_var)), ctx.mkInt(outputCardinality)));
                   exp_final=ctx.mkAdd(exp_final,ctx.mkIntConst(meta_var));
                   
                	continue;
                }
                
                
                //THIS LINE ADDS ALL THE USUAL EQUATIONS INTO THE SOLVER STATEMENT
                solver.Add(ctx.mkEq(ctx.mkAdd(addList.toArray(new ArithExpr[addList.size()])), ctx.mkInt(outputCardinality)));
                
                solverStats.solverConstraintCount++;
            }
///////////////// Start dk
            List<List<IntExpr>> solverConstraintsToExport = new ArrayList<>(indexKeeper.size());
            for(int j = bvalues.size(); j < solverConstraints.size(); j++) {
            	solverConstraintsToExport.add(solverConstraints.get(j));
            }
            solverConstraintsToExport.add(solverConstraints.get(bvalues.size() - 1));
            allSolverConstraints.add(solverConstraintsToExport);
///////////////// End dk
        }
        
///////////////// Start dk
        
        //UNIFICATION : CHECK IF NEEDED
        
        int countConsistencyConstraint = 0;
        
        if(consistencyConstraints.length != 0) {
	        for (int c1index = 0; c1index < cliqueCount; c1index++) {
				HashMap<Integer, Integer> c1indexKeeper = mappedIndexOfConsistencyConstraint.get(c1index);
				if(c1indexKeeper.isEmpty())
					continue;
				List<List<IntExpr>> c1solverConstraints = allSolverConstraints.get(c1index);
				for (int c2index = c1index + 1; c2index < cliqueCount; c2index++) {
					HashMap<Integer, Integer> c2indexKeeper = mappedIndexOfConsistencyConstraint.get(c2index);
					if(c2indexKeeper.isEmpty())
						continue;
					List<List<IntExpr>> c2solverConstraints = allSolverConstraints.get(c2index);
					HashSet<Integer> applicableConsistencyConstraints = new HashSet<>();
					Set<Integer> temp = new HashSet<>(c1indexKeeper.keySet());
					temp.retainAll(c2indexKeeper.keySet());
					if(temp.isEmpty())
						continue;
					for (Integer ccIndex : temp) {
						applicableConsistencyConstraints.add(ccIndex);
					}
//    					System.err.println("First " + applicableConsistencyConstraints);
					List<List<IntExpr>> c1ApplicableSolverConstraints = new ArrayList<>();
					List<List<IntExpr>> c2ApplicableSolverConstraints = new ArrayList<>();
					for (Integer originalConsistencyConstraintIndex : applicableConsistencyConstraints) {
						c1ApplicableSolverConstraints.add(c1solverConstraints.get(c1indexKeeper.get(originalConsistencyConstraintIndex)));
						c2ApplicableSolverConstraints.add(c2solverConstraints.get(c2indexKeeper.get(originalConsistencyConstraintIndex)));
					}
					
					c1ApplicableSolverConstraints.add(c1solverConstraints.get(c1solverConstraints.size() - 1));
					c2ApplicableSolverConstraints.add(c2solverConstraints.get(c2solverConstraints.size() - 1));

					HashMap<IntList, List<List<IntExpr>>> conditionListToSetOfVarList = new HashMap<>();
					getVarToConditionList(c1ApplicableSolverConstraints, conditionListToSetOfVarList);
					getVarToConditionList(c2ApplicableSolverConstraints, conditionListToSetOfVarList);
					
					for (List<List<IntExpr>> list : conditionListToSetOfVarList.values()) {
						List<IntExpr> set1 = list.get(0);
						List<IntExpr> set2 = list.get(1);
						ArithExpr set1expr = ctx.mkAdd(set1.toArray(new ArithExpr[set1.size()]));
						ArithExpr set2expr = ctx.mkAdd(set2.toArray(new ArithExpr[set2.size()]));
						solver.Add(ctx.mkEq(set1expr, set2expr));
		                countConsistencyConstraint++;
					}
		        }
	        }
        }
        onlyFormationSW.displayTimeAndDispose();
        
        //System.err.println("Solver statement :\n" + solver.toString());
       
        StopWatch onlySolvingSW = new StopWatch("LP-OnlySolving" + viewname);
        
 		String answerFileContent = "";
 		String lpFileContent = "";
 			
        //UNCOMMENT THIS FOR NORMAL ESTIMATE
        solver.MkMinimize(exp_final);			        
        
        System.err.println("Started Solving...");
        
       //UNCOMMENT THIS FOR NORMAL ESTIMATE
        Status solverStatus = solver.Check();
        //Status solverStatus = Status.SATISFIABLE;
        
        //System.gc();
        
        System.out.println("Solver Status: " + solverStatus);
		
		 
        System.out.println("Current viewname = " + viewname);
        
        //for(Entry<String, String> d : viewNameAndAnonymizedViewNameMap.entrySet()){
        //	if(d.getValue().equals(viewname))
        //		System.out.println("Current viewname = " + d.getKey());
        //}
        
        System.out.println("Current fileNumber = " + DoubleReductionBasedViewSolver.fileCount);

        if (!Status.SATISFIABLE.equals(solverStatus)) {
        	System.err.println("Solver statement :\n" + solver.toString() + "\n"  + solver.getUnsatCore().length);
        	    for (Expr c : solver.getUnsatCore())
                {
                    System.out.println("Unsat : " + c);
                }
            
		  	ctx.close();
		      //throw new RuntimeException("solverStatus is not SATISFIABLE");
		}

        //UNCOMMENT THIS FOR NORMAL ESTIMATE
        Model model = solver.getModel();
        
        //System.gc();
        
        System.err.println("Started Solving ... Got Model");
        
    	int regionCount = 1;
   
        List<LinkedList<VariableValuePair>> cliqueIdxToVarValuesList = new ArrayList<>(cliqueCount);
        for (int i = 0; i < cliqueCount; i++) {

            IntList colIndxs = arasuCliquesAsColIndxs.get(i);
            Partition partition = cliqueIdxtoPList.get(i);
            LinkedList<VariableValuePair> varValuePairs = new LinkedList<>();
            
            for (int j = 0; j < partition.size(); j++) {
                String varname = "var" + i + "_" + j;
                
                //UNCOMMENT THIS FOR NORMAL ESTIMATE
                long rowcount = Long.parseLong(model.evaluate(ctx.mkIntConst(varname), true).toString());
                answerFileContent = answerFileContent + varname + " " + rowcount + "\n";
                
             
                //long rowcount = allEstimateList.get(estimateListCounterForPrinting);
               
                //if(rowcount - allEstimateList.get(estimateListCounterForPrinting) != 0)
                // new RuntimeException("Getting error");
                
                Region variable = getTruncatedRegion(partition.at(j), colIndxs);
                VariableValuePair varValuePair = new VariableValuePair(variable, rowcount);
                if (rowcount != 0) {
                    varValuePairs.add(varValuePair);                
                }                 
            }
            cliqueIdxToVarValuesList.add(varValuePairs);
        }
        
        FileUtils.writeStringToFile(PostgresVConfig.getProp(Key.SOLVER_ANS_FILE) + "_" + viewname  + ".txt", answerFileContent);
		System.out.println("Checking values:"+viewname);
        System.err.println("Started Solving... Got all answers written to file");
		System.err.println("Started Solving...Writing Lp to file");        
        lpFileContent = solver.toString() + "\n\nSolving status was : " + solverStatus ;       
        
        FileUtils.writeStringToFile(PostgresVConfig.getProp(Key.SOLVER_LP_FILE) + "_" + viewname + ".txt"  , lpFileContent);
		
        
        
    	System.err.println("Started Solving...Lp file written");
        
        
        onlySolvingSW.displayTimeAndDispose();
        
        ctx.close();
        
       // System.out.println("VV Pair in solver " + cliqueIdxToVarValuesList);

        return cliqueIdxToVarValuesList;
    
    }

    //UNIFICATION : CHECK IF NEEDED
	private void getVarToConditionList(List<List<IntExpr>> applicableSolverConstraints, HashMap<IntList, List<List<IntExpr>>> conditionListToSetOfVarList) {
    	HashMap<IntExpr, IntList> varToConditionList = new HashMap<>();
		for (int i = 0; i < applicableSolverConstraints.size(); i++) {
			for (IntExpr intExpr : applicableSolverConstraints.get(i)) {
				if(!varToConditionList.containsKey(intExpr))
					varToConditionList.put(intExpr, new IntArrayList());
				varToConditionList.get(intExpr).add(i);
			}
		}
		HashMap<IntList, List<IntExpr>> conditionListToVarList = new HashMap<>();
        for (Entry<IntExpr, IntList> entry : varToConditionList.entrySet()) {
        	IntExpr var = entry.getKey();
        	IntList conditionsList = entry.getValue();
			if(!conditionListToVarList.containsKey(conditionsList)) {
				conditionListToVarList.put(conditionsList, new ArrayList<>());
			}
			conditionListToVarList.get(conditionsList).add(var);
		}
        
        for (Entry<IntList, List<IntExpr>> entry : conditionListToVarList.entrySet()) {
			if(!conditionListToSetOfVarList.containsKey(entry.getKey())) {
				conditionListToSetOfVarList.put(entry.getKey(), new ArrayList<>());
			}
			conditionListToSetOfVarList.get(entry.getKey()).add(entry.getValue());
		}
    }

	private void dividingSkew(List<FormalCondition> conditions) {
		
     
      for(String fkey : fkeyToCliqueIdx.keySet()) {
    	  
    	  int cliqueIdx = fkeyToCliqueIdx.get(fkey);
    	  Set<String> currentClique = this.arasuCliques.get(cliqueIdx);
    	  
    	  Partition partition = this.cliqueIdxtoPList.get(cliqueIdx);
    	  
    	  Map<String, List<FormalCondition>> regionToCCMap = new HashMap<>();
    	  
    	  Map<String, Region> intervalisedRegions = fkeyToActualInteervalisedRegMap.get(fkey);
    	  
    	  for(String varname : varToIntervalisedRegionMapPerFkey.get(fkey).keySet()) {
    		  
    		  for(String regname : varToIntervalisedRegionMapPerFkey.get(fkey).get(varname) ) {
    			  Long val = allIntervalisedRegionsMap.get(regname);
        		  if(val == 0) {
        			  continue;
        		  }
        		  
        		  Region intervalisedRegion = intervalisedRegions.get(regname);
        		  for(int c=0; c< conditions.size(); c++) {
        			 FormalCondition curCondition = conditions.get(c); 
          			 Set<String> appearingCols = new HashSet<>();
                     getAppearingCols(appearingCols, curCondition);
          			 if (currentClique.containsAll(appearingCols)) {
          				 
          				 if(checkCCSatifyRegion(intervalisedRegion,appearingCols,curCondition)) {
          					
          					 
          					 //System.out.println("Clique_" + i + "Region" + j + " -> " + " CC_" + c);
          					 if(!regionToCCMap.containsKey(regname)) {
          						regionToCCMap.put(regname, new ArrayList<>());
          					 }
          					
          					 regionToCCMap.get(regname).add(conditions.get(c));
          					 
          				 }
          				 
          			 }
        		  }
    		  }
    		  
    		  
    		  
    	  }
    	  
    	 
    	  
    	  
    	  // CC to region Map
    	  Map<FormalCondition, List<String>> CCToRegionMap = new HashMap<>();
    	  for(String regionName : regionToCCMap.keySet() ) {
    		  
    		  for(FormalCondition fc : regionToCCMap.get(regionName)) {
    			  if(!CCToRegionMap.containsKey(fc)) {
    				  CCToRegionMap.put(fc, new ArrayList<>());
    			  }
    			  CCToRegionMap.get(fc).add(regionName);
    			  
    		  }
    		  
    		  
    	  }
    	  
    	  
    	  
    	  List<String> orderedRegions =  new ArrayList<>(); // orderedRegions on the basis of most intersecting CCs with a region
		  List<Integer> orderedRegionsCCcount = new ArrayList<>();
		  for(String region : regionToCCMap.keySet()) {
				if(orderedRegions.isEmpty()) {
					orderedRegions.add(region);
					orderedRegionsCCcount.add(regionToCCMap.get(region).size());
				}
				else {
					int i=0;
					for(i=0; i<orderedRegions.size(); i++) {
						
						if(regionToCCMap.get(region).size() >= orderedRegionsCCcount.get(i)) {
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
		  for(int i=1; i < cliqueIdxtoPSimplifiedList.get(cliqueIdx).size(); i++) {
			  CCSet.retainAll(cliqueIdxtoPSimplifiedList.get(cliqueIdx).get(i));
		  }
		  
		  if(CCSet.size() != 1 ) {
			  throw new RuntimeException(" not expecting this");
		  }
		  int allTrueRegionIdx = -1; // var number of all left over of true region
		  for(int i=0; i < cliqueIdxtoPSimplifiedList.get(cliqueIdx).size(); i++){
			  
			  Set<Integer> cp =  new HashSet<>(cliqueIdxtoPSimplifiedList.get(cliqueIdx).get(i));
			  
			  if(CCSet.equals(cp)) {
				  
				  allTrueRegionIdx = i;
				  break;
				  
			  }
		  }
		  
		 
		  
		// solveDF(orderedRegions, regionToCCMap, CCToRegionMap, fkey, cliqueIdx, allTrueRegionIdx);
		  
		 //solveDFPerFK(orderedRegions, regionToCCMap, CCToRegionMap, fkey, cliqueIdx, allTrueRegionIdx);
		   solveDFPerFK1(orderedRegions, regionToCCMap, CCToRegionMap, fkey, cliqueIdx, allTrueRegionIdx);
    	  
    	 
		  checkCCsAccuracy(CCToRegionMap, fkey);
    	  
    	  
      }
      
      
      checkEverything();
      
      
      
     
    	
    	
    	
      
		
	}

    
    private void checkCCsAccuracy(Map<FormalCondition, List<String>> cCToRegionMap, String fkey) {
		
    	//ss_sold_date_sk___2_q002.json
    	if(PostgresVConfig.ccsDFvectors.containsKey("ss_sold_date_sk___2_q002.json")) {
    		DFvector dfvector = PostgresVConfig.ccsDFvectors.get("ss_sold_date_sk___2_q002.json");
    		System.out.print("");
    	}
    	
    	
    	for(FormalCondition condition : cCToRegionMap.keySet()) {
			
			
			String actualFkeyName = PostgresVConfig.reverseColumnAnonyMap.get(fkey);
			Integer counter = condition.getCounter();
			String queryname = condition.getQueryname();
			String dfVecKey = actualFkeyName + "___" + counter + "_" + queryname;
			Map<String, DFvector> ccsDFvectors = PostgresVConfig.ccsDFvectors;
			if(ccsDFvectors.containsKey(dfVecKey)) {
				DFvector dfvector = ccsDFvectors.get(dfVecKey);
				List<String> regionsList = cCToRegionMap.get(condition);
				List<Long> allPkVals = new ArrayList<>();
				Map<Long,Long> pkValCount = new HashMap<>();
				for(int i=0; i < regionsList.size(); i++) {
					
					Map<Long, List<Long>> pkValDistribution = this.varPKValDistribution.get(regionsList.get(i));
					for(Long di : pkValDistribution.keySet()) {
						
						for(Long pkVal : pkValDistribution.get(di) ) {
							
							if(!pkValCount.containsKey(pkVal)) {
								pkValCount.put(pkVal, 0L);
							}
							pkValCount.put(pkVal,pkValCount.get(pkVal) + di);
							
							
						}
						
					}
					
				}
				
				Map<Long,Long> dfMap = new HashMap<>();
				for(Long pkVal : pkValCount.keySet()) {
					
					Long dVal = pkValCount.get(pkVal);
					if(!dfMap.containsKey(dVal)) {
						dfMap.put(dVal, 0L);
					}
					dfMap.put(dVal, dfMap.get(dVal) +  1);
					
					
				}
				
				System.out.print("");
				List<Long> dValues = new ArrayList<>();
				List<Long> fValues = new ArrayList<>();
				for(long d : dfMap.keySet() ) {
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
    	
    	for(String regionName : this.varPKValDistribution.keySet()) {
    		 
    		Long val = this.allIntervalisedRegionsMap.get(regionName);
    		
    		Long tupleCount = 0L;
    		for( Long dVal : this.varPKValDistribution.get(regionName).keySet() ) {
    			
    			tupleCount += dVal * this.varPKValDistribution.get(regionName).get(dVal).size();
    			
    		}
    		
    		
    		if(tupleCount.longValue() != val.longValue()) {
    			
    			System.out.print("");
    		}
    		
    		

    		
    	}
    	
    	
    	
		
	}
	
	
	private void solveDFPerFK1(List<String> orderedRegions, Map<String, List<FormalCondition>> regionToCCMap,
			Map<FormalCondition, List<String>> cCToRegionMap, String fkey, int cliqueIdx, int allTrueRegionIdx) {
		
		// IntervalBoundaries			
    	List<Long> pkValBoundaryList = new ArrayList<>();
    	Map<Integer, Integer> intervalIdxMap = new HashMap<>();
    	Long sumx=0L;
    	pkValBoundaryList.add(sumx);
    	for(int i=0; i<this.fkeyToIntervalRegionMap.get(fkey).size(); i++) {
    		// t17_c018_clique0interval0
    		intervalIdxMap.put(Integer.parseInt(this.fkeyToIntervalRegionMap.get(fkey).get(i).split("interval")[1]),i);
    		
    		sumx+=this.relationCardinality;
    		pkValBoundaryList.add(sumx);
    	}
    	
    	Map<Integer,Map<Long,List<Long>>> futureFKValToAdd = new HashMap<>();
    	
    	HashMap<Integer, List<String>> intervalToRegions = new HashMap<>();
		for(String regionname : orderedRegions) {
			
			//t17_c018_var0_0_interval_1
			int intervalIdx = Integer.parseInt(regionname.split("_")[5]) ;
			if(!intervalToRegions.containsKey(intervalIdx)) {
				intervalToRegions.put(intervalIdx, new ArrayList<>());
			}
			intervalToRegions.get(intervalIdx).add(regionname);
		}
		

		Map<String, Set<String>> fkeyToBorrowedAttr = PostgresVConfig.fkeyToBorrowedAttr.get(viewname);
		Set<String> borrowedAttrs = fkeyToBorrowedAttr.get(fkey);		
		
		if(borrowedAttrs.isEmpty()) {
			//System.out.print("NO need to manage fkey ");
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
		
		for(int i=0; i < intervalRegionsList.size(); i++) {
			
			String intervalName = intervalRegionsList.get(i);
			int intervalIdx = Integer.parseInt(intervalName.split("interval")[1]);
			List<Long> dList = new ArrayList<>();
			List<Long> fList = new ArrayList<>();
			for(int j=0; j < d.length(); j++) {
				// t17_c018_interval_0_d_1
				String dxVal = fkey + "_interval_"  + intervalIdx + "_d_" + j;
				if(!this.allDxValuesMap.containsKey(dxVal)) {
					continue;
				}
				Long fval = this.allDxValuesMap.get(fkey + "_interval_"  + intervalIdx + "_d_" + j );
				
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
		for(FormalCondition condition : cCToRegionMap.keySet()) {
					
					
			String actualFkeyName = PostgresVConfig.reverseColumnAnonyMap.get(fkey);
			Integer counter = condition.getCounter();
			String queryname = condition.getQueryname();
			String dfVecKey = actualFkeyName + "___" + counter + "_" + queryname;
			Map<String, DFvector> ccsDFvectors = PostgresVConfig.ccsDFvectors;
			if(ccsDFvectors.containsKey(dfVecKey)) {
				DFvector dfvector = ccsDFvectors.get(dfVecKey);
				DFvector dfvectorCopy = dfvector.copy();
				conditionToDFMap.put(condition, dfvectorCopy);	
			}
			else {
							
				// remove that CC for now will add it later
				List<String> regionList = cCToRegionMap.get(condition);
				removedRegion.addAll(regionList);
				for( String region : regionList ) {
								
					 regionToCCMap.get(region).remove(condition);
								 
				}
							
				removeList.add(condition);
			}
					
		}
		
		// removing CCs just because don't have df vector for it ..
		for(FormalCondition condition : removeList) {
			cCToRegionMap.remove(condition);
		}
		
		
		
		List<String> allTrueRegionList = varToIntervalisedRegionMap.get("var" + cliqueIdx + "_" + allTrueRegionIdx);
		
		// Interval -> [ [d][f] -> pkVal ] 
		Map<Integer, Map<DFvector, List<Long>>> futurePkValDFToAdd = new HashMap<>();
		// Keeps track of tuplesCovered by each region 
    	Map<String,Long> tuplesPerRegionCovered = new HashMap<>();
    	Map<String,Long> tuplesPerIntervalCovered = new HashMap<>();
		
    	// Select maxd from set of intervals and and satisy that
    	// and go on
    	System.out.println("FKey going on " + fkey);
    	Integer loop = 1;
    	
    	while(true) {
    		
    		long maxd = -1;
    		long maxf = -1;
    		
    		String selectedInterval = null; // maxd interval
    		
    		// if all interval df values are finished
    		if(intervalToDFVectorMap.isEmpty()) {
    			break;
    		}
    		
    		
    		for(String interval : intervalToDFVectorMap.keySet()) {
    			
    			DFvector dfVector = intervalToDFVectorMap.get(interval);
				if(maxd < dfVector.getD().get(0) ) {
					maxd = dfVector.getD().get(0);
					maxf = dfVector.getF().get(0);
					selectedInterval = interval;
				}
    			
    		}
    		
    		
    		// t17_c018_clique0interval1
    		int intervalIdx = Integer.parseInt(selectedInterval.split("interval")[1]);
    		
    		// all true region in current Interval
    		List<String> intervalAllTrueRegionList = new ArrayList<>();
    		
    		if(intervalAllTrueRegionList.size() > 1) {
				 throw new RuntimeException(" Was not expecting this ");
			}
    		
    		// intervalRemoved Region
			List<String> intervalRemovedRegionList = new ArrayList<>();
			for(String region : removedRegion) {
				 
			  if(intervalIdx == Integer.parseInt(region.split("interval_")[1]) ) {
					 intervalRemovedRegionList.add(region);
			  }
				 
			 }
			
			
			/*
			 *     ------------    All True Region Covering ---------------
			 * 
			 */
				
			// intervalToRegions contains all left over region yet to finished
			// allTrue REgion check
			 
			if(!intervalToRegions.containsKey(intervalIdx)) {
				
				// Either interval is finished
				//If all true region only left in that interval
				// once we are here we can completely cover whole interval
				
				// Pass it to future it will handle
				
				
				 if(!futurePkValDFToAdd.containsKey(intervalIdx)) {
					 futurePkValDFToAdd.put(intervalIdx, new HashMap<>());
				 }
				 
				
				
				if(!tuplesPerIntervalCovered.containsKey(selectedInterval)) {
					tuplesPerIntervalCovered.put(selectedInterval, 0L);
				}
				DFvector dfvector = intervalToDFVectorMap.get(selectedInterval);
				Long tupleSum = 0L;
				
				for(int di = 0; di < dfvector.size(); di++ ) {
					
					List<Long> dValues = new ArrayList<>();
					List<Long> fValues = new ArrayList<>();
					dValues.add(dfvector.getD().get(di));
					fValues.add(dfvector.getF().get(di));
					Long pkValStart = pkValBoundaryList.get(intervalIdxMap.get(intervalIdx));
					DFvector dfvec = new DFvector(dValues, fValues);
					
					if(!futurePkValDFToAdd.get(intervalIdx).containsKey(dfvec)) {
						 futurePkValDFToAdd.get(intervalIdx).put(dfvec, new ArrayList<>());
					 }
					futurePkValDFToAdd.get(intervalIdx).get(dfvec).add(pkValStart);
					pkValBoundaryList.set(intervalIdxMap.get(intervalIdx), pkValStart + dfvector.getF().get(di));
					tupleSum += dfvec.getD().get(0) * dfvec.getF().get(0); 
					
				}
				
				tuplesPerIntervalCovered.put(selectedInterval, tuplesPerIntervalCovered.get(selectedInterval) + tupleSum );
				
				// introduce check stmt for boundary check
				if(this.allIntervalRegionValueMap.get(selectedInterval).longValue() != tuplesPerIntervalCovered.get(selectedInterval).longValue() ) {
					
					throw new RuntimeException("Interval values covered should match");
					
				}
				
				
				intervalToDFVectorMap.remove(selectedInterval);
				
				continue;
				
				
			}
			
			
			
			// Now we have maxd and maxf
			// 
			List<String> overlappingRegionsWithInterval = intervalToRegions.get(intervalIdx);
			List<Set<FormalCondition>> overlappingCCsSet = new ArrayList<>();
			HashMap<FormalCondition, List<Integer>>  conditionsToOverlappingRegions = new HashMap<>();
			for(int i=0; i < overlappingRegionsWithInterval.size(); i++ ) {
				
				String overlappingRegion = overlappingRegionsWithInterval.get(i);
				Set<FormalCondition> overlappingCCs = new HashSet<>(regionToCCMap.get(overlappingRegion));				
				overlappingCCsSet.add(overlappingCCs);
				for(FormalCondition fc : overlappingCCs) {
					if(!conditionsToOverlappingRegions.containsKey(fc)) {
						conditionsToOverlappingRegions.put(fc, new ArrayList<>());
					}
					conditionsToOverlappingRegions.get(fc).add(i);
				}
			}
			
			
			
			// handle things at region level
			// remove things from other area
			// do the things in much better way
			// take care of region cardinality
			// remove CC cardinality accordingly as per reduction
			
			
			// Earlier grouping of regions
			// find overlapping nature of intervalised regions inside current interval
			
			int[][] overlappingRegionNature = new int[overlappingRegionsWithInterval.size()][overlappingRegionsWithInterval.size()];
			int mostIntersectingRegionIdx = findAllRegionsOverlappingNature(overlappingRegionsWithInterval, intervalIdx, overlappingRegionNature);
			
			String mostIntersectingRegion = overlappingRegionsWithInterval.get(mostIntersectingRegionIdx);
			
			// CCs intersecting with mostIntersectingRegion
			List<FormalCondition> mostIntersectingRegionCCs = regionToCCMap.get(mostIntersectingRegion);
			
			// Extracting regions that overlaps with the current set of CCs
			List<String> regionsToBeConsidered = new ArrayList<>();
			for(String regionname : overlappingRegionsWithInterval) {
				
				List<FormalCondition> ccs = new ArrayList<>(regionToCCMap.get(regionname));
				ccs.retainAll(mostIntersectingRegionCCs);
				if(!ccs.isEmpty()) {
					regionsToBeConsidered.add(regionname);
				}
				
			}
			
			
			
			
			List<DFvector> dfVectorList = new ArrayList<>();
			for(FormalCondition condition : mostIntersectingRegionCCs) {
				dfVectorList.add(conditionToDFMap.get(condition));
			}
			
			
			
			// topo seq number assigning
			Map<String,Set<String>> precedenceMap = new HashMap<>();
			Map<String,List<String>> edgeInfoMap = new HashMap<>();
			List<List<String>> topologicalWay = topoSeqAss(regionsToBeConsidered, mostIntersectingRegionCCs, 
					regionToCCMap, dfVectorList,precedenceMap,mostIntersectingRegion,edgeInfoMap);
			
			Map<String, Set<String>> revPrecedenceMap = getRevPrecedenceMap(precedenceMap);
			
			List<Long> appropriateDF = new ArrayList<>();
			findAppropriateDF(appropriateDF , dfVectorList , maxd, maxf);
			
			
			
			newDistributeDF(appropriateDF, dfVectorList, maxd, maxf,mostIntersectingRegionCCs,regionToCCMap,
					topologicalWay, precedenceMap, futurePkValDFToAdd, pkValBoundaryList, mostIntersectingRegion,
					revPrecedenceMap, edgeInfoMap,conditionToDFMap);
					
			
			
			
			
			// Once we know overlapping nature 
			// Call findApprox
			// Then deduct from interval region and CC
			// and process continues
			
			
			
			// Assign appD,appF to current region
			// and other regions overlapping with it distribute rest of the regions
			
			distributeDF(appropriateDF, dfVectorList, maxd, maxf, overlappingRegionNature, overlappingRegionsWithInterval,
					futurePkValDFToAdd,mostIntersectingRegionIdx,pkValBoundaryList,regionToCCMap);
			
			
			
			
			
			
			
		
			
			
			
			
			
			
			
    		
    	}
    	
    	
    	leftOverDF(futurePkValDFToAdd);
    	
    	
    	
		
		
		
    	
    	
    	
    	
		
		
	}

	

	private Map<String, Set<String>> getRevPrecedenceMap(Map<String, Set<String>> precedenceMap) {
		// TODO Auto-generated method stub
		Map<String,Set<String>> revPrecedenceMap = new HashMap<>();
		for(String key : precedenceMap.keySet()) {
			
			for(String reg : precedenceMap.get(key)) {
				
				if(!revPrecedenceMap.containsKey(reg)) {
					revPrecedenceMap.put(reg, new HashSet<>());
				}
				revPrecedenceMap.get(reg).add(key);
				
			}
		}
		
		return revPrecedenceMap;
	}

	private List<List<String>> topoSeqAss(List<String> regionsToBeConsidered, List<FormalCondition> mostIntersectingRegionCCs,
			Map<String, List<FormalCondition>> regionToCCMap, List<DFvector> dfVectorList,Map<String, Set<String>> precedenceMap, String mostIntersectingRegion,
			Map<String,List<String>> edgeInfoMap) {
		
		// Only those regions which have common CCs
		/*
		 *  Topological ordering
		 *  index number indicates number of CCs matched
		 */
		
		List<List<String>> topologicalWay = new ArrayList<>();
		
		for(int i=0; i < mostIntersectingRegionCCs.size(); i++) {
			topologicalWay.add(new ArrayList<>());
		}
		
		for(String regionname : regionsToBeConsidered) {
			
			List<FormalCondition> ccs = new ArrayList<>(regionToCCMap.get(regionname));
			ccs.retainAll(mostIntersectingRegionCCs);
			
			if(ccs.size() <= 0 || ccs.size() > mostIntersectingRegionCCs.size()) {
				throw new RuntimeException("Unexpected point");
			}
			
			topologicalWay.get(ccs.size()-1).add(regionname);
			
			
		}
		
		
		// Now defining edges between the nodes of toplogicalWay
		// using precedence map
		for(int i=topologicalWay.size()-1; i>=0; i--) {
			
			for(int j=0; j < topologicalWay.get(i).size(); j++) {
				
				String currentReg = topologicalWay.get(i).get(j);
				List<FormalCondition> currentRegCCs = new ArrayList<>(regionToCCMap.get(currentReg));
				currentRegCCs.retainAll(mostIntersectingRegionCCs);
				
				Set<String> regionsList = new HashSet<>(); 
				
				for(int k=i+1; k <topologicalWay.size(); k++) {
					
					for(int l=0; l < topologicalWay.get(k).size();l++) {
						String otherReg = topologicalWay.get(k).get(l);
						List<FormalCondition> otherRegCCs = new ArrayList<>(regionToCCMap.get(otherReg));
						otherRegCCs.retainAll(mostIntersectingRegionCCs);
						
						currentRegCCs.retainAll(otherRegCCs);
						// if CCs intersects then it will be non empty
						if(!currentRegCCs.isEmpty()) {
							regionsList.add(otherReg);
						}
						
					}
					
				}
				
				precedenceMap.put(currentReg, regionsList);
				
				
			}
			
		}
		
		
		
		
		
		// create new map and remove transitive edges
		for(int i=topologicalWay.size()-2; i>=0; i--) {
			
			for(int j=0; j < topologicalWay.get(i).size(); j++) {
				
				String currentReg = topologicalWay.get(i).get(j);
				if(i+1 <= topologicalWay.size()-1) {
					
					for(int k=0; k < topologicalWay.get(i+1).size();k++) {
						
						
						if(precedenceMap.get(currentReg).contains(topologicalWay.get(i+1).get(k))) {
							if(!edgeInfoMap.containsKey(topologicalWay.get(i).get(k))) {
								edgeInfoMap.put(topologicalWay.get(i).get(k), new ArrayList<>());
							}
							edgeInfoMap.get(topologicalWay.get(i).get(k)).add(currentReg);
						}
						
					}
				}
			}
		}
		
		
		
		
		
		return topologicalWay;
		
		
	}


	

	private void leftOverDF(Map<Integer, Map<DFvector, List<Long>>> futurePkValDFToAdd) {
		
		// TODO Auto-generated method stub
		
		
		
		
	}


	private void newDistributeDF(List<Long> appropriateDF, List<DFvector> dfVectorList, long maxd, long maxf,
			List<FormalCondition> mostIntersectingRegionCCs, Map<String, List<FormalCondition>> regionToCCMap,
			List<List<String>> topologicalWay, Map<String, Set<String>> precedenceMap,
			Map<Integer, Map<DFvector, List<Long>>> futurePkValDFToAdd, List<Long> pkValBoundaryList,
			String mostIntersectingRegion, Map<String, Set<String>> revPrecedenceMap, Map<String, List<String>> edgeInfoMap, Map<FormalCondition, DFvector> conditionToDFMap) {
		
		Long appD = appropriateDF.get(0);
		Long appF = appropriateDF.get(1);
		
		// assigns df to current region
		assignFKVal(mostIntersectingRegion,appD,appF,pkValBoundaryList);
		
		
		// create diff ordered list to be used one by one for 
		// left over data
		// creating this list 
	
		
		
	
		
		
		
		// assign leftover appropriateDF values		
		List<String> regionsCovered =  new ArrayList<>();
		
		
		
		
		
		
		
		
		
		
		List<String> currentList = new ArrayList<>();
		currentList.add(mostIntersectingRegion);
		
		// Used stack for dfs traversal
		Stack<String> regionStack = new Stack<>();
		
		regionStack.add(mostIntersectingRegion);
		
		
		
		while(!regionStack.isEmpty()) {
			
			
			// distribute among the current list
			String currentTop = regionStack.peek();
			regionStack.pop();
			if(edgeInfoMap.containsKey(currentTop)) {
				List<String> associatedRegions = edgeInfoMap.get(currentTop);
				
				
				for(String reg : associatedRegions ) {
					
					List<FormalCondition> ccsList = regionToCCMap.get(reg);
					ccsList.retainAll(mostIntersectingRegionCCs);
					List<DFvector> newDfVectorList = new ArrayList<>();
					for(FormalCondition condition : ccsList) {
						newDfVectorList.add(conditionToDFMap.get(condition));
					}
					List<Long> appropriateDFnew = new ArrayList<>();
					// need to create modified findAppropriateDF
					// which finds the closest to current
					findAppropriateDF(appropriateDFnew , dfVectorList , maxd, maxf);
					
					
					
				}
				
				
				// Add regions on the basis of closest to appD
				regionStack.addAll(associatedRegions);
			}
			
			
			// Maximum allocation possible f value
			Long appFnew =  appF; // for now its wrong
			assignFKVal(currentTop,appD,appF,pkValBoundaryList);
			
			
		}
		
		
	
		
		
		
		// Traverse all regions one by one and add CCs and 
		// distribution 
		
		
		
		
		
		
		
		
		
		
		
		
		
	}
	
	private void distributeDF(List<Long> appropriateDF, List<DFvector> dfVectorList, long maxd, long maxf,
			int[][] overlappingRegionNature, List<String> overlappingRegionsWithInterval, Map<Integer, Map<DFvector, List<Long>>> futurePkValDFToAdd, 
			int mostIntersectingRegionIdx, List<Long> pkValBoundaryList, Map<String, List<FormalCondition>> regionToCCMap) {
		
		// Give appD,appF to region
		// and remaining to leftover
		// varPKValDistribution
		// futurePkValDFToAdd
		
		
		// Assigns arbitrary FK value 
		
		Long appD = appropriateDF.get(0);
		Long appF = appropriateDF.get(1);
		
		String mostIntersectingRegion = overlappingRegionsWithInterval.get(mostIntersectingRegionIdx);
		
		// assigns df to current region
		assignFKVal(mostIntersectingRegion,appD,appF,pkValBoundaryList);
		
		
		// now its time for other regions
		long leftd = maxd - appD;
		
		// f value would be appf only
		
		otherRegionsInInterval(leftd, appF, pkValBoundaryList,overlappingRegionsWithInterval,
				mostIntersectingRegionIdx,overlappingRegionNature,futurePkValDFToAdd,dfVectorList,regionToCCMap);
		
		
		
		// Deduct the DC after deduction
		
		
		
		
		
		
		
		
	}

	private void otherRegionsInInterval(long leftd, Long appF, List<Long> pkValBoundaryList,
			List<String> overlappingRegionsWithInterval, int mostIntersectingRegionIdx,
			int[][] overlappingRegionNature, Map<Integer, Map<DFvector, List<Long>>> futurePkValDFToAdd,
			List<DFvector> dfVectorList, Map<String, List<FormalCondition>> regionToCCMap) {
		
		/*
		 *    2 : Region 2 subsumes Region 1
		 *    3 : Partially overlaps 
		 */
		
		
		
		List<Integer> subsumingRegionsIdx = new ArrayList<>();
		List<Integer> partiallyRegionsIdx = new ArrayList<>();
		
		
		
		for(int i=0; i < overlappingRegionNature.length; i++) {
			
			String regionname = overlappingRegionsWithInterval.get(i);
			
			List<FormalCondition> overlappingCCsWithCurrentRegion = regionToCCMap.get(regionname);
			List<FormalCondition> conditionList = regionToCCMap.get(overlappingRegionsWithInterval.get(i)) ;
			overlappingCCsWithCurrentRegion.retainAll(conditionList);
			
			
			// removes those regions whose CCs don't overlap with current set of CCs
			if(!overlappingCCsWithCurrentRegion.isEmpty()) {
				continue;	
			}
			
			if(i != mostIntersectingRegionIdx) {
				
				if(overlappingRegionNature[mostIntersectingRegionIdx][i] == 2 ) {
					subsumingRegionsIdx.add(i);
				}
				else if(overlappingRegionNature[mostIntersectingRegionIdx][i] == 3) {
					partiallyRegionsIdx.add(i);
				}
				
			}
				
		}
		
		
		
		
		
		// sort subsuming regionIDx on the basis of number 
		
		// Outer Loop that covers things
		List<Integer> coveredRegion = new ArrayList<>();
		while(true) {
			
			
			while(true) {
				
				for(int i=0; i < subsumingRegionsIdx.size(); i++) {
					
					
					
				}
				
			}
			
		}
		
		
		
		
		
		
		
		
		
	}

	private void assignFKVal(String mostIntersectingRegion, Long appD, Long appF, List<Long> pkValBoundaryList) {
		// TODO Auto-generated method stub
		
		//t17_c018_var0_3_interval_1
	
		int intervalIdx = Integer.parseInt(mostIntersectingRegion.split("_interval_")[1]);
		
		if(!this.varPKValDistribution.containsKey(mostIntersectingRegion)) {
			
			this.varPKValDistribution.put(mostIntersectingRegion, new HashMap<>());
			
		}
		
		
		if(!this.varPKValDistribution.get(mostIntersectingRegion).containsKey(appD)) {
			this.varPKValDistribution.get(mostIntersectingRegion).put(appD, new ArrayList<>());
		}
		
		for(long i=0; i < appF; i++) {
			
			this.varPKValDistribution.get(mostIntersectingRegion).get(appD).add(pkValBoundaryList.get(intervalIdx) + i);		
		}
		
		
		// This maybe needed at later point of time
		//pkValBoundaryList.set(intervalIdx, pkValBoundaryList.get(intervalIdx) + appF);l
		
		
		
		
	}

	private int findAllRegionsOverlappingNature(List<String> overlappingRegionsWithInterval, int intervalIdx, int[][] overlappingRegionNature) {
		
		
		
		int mostOverlappingRegion = 0;
		int maxIntersectionCount = -1;
		for(int i=0; i < overlappingRegionsWithInterval.size(); i++) {
			
			String regionName = overlappingRegionsWithInterval.get(i);
			int intersectionCount = 0;
			for(int j= i+1; j < overlappingRegionsWithInterval.size(); j++) {
				String otherRegionName = overlappingRegionsWithInterval.get(j);
				int val = findOverlappingNature(regionName, otherRegionName, intervalIdx);
				overlappingRegionNature[i][j] = val;
				overlappingRegionNature[j][i] = val;
				if(val == 1 || val == 0 || val == 3) {
					intersectionCount++;
				}
				
			}
			if(maxIntersectionCount < intersectionCount) {
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
		
		
		for(BucketStructure bs : region1.getAll()) {
			 BucketStructure newBs = new BucketStructure();
			 int c=0;
			 for(Bucket b : bs.getAll()) {
				 String currentCol = this.sortedViewColumns.get(c);
				 if(sortedCliqueColumns.contains(currentCol)) {
					 newBs.add(b);
				 }
				 c++;
			 }
			 modifiedRegion1.add(newBs);
		}
		
		for(BucketStructure bs : region2.getAll()) {
			 BucketStructure newBs = new BucketStructure();
			 int c=0;
			 for(Bucket b : bs.getAll()) {
				 String currentCol = this.sortedViewColumns.get(c);
				 if(sortedCliqueColumns.contains(currentCol)) {
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
		 *   -1 : non-intersecting
		 *    0 : fully intersecting
		 *    1 : Region 1 subsumes Region 2
		 *    2 : Region 2 subsumes Region 1
		 *    3 : Partially overlaps 
		 */
		
		
		Region minus1 = modifiedRegion1.minus(modifiedRegion2);
		Region minus2 = modifiedRegion2.minus(modifiedRegion1);
		
		if(minus1.isEmpty() && minus2.isEmpty()) {
			// either no intersection or fully overlap
			Region intersectingRegion = modifiedRegion1.intersection(modifiedRegion2);
			if(intersectingRegion.isEmpty()) {
				// no intersection
				return -1;
			}
			else {
				// fully intersecting
				return 0;
				
				
			}
		}
		else if(minus1.isEmpty()) {
			// Region2 is bigger and overlaps with region1
			return 2;
		}
		else if(minus2.isEmpty()) {
			// Region2 is bigger and overlaps with region1
			return 1;
		}
		else {
			// Both regions partially overlaps each other
			return 3;
		}
		
		
		
		
		
	}

	private void solveDFPerFK(List<String> orderedRegions, Map<String, List<FormalCondition>> regionToCCMap,
			Map<FormalCondition, List<String>> cCToRegionMap, String fkey, int cliqueIdx, int allTrueRegionIdx) {
    	
    	
    	
    	
    	// IntervalBoundaries			
    	List<Long> pkValBoundaryList = new ArrayList<>();
    	Map<Integer, Integer> intervalIdxMap = new HashMap<>();
    	Long sumx=0L;
    	pkValBoundaryList.add(sumx);
    	for(int i=0; i<this.fkeyToIntervalRegionMap.get(fkey).size(); i++) {
    		// t17_c018_clique0interval0
    		intervalIdxMap.put(Integer.parseInt(this.fkeyToIntervalRegionMap.get(fkey).get(i).split("interval")[1]),i);
    		
    		sumx+=this.relationCardinality;
    		pkValBoundaryList.add(sumx);
    	}
    	
    	HashMap<Integer, List<String>> intervalToRegions = new HashMap<>();
		for(String regionname : orderedRegions) {
			
			//t17_c018_var0_0_interval_1
			int intervalIdx = Integer.parseInt(regionname.split("_")[5]) ;
			if(!intervalToRegions.containsKey(intervalIdx)) {
				intervalToRegions.put(intervalIdx, new ArrayList<>());
			}
			intervalToRegions.get(intervalIdx).add(regionname);
		}
		

		Map<String, Set<String>> fkeyToBorrowedAttr = PostgresVConfig.fkeyToBorrowedAttr.get(viewname);
		Set<String> borrowedAttrs = fkeyToBorrowedAttr.get(fkey);		
		
		if(borrowedAttrs.isEmpty()) {
			//System.out.print("NO need to manage fkey ");
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
		
		for(int i=0; i < intervalRegionsList.size(); i++) {
			
			String intervalName = intervalRegionsList.get(i);
			int intervalIdx = Integer.parseInt(intervalName.split("interval")[1]);
			List<Long> dList = new ArrayList<>();
			List<Long> fList = new ArrayList<>();
			for(int j=0; j < d.length(); j++) {
				// t17_c018_interval_0_d_1
				String dxVal = fkey + "_interval_"  + intervalIdx + "_d_" + j;
				if(!this.allDxValuesMap.containsKey(dxVal)) {
					continue;
				}
				Long fval = this.allDxValuesMap.get(fkey + "_interval_"  + intervalIdx + "_d_" + j );
				
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
		for(FormalCondition condition : cCToRegionMap.keySet()) {
					
					
			String actualFkeyName = PostgresVConfig.reverseColumnAnonyMap.get(fkey);
			Integer counter = condition.getCounter();
			String queryname = condition.getQueryname();
			String dfVecKey = actualFkeyName + "___" + counter + "_" + queryname;
			Map<String, DFvector> ccsDFvectors = PostgresVConfig.ccsDFvectors;
			if(ccsDFvectors.containsKey(dfVecKey)) {
				DFvector dfvector = ccsDFvectors.get(dfVecKey);
				DFvector dfvectorCopy = dfvector.copy();
				conditionToDFMap.put(condition, dfvectorCopy);	
			}
			else {
							
				// remove that CC for now will add it later
				List<String> regionList = cCToRegionMap.get(condition);
				removedRegion.addAll(regionList);
				for( String region : regionList ) {
								
					 regionToCCMap.get(region).remove(condition);
								 
				}
							
				removeList.add(condition);
			}
					
		}
		
		// removing CCs just because don't have df vector for it ..
		for(FormalCondition condition : removeList) {
			cCToRegionMap.remove(condition);
		}
		
		
		
		List<String> allTrueRegionList = varToIntervalisedRegionMap.get("var" + cliqueIdx + "_" + allTrueRegionIdx);
		
		// Interval -> [ [d][f] -> pkVal ] 
		Map<Integer, Map<DFvector, List<Long>>> futurePkValDFToAdd = new HashMap<>();
		// Keeps track of tuplesCovered by each region 
    	Map<String,Long> tuplesPerRegionCovered = new HashMap<>();
    	Map<String,Long> tuplesPerIntervalCovered = new HashMap<>();
    	
    	
    	
    	
		
    	// Select maxd from set of intervals and and satisy that
    	// and go on
    	System.out.println("FKey going on " + fkey);
    	Integer loop = 1;
    	while(true) {
    		
    		loop += 1;
    		
    		long maxd = -1;
			long maxf = -1;
			String selectedInterval =null; // maxd interval
			if(intervalToDFVectorMap.isEmpty()) {
				break;
			}
			
			for(String interval : intervalToDFVectorMap.keySet() ) {
				
				DFvector dfVector = intervalToDFVectorMap.get(interval);
				if(maxd < dfVector.getD().get(0) ) {
					maxd = dfVector.getD().get(0);
					maxf = dfVector.getF().get(0);
					selectedInterval = interval;
				}
				
			}
			
			// t17_c018_clique0interval1
			int intervalIdx = Integer.parseInt(selectedInterval.split("interval")[1]);
			
			// all true region in current Interval
			List<String> intervalAllTrueRegionList = new ArrayList<>();
			
			
			if(intervalAllTrueRegionList.size() > 1) {
				 throw new RuntimeException(" Was not expecting this ");
			 }
			
			// intervalRemoved Region
			 List<String> intervalRemovedRegionList = new ArrayList<>();
			 for(String region : removedRegion) {
				 
				 if(intervalIdx == Integer.parseInt(region.split("interval_")[1]) ) {
					 intervalRemovedRegionList.add(region);
				 }
				 
			 }
			 
			 
			 
			 
			
			
			/*
			 *     ------------    All True Region Covering ---------------
			 * 
			 */
				
			// intervalToRegions contains all left over region yet to finished
			// allTrue REgion check
			 
			if(!intervalToRegions.containsKey(intervalIdx)) {
				
				// Either interval is finished
				//If all true region only left in that interval
				// once we are here we can completely cover whole interval
				
				// Pass it to future it will handle
				
			
				 if(!futurePkValDFToAdd.containsKey(intervalIdx)) {
					 futurePkValDFToAdd.put(intervalIdx, new HashMap<>());
				 }
				 
				
				
				if(!tuplesPerIntervalCovered.containsKey(selectedInterval)) {
					tuplesPerIntervalCovered.put(selectedInterval, 0L);
				}
				DFvector dfvector = intervalToDFVectorMap.get(selectedInterval);
				Long tupleSum = 0L;
				
				for(int di = 0; di < dfvector.size(); di++ ) {
					
					List<Long> dValues = new ArrayList<>();
					List<Long> fValues = new ArrayList<>();
					dValues.add(dfvector.getD().get(di));
					fValues.add(dfvector.getF().get(di));
					Long pkValStart = pkValBoundaryList.get(intervalIdxMap.get(intervalIdx));
					DFvector dfvec = new DFvector(dValues, fValues);
					
					if(!futurePkValDFToAdd.get(intervalIdx).containsKey(dfvec)) {
						 futurePkValDFToAdd.get(intervalIdx).put(dfvec, new ArrayList<>());
					 }
					futurePkValDFToAdd.get(intervalIdx).get(dfvec).add(pkValStart);
					pkValBoundaryList.set(intervalIdxMap.get(intervalIdx), pkValStart + dfvector.getF().get(di));
					tupleSum += dfvec.getD().get(0) * dfvec.getF().get(0); 
					
				}
				
				tuplesPerIntervalCovered.put(selectedInterval, tuplesPerIntervalCovered.get(selectedInterval) + tupleSum );
				
				// introduce check stmt for boundary check
				if(this.allIntervalRegionValueMap.get(selectedInterval).longValue() != tuplesPerIntervalCovered.get(selectedInterval).longValue() ) {
					
					throw new RuntimeException("Interval values covered should match");
					
				}
				
				
				intervalToDFVectorMap.remove(selectedInterval);
				
				continue;
				
				
				
			}
			
			
			
			// Now we have maxd and maxf
			// have 
			
			
			
			List<String> overlappingRegionsWithInterval = intervalToRegions.get(intervalIdx);
			List<Set<FormalCondition>> overlappingCCsSet = new ArrayList<>();
			HashMap<FormalCondition, List<Integer>>  conditionsToOverlappingRegions = new HashMap<>();
			for(int i=0; i < overlappingRegionsWithInterval.size(); i++ ) {
				
				String overlappingRegion = overlappingRegionsWithInterval.get(i);
				Set<FormalCondition> overlappingCCs = new HashSet<>(regionToCCMap.get(overlappingRegion));				
				overlappingCCsSet.add(overlappingCCs);
				for(FormalCondition fc : overlappingCCs) {
					if(!conditionsToOverlappingRegions.containsKey(fc)) {
						conditionsToOverlappingRegions.put(fc, new ArrayList<>());
					}
					conditionsToOverlappingRegions.get(fc).add(i);
				}
			}
			
			

			// Grouping conditions on the basis same regions overlapping
			
			HashMap<List<Integer>,List<FormalCondition>> groupMap = new HashMap<>();
			for(FormalCondition formalCondition : conditionsToOverlappingRegions.keySet() ) {
				List<Integer> regionList = conditionsToOverlappingRegions.get(formalCondition);
				if(!groupMap.containsKey(regionList)) {
					groupMap.put(regionList, new ArrayList<>());
				}
				groupMap.get(regionList).add(formalCondition);
				
			
			}
			
			
			// SuperSet Map
			HashMap<List<Integer>, Set<List<Integer>>> superSetMap = new HashMap<>();
			int maxlen = -1;
			Set<List<Integer>> groupKeys = groupMap.keySet();
			for(List<Integer> groupKey : groupKeys) {
				if(maxlen < groupKey.size()) {
					maxlen = groupKey.size();
				}
				superSetMap.put(groupKey, new HashSet<>());
				for(List<Integer> key : groupKeys) {
					
					Set<Integer> keySet = new HashSet<>(groupKey);
					keySet.removeAll(key);
					if(keySet.isEmpty()) {
						superSetMap.get(groupKey).add(key);
						
					}
					
					
				}
				
			}
			
			
			//sorting on basis of List<Integer>
			List<List<Integer>>sortedGroupIdxs = new ArrayList<>();
			for(int i=1; i <= maxlen; i++) {
				
				for(List<Integer> groupIdx : groupMap.keySet()) {
					
					if(groupIdx.size() == i) {
						sortedGroupIdxs.add(groupIdx);
					}
					
				}
				
			}
			
			
			//Group to region map
			Set<String> regionsCovered = new HashSet<>();
			HashMap<List<Integer>,String> groupToRegionMap= new HashMap<>();
			for(List<Integer> groupKey : sortedGroupIdxs) {
				
				List<FormalCondition> conditionList = groupMap.get(groupKey);
				for(FormalCondition fc : conditionList) {
					
					List<Integer> regionIdxList = conditionsToOverlappingRegions.get(fc);
					Set<String> regionsSet = new HashSet<>();
					for(int i : regionIdxList) {
						String region = overlappingRegionsWithInterval.get(i);
						regionsSet.add(region);
					}
					regionsSet.removeAll(regionsCovered);
					if(!regionsSet.isEmpty()) {
						if(regionsSet.size() != 1) {
							throw new RuntimeException(" Not expecting this");
						}
						
						List<String>regionsList = new ArrayList<>(regionsSet);
						String region= regionsList.get(0);
						groupToRegionMap.put(groupKey, region);
						regionsCovered.add(region);
					}
					
					
					
				}
				
				
			}
			
			
			
			
			
			
			/*
			 *  1. Find max d closest in all group
			 *  2. If exact match found in any group then directly replace
			 *  3. If exact match not found and divide the d into all groups
			 *  4. No hopes flag will be there after that whatever is there just put it
			 *  
			 *  
			 */
			

			// Step 1 : Find max d closest to maxd for each group
			Map<List<Integer>, List<Long> > appropriateDFMap = new HashMap<>();
			Map<List<Integer>, List<Integer>> dLocationsMap = new HashMap<>();
			Integer minLength = null;
			Integer maxLength = null;
			
			for(List<Integer> groupIdx : groupMap.keySet()) {
				
				List<FormalCondition> conditionList = groupMap.get(groupIdx);
				List<DFvector> dfVectorList = new ArrayList<>();
				
				for(FormalCondition condition : conditionList) {
					DFvector dfvector = conditionToDFMap.get(condition);
					if(dfvector.isEmpty()) {
						continue;
					}
					dfVectorList.add(dfvector);
				}
				List<Long> appropriateDF = new ArrayList<>();
				
				if(dfVectorList.isEmpty()) {
					continue;
				}
				
				
				boolean flag = findAppropriateDF(appropriateDF, dfVectorList, maxd, maxf);
				if(flag == false) {
					break;
				}
			
				if(appropriateDF.get(0) <= maxd) {
					appropriateDFMap.put(groupIdx, appropriateDF);
					
				}
				
				
				
				
				if(minLength == null) {
					minLength = groupIdx.size();
					maxLength = groupIdx.size();
				}
				else {
					
					if(groupIdx.size() > maxLength) {
						maxLength = groupIdx.size();
					}
					if(groupIdx.size() < minLength) {
						minLength = groupIdx.size();
					}
					
				}
					
			
				
			}
			
			System.out.print("");
		
				
				
				

				/*
				 *  FROM SET OF DF's available
				 *  
				 *  1. if any of d value is equal to maxd choose it
				 *  2. if any of d Value is greater than maxd and other have smaller
				 */
				
				
				
				
				
				
				/*
				 *   No appropriate df found
				 *   end up this interval
				 */
				
					if(appropriateDFMap.isEmpty()) {
						
						System.out.print("");
						// Shift everything to future 
						// Since nothing is left in df vector to pull off
						DFvector dfvector = intervalToDFVectorMap.get(selectedInterval);
						for(int di=0; di < dfvector.getD().size(); di++) {
							
							Long dVal = dfvector.getD().get(di);
							Long fVal = dfvector.getF().get(di);
							ArrayList<Long> dList = new ArrayList<>();
							dList.add(dVal);
							ArrayList<Long> fList = new ArrayList<>();
							fList.add(fVal);
							DFvector dfvec = new DFvector(dList, fList);
							
							Long pkValStart = pkValBoundaryList.get(intervalIdxMap.get(intervalIdx));
							
							if(!futurePkValDFToAdd.containsKey(intervalIdx)) {
								 futurePkValDFToAdd.put(intervalIdx, new HashMap<>());
							 }
							 if(!futurePkValDFToAdd.get(intervalIdx).containsKey(dfvec)) {
								 futurePkValDFToAdd.get(intervalIdx).put(dfvec, new ArrayList<>());
							 }
							 futurePkValDFToAdd.get(intervalIdx).get(dfvec).add(pkValStart);
							 
							 pkValBoundaryList.set(intervalIdxMap.get(intervalIdx), pkValStart + fVal);
							 
						}
						
						if(!tuplesPerIntervalCovered.containsKey(selectedInterval)) {
							tuplesPerIntervalCovered.put(selectedInterval, 0L);
						}
						
						
						
						Long tupleSum = 0L;
						for(int di = 0; di < dfvector.size(); di++ ) {
							
							tupleSum += dfvector.getD().get(di) * dfvector.getF().get(di); 
							
						}
						
						tuplesPerIntervalCovered.put(selectedInterval, tuplesPerIntervalCovered.get(selectedInterval) + tupleSum );
						long val = this.allIntervalRegionValueMap.get(selectedInterval).longValue();
						// introduce check stmt for boundary check
						if(val != tuplesPerIntervalCovered.get(selectedInterval).longValue() ) {
							
							throw new RuntimeException("Interval values covered should match");
							
						}
						
						intervalToDFVectorMap.remove(selectedInterval);
						continue;
						
						
					}
				
				
				
				
				
				// From each group find maximum f that can taken from all groups
				Long minFofAll =null;
				for(List<Integer> groupIdx : appropriateDFMap.keySet()) {
					Long fVal = appropriateDFMap.get(groupIdx).get(1);
					if(minFofAll == null) {
						minFofAll = fVal;
					}
					else {
						if(minFofAll > fVal) {
							minFofAll = fVal;
						}
					}
					
				}
				
				
				 // find smallest d value among all groups
				Long minD = null;
				 List<Integer> currentGroup = null;
				 for(List<Integer> groupIdx : appropriateDFMap.keySet()) {
					
					 
					 if(minD == null) {
						 minD = appropriateDFMap.get(groupIdx).get(0);
						 currentGroup = groupIdx;
					 }
					 else if(minD > appropriateDFMap.get(groupIdx).get(0)) {
						 
						 minD = appropriateDFMap.get(groupIdx).get(0);
						 currentGroup = groupIdx;
						 
					 }
				 }
				 
				 
				 
				 
				 
				 
				 List<Long> appropriateDF = appropriateDFMap.get(currentGroup);
				 Long dVal = appropriateDF.get(0);
				 Long fVal = appropriateDF.get(1);
				 Long dCompleted = 0L;
				 boolean maxdDone = false;
				 
				 if(dVal < maxd) {
					 
					 // cover all supersets
					 // Remove all respective df value from  current group and supeset group
					 // if there is advance pkVal exercise that also
					 Set<List<Integer>> supersetGroups = superSetMap.get(currentGroup); 
					 List<List<Integer>> sortedSuperSetGroups = new ArrayList<>();
					 for(List<Integer> groupIdx : sortedGroupIdxs) {
						 
						 if(sortedSuperSetGroups.contains(groupIdx)) {
							 sortedSuperSetGroups.add(groupIdx);
						 }
						 
					 }
					 
					 
					 Map<FormalCondition, Map<Integer,List<Long>>> ccsToPKValDFMap = new HashMap<>();
					 
					 Long pkValStart = pkValBoundaryList.get(intervalIdxMap.get(intervalIdx));
					 
					 List<List<Integer>> groupsUsedEqualDValue = new ArrayList<>();					 
					 List<List<Integer>> groupsUsedLTdValue = new ArrayList<>(); // less than
					 List<Long> dUsedByLTgroups = new ArrayList<>();
					 
					 for(List<Integer> groupIdx : supersetGroups ) {
						 
						 if(!appropriateDFMap.containsKey(groupIdx)) {
							 continue;
						 }
						 
						 Long dValue  = appropriateDFMap.get(groupIdx).get(0);
						 String regionName = groupToRegionMap.get(groupIdx);
						 if(regionName == null) {
							 continue;
						 }
						 if(!this.varPKValDistribution.containsKey(regionName)) {
								this.varPKValDistribution.put(regionName, new HashMap<>());
						  }
						// can create issue
						Long val  = this.allIntervalisedRegionsMap.get(regionName);						
						Long noOFtuplesToBeCovered = dValue * minFofAll;						
						if(!tuplesPerRegionCovered.containsKey(regionName)) {
							tuplesPerRegionCovered.put(regionName, 0L);
						}						
						if(tuplesPerRegionCovered.get(regionName) + noOFtuplesToBeCovered > val) {
							// will lead to negative tuple 
							// add to future		
							break;			
						}
						else {
							
							if(dValue.longValue() == dVal) {
								
								
								for(int i=0; i < minFofAll; i++) {
									
									if(!this.varPKValDistribution.get(regionName).containsKey(dVal)) {
										this.varPKValDistribution.get(regionName).put(dVal, new ArrayList<>());
									}
									this.varPKValDistribution.get(regionName).get(dValue).add(pkValStart + i);
									
								}								
								tuplesPerRegionCovered.put(regionName, tuplesPerRegionCovered.get(regionName) + dValue * minFofAll );
								dCompleted += dValue;
								groupsUsedEqualDValue.add(groupIdx);
								
								
							}
							
							else if (dValue.longValue() > dVal) {
								
								long availableD = dValue - dCompleted;
								Long usedD = null;
								if(availableD + dCompleted < maxd) {
									// assign availabled
									
									usedD = availableD;	
									dCompleted += usedD;
									
								}
								else {
									// assign whatever left to current region(availableD + dCompleted >= maxd)
									
									 usedD = (maxd - dCompleted);									 
									 maxdDone = true;
									 
								}
								
								
								for(int i=0; i < minFofAll; i++) {
									
									if(!this.varPKValDistribution.get(regionName).containsKey(usedD)) {
										this.varPKValDistribution.get(regionName).put(usedD, new ArrayList<>());
									}
									this.varPKValDistribution.get(regionName).get(usedD).add(pkValStart + i);
									
								}
								
								tuplesPerRegionCovered.put(regionName, tuplesPerRegionCovered.get(regionName) + usedD * minFofAll );
								groupsUsedLTdValue.add(groupIdx);
								dUsedByLTgroups.add(usedD);
								
								
								
								
								if(maxdDone == true) {
									break;
								}
								
							}
							
							else {
								
								throw new RuntimeException("Doing something wrong, dValue should <= maxd");
							}
							
							
						}
						
						
						
						 
					 }
					 
					 // Future additon comes here					 
					 if(dCompleted.longValue() < maxd) {
						 
						 List<Long> dValues = new ArrayList<>();
						 List<Long> fValues = new ArrayList<>();
						 dValues.add(maxd - dCompleted.longValue());
						 fValues.add(minFofAll);
						 
						 DFvector dfvector = new DFvector(dValues, fValues);
						 
						 if(!futurePkValDFToAdd.containsKey(intervalIdx)) {
							 futurePkValDFToAdd.put(intervalIdx, new HashMap<>());
						 }
						 if(!futurePkValDFToAdd.get(intervalIdx).containsKey(dfvector)) {
							 futurePkValDFToAdd.get(intervalIdx).put(dfvector, new ArrayList<>());
						 }
						 futurePkValDFToAdd.get(intervalIdx).get(dfvector).add(pkValStart);
						 maxdDone =true;
						 
					 }
					 else {
						 
						 if(maxd > dCompleted.longValue()) {
							 throw new RuntimeException("Doing wrong ");
						 }
						 if(maxd == dCompleted && maxdDone == false) {
							 
							 throw new RuntimeException(" maxdDone is not getting updated");							 
						 }
						 
					 }
					 
					 
					 
					 
					 /*
					  *   Remove CCs df from CCToDFvector
					  * 
					  */
					 // remove (dVal,minFForALl) from all CCs
					 for(List<Integer> groupIdx : groupsUsedEqualDValue) {
						
						 List<FormalCondition> conditionList = groupMap.get(groupIdx);
						 for(FormalCondition condition : conditionList) {
							 
							 
							 DFvector dfvector = conditionToDFMap.get(condition);
							  List<Long>dValues = dfvector.getD();
							  Integer pos = null;
							  for(int i=0; i < dValues.size(); i++) {
								  
								  if(dValues.get(i).intValue() == dVal.intValue() ) {
									  pos = i;
									  break;
								  }
								  
							  }
							  
							  if(pos == null) {
								  continue;
							  }
							  
							  Long fValue = dfvector.getF().get(pos);
							  if(fValue.longValue() > minFofAll.longValue()) {
									 
									 dfvector.update(pos, fValue - minFofAll);
									 
						    	}  
								 else if(fValue.longValue() == minFofAll.longValue()) {
									 
									 dfvector.remove(pos);
									 
								 }
								 else {
									 
									 throw new RuntimeException(" Doing something wrong with minFofAll ");
									 
								 }
						 }
					 }
					 
					 for(int i=0; i < groupsUsedLTdValue.size(); i++) {
						 
						 List<FormalCondition> conditionList = groupMap.get(groupsUsedLTdValue.get(i));
						 Long dUsed = dUsedByLTgroups.get(i);
						 for(FormalCondition condition : conditionList) {
							 
							 
							 DFvector dfvector = conditionToDFMap.get(condition);
							  List<Long>dValues = dfvector.getD();
							  Integer pos = null;
							  for(int di=0; di < dValues.size(); di++) {
								  
								  if(dValues.get(di).longValue() == dUsed.longValue() ) {
									  pos = di;
									  break;
								  }
								  
							  }
							  
							  if(pos == null) {
								  
								  // if usedD not found go on 
								  continue;
							  }
							  
							  Long fValue = dfvector.getF().get(0);
							  if(fValue.intValue() > minFofAll.intValue()) {
									 
									 dfvector.update(pos, fValue - minFofAll);
									 
						      }  
							  else if(fValue.longValue() == minFofAll.intValue()) {
									 
									 dfvector.remove(pos);
									 
							  }
							 else {
									 
									 throw new RuntimeException(" Doing something wrong with minFofAll ");
									 
						      }
						 }
						 
						 
					 }
					 
					 
					 
					 pkValBoundaryList.set(intervalIdxMap.get(intervalIdx), pkValStart + minFofAll );
					 
					 
					 
					 
				 }
				 else if(dVal == maxd) {
					 
					 
					 // Assign tuples to all region
					 // remove df value from all overlapping CCs
					 Long pkValStart = pkValBoundaryList.get(intervalIdxMap.get(intervalIdx));
					 Set<List<Integer>> supersetGroups = superSetMap.get(currentGroup);
					 String regionName = groupToRegionMap.get(currentGroup);
					 
					 Long val  = this.allIntervalisedRegionsMap.get(regionName);
						
					 Long noOFtuplesToBeCovered = dVal * minFofAll;
						
					if(!tuplesPerRegionCovered.containsKey(regionName)) {
							tuplesPerRegionCovered.put(regionName, 0L);
					}
						
					if(tuplesPerRegionCovered.get(regionName) + noOFtuplesToBeCovered > val) {
							// will lead to negative tuple 
							// add to future
							// make maxdDone true
						 List<Long> dValues = new ArrayList<>();
						 List<Long> fValues = new ArrayList<>();
						 dValues.add(dVal);
						 fValues.add(minFofAll);
						 
						 DFvector dfvector = new DFvector(dValues, fValues);
						 
						 if(!futurePkValDFToAdd.containsKey(intervalIdx)) {
							 futurePkValDFToAdd.put(intervalIdx, new HashMap<>());
						 }
						 if(!futurePkValDFToAdd.get(intervalIdx).containsKey(dfvector)) {
							 futurePkValDFToAdd.get(intervalIdx).put(dfvector, new ArrayList<>());
						 }
						 futurePkValDFToAdd.get(intervalIdx).get(dfvector).add(pkValStart);
						
						 maxdDone = true;
							
					}
					else {
						
						
						if(!this.varPKValDistribution.containsKey(regionName)) {
							this.varPKValDistribution.put(regionName, new HashMap<>());
						}
						
						if(!this.varPKValDistribution.get(regionName).containsKey(dVal)) {
							this.varPKValDistribution.get(regionName).put(dVal, new ArrayList<>());
						}
					
						for(int i=0; i < minFofAll; i++) {
							
							this.varPKValDistribution.get(regionName).get(dVal).add(pkValStart + i);
							
						}
						tuplesPerRegionCovered.put(regionName, tuplesPerRegionCovered.get(regionName) + noOFtuplesToBeCovered);
						pkValBoundaryList.set(intervalIdxMap.get(intervalIdx), pkValStart + minFofAll );
						
						maxdDone = true;
						
						 Set<FormalCondition> doneFormalCondition = new HashSet<>();
						 for(List<Integer> groupIdx : supersetGroups) {
							 
							 if(!appropriateDFMap.containsKey(groupIdx)) {
								 continue;
							 }
							 Long dValue  = appropriateDFMap.get(groupIdx).get(0);
							 
							 if(dValue.longValue() == dVal.longValue()) {
								 
								  List<FormalCondition> conditionList = groupMap.get(groupIdx);
								  for(FormalCondition condition : conditionList) {
									  
									  if(doneFormalCondition.contains(condition)) {
										  continue;
									  }
									  else {
										  doneFormalCondition.add(condition);
									  }
									  
									  DFvector dfvector = conditionToDFMap.get(condition);
									  List<Long>dValues = dfvector.getD();
									  if(dValues.isEmpty()) {
										  continue;
									  }
									  Integer pos = null;
									  for(int i=0; i < dValues.size(); i++) {
										  
										  if(dValues.get(i).longValue() == dVal.longValue() ) {
											  pos = i;
											  break;
										  }
										  
									  }
									  
									 Long fValue = dfvector.getF().get(pos);
									 if(fValue.intValue() > minFofAll.intValue()) {
										 
										 dfvector.update(pos, fValue - minFofAll);
										 
									 }
									 else if(fValue.intValue() == minFofAll.intValue()) {
										 
										 dfvector.remove(pos);
										 
									 }
									 else {
										 
										 throw new RuntimeException(" Doing something wrong with minFofAll ");
										 
									 }
									  
									  
									  
									  
								  }
								 						 
								 
								 
							 }
							 else if(dValue > dVal) {
								 
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
				 
				 
				
				 
				 if(maxdDone) {
						
						if(maxf == minFofAll) {
							// remove df from interval
							// remove <maxd,f> from that interval df
							intervalToDFVectorMap.get(selectedInterval).remove(0);
							
							// if dfVector becomes empty then remove from intervalToDFVectorMap
							if(intervalToDFVectorMap.get(selectedInterval).isEmpty()) {
								
								intervalToDFVectorMap.remove(selectedInterval);
								
							}
							
							if(!tuplesPerIntervalCovered.containsKey(selectedInterval)) {
								tuplesPerIntervalCovered.put(selectedInterval, 0L);
							}
							Long val = this.allIntervalRegionValueMap.get(selectedInterval);
							if(tuplesPerIntervalCovered.get(selectedInterval) + maxd*minFofAll > val ) {
								System.out.print("Doing wrong");
							}
							else {
								tuplesPerIntervalCovered.put(selectedInterval,tuplesPerIntervalCovered.get(selectedInterval) + maxd*minFofAll );
							}
							
						}
						else {
							
							if(!tuplesPerIntervalCovered.containsKey(selectedInterval)) {
								tuplesPerIntervalCovered.put(selectedInterval, 0L);
							}
							Long val = this.allIntervalRegionValueMap.get(selectedInterval);
							if(tuplesPerIntervalCovered.get(selectedInterval) + maxd*minFofAll > val ) {
								System.out.print("Doing wrong");
							}
							else {
								tuplesPerIntervalCovered.put(selectedInterval, tuplesPerIntervalCovered.get(selectedInterval) + maxd*minFofAll );
							}
							
							intervalToDFVectorMap.get(selectedInterval).update(0, maxf - minFofAll);
							
						}
						
					}
			
				 
			
			
    		
    	}
    	
    	
    	
    	
    	
    	// now its time for future addition
    	
    	

		for(Integer intervalIdx : futurePkValDFToAdd.keySet()) {
			
			List<String> regionList = new ArrayList<>();
			Long tupleC = 0L;
			for (DFvector dfvector  : futurePkValDFToAdd.get(intervalIdx).keySet() ) {
	  			  
			  	tupleC += dfvector.getD().get(0) * dfvector.getF().get(0) * futurePkValDFToAdd.get(intervalIdx).get(dfvector).size();
			}
			
		
			
			
			for(String region : this.allIntervalisedRegionsMap.keySet()) {
				
				if(!region.contains(fkey)) {
					continue;
				}
				if(!region.contains("var" + cliqueIdx)) {
					continue;
				}
				
				if(Integer.parseInt(region.split("interval_")[1]) ==  intervalIdx  ) {
					regionList.add(region);
				}
			}
			
			List<Long> filledTupleList = new ArrayList<>();
			List<Long> actualTupleCount = new ArrayList<>();
			List<Long> fillingTuples = new ArrayList<>();
			List<Long> copyOfActualTupleCount = new ArrayList<>();
			List<String> copyOfRegions = new ArrayList<>();
			
			for(String region :  regionList) {
				copyOfRegions.add(region);
				Long tupleCount = 0l;
				if(!this.varPKValDistribution.containsKey(region)) {
					tupleCount = 0l;
				}
				else {
					for(Long di : this.varPKValDistribution.get(region).keySet()) {
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
			for(int ci=0; ci < actualTupleCount.size(); ci++) {
				
				sum1 +=  actualTupleCount.get(ci);
				sum2 += filledTupleList.get(ci);
				
			}
			
			if((sum1-sum2) != tupleC.longValue()) {
				throw new RuntimeException("Above code is wrong");
			}
			
			Long addedTupleCount = 0L;
			int currentRegIdx = 0;
			List<DFvector> dfvectorList = new ArrayList<>(futurePkValDFToAdd.get(intervalIdx).keySet());
			while(!dfvectorList.isEmpty()) {
				DFvector dfvector = dfvectorList.get(0);
				
				if(dfvector.isEmpty()) {
					dfvectorList.remove(0);
					continue;
				}
				Long dVal = dfvector.getD().get(0);
				Long fVal = dfvector.getF().get(0);
				List<Long> pkValList = futurePkValDFToAdd.get(intervalIdx).get(dfvector);
			
				
				while(!pkValList.isEmpty()) {
					
					Long pkStart = pkValList.get(0);	
					
					long leftCount = actualTupleCount.get(0) - filledTupleList.get(0);
					
					if(leftCount < 0) {
						throw new RuntimeException("Wrong implementation");
					}
					
					
					if(leftCount >= dVal * fVal) {
						long tupleCheck = 0L;
						before = getTupleCount(regionList.get(0));
						for(int fi=0; fi < fVal ;fi++) {
							if(!this.varPKValDistribution.containsKey(regionList.get(0))) {
								this.varPKValDistribution.put(regionList.get(0), new HashMap<>());
							}
							
							if(!this.varPKValDistribution.get(regionList.get(0)).containsKey(dVal)) {
								this.varPKValDistribution.get(regionList.get(0)).put(dVal, new ArrayList<>() );
							}
							this.varPKValDistribution.get(regionList.get(0)).get(dVal).add(pkStart + fi);
							tupleCheck += dVal;
						}
						after= getTupleCount(regionList.get(0));
						if(tupleCheck != dVal * fVal) {
							throw new RuntimeException("Prob;lem");
						}
						
						if(before + dVal * fVal != after) {
							throw new RuntimeException("Prob;lem");
						}
						
						
						
						
						addedTupleCount += dVal * fVal;
						filledTupleList.set(0, filledTupleList.get(0) + dVal * fVal);
						fillingTuples.set(currentRegIdx, fillingTuples.get(currentRegIdx) +  dVal * fVal);
						
						if(leftCount == dVal * fVal) {
							
							// region is finised
							// time for next region
							regionList.remove(0);
							actualTupleCount.remove(0);
							filledTupleList.remove(0);
							currentRegIdx++;
							
							if(regionList.isEmpty()) {
								//current pkVal is finished
								pkValList.remove(0);
								dfvectorList.remove(0);
							}
							
							continue;
						}
						
						//current pkVal is finished
						pkValList.remove(0);
						dfvectorList.remove(0);
						
					}
					
					else if (leftCount >= dVal) {

						Long newf = leftCount/dVal;
						fVal = fVal - newf;
						long tupleCheck=0L;
						before = getTupleCount(regionList.get(0));
						for(int fi=0; fi < newf ;fi++) {
							if(!this.varPKValDistribution.containsKey(regionList.get(0))) {
								this.varPKValDistribution.put(regionList.get(0), new HashMap<>());
							}
							
							if(!this.varPKValDistribution.get(regionList.get(0)).containsKey(dVal)) {
								this.varPKValDistribution.get(regionList.get(0)).put(dVal, new ArrayList<>() );
							}
							this.varPKValDistribution.get(regionList.get(0)).get(dVal).add(pkStart + fi);
							tupleCheck += dVal;
						}
						after = getTupleCount(regionList.get(0));
						if(tupleCheck != dVal * newf) {
							throw new RuntimeException("Prob;lem");
						}
						if(before + dVal * newf != after) {
							throw new RuntimeException("Prob;lem");
						}
						fillingTuples.set(currentRegIdx, fillingTuples.get(currentRegIdx) + dVal * newf);
						if(leftCount == dVal * newf) {
							regionList.remove(0);
							actualTupleCount.remove(0);
							filledTupleList.remove(0);
							currentRegIdx++;
							if(regionList.isEmpty()) {
								//current pkVal is finished
								pkValList.remove(0);
								dfvectorList.remove(0);
							}
							
						}
						
					
						
					}
					else {
						
						// leftCount < dVal
						fVal = fVal - 1;
						
						
						// completing current region and invoking next region
						long tupleCheck = 0;
						before = getTupleCount(regionList.get(0));
						for(int fi=0; fi < 1 ;fi++) {
							if(!this.varPKValDistribution.containsKey(regionList.get(0))) {
								this.varPKValDistribution.put(regionList.get(0), new HashMap<>());
							}
							
							if(!this.varPKValDistribution.get(regionList.get(0)).containsKey(leftCount)) {
								this.varPKValDistribution.get(regionList.get(0)).put(leftCount, new ArrayList<>() );
							}
							this.varPKValDistribution.get(regionList.get(0)).get(leftCount).add(pkStart + fi);
							tupleCheck += leftCount;
						}
						after = getTupleCount(regionList.get(0));
						if(tupleCheck != leftCount ) {
							throw new RuntimeException("Prob;lem");
						}
						if(before + leftCount != after) {
							throw new RuntimeException("Prob;lem");
						}
						fillingTuples.set(currentRegIdx, fillingTuples.get(currentRegIdx) + leftCount);
						Long tempD =  (dVal - leftCount);
						
						regionList.remove(0);
						actualTupleCount.remove(0);
						filledTupleList.remove(0);
						currentRegIdx++;
						if(regionList.isEmpty()) {
							//current pkVal is finished
							pkValList.remove(0);
							dfvectorList.remove(0);
							break;
						}
						
						while(true) {
							
							
							leftCount = actualTupleCount.get(0) - filledTupleList.get(0);
							if(leftCount == 0) {
								regionList.remove(0);
								actualTupleCount.remove(0);
								filledTupleList.remove(0);
								currentRegIdx++;
								if(regionList.isEmpty()) {
									//current pkVal is finished
									pkValList.remove(0);
									dfvectorList.remove(0);
									break;
									
								}
								break;
							}
							
							
							if(tempD >= leftCount) {
								tupleCheck = 0L;
								before = getTupleCount(regionList.get(0));
								for(int fi=0; fi < 1 ;fi++) {
									if(!this.varPKValDistribution.containsKey(regionList.get(0))) {
										this.varPKValDistribution.put(regionList.get(0), new HashMap<>());
									}
									
									if(!this.varPKValDistribution.get(regionList.get(0)).containsKey(leftCount)) {
										this.varPKValDistribution.get(regionList.get(0)).put(leftCount, new ArrayList<>() );
									}
									this.varPKValDistribution.get(regionList.get(0)).get(leftCount).add(pkStart + fi);
									tupleCheck +=  leftCount;;
								}
								after = getTupleCount(regionList.get(0));
								if(tupleCheck != leftCount) {
									throw new RuntimeException("Prob;lem");
								}
								if(before + leftCount != after) {
									throw new RuntimeException("Prob;lem");
								}
								
								fillingTuples.set(currentRegIdx, fillingTuples.get(currentRegIdx) + leftCount);
								regionList.remove(0);
								actualTupleCount.remove(0);
								filledTupleList.remove(0);
								currentRegIdx++;
								if(regionList.isEmpty()) {
									//current pkVal is finished
									pkValList.remove(0);
									dfvectorList.remove(0);
									break;
									
								}
								
								
								
							}
							
							else {
								
								tupleCheck =0;
								before = getTupleCount(regionList.get(0));
								for(int fi=0; fi < 1 ;fi++) {
									if(!this.varPKValDistribution.containsKey(regionList.get(0))) {
										this.varPKValDistribution.put(regionList.get(0), new HashMap<>());
									}
									
									if(!this.varPKValDistribution.get(regionList.get(0)).containsKey(tempD)) {
										this.varPKValDistribution.get(regionList.get(0)).put(tempD, new ArrayList<>() );
									}
									this.varPKValDistribution.get(regionList.get(0)).get(tempD).add(pkStart + fi);
									tupleCheck += tempD;
								}
								after = getTupleCount(regionList.get(0));
								if(tupleCheck != tempD) {
									throw new RuntimeException("Prob;lem");
								}
								if(before + tempD != after) {
									throw new RuntimeException("Prob;lem");
								}
								
								
								filledTupleList.set(0, filledTupleList.get(0) + tempD);
								fillingTuples.set(currentRegIdx, fillingTuples.get(currentRegIdx) + tempD);
								break;
							}
							
							
							
						}
						
						
						
						if(fVal == 0) {
							
							if(!pkValList.isEmpty()) {
								pkValList.remove(0);
							}
							if(!dfvectorList.isEmpty()) {
								dfvectorList.remove(0);
							}
							
							
						}
						
						
					
						
					}
					
					
					
					
					
					
				}
				

				
			
			}
			
			for(String regionName : copyOfRegions) {
				Long val = this.allIntervalisedRegionsMap.get(regionName);
	    		
	    		Long tupleCount = 0L;
	    		for( Long dVal : this.varPKValDistribution.get(regionName).keySet() ) {
	    			
	    			tupleCount += dVal * this.varPKValDistribution.get(regionName).get(dVal).size();
	    			
	    		}
	    		
	    		
	    		if(tupleCount.longValue() != val.longValue()) {
	    			
	    			throw new RuntimeException("Problem here");
	    		}
				
			}

			System.out.print("");
			
		}
			
    	
    	
    	
    	
    	
    	
    }
	
	
	public Long getTupleCount(String regionName) {
		
		Long tupleCount = 0L;
		if(!this.varPKValDistribution.containsKey(regionName)) {
			return 0L;
		}
		for( Long dVal : this.varPKValDistribution.get(regionName).keySet() ) {
			
			tupleCount += dVal * this.varPKValDistribution.get(regionName).get(dVal).size();
			
		}
		return tupleCount;
		
	}
    



	private boolean findAppropriateDF(List<Long> appropriateDF, List<DFvector> dfVectorList, Long maxd, Long maxf) {
		// TODO Auto-generated method stub
		
		// first find common d values in all dfVectorList<>
		/*
		List<Long> commonDValuesSet = new ArrayList<>(dfVectorList.get(0).getD());
		for(int i=1; i < dfVectorList.size(); i++) {
			
			commonDValuesSet.retainAll(dfVectorList.get(i).getD());
		}
		
		// decreasing order sort
		Collections.sort(commonDValuesSet, Collections.reverseOrder());
		// find d closest to maxd in commonDValuesSet
		
		// 10 -> [9 or 11] give it to 11 Since no way 11 can come in maxd
		
		if(commonDValuesSet.isEmpty()) {
			return false;
			//throw new RuntimeException(" Was not expecting this, think something to solve this");
		}
		
		int di=0;
		boolean foundFlag = false;
		for(; di <  commonDValuesSet.size(); di++) {
			
			if(commonDValuesSet.get(di) == maxd) {
				// found maxd
				foundFlag = true;
				break;
			}
		    else if(commonDValuesSet.get(di) < maxd) {
				break;
			}
			
		}
		
		Long appropriateD = null;
		if(di == 0) {
			// no dValues is more than maxd
			// choose max(dValues)
			appropriateD =  commonDValuesSet.get(0);
			
		}
		else if(foundFlag) {
			appropriateD = commonDValuesSet.get(di);
		
		}
		else {
			appropriateD = commonDValuesSet.get(di-1);
			
		}
		
		// find appropriateF
		Long appropriateF = null;
		
		for(int i=0; i < dfVectorList.size(); i++) {
			List<Long> dValues = dfVectorList.get(i).getD();
			List<Long> fValues = dfVectorList.get(i).getF();
			for(di=0; di < dValues.size(); di++) {
				
				if(dValues.get(di) == appropriateD) {
					if(appropriateF == null) {
						appropriateF = fValues.get(di);
						
					}
					else if(appropriateF > fValues.get(di)) {
						appropriateF = fValues.get(di);
						
					}
					break;
					
				}
				
			}
		}
		
		*/
		
		
		Long appropriateD=null;
		for(int i=0; i < dfVectorList.size(); i++) {
			
			if(appropriateD == null) {
				
				appropriateD = dfVectorList.get(i).getD().get(0);
				
			}
			else {
				
				if(appropriateD > dfVectorList.get(i).getD().get(0)) {
					appropriateD = dfVectorList.get(i).getD().get(0);
				}
				
			}
			
			
		}
		
		Long appropriateF = null;
		for(int i=0; i < dfVectorList.size(); i++) {
			List<Long> dValues = dfVectorList.get(i).getD();
			List<Long> fValues = dfVectorList.get(i).getF();
			Long sumf = 0L;
			for(int di=0; di < dValues.size(); di++ ) {
				
				if(dValues.get(di) < appropriateD) {
					break;
				}
				else {
					
					sumf += fValues.get(di);
				}
				
			}
			if(appropriateF == null) {
				appropriateF = sumf;
			}
			else {
				
				if(appropriateF > sumf) {
					sumf = appropriateF;
				}
				
			}
			
		}
		
		
		
		if(appropriateF > maxf) {
			appropriateF = maxf;
		}
		
		appropriateDF.add(appropriateD);
		appropriateDF.add(appropriateF);
		
		return  true;
		
		
		
		
	}
	


	private int checkIntersection(Map<String, Set<Integer>> map, Map<String, Set<Integer>> map2) {
		
		
		if(map.keySet().size() != map2.keySet().size()) {
			System.out.print("");
		}
		
		List<Integer> allIntersectionVals = new ArrayList<>();
		for(String column : map.keySet()) {
			
			Set<Integer> set =  new HashSet<>(map.get(column));
			Set<Integer> set2 = new HashSet<>(map2.get(column));
			
			if(set.equals(set2)) {
				allIntersectionVals.add(0);
				
			}
			else {
				Set<Integer> testSet =  new HashSet<>(set);
				testSet.retainAll(set2);
				if(!testSet.isEmpty()) {
					allIntersectionVals.add(1);
					
				}
				else {
					allIntersectionVals.add(-1);
					
				}
			}
			
			
			
			System.out.print("");
			
			/*
			
			
			
			testSet =  new HashSet<>(set2);
			testSet.removeAll(set);
			if(testSet.removeAll(set)) {
				allIntersectionVals.add(-1);
				break;
			}
			else {
			*/
			
		}
		
		return 0;
	}

	private void findAssociatedVal(List<String> sortedBorrowedAttr, List<FormalCondition> conditions,
			Map<String, Set<Integer>> smallbfc) {
		// TODO Auto-generated method stub
		
		for (FormalCondition condition : conditions) {
			
			if (condition instanceof FormalConditionComposite) {
				findAssociatedVal(sortedBorrowedAttr, ((FormalConditionComposite) condition).getConditionList(), smallbfc);
			}
			else  if (condition instanceof FormalConditionSimpleInt){
				
				FormalConditionSimpleInt formalConditionSimpleInt = (FormalConditionSimpleInt) condition;
                String columnName = formalConditionSimpleInt.getColumnname();
                int a = formalConditionSimpleInt.getValue();
                if(!sortedBorrowedAttr.contains(columnName)) {
                	continue;
                }
                Set<Integer> integerSet = smallbfc.get(columnName);
                IntList intervals = this.bucketFloorsByColumns.get(columnName);
                switch (formalConditionSimpleInt.getSymbol()) {
                    case LT:{
                    	
                    	for(int i=0; i < intervals.size(); i++) {
                    		if(intervals.get(i) < a) {
                    			integerSet.add(a);
                    		}
                    	}
                    	
                    	break;
                    }
                        
                        
                    case LE:{
                    	
                    	for(int i=0; i < intervals.size(); i++) {
                    		if(intervals.get(i) <= a) {
                    			integerSet.add(a);
                    		}
                    	}
                    	
                    	break;
                    }
                    case GT:{
                    	
                    	for(int i=0; i < intervals.size(); i++) {
                    		if(intervals.get(i) > a) {
                    			integerSet.add(a);
                    		}
                    	}
                    	
                    	break;
                    }
                    case GE:{
                    	
                    	for(int i=0; i < intervals.size(); i++) {
                    		if(intervals.get(i) >= a) {
                    			integerSet.add(a);
                    		}
                    	}
                    	
                    	break;
                    }
                    case EQ:{
                    	
                    	for(int i=0; i < intervals.size(); i++) {
                    		if(intervals.get(i) == a) {
                    			integerSet.add(a);
                    		}
                    	}
                    	
                    	break;
                    }
                    default:
                        throw new RuntimeException("Unrecognized Symbol " + formalConditionSimpleInt.getSymbol());
				
			}
		}
		else if (condition instanceof FormalConditionBaseAggregate) {
            
		} 
		else
            throw new RuntimeException("Unrecognized type of FormalCondition " + condition.getClass());
			
		}
		
		
	}

	

	public void solveView1(List<FormalCondition> conditions, List<Region> conditionRegions, FormalCondition consistencyConstraints[], ConsistencyMakerType consistencyMakerType, Map<String, List<Region>> aggregateColumnsToSingleSplitPointRegions) {
    	
    	StopWatch formulationPlusSolvingSW = new StopWatch("LP-Solving (meging cliques not included)" + viewname);
        beginLPFormulation();
        List<LinkedList<VariableValuePair>> cliqueIdxToVarValuesList = formulateAndSolve(conditions, conditionRegions, consistencyConstraints, consistencyMakerType);
        finishSolving();
        solverStats.millisToSolve = formulationPlusSolvingSW.getTimeAndDispose();
        return ;
	}
    
    public ViewSolutionWithSolverStats mergeCliques(List<LinkedList<VariableValuePair>> cliqueIdxToVarValuesList) {
		
    	ViewSolution viewSolution = mergeCliqueSolutions(cliqueIdxToVarValuesList);
    	finishPostSolving();
    	return new ViewSolutionWithSolverStats(viewSolution, solverStats);
	}
    
    private ViewSolutionInMemory mergeCliqueSolutionsRegionwise(List<LinkedList<VariableValuePair>> cliqueIdxToVarValuesList) {

        IntList mergedColIndxs = new IntArrayList();
        List<ValueCombination> mergedValueCombinations = new ArrayList<>();
        //S
        List<VariableValuePair>mergedVarValuePairs=new ArrayList();
        //arasuCliquesAsColIndxs --list of list of columns index (only those present in some constraint) in a subview.  
        mergedColIndxs.addAll(arasuCliquesAsColIndxs.get(0));
        //Instantiating variables of first clique
        for (VariableValuePair varValuePair : cliqueIdxToVarValuesList.get(0)) {
            mergedVarValuePairs.add(varValuePair);
        }
        //Shadab, mergeWithAlignmentRegionwise deletes the regions from arasuCliquesAsColIndxs. So if regions are needed post merging too, then make a deep copy in the function.
        for (int i = 1; i < cliqueCount; i++) {
            mergeWithAlignmentRegionwise(mergedColIndxs, mergedVarValuePairs, arasuCliquesAsColIndxs.get(i), cliqueIdxToVarValuesList.get(i));
        }
        System.gc();
        
        
        //THIS CALL WAS ADDED BY SHADAB BUT TAKES TOOOOOO LONG TO COMPUTE, SO COMMENTED
        // added by Shadab for disjoint check
        //areDisjointCheck(mergedVarValuePairs);
        
        
        /*
        for(VariableValuePair var:mergedVarValuePairs) {
        	IntList columnValues = getFloorInstantiation(var.variable);
        	
        	ValueCombination valueCombination = new ValueCombination(columnValues, var.rowcount);
        	mergedValueCombinations.add(valueCombination);
        	var.variable=getExpandedRegion(var.variable);
        	
        	
        }
        for (ListIterator<ValueCombination> iter = mergedValueCombinations.listIterator(); iter.hasNext();) {
            ValueCombination valueCombination = iter.next();
            valueCombination = getReverseMappedValueCombination(valueCombination);
            valueCombination = getExpandedValueCombination(valueCombination);
            iter.set(valueCombination);
        }
        */
        // Shadab code
        for(VariableValuePair var:mergedVarValuePairs) {
            
            var.variable=getReverseMappedRegion(var.variable);
            var.variable=getExpandedRegion(var.variable);
            IntList columnValues = getFloorInstantiation(var.variable);
            ValueCombination valueCombination = new ValueCombination(columnValues, var.rowcount);//if you wish to get the valuecombination too
            mergedValueCombinations.add(valueCombination);
           
        }
        
       

        ViewSolutionInMemory viewSolutionInMemory = new ViewSolutionInMemory(mergedValueCombinations.size(),mergedVarValuePairs);
        for (ValueCombination mergedValueCombination : mergedValueCombinations) {
            viewSolutionInMemory.addValueCombination(mergedValueCombination);
        }
      // ViewSolutionRegion viewSolution=new ViewSolutionRegion(viewSolutionInMemory,mergedVarValuePairs);

        return viewSolutionInMemory;
       //commented by shadab return viewSolutionInMemory;
    }

    private void mergeWithAlignmentRegionwise(IntList lhsColIndxs,List<VariableValuePair> lhsVarValuePairs,
    		IntList rhsColIndxs, LinkedList<VariableValuePair> rhsVarValuePairs) {
    		for(VariableValuePair var: lhsVarValuePairs) {
    		if (var.rowcount==0)
    		System.out.print("sd");
    		}
    		for(VariableValuePair var: rhsVarValuePairs) {
    		if (var.rowcount==0)
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
    		// List<RegionSummary>mergedRegionsSummary=new ArrayList<>();
    		//List<RegionSummary> mergedSum= new ArrayList<>();// new table after merging
    		for (VariableValuePair lhsVarValue : lhsVarValuePairs) {
    		Region lhsRegion = lhsVarValue.variable;
    		long lhsRowcount = lhsVarValue.rowcount;
    		List<VariableValuePair>compatitbleRegions=new ArrayList<>();
    		List<VariableValuePair>mergedVars=new ArrayList<>();
    		boolean check = false;
    		count++;
    		int ind = 0;
    		for (ListIterator<VariableValuePair> rhsIter = rhsVarValuePairs.listIterator();rhsIter.hasNext();) {
    		VariableValuePair rhsVarValuePair = rhsIter.next();
    		Region rhsVariable = rhsVarValuePair.variable;
    		long rhsRowcount = rhsVarValuePair.rowcount;
    		ind++;
    		//if (checkCompatibleRegions(posInLHS, lhsRegion, posInRHS, rhsVariable)) {// if rhsregion is compatible
    		//check = true;

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
    		if(mergedTemp.isEmpty())
    		continue;
    		else {
    		VariableValuePair mergedVar=new VariableValuePair(mergedTemp,0);
    		compatitbleRegions.add(rhsVarValuePair);
    		mergedVars.add(mergedVar);
    		check=true;
    		}
    		}
    		// do the rowcount
    		// if (lhsRowcount <= rhsRowcount) {
    		//
    		//
    		// VariableValuePair mergedVariable = new VariableValuePair(mergedTemp, lhsRowcount);
    		// mergedVarValuePairs.add(mergedVariable);
    		//
    		// // lhsValueCombination.reduceRowcount(lhsRowcount);
    		// lhsVarValue.rowcount = 0;
    		// rhsVarValuePair.rowcount -= lhsRowcount;
    		// if (rhsVarValuePair.rowcount == 0) {
    		// rhsIter.remove();// removes this region from RHSvar
    		// }
    		// break;
    		// } else {
    		// VariableValuePair mergedVariable = new VariableValuePair(mergedTemp, rhsRowcount);
    		// mergedVarValuePairs.add(mergedVariable);
    		// lhsVarValue.rowcount -= rhsRowcount;
    		// lhsRowcount = lhsVarValue.rowcount;
    		// rhsVarValuePair.rowcount = 0;
    		// rhsIter.remove();
    		// }
    		//
    		//
    		//
    		// }
    		// if (!check) {
    		// // System.out.println("failed");
    		// throw new RuntimeException("You Failed!!!!!Couldn't find a region in rhs for lhs region:" + lhsRegion);
    		// }
    		if(compatitbleRegions.size()==0)
    		throw new RuntimeException("You Failed!!!!!Couldn't find a region in rhs for lhs region:" + lhsRegion);
    		
    		mergeUniform(lhsVarValue,compatitbleRegions,mergedVars);
    		mergedVarValuePairs.addAll(mergedVars);
    		for (ListIterator<VariableValuePair> rhsIter = rhsVarValuePairs.listIterator(); rhsIter.hasNext();) {
    		if(rhsIter.next().rowcount==0)
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
    		for (ListIterator<VariableValuePair> Iter = mergedVarValuePairs.listIterator();Iter.hasNext();) {
    		VariableValuePair var=Iter.next();
    		if (var.rowcount == 0)
    		Iter.remove();
    		if(var.rowcount<0) {
    			System.out.println("vvp ng" + var.rowcount);
    		}
    		
    		}
    		// Updating targetColIndxs
    		lhsColIndxs.clear();
    		lhsColIndxs.addAll(mergedColIndxsList);

    		lhsVarValuePairs.clear();
    		lhsVarValuePairs.addAll(mergedVarValuePairs);

    		}
    		private void mergeUniform(VariableValuePair lhsVarValue,
    		List<VariableValuePair> compatitbleRegions, List<VariableValuePair> mergedVars) {
    		Long totRowcount=0L;
    		Long lhsRowcount=lhsVarValue.rowcount;
    		for(VariableValuePair var:compatitbleRegions) {
    		totRowcount+=var.rowcount;
    		}
    		if(lhsRowcount > totRowcount) {
    			System.out.print("tot" + lhsRowcount + " : "  + totRowcount);
    		}
    		for(int i=0;i<compatitbleRegions.size()-1;i++) {
    		VariableValuePair rhsvar=compatitbleRegions.get(i);
    		VariableValuePair mergedVar=mergedVars.get(i);
    		double ratio=rhsvar.rowcount/(double)totRowcount;
    		
    		Long card= Math.min(Math.round(ratio*lhsRowcount), lhsVarValue.rowcount);
    		
    		if(card < 0)
    		{
    			System.out.println("card " + card + "ratio :" + ratio + " lhsCount : " + lhsRowcount );
    		}
    		
    		if(card > rhsvar.rowcount)
    		{
    			System.out.println("card > rhsvar.rowcount" + card +  " : " + rhsvar.rowcount);
    		}
    		mergedVar.rowcount=card;
    		if(mergedVar.rowcount < 0)
    		{
    			System.out.println("mergedVar " + mergedVar.rowcount + "card :" + card + "ratio :" + ratio + " lhsCount : " + lhsRowcount );
    		}
    		lhsVarValue.rowcount-=card;
    		rhsvar.rowcount-=card;
    		if(lhsVarValue.rowcount == 0) {
    			//System.out.println("lhsVarValue.rowcount : " +  lhsVarValue.rowcount);
    			return;
    		}
    		//divideCard(var,card);
    		}
    		
    		VariableValuePair lastmerged=mergedVars.get(compatitbleRegions.size()-1);
    		lastmerged.rowcount=lhsVarValue.rowcount;
    		if(lastmerged.rowcount < 0) {
    			System.out.println("lastmerged.rowcount < 0" + lastmerged.rowcount);
    		}
    		VariableValuePair lastrhs=compatitbleRegions.get(compatitbleRegions.size()-1);
    		lastrhs.rowcount-=lhsVarValue.rowcount;
    		lhsVarValue.rowcount=0;
    		
    		if(lastrhs.rowcount<0L)
    		throw new RuntimeException("check mergeuniform");
    		
    		
    		}
    private static boolean checkCompatibleRegions(IntList posInLHS, Region lhsRegion, IntList posInRHS, Region rhsRegion) {
    	//returns true if two regions are consistent. 
    		
		for (IntIterator iterLHS = posInLHS.iterator(), iterRHS = posInRHS.iterator(); iterLHS.hasNext();) {
			int posL = iterLHS.nextInt();
            int posR = iterRHS.nextInt();
            Bucket lB=new Bucket();
    		Bucket rB=new Bucket();

			for (BucketStructure bs : lhsRegion.getAll()) 
				lB=Bucket.union(lB,bs.at(posL));
			//lhsUnion.add(lB);
			for (BucketStructure bs : rhsRegion.getAll()) 
				rB=Bucket.union(rB,bs.at(posR));
			//lhsUnion.add(rB);
			if(!lB.isEqual(rB))
				return false;
		}
		return true;
	}
    
    private static boolean isCompatibleBS(IntList posInLHS, BucketStructure lhsBs, IntList posInRHS, BucketStructure rhsBs) {
    	//returns true if two BS's are consistent wrt common attribute 
    	
        for (IntIterator iterLHS = posInLHS.iterator(), iterRHS = posInRHS.iterator(); iterLHS.hasNext();) {
            int posL = iterLHS.nextInt();
            int posR = iterRHS.nextInt();
            Bucket lB=lhsBs.at(posL);
            Bucket rB=rhsBs.at(posR);
          //  if (!lhsBs.at(posL).equals(rhsBs.at(posR))
            if (Bucket.getIntersection(lB, rB)==null)
            	return false;
            
            //if (!RhsBs.at(posR).contains(lhsColValues.getInt(posL)))
            //    return false;
        }
//        for (IntIterator iterLHS = posInLHS.iterator(), iterRHS = posInRHS.iterator(); iterLHS.hasNext();) {
//            int posL = iterLHS.nextInt();
//            int posR = iterRHS.nextInt();
//            Bucket lVal=lhsBs.at(posL);
//            Bucket rVal=rhsBs.at(posR);
//            if (!lVal.isEqual(rVal)){
//            	//throw new RuntimeException("Buckets intersect but not complete overlap");
//            	System.out.println("Gotcha");
//            }
//        }
        return true;
    }

    

		    private List<LinkedList<VariableValuePair>> subhoFormulateAndSolve(List<FormalCondition> conditions, List<Region> conditionRegions, FormalCondition consistencyConstraints[]
		    		, ConsistencyMakerType consistencyMakerType) {
		    	
		    	// TODO : remove IntExpr with their original String names in projection code
		 	
		    	

		    	
		    	StopWatch onlyReductionSW = new StopWatch("LP-OnlyReduction" + viewname);
		    	
		        //STEP 1: For each clique find set of applicable conditions and call variable reduction
		        
		    	List<Region> subhoCRegions = new ArrayList();
		
		        for (int i = 0; i < cliqueCount; i++) {
		
		            LongList bvalues = new LongArrayList();
		            Set<String> clique = arasuCliques.get(i);   // set of columns
		            List<Region> cRegions = new ArrayList<>();
		            List<Pair<Integer, Boolean>> applicableConditions = new ArrayList<>();
		            for (int j = 0; j < conditions.size(); j++) {      
		            	FormalCondition curCondition = conditions.get(j);
		                Set<String> appearingCols = new HashSet<>();
		                getAppearingCols(appearingCols, curCondition);   // appearing columns will have columns appeared in current condition
		
		                if (clique.containsAll(appearingCols)) {
		                    cRegions.add(conditionRegions.get(j));
		                    bvalues.add(curCondition.getOutputCardinality());
		                    if (curCondition instanceof FormalConditionAggregate)
		                    	applicableConditions.add(new Pair<>(j ,true));
		                    else
		                    	applicableConditions.add(new Pair<>(j ,false));
		                } else if (curCondition instanceof FormalConditionAggregate) {
		                	removeAggregateCols(appearingCols, curCondition);
		                	if (clique.containsAll(appearingCols)) {
		                        cRegions.add(conditionRegions.get(j));
		                        bvalues.add(curCondition.getOutputCardinality());
		                        applicableConditions.add(new Pair<>(j ,false));
		                	}
		                }
		            }
		            applicableConditionsOnClique.add(applicableConditions);
		
		            //Adding extra cRegion for all 1's condition
		            Region allOnesCRegion = new Region();
		            BucketStructure subConditionBS = new BucketStructure();
		            for (int j = 0; j < allTrueBS.size(); j++) {
		                Bucket bucket = new Bucket();
		                for (int k = 0; k < allTrueBS.get(j).length; k++) {
		                    if (allTrueBS.get(j)[k]) {		// Is this check needed?
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
//								System.out.println("cons const no" + j);
								indexKeeperForConsistency.put(j, tempIndexForConsistency++);
								cRegions.add(conditionRegions.get(conditions.size() + j));
							}
						}

						mappedIndexOfConsistencyConstraint.add(indexKeeperForConsistency);
					}

		            
		///////////////// End dk
		//            DebugHelper.printInfo("Bachaaaao!");
		//            DebugHelper.printInfo(viewname + " " +clique + " " + cRegions);
		            
		            
		            subhoCRegions = cRegions;
		//            SUbho adds
		            
		//            While uncommenting, there is one more line
		            Reducer reducer = new Reducer(allTrueBS, cRegions);
		            
		           
		           
		            // Get maximum size of heap in bytes. The heap cannot grow beyond this size.// Any attempt will result in an OutOfMemoryException.
		//            long heapMaxSize = Runtime.getRuntime().maxMemory();
		
		            // Get amount of free memory within the heap in bytes. This size will increase // after garbage collection and decrease as new objects are created.
		            long heapFreeSize = Runtime.getRuntime().freeMemory();
		            long heapSize = Runtime.getRuntime().totalMemory();
		//            long memory2 = heapSize-heapFreeSize;
		            System.out.println("Memory after region partitioning1: "  + (heapSize-heapFreeSize)/(1024.0*1024.0*1024.0) + "GB");
		
		                   
		            Map<IntList, Region> P = reducer.getMinPartition();
		
		            //Added by Anupam for Skew Mimicking
		            reducer.refineRegionsforSkewMimicking();
		
		            //Using varIds instead of old variable regions
		            List<Region> oldVarList = new ArrayList<>();	// List of regions corresponding to below labels
		            List<IntList> conditionIdxsList = new ArrayList<>();	// List of labels
		            reducer.getVarsAndConditionsSimplified(oldVarList, conditionIdxsList);
		
		            Partition cliqueP = new Partition(new ArrayList<>(oldVarList));
		            cliqueIdxtoPList.add(cliqueP);
		
		            cliqueIdxtoPSimplifiedList.add(conditionIdxsList);
		        }
		        long heapSize = Runtime.getRuntime().totalMemory();
		
		        // Get amount of free memory within the heap in bytes. This size will increase // after garbage collection and decrease as new objects are created.
		        long heapFreeSize = Runtime.getRuntime().freeMemory();
		
		        heapSize = Runtime.getRuntime().totalMemory();
		
		        long memory2 = heapSize-heapFreeSize;
		        System.out.println("Memory after region partitioning2: "  + (heapSize-heapFreeSize)/(1024.0*1024.0*1024.0) + "GB");
		
		        
		        /*
		         * Code for subhodeep for Finding regions satisfying set of CCs
		         *
		         */
		     
		        HashMap<String,List<String>> regionToCCMap = new HashMap<>();
		        for (int i = 0; i < cliqueCount; i++) {
		
		        	Set<String> clique = arasuCliques.get(i);
		
		        	Partition partition = cliqueIdxtoPList.get(i);
		
		        	for(int j=0; j < partition.size(); j++) {
		
		        		Region r = partition.at(j);
		        		regionToCCMap.put("View " + this.viewname + "_Clique" + i + "_Region" + j, new ArrayList<>());
		        		for(int c=0; c< conditions.size(); c++) {
		        			FormalCondition curCondition = conditions.get(c);
		        			Set<String> appearingCols = new HashSet<>();
		        			getAppearingCols(appearingCols, curCondition);
		        			if (clique.containsAll(appearingCols)) {
		
		        				if(checkCCSatifyRegion(r,appearingCols,curCondition)) {
		
		        					//System.out.println("Clique_" + i + "Region" + j + " -> " + " CC_" + c);
		        					regionToCCMap.get("View " + this.viewname + "_Clique" + i + "_Region" + j).add("CC" + c);
		        				}
		
		        			}
		        		}
		        	}
		        }
		        
		        heapSize = Runtime.getRuntime().totalMemory();
		        //        long heapSize = Runtime.getRuntime().totalMemory();
		
		        // Get amount of free memory within the heap in bytes. This size will increase // after garbage collection and decrease as new objects are created.
		        heapFreeSize = Runtime.getRuntime().freeMemory();
		
		        heapSize = Runtime.getRuntime().totalMemory();
		
		        memory2 = heapSize-heapFreeSize;
		        System.out.println("Memory after region partitioning3: "  + (heapSize-heapFreeSize)/(1024.0*1024.0*1024.0) + "GB");
		
		
		        
		        for(String region : regionToCCMap.keySet()) {
		        	//System.out.println(region + " ---> " + regionToCCMap.get(region));
		        }
		
		
		        
		        
		        onlyReductionSW.displayTimeAndDispose();
		
		        
		        if (consistencyMakerType == ConsistencyMakerType.BRUTEFORCE) {	// Further divide regions for consistency
			        for (int i = 0; i < cliqueCount; i++) {
			            for (int j = i + 1; j < cliqueCount; j++) {
			                IntList intersectingColIndices = getIntersectionColIndices(arasuCliques.get(i), arasuCliques.get(j));
			                if (intersectingColIndices.isEmpty()) {
			                    continue;
			                }
			                CliqueIntersectionInfo cliqueIntersectionInfo =
			                        replaceWithFreshVariablesToEnsureConsistency(cliqueIdxtoPList, cliqueIdxtoPSimplifiedList, i, j, intersectingColIndices);
			                cliqueIntersectionInfos.add(cliqueIntersectionInfo);
			            }
			        }
		        }
		
		        long varcountDR = 0;
		        for (int i = 0; i < cliqueCount; i++) {
		            varcountDR += cliqueIdxtoPList.get(i).getAll().size();
		        }
		        DebugHelper.printInfo("Number of variables after double reduction " + varcountDR);
		        
		        // Subho starts
		        
		        int cliqueIndex = 0;
		        
		        LongList bvalues = cliqueIdxtoConditionBValuesList.get(cliqueIndex);
		//    	regions
		    	List<IntList> regions = cliqueIdxtoPSimplifiedList.get(cliqueIndex);		// Partition is a list of regions corresponding to below labels
		    	
		        
		        int numRegions = regions.size();
		        int numCC = bvalues.size();
		        
		        double [][] x= new double[numCC][numRegions];
		
		//        Uncomment
		        for(int i=0;i<numCC;i++) {
		        	for(int j=0;j<regions.get(i).size();j++) {
		        		x[i][regions.get(i).get(j)] = 1;
		        	}
		        }
		        
		        
		        
		        
		        
		
		//        RealMatrix A = MatrixUtils.createRealMatrix(x);
		//        SingularValueDecomposition svd = new SingularValueDecomposition(A);
		//		if(svd.getRank()< numCC)
		//			return formAndSolveLP(consistencyMakerType, consistencyConstraints, conditions, aggregateColumnsToSingleSplitPointRegions);
		 
		          
		    
		//        return temp;
		        //        return null;
		        Runtime.getRuntime().gc();
		        heapSize = Runtime.getRuntime().totalMemory();
		 //        long heapSize = Runtime.getRuntime().totalMemory();
		
		        // Get maximum size of heap in bytes. The heap cannot grow beyond this size.// Any attempt will result in an OutOfMemoryException.
		//        heapMaxSize = Runtime.getRuntime().maxMemory();
		
		        // Get amount of free memory within the heap in bytes. This size will increase // after garbage collection and decrease as new objects are created.
		        heapFreeSize = Runtime.getRuntime().freeMemory();
		
		//        System.out.println(heapSize / (1024 * 1024));
		//        System.out.println(heapMaxSize / (1024 * 1024));
		//        System.out.println(heapFreeSize / (1024 * 1024));
		
		        heapSize = Runtime.getRuntime().totalMemory();
		        System.out.println("Memory used before: "  + (heapSize-heapFreeSize)/(1024.0*1024.0*1024.0) + "GB");
		        
		        
		        long memory1 = heapSize-heapFreeSize;
		        
		
		       // DoubleReductionBasedViewSolver.memory = memory1;
		        		
		        System.out.println(this.viewname);
		//        if(viewname!="t18")
		//        	return null;
		        List<LinkedList<VariableValuePair>> temp = new ArrayList<LinkedList<VariableValuePair>>();
		        
		        
		
		        StopWatch subhoSolverSW = new StopWatch("SubhoSolver" + viewname);
				
		//        if(!(this.viewname.equals("t09")) && !(this.viewname.equals("t07")) )
		//        temp = subhoSolver(subhoCRegions);
		//
		        temp = subhoFormAndSolveLP(consistencyMakerType, consistencyConstraints, conditions);
		        
		        subhoSolverSW.displayTimeAndDispose();
		        
		
		        heapSize = Runtime.getRuntime().totalMemory();
		 //        long heapSize = Runtime.getRuntime().totalMemory();
		
		        // Get maximum size of heap in bytes. The heap cannot grow beyond this size.// Any attempt will result in an OutOfMemoryException.
		//        heapMaxSize = Runtime.getRuntime().maxMemory();
		
		        // Get amount of free memory within the heap in bytes. This size will increase // after garbage collection and decrease as new objects are created.
		        heapFreeSize = Runtime.getRuntime().freeMemory();
		
		        heapSize = Runtime.getRuntime().totalMemory();
		
		        memory2 = heapSize-heapFreeSize;
		        System.out.println("Memory used after: "  + (heapSize-heapFreeSize)/(1024.0*1024.0*1024.0) + "GB");
		        return temp;
		        		
		        		
		     }
		    
		//    The call to reducer class should be uncommented to use this function. There is one more line a few lines below it
		//    It is below "Bachaoooo!!" print
		//    public List<LinkedList<VariableValuePair>> subhoSolver() {
		//int cliqueIndex = 0;
		//    	
		////    	bValues
		//    	LongList bvalues = cliqueIdxtoConditionBValuesList.get(cliqueIndex);
		////    	regions
		//    	List<IntList> regions = cliqueIdxtoPSimplifiedList.get(cliqueIndex);		// Partition is a list of regions corresponding to below labels
		//    	
		//    	LPSolver lps = new LPSolver();
		//    	
		////    	System.out.println("Actually allowed regions");
		////    	System.out.println(regions);
		//    	
		//    	Map<double[], Double> regionToCardinality = lps.main(regions, bvalues);
		//
		////    	Map<double[], Double> regionToCardinality = lps.main(regions, bvalues);
		//    	
		//    	
		//    	
		//    	
		//    	List<LinkedList<VariableValuePair>> cliqueIdxToVarValuesList = new ArrayList<>(cliqueCount);
		//    	
		//    	Partition partition = cliqueIdxtoPList.get(0);
		//	      
		////    	Bug -- Artificial columns should also be permitted always
		//    	
		//    	LinkedList<VariableValuePair> varValuePairs = new LinkedList<>();
		//	      
		//    	for(Map.Entry<double[], Double> entry : regionToCardinality.entrySet()) {
		//    		
		//    		
		//    		double[] region = entry.getKey();
		//    		
		////    		Double to int conversion here
		////    		Take care
		//    		double rowcount = entry.getValue();
		//    		if(rowcount==0)
		//    			continue;
		//    		
		//    		int regionIndex = findRegionIndex(region);
		//    		System.out.println("row count:" + rowcount);
		//    		
		//    		Region variable = partition.at(regionIndex);
		//    		
		//    		VariableValuePair varValuePair = new VariableValuePair(variable, (int)rowcount);
		//            varValuePairs.add(varValuePair);
		//    	}
		//    	
		//    	
		//     
		//    	cliqueIdxToVarValuesList.add(varValuePairs);
		//    	
		////    	   if (rowcount != 0) {
		////	              Region variable = getTruncatedRegion(partition.at(j), colIndxs);
		////	              VariableValuePair varValuePair = new VariableValuePair(variable, rowcount);
		////	              varValuePairs.add(varValuePair);
		////	          }
		////	      }
		////	      cliqueIdxToVarValuesList.add(varValuePairs);
		//
		//    	return cliqueIdxToVarValuesList;
		//    }
		    
		    public List<LinkedList<VariableValuePair>> subhoSolver(List<Region> conditionRegions) {
		    	int cliqueIndex = 0;
		    	
		//    	bValues
		    	LongList bvalues = cliqueIdxtoConditionBValuesList.get(cliqueIndex);
		//    	regions
		//    	List<IntList> regions = cliqueIdxtoPSimplifiedList.get(cliqueIndex);		// Partition is a list of regions corresponding to below labels
		    	
		    	double[] newBVals = new double[bvalues.size()];
		    	for(int i=0;i<bvalues.size();i++)
		    		newBVals[i] = bvalues.get(i);
		    	
		    	LPSolver lps = new LPSolver();
		    	
		//    	System.out.println("Actually allowed regions");
		//    	System.out.println(regions);
		    	
		//    	Map<double[], Double> regionToCardinality = lps.main(regions, bvalues);
		
		    	Map<double[], Double> regionToCardinality = new HashMap();
				try {
					regionToCardinality = lps.newMain(conditionRegions, newBVals);
				} catch (InterruptedException e) {
					// TODO Auto-generated catch block
					e.printStackTrace();
				}
		    	
		    	
		    	
		    	
		    	List<LinkedList<VariableValuePair>> cliqueIdxToVarValuesList = new ArrayList<>(cliqueCount);
		    	
		    	Partition partition = cliqueIdxtoPList.get(0);
			      
		    	LinkedList<VariableValuePair> varValuePairs = new LinkedList<>();
			      
		    	for(Map.Entry<double[], Double> entry : regionToCardinality.entrySet()) {
		    		double[] region = entry.getKey();
		    		
		//    		Double to int conversion here
		//    		Take care
		    		double rowcount = entry.getValue();
		    		if(rowcount==0)
		    			continue;
		    		
		    		
		//    		System.out.println("Region Label: " + region.ge)
		//    		int regionIndex = findRegionIndex(region);
		//    		System.out.println("row count:" + rowcount);
		//    		
		//    		Region variable = partition.at(regionIndex);
		    		Region variable = formRegion(region, conditionRegions);
		    		
		    		VariableValuePair varValuePair = new VariableValuePair(variable, (int)rowcount);
		            varValuePairs.add(varValuePair);
		    	}
		    	
		    	
		     
		    	cliqueIdxToVarValuesList.add(varValuePairs);
		    	
		//    	   if (rowcount != 0) {
		//	              Region variable = getTruncatedRegion(partition.at(j), colIndxs);
		//	              VariableValuePair varValuePair = new VariableValuePair(variable, rowcount);
		//	              varValuePairs.add(varValuePair);
		//	          }
		//	      }
		//	      cliqueIdxToVarValuesList.add(varValuePairs);
		
		    	return cliqueIdxToVarValuesList;
		    }
		    
		
		private Region formRegion(double[] region, List<Region> conditionRegions) {
				// TODO Auto-generated method stub
			
		//	Last one is allTrueRegion
				Region allTrueRegion = conditionRegions.get(conditionRegions.size()-1);
				Region answer = allTrueRegion;
				
				for(int i=0;i<region.length;i++) {
					if(region[i]==1) 
						answer = answer.intersection(conditionRegions.get(i));
					else
						answer = answer.intersection(allTrueRegion.minus(conditionRegions.get(i)));
				}
				
				return answer;
			}
		
		private int findRegionIndex(double[] region) {
				// TODO Auto-generated method stub
			
				List<IntList> regionList = cliqueIdxtoPSimplifiedList.get(0);
				
		
			    List<Integer> intRegion = new ArrayList();
			    for(int i=0;i<region.length;i++)
			    	if(region[i]==1)
			    		intRegion.add(i);
				
			    
			    Set<Integer> region1 = new HashSet();
			    region1.addAll(intRegion);
			    
			    Set<Integer> region2 = new HashSet<>();
			    
				for(int i=0;i<regionList.size();i++) {
					region2.clear();
					region2.addAll(regionList.get(i));
					
					if(region1.equals(region2))
						return i;
				}
				
		//		System.out.println("Original region partitioning did not have this region. Bug!!!");
				System.out.println("Probed region: " + intRegion);
		//		System.out.println("All regions");
		//		System.out.println(cliqueIdxtoPSimplifiedList);
				return -1;
			}    
		    
    
		public List<LinkedList<VariableValuePair>> subhoFormAndSolveLP(ConsistencyMakerType consistencyMakerType,FormalCondition[] consistencyConstraints, 
				List<FormalCondition> conditions) {


long heapSize = Runtime.getRuntime().totalMemory();
//        long heapSize = Runtime.getRuntime().totalMemory();
// Get amount of free memory within the heap in bytes. This size will increase // after garbage collection and decrease as new objects are created.
long heapFreeSize = Runtime.getRuntime().freeMemory();
heapSize = Runtime.getRuntime().totalMemory();
long memory2 = heapSize-heapFreeSize;
System.out.println("Memory used (formAndSolve)1: " + (memory2)/(1024.0*1024.0*1024.0) + "GB") ;




// added by tarun ends


/////////////// Start dk
  /* Compare partitions
  CliqueComparator cliqueComparator = new CliqueComparator(viewname);
  cliqueComparator.comparePartitions(cliqueIdxtoPList);
  /**/
  
//Remove till "// end dk" ?
  Map<String, String> contextmaptest = new HashMap<>();
  contextmaptest.put("model", "true");
  contextmaptest.put("unsat_core", "true");
  Context ctxtest = new Context(contextmaptest);

  Optimize osolver = ctxtest.mkOptimize();
  IntExpr x = ctxtest.mkIntConst("x");
  IntExpr y = ctxtest.mkIntConst("y");
  ArithExpr arithexpr = ctxtest.mkAdd(x, y);
  osolver.Add(ctxtest.mkGt(arithexpr, ctxtest.mkInt(10)));
  osolver.Add(ctxtest.mkLt(arithexpr, ctxtest.mkInt(20)));
  
  osolver.MkMaximize(arithexpr);
  
  osolver.Check();
  
  Model modeltest = osolver.getModel();
  System.out.println(modeltest.evaluate(x, true) + " : " + modeltest.evaluate(y, true));
  ctxtest.close();
///////////////// End dk
  
  StopWatch onlyFormationSW = new StopWatch("LP-OnlyFormation" + viewname);
  
  Map<String, String> contextmap = new HashMap<>();
  contextmap.put("model", "true");
  contextmap.put("unsat_core", "true");
  Context ctx = new Context(contextmap);

//Solver solver = ctx.mkSolver();
  Optimize solver = ctx.mkOptimize();
  
  heapSize = Runtime.getRuntime().totalMemory();
  //        long heapSize = Runtime.getRuntime().totalMemory();
  // Get amount of free memory within the heap in bytes. This size will increase // after garbage collection and decrease as new objects are created.
  heapFreeSize = Runtime.getRuntime().freeMemory();
  heapSize = Runtime.getRuntime().totalMemory();
  memory2 = heapSize-heapFreeSize;
  System.out.println("Memory used (formAndSolve)2: " + (memory2)/(1024.0*1024.0*1024.0) + "GB") ;

  //adding expression for optimization function -- Anupam
  //start
  //ArithExpr exp_final = ctx.mkIntConst("");
  //stop
  
  List<List<List<IntExpr>>> solverConstraintsRequiredForConsistency = new ArrayList<>();
  int projectionVarsIndex = 0;
  List<HashMap<String, ProjectionStuffInColumn>> cliqueWColumnWProjectionStuff = new ArrayList<>();
  
  // Create lp variables for cardinality constraints
  for (int cliqueIndex = 0; cliqueIndex < cliqueCount; cliqueIndex++) {
      LongList bvalues = cliqueIdxtoConditionBValuesList.get(cliqueIndex);
      Partition partition = cliqueIdxtoPList.get(cliqueIndex);		// Partition is a list of regions corresponding to below labels
      List<IntList> conditionIdxsList = cliqueIdxtoPSimplifiedList.get(cliqueIndex);	// Getting label list for this clique

      HashMap<Integer, Integer> indexKeeper;
      int solverConstraintSize;
      
      if (consistencyMakerType == ConsistencyMakerType.CONSISTENCYFILTERS) {
      	indexKeeper = mappedIndexOfConsistencyConstraint.get(cliqueIndex);
      	solverConstraintSize = bvalues.size() + indexKeeper.size();
      }
      else {
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

        //adding expression for computing l2 norm -- Anupam
          //start
          //IntExpr expr = ctx.mkIntConst(varname);
          //L1 norm minimization
          //exp_final = ctx.mkAdd(exp_final, expr);
          //L2 norm minimization
          //exp_final = ctx.mkAdd(exp_final, ctx.mkMul(expr, expr));
          //stop
          
          
          
          //Adding non-negativity constraints
          solver.Add(ctx.mkGe(ctx.mkIntConst(varname), ctx.mkInt(0)));

          for (IntIterator iter = conditionIdxsList.get(blockIndex).iterator(); iter.hasNext();) {
              int k = iter.nextInt();
              solverConstraints.get(k).add(ctx.mkIntConst(varname));
          }
      }
      //Adding normal constraints
      for (int conditionIndex = 0; conditionIndex < bvalues.size(); conditionIndex++) {
          long outputCardinality = bvalues.getLong(conditionIndex);
          List<IntExpr> addList = solverConstraints.get(conditionIndex);
          solver.Add(ctx.mkEq(ctx.mkAdd(addList.toArray(new ArithExpr[addList.size()])), ctx.mkInt(outputCardinality)));
          solverStats.solverConstraintCount++;
      }
      
///////////////// Start dk
      if (consistencyMakerType == ConsistencyMakerType.CONSISTENCYFILTERS) {
          List<List<IntExpr>> solverConstraintsToExport = new ArrayList<>(indexKeeper.size());
          for(int j = bvalues.size(); j < solverConstraintSize; j++) {
          	solverConstraintsToExport.add(solverConstraints.get(j));
          }
          solverConstraintsToExport.add(solverConstraints.get(bvalues.size() - 1));   // Clique size
          solverConstraintsRequiredForConsistency.add(solverConstraintsToExport);
      }

  }
  heapSize = Runtime.getRuntime().totalMemory();
  //        long heapSize = Runtime.getRuntime().totalMemory();
  // Get amount of free memory within the heap in bytes. This size will increase // after garbage collection and decrease as new objects are created.
  heapFreeSize = Runtime.getRuntime().freeMemory();
  heapSize = Runtime.getRuntime().totalMemory();
  memory2 = heapSize-heapFreeSize;
  System.out.println("Memory used (formAndSolve)3: " + (memory2)/(1024.0*1024.0*1024.0) + "GB") ;


///////////////// Start dk
  DebugHelper.printInfo("variablesRequiredForProjection: " + projectionVarsIndex);
  
  // Consistency
  List<ProjectionConsistencyInfoPair> projectionConsistencyInfoPairs = new LinkedList<>();
  int countConsistencyConstraint = 0;
  if (consistencyMakerType == ConsistencyMakerType.CONSISTENCYFILTERS) {
      
  	if(consistencyConstraints.length != 0 ) {
	        for (int c1index = 0; c1index < cliqueCount; c1index++) {
				HashMap<Integer, Integer> c1indexKeeper = mappedIndexOfConsistencyConstraint.get(c1index);
				if(c1indexKeeper.isEmpty())
					continue;
				List<List<IntExpr>> c1solverConstraints = solverConstraintsRequiredForConsistency.get(c1index);
				for (int c2index = c1index + 1; c2index < cliqueCount; c2index++) {
					HashMap<Integer, Integer> c2indexKeeper = mappedIndexOfConsistencyConstraint.get(c2index);
					if(c2indexKeeper.isEmpty())
						continue;
					List<List<IntExpr>> c2solverConstraints = solverConstraintsRequiredForConsistency.get(c2index);
					Set<Integer> applicableConsistencyConstraints = new HashSet<>(c1indexKeeper.keySet());
					applicableConsistencyConstraints.retainAll(c2indexKeeper.keySet());
					if(applicableConsistencyConstraints.isEmpty())
						continue;
					List<List<IntExpr>> c1ApplicableSolverConstraints = new ArrayList<>();
					List<List<IntExpr>> c2ApplicableSolverConstraints = new ArrayList<>();
					for (Integer originalConsistencyConstraintIndex : applicableConsistencyConstraints) {
						c1ApplicableSolverConstraints.add(c1solverConstraints.get(c1indexKeeper.get(originalConsistencyConstraintIndex)));
						c2ApplicableSolverConstraints.add(c2solverConstraints.get(c2indexKeeper.get(originalConsistencyConstraintIndex)));
					}
					
					c1ApplicableSolverConstraints.add(c1solverConstraints.get(c1solverConstraints.size() - 1));
					c2ApplicableSolverConstraints.add(c2solverConstraints.get(c2solverConstraints.size() - 1));

					HashMap<IntList, MutablePair<List<IntExpr>, List<IntExpr>>> conditionListToPairOfVarList = new HashMap<>();
					addTo_ConditionListToPairOfVarList(c1ApplicableSolverConstraints, conditionListToPairOfVarList);
					addTo_ConditionListToPairOfVarList(c2ApplicableSolverConstraints, conditionListToPairOfVarList);
					
					Set<String> commonCols = new HashSet<>(arasuCliques.get(c1index));
					commonCols.retainAll(arasuCliques.get(c2index));
					
					for (MutablePair<List<IntExpr>, List<IntExpr>> pair : conditionListToPairOfVarList.values()) {
						List<IntExpr> c1Set = pair.getFirst();
						List<IntExpr> c2Set = pair.getSecond();
						ArithExpr set1expr = ctx.mkAdd(c1Set.toArray(new ArithExpr[c1Set.size()]));
						ArithExpr set2expr = ctx.mkAdd(c2Set.toArray(new ArithExpr[c2Set.size()]));
						solver.Add(ctx.mkEq(set1expr, set2expr));
		                countConsistencyConstraint++;

		                // 1-D projection
		                collectProjectionConsistencyData(solver,ctx, c1Set, c2Set, c1index, c2index, commonCols, projectionConsistencyInfoPairs, cliqueWColumnWProjectionStuff);
					}
		        }
	        }
      }
  }
///////////////// End dk

  else if (consistencyMakerType == ConsistencyMakerType.BRUTEFORCE) {
      for (CliqueIntersectionInfo cliqueIntersectionInfo : cliqueIntersectionInfos) {		// Create lp variables for consistency constraints

          int i = cliqueIntersectionInfo.i;
          int j = cliqueIntersectionInfo.j;
          IntList intersectingColIndices = cliqueIntersectionInfo.intersectingColIndices;

          Partition partitionI = cliqueIdxtoPList.get(i);
          Partition partitionJ = cliqueIdxtoPList.get(j);

          //Recomputing SplitRegions for every pair of intersecting cliques
          //as the SplitRegions might have become more granular due to
          //some other pair of intersecting cliques having its intersectingColIndices
          //overlapping with this pair's intersectingColIndices
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

              //Adding consistency constraints
              solver.Add(ctx.mkEq(ctx.mkAdd(consistencyLHS.toArray(new ArithExpr[consistencyLHS.size()])),
                      ctx.mkAdd(consistencyRHS.toArray(new ArithExpr[consistencyRHS.size()]))));
              solverStats.solverConstraintCount++;
              countConsistencyConstraint++;

              // 1-D projection
              collectProjectionConsistencyData(solver,ctx, consistencyLHS, consistencyRHS, i, j, commonCols, projectionConsistencyInfoPairs, cliqueWColumnWProjectionStuff);
          }
      }
  }
  else {
  	ctx.close();
  	throw new RuntimeException("Unknown consistency maker " + consistencyMakerType);
  }
  DebugHelper.printInfo("countConsistencyConstraint for " + viewname + " = " + countConsistencyConstraint);
  
  heapSize = Runtime.getRuntime().totalMemory();
  //        long heapSize = Runtime.getRuntime().totalMemory();
  // Get amount of free memory within the heap in bytes. This size will increase // after garbage collection and decrease as new objects are created.
  heapFreeSize = Runtime.getRuntime().freeMemory();
  heapSize = Runtime.getRuntime().totalMemory();
  memory2 = heapSize-heapFreeSize;
  System.out.println("Memory used (formAndSolve)4: " + (memory2)/(1024.0*1024.0*1024.0) + "GB") ;

/////////////// Start dk
  // Consistency for projection: Phase 1
  Set<IntExpr> allSlackVars = new HashSet<>();
  for (int cliqueIndex = 0; cliqueIndex < cliqueWColumnWProjectionStuff.size(); ++cliqueIndex) {
  	HashMap<String, ProjectionStuffInColumn> columnWProjectionStuff = cliqueWColumnWProjectionStuff.get(cliqueIndex);
  	for (Entry<String, ProjectionStuffInColumn> entry : columnWProjectionStuff.entrySet()) {
  		String columnname = entry.getKey();
  		ProjectionStuffInColumn projectionStuff = entry.getValue();
  		// All AggVars in an atomic set satisfy the same set of consistency constraints
			List<Set<IntExpr>> listOfAtomicSetOfNonAggVars = projectionStuff.doPartition_ConsistencyConstraintSetWiseNonAggVars();
			for (int j = 0; j < listOfAtomicSetOfNonAggVars.size(); ++j) {
				Set<IntExpr> atomicSetOfNonAggVars = listOfAtomicSetOfNonAggVars.get(j);
				IntExpr slackVar = ctx.mkIntConst(getSlackVarStringName(cliqueIndex, columnname, j));		// SlackVar value is the number of unique points from Atomic set vars
				solver.Add(ctx.mkGe(slackVar, ctx.mkInt(0)));
				solver.Add(ctx.mkGe(ctx.mkAdd(atomicSetOfNonAggVars.toArray(new ArithExpr[atomicSetOfNonAggVars.size()])), slackVar));
				
				allSlackVars.add(slackVar);
			}
		}
	}
  
  heapSize = Runtime.getRuntime().totalMemory();
  //        long heapSize = Runtime.getRuntime().totalMemory();
  // Get amount of free memory within the heap in bytes. This size will increase // after garbage collection and decrease as new objects are created.
  heapFreeSize = Runtime.getRuntime().freeMemory();
  heapSize = Runtime.getRuntime().totalMemory();
  memory2 = heapSize-heapFreeSize;
  System.out.println("Memory used (formAndSolve)5: " + (memory2)/(1024.0*1024.0*1024.0) + "GB") ;

  
  for (ProjectionConsistencyInfoPair projectionConsistencyInfoPair : projectionConsistencyInfoPairs) {
		String columnname = projectionConsistencyInfoPair.columnname;
		ProjectionConsistencyInfo c1ProjectionConsistencyInfo = projectionConsistencyInfoPair.getFirst();
		ProjectionConsistencyInfo c2ProjectionConsistencyInfo = projectionConsistencyInfoPair.getSecond();
		ProjectionStuffInColumn c1ProjectionStuff = cliqueWColumnWProjectionStuff.get(c1ProjectionConsistencyInfo.cindex).get(columnname);
		ProjectionStuffInColumn c2ProjectionStuff = cliqueWColumnWProjectionStuff.get(c2ProjectionConsistencyInfo.cindex).get(columnname);
		List<Integer> c1SlackVarsIndexs = c1ProjectionStuff.getSlackVarsIndexsContainedInNonAggVars(c1ProjectionConsistencyInfo.nonAggVars);
		List<Integer> c2SlackVarsIndexs = c2ProjectionStuff.getSlackVarsIndexsContainedInNonAggVars(c2ProjectionConsistencyInfo.nonAggVars);
		
		projectionConsistencyInfoPair.setSlackVarsIndexes(c1SlackVarsIndexs, c2SlackVarsIndexs);
		
		List<IntExpr> c1ProjVarsUnionSlackVar = new LinkedList<>(c1ProjectionConsistencyInfo.projVars);
		for (Integer index : c1SlackVarsIndexs) {
			c1ProjVarsUnionSlackVar.add(ctx.mkIntConst(getSlackVarStringName(c1ProjectionConsistencyInfo.cindex, columnname, index)));
		}
		List<IntExpr> c2ProjVarsUnionSlackVar = new LinkedList<>(c2ProjectionConsistencyInfo.projVars);
		for (Integer index : c2SlackVarsIndexs) {
			c2ProjVarsUnionSlackVar.add(ctx.mkIntConst(getSlackVarStringName(c2ProjectionConsistencyInfo.cindex, columnname, index)));
		}
		
		solver.Add(ctx.mkEq(ctx.mkAdd(c1ProjVarsUnionSlackVar.toArray(new ArithExpr[c1ProjVarsUnionSlackVar.size()])), ctx.mkAdd(c2ProjVarsUnionSlackVar.toArray(new ArithExpr[c2ProjVarsUnionSlackVar.size()]))));
	}
  
  heapSize = Runtime.getRuntime().totalMemory();
  //        long heapSize = Runtime.getRuntime().totalMemory();
  // Get amount of free memory within the heap in bytes. This size will increase // after garbage collection and decrease as new objects are created.
  heapFreeSize = Runtime.getRuntime().freeMemory();
  heapSize = Runtime.getRuntime().totalMemory();
  memory2 = heapSize-heapFreeSize;
  System.out.println("Memory used (formAndSolve)6: " + (memory2)/(1024.0*1024.0*1024.0) + "GB") ;

  
  // 1-D projection: This is not in report. The dVars maximize the difference between nonAggVars and ProjVars so that more slack is available
  // While, at the same time, the sum of all slackVars is minimized to prevent generating extra unique points which were originally not required: proj1 + slack1 = proj2 + slack2; 1+1=2+0 is better then 1+2=2+1
  int dVarIndex = 0;
  List<IntExpr> allDVars = new ArrayList<>();
  
  for (ProjectionConsistencyInfoPair projectionConsistencyInfoPair : projectionConsistencyInfoPairs) {
		ProjectionConsistencyInfo c1ProjectionConsistencyInfo = projectionConsistencyInfoPair.getFirst();
		Set<IntExpr> projVars = c1ProjectionConsistencyInfo.projVars;
		if (projVars.size() != 0 && c1ProjectionConsistencyInfo.nonAggVars.size() != 0) {
			IntExpr dVar = ctx.mkIntConst("d_var" + dVarIndex++);
			allDVars.add(dVar);
			Set<IntExpr> nonAggVars = new HashSet<>(c1ProjectionConsistencyInfo.nonAggVars);
			ArithExpr nonAggVarsSum = ctx.mkAdd(nonAggVars.toArray(new ArithExpr[nonAggVars.size()]));
			ctx.mkEq(dVar, ctx.mkSub(nonAggVarsSum, ctx.mkAdd(projVars.toArray(new ArithExpr[projVars.size()]))));
		}
		
		ProjectionConsistencyInfo c2ProjectionConsistencyInfo = projectionConsistencyInfoPair.getFirst();
		projVars = c2ProjectionConsistencyInfo.projVars;
		if (projVars.size() != 0 && c2ProjectionConsistencyInfo.nonAggVars.size() != 0) {
			IntExpr dVar = ctx.mkIntConst("d_var" + dVarIndex++);
			allDVars.add(dVar);
			Set<IntExpr> nonAggVars = new HashSet<>(c2ProjectionConsistencyInfo.nonAggVars);
			ArithExpr nonAggVarsSum = ctx.mkAdd(nonAggVars.toArray(new ArithExpr[nonAggVars.size()]));
			ctx.mkEq(dVar, ctx.mkSub(nonAggVarsSum, ctx.mkAdd(projVars.toArray(new ArithExpr[projVars.size()]))));
		}
  }
  
  heapSize = Runtime.getRuntime().totalMemory();
  //        long heapSize = Runtime.getRuntime().totalMemory();
  // Get amount of free memory within the heap in bytes. This size will increase // after garbage collection and decrease as new objects are created.
  heapFreeSize = Runtime.getRuntime().freeMemory();
  heapSize = Runtime.getRuntime().totalMemory();
  memory2 = heapSize-heapFreeSize;
  System.out.println("Memory used (formAndSolve)7: " + (memory2)/(1024.0*1024.0*1024.0) + "GB") ;

  
  ArithExpr objective = null;
  if (allDVars.size() > 0) {
  	objective = ctx.mkMul(ctx.mkInt(-1), ctx.mkAdd(allDVars.toArray(new ArithExpr[allDVars.size()])));
  	if (allSlackVars.size() > 0)
  		objective = ctx.mkAdd(objective, ctx.mkAdd(allSlackVars.toArray(new ArithExpr[allSlackVars.size()])));
  }
  
  if (objective != null)
  	solver.MkMinimize(objective);
  
  heapSize = Runtime.getRuntime().totalMemory();
  //        long heapSize = Runtime.getRuntime().totalMemory();
  // Get amount of free memory within the heap in bytes. This size will increase // after garbage collection and decrease as new objects are created.
  heapFreeSize = Runtime.getRuntime().freeMemory();
  heapSize = Runtime.getRuntime().totalMemory();
  memory2 = heapSize-heapFreeSize;
  System.out.println("Memory used (formAndSolve)8: " + (memory2)/(1024.0*1024.0*1024.0) + "GB") ;

///////////////// End dk
  
  // Adding an optimization function to the solver -- Anupam
  //start
  //solver.MkMinimize(exp_final);
  //stop
  
  
  
  onlyFormationSW.displayTimeAndDispose();
  
  //Dumping LP into a file -- Anupam
  //start
  FileWriter fw;
	try {
		fw = new FileWriter("lpfile-"+viewname+".txt");
		fw.write(solver.toString());
      fw.close();
	} catch (IOException e) {
		// TODO Auto-generated catch block
		e.printStackTrace();
	} 
  //System.err.println(solver.toString());
  //stop
  
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
          
          //Variable to column indices mapping -- Anupam
          //start
          FileWriter fw1;
  		try {
  			fw1 = new FileWriter(viewname+"-var-to-colindices.txt", true);
  			fw1.write(varname+" "+colIndxs.toString()+ "\n");
  	        fw1.close();
  		} catch (IOException e) {
  			// TODO Auto-generated catch block
  			e.printStackTrace();
  		} 
  		//stop
          //System.err.println(varname+colIndxs.toString());
          long rowcount = Long.parseLong(model.evaluate(ctx.mkIntConst(varname), true).toString());
        //Variable to value mapping -- Anupam
          //start
          FileWriter fw2;
  		try {
  			fw2 = new FileWriter(viewname+"-var-to-value.txt", true);
  			fw2.write(varname+" "+rowcount+ "\n");
  	        fw2.close();
  		} catch (IOException e) {
  			// TODO Auto-generated catch block
  			e.printStackTrace();
  		} 
  		//stop
		  
          if (rowcount != 0) {
              Region variable = getTruncatedRegion(partition.at(j), colIndxs);
              VariableValuePair varValuePair = new VariableValuePair(variable, rowcount);
              varValuePairs.add(varValuePair);
          }
      }
      cliqueIdxToVarValuesList.add(varValuePairs);
  }
  
  heapSize = Runtime.getRuntime().totalMemory();
  //        long heapSize = Runtime.getRuntime().totalMemory();
  // Get amount of free memory within the heap in bytes. This size will increase // after garbage collection and decrease as new objects are created.
  heapFreeSize = Runtime.getRuntime().freeMemory();
  heapSize = Runtime.getRuntime().totalMemory();
  memory2 = heapSize-heapFreeSize;
  System.out.println("Memory used (formAndSolve)9: " + (memory2)/(1024.0*1024.0*1024.0) + "GB") ;

  
  onlySolvingSW.displayTimeAndDispose();
/*        
  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
  // DIRTY START DIRTY START DIRTY START DIRTY START DIRTY START DIRTY START DIRTY START DIRTY START DIRTY START DIRTY START DIRTY START 
  
  StopWatch onlyPhase2SW = new StopWatch("onlyPhase2SW " + viewname);
  
  HashMap<String, HashMap<Region, List<ProjectionConsistencyInfoPair>>> columnWSSPRegionToAllProjectionConsistencyInfoPairs = new HashMap<>();
  for (ProjectionConsistencyInfoPair projectionConsistencyInfoPair : projectionConsistencyInfoPairs) {
  	HashMap<Region, List<ProjectionConsistencyInfoPair>> sspRegionToAllProjectionConsistencyInfoPairs = columnWSSPRegionToAllProjectionConsistencyInfoPairs.get(projectionConsistencyInfoPair.columnname);
  	if (sspRegionToAllProjectionConsistencyInfoPairs == null) {
  		sspRegionToAllProjectionConsistencyInfoPairs = new HashMap<>();
  		columnWSSPRegionToAllProjectionConsistencyInfoPairs.put(projectionConsistencyInfoPair.columnname, sspRegionToAllProjectionConsistencyInfoPairs);
  	}
  	IntExpr aVar = null;
  	ProjectionConsistencyInfo c1ProjectionConsistencyInfo = projectionConsistencyInfoPair.getFirst();
  	if (c1ProjectionConsistencyInfo.aggVars.size() != 0) {
  		aVar = c1ProjectionConsistencyInfo.aggVars.iterator().next();
  	} else if (c1ProjectionConsistencyInfo.nonAggVars.size() != 0) {
  		aVar = c1ProjectionConsistencyInfo.nonAggVars.iterator().next();
  	} else
  		DirtyCode.throwError("Should not happen!");

  	HashMap<Region, ProjectionStuffInSSPRegion> sspRegionToProjectionStuff = cliqueWColumnWProjectionStuff.get(projectionConsistencyInfoPair.getFirst().cindex).get(projectionConsistencyInfoPair.columnname).getMapSSPRegionToProjectionStuff();
  	List<ProjectionConsistencyInfoPair> listOfProjectionConsistencyInfoPairs = getCorrespondingRegionList(sspRegionToAllProjectionConsistencyInfoPairs, sspRegionToProjectionStuff, aVar);
		listOfProjectionConsistencyInfoPairs.add(projectionConsistencyInfoPair);
	}
  
  for (int i = 0; i < cliqueCount; i++) {
  	HashMap<String, ProjectionStuffInColumn> columnWiseProjectionStuff = cliqueWColumnWProjectionStuff.get(i);
		for (ProjectionStuffInColumn projectionStuffInColumn : columnWiseProjectionStuff.values()) {
			projectionStuffInColumn.updateAggVarToProjVarOfProjectionStuffInSSPRegion();
		}
  }

	// Assigning intervals to projVars and finding MaxUniqePoints per sspRegion
  List<HashMap<IntExpr, DirtyValueInterval>> cliqueWiseProjVarToInterval = new ArrayList<>();
  HashMap<String, HashMap<Region, Long>> columnWSSPRegionToMaxUniqePoints = new HashMap<>();
  
  if (false)
  // heuristic
  	createProjVarToIntervalAndSSPRegionToMaxUniquePoints_hueristic(model, ctx, cliqueWiseProjVarToInterval, columnWSSPRegionToAllProjectionConsistencyInfoPairs, cliqueWColumnWProjectionStuff, columnWSSPRegionToMaxUniqePoints);
  // sequential
  else
  	createProjVarToIntervalAndSSPRegionToMaxUniquePoints_sequential(model, ctx, cliqueWiseProjVarToInterval, cliqueWColumnWProjectionStuff, columnWSSPRegionToMaxUniqePoints);
  
  List<HashMap<IntExpr, ProjectionValues>> cliqueWAggAndNonAggVarsToProjectionValues= new ArrayList<>(cliqueCount);
  for (int i = 0; i < cliqueCount; ++i)
  	cliqueWAggAndNonAggVarsToProjectionValues.add(new HashMap<>());
  
  // Projection consistency Phase 2
  for (Entry<String, HashMap<Region, List<ProjectionConsistencyInfoPair>>> outerEntry : columnWSSPRegionToAllProjectionConsistencyInfoPairs.entrySet()) {
		String columnname = outerEntry.getKey();
		HashMap<Region, List<ProjectionConsistencyInfoPair>> sspRegionToAllProjectionConsistencyInfoPairs = outerEntry.getValue();
		HashMap<Region, Long> sspRegionToMaxUniqePoints = columnWSSPRegionToMaxUniqePoints.get(columnname);
  	int colIndx = sortedViewColumns.indexOf(columnname);
		for (Entry<Region, List<ProjectionConsistencyInfoPair>> innerEntry : sspRegionToAllProjectionConsistencyInfoPairs.entrySet()) {
			Region region = innerEntry.getKey();
			Long maxUniqePoints = sspRegionToMaxUniqePoints.get(region);
			if (maxUniqePoints == 0)
				continue;
			
			// TODO: Problem: LongIndexNeeded : Need to change this code because using long array indexes!
			long maxint = Integer.MAX_VALUE;
			if (maxUniqePoints.longValue() >= maxint)
				DirtyCode.throwError("problem");
			
			List<ProjectionConsistencyInfoPair> listProjectionConsistencyInfoPairs = innerEntry.getValue();
			
			Map<String, String> contextmapTemp = new HashMap<>();
	        contextmapTemp.put("model", "true");
	        contextmapTemp.put("unsat_core", "true");
	        Context ctxPhase2 = new Context(contextmapTemp);
	        Solver solverPhase2 = ctxPhase2.mkSolver();
	        
	        IntNum zero = ctxPhase2.mkInt(0);
	        
	        List<List<IntExpr>> c1PointWListOfNewVars = new ArrayList<>((int)maxUniqePoints.longValue());			// value of point - list of vars
	        List<List<IntExpr>> c2PointWListOfNewVars = new ArrayList<>((int)maxUniqePoints.longValue());			// value of point - list of vars
			for(int i = 0; i < (int)maxUniqePoints.longValue(); ++i) {
				c1PointWListOfNewVars.add(new ArrayList<>());
				c2PointWListOfNewVars.add(new ArrayList<>());
			}
			
	        for (ProjectionConsistencyInfoPair pInfoPair : listProjectionConsistencyInfoPairs) {
	        	ProjectionConsistencyInfo c1ProjectionConsistencyInfo = pInfoPair.getFirst();
	        	ProjectionConsistencyInfo c2ProjectionConsistencyInfo = pInfoPair.getSecond();
	        	createPointWiseConstraints(model, solverPhase2, ctxPhase2, c1ProjectionConsistencyInfo, cliqueWColumnWProjectionStuff, cliqueWiseProjVarToInterval, c1PointWListOfNewVars, columnname, maxUniqePoints);
	        	createPointWiseConstraints(model, solverPhase2, ctxPhase2, c2ProjectionConsistencyInfo, cliqueWColumnWProjectionStuff, cliqueWiseProjVarToInterval, c2PointWListOfNewVars, columnname, maxUniqePoints);

	    		for(int i = 0; i < (int)maxUniqePoints.longValue(); ++i) {
	    			List<IntExpr> c1NewVars = c1PointWListOfNewVars.get(i);
	    			List<IntExpr> c2NewVars = c2PointWListOfNewVars.get(i);
	    			
	    			if (c1NewVars.isEmpty() && c2NewVars.isEmpty())
	    				continue;
	    			if (c1NewVars.isEmpty() || c2NewVars.isEmpty()) {
	    				if (c1NewVars.isEmpty() && containsOnlySlacks(c2NewVars))
	    					c1NewVars.add(zero);
	    				else if (c2NewVars.isEmpty() && containsOnlySlacks(c1NewVars))
	    					c2NewVars.add(zero);
	    				else
	    					DirtyCode.throwError("Phase 2: No space to multiply points!");
	    			}
	    			
	    			solverPhase2.add(ctxPhase2.mkEq(ctxPhase2.mkAdd(c1NewVars.toArray(new ArithExpr[c1NewVars.size()])), ctxPhase2.mkAdd(c2NewVars.toArray(new ArithExpr[c2NewVars.size()]))));
	    		}
	        }
	        
	        /////
	        long numberOfVars = 0;
	        for (List<IntExpr> list : c1PointWListOfNewVars) {
				numberOfVars += list.size();
			}
	        for (List<IntExpr> list : c2PointWListOfNewVars) {
				numberOfVars += list.size();
			}
	        System.out.println("Number of variables for phase 2: " + numberOfVars + " , maxUniqePoints: " + maxUniqePoints);
	        /////
	        
			
			if (solverPhase2.check() != Status.SATISFIABLE)
				DirtyCode.throwError("Phase 2 Unsatisfiable!!");
			Model modelTemp = solverPhase2.getModel();
	        
			// Assigning projection intervals with number of occurrences (count) to regions (vars)
			// To AggVars
			for (int cindex = 0; cindex < cliqueCount; ++cindex) {
				ProjectionStuffInColumn projectionStuffInColumn = cliqueWColumnWProjectionStuff.get(cindex).get(columnname);
				if (projectionStuffInColumn == null)
					continue;
				ProjectionStuffInSSPRegion projectionStuffInSSPRegion = projectionStuffInColumn.getProjectionStuffInSSPRegion(region);
				HashMap<IntExpr, DirtyValueInterval> projVarToInterval = cliqueWiseProjVarToInterval.get(cindex);
				HashMap<IntExpr, ProjectionValues> varsToProjectionValues = cliqueWAggAndNonAggVarsToProjectionValues.get(cindex);
	        	createAggVarsToProjectionValues(model, ctxPhase2, modelTemp, projectionStuffInSSPRegion, projVarToInterval, columnname, maxUniqePoints, varsToProjectionValues, colIndx, cindex);
			}
			
			List<Set<Integer>> cliqueWSlackVarsIndexes = new ArrayList<>(cliqueCount);
			for (int i = 0; i < cliqueCount; ++i)
				cliqueWSlackVarsIndexes.add(new HashSet<>());
			
			for (ProjectionConsistencyInfoPair pInfoPair : listProjectionConsistencyInfoPairs) {
	        	ProjectionConsistencyInfo c1ProjectionConsistencyInfo = pInfoPair.getFirst();
	        	cliqueWSlackVarsIndexes.get(c1ProjectionConsistencyInfo.cindex).addAll(c1ProjectionConsistencyInfo.slackVarsIndexes);
	        	ProjectionConsistencyInfo c2ProjectionConsistencyInfo = pInfoPair.getSecond();
	        	cliqueWSlackVarsIndexes.get(c2ProjectionConsistencyInfo.cindex).addAll(c2ProjectionConsistencyInfo.slackVarsIndexes);
			}
			
			// To NonAggVars
			for (int cindex = 0; cindex < cliqueCount; ++cindex) {
				ProjectionStuffInColumn projectionStuffInColumn = cliqueWColumnWProjectionStuff.get(cindex).get(columnname);
				if (projectionStuffInColumn == null)
					continue;
				HashMap<IntExpr, ProjectionValues> varsToProjectionValues = cliqueWAggAndNonAggVarsToProjectionValues.get(cindex);
				Set<Integer> slackVarsIndexes = cliqueWSlackVarsIndexes.get(cindex);
				createNonAggVarsToProjectionValues(model, ctxPhase2, modelTemp, projectionStuffInColumn, slackVarsIndexes, columnname, maxUniqePoints, varsToProjectionValues, colIndx, cindex);
			}
		}
	}
  
  onlyPhase2SW.displayTimeAndDispose();
  
  // Assigning intervals to aggVars of those columns which have not taken part in any of the consistency constraints
  Set<String> projColsTakingPartInConsistency = columnWSSPRegionToAllProjectionConsistencyInfoPairs.keySet();
  Set<String> projColsNotTakingPartInConsistency = columnWSSPRegionToMaxUniqePoints.keySet();
  projColsNotTakingPartInConsistency.removeAll(projColsTakingPartInConsistency);
  for (int cIndex = 0; cIndex < cliqueCount; ++cIndex) {
  	HashMap<String, ProjectionStuffInColumn> columnWProjectionStuff = cliqueWColumnWProjectionStuff.get(cIndex);
  	HashMap<IntExpr, ProjectionValues> varsToProjectionValues = cliqueWAggAndNonAggVarsToProjectionValues.get(cIndex);
  	HashMap<IntExpr, DirtyValueInterval> projVarToInterval = cliqueWiseProjVarToInterval.get(cIndex);
  	for (String columnname : projColsNotTakingPartInConsistency) {
  		ProjectionStuffInColumn projectionStuffInColumn = columnWProjectionStuff.get(columnname);
  		if (projectionStuffInColumn == null)
  			continue;
  		int colIndx = sortedViewColumns.indexOf(columnname);
  		for (Entry<IntExpr, List<IntExpr>> entry : projectionStuffInColumn.getAggVarsToProjVars().entrySet()) {
				IntExpr aggVar = entry.getKey();
  			long rowcount = Long.parseLong(model.evaluate(aggVar, true).toString());
  			if (rowcount > 0) {
  				long leftover = rowcount;
  				List<IntExpr> projVars = entry.getValue();
  				ProjectionValues projectionValues = getOrAdd(varsToProjectionValues, aggVar);
  				Iterator<IntExpr> it = projVars.iterator();
  				DirtyValueInterval interval = null;
  				do {
  					interval = projVarToInterval.get(it.next());
  				} while (interval == null);
  				long firstStart = interval.start;
  				long intervalSizeExceptFirstElement = interval.end - (interval.start + 1);		// Will repeat first element
  				if (intervalSizeExceptFirstElement > 0) {
  					projectionValues.addToList(colIndx, interval.start + 1, interval.end, 1);
  					leftover -= intervalSizeExceptFirstElement;
  				}
  				while (it.hasNext()) {
  					interval = projVarToInterval.get(it.next());
  					if (interval != null) {
  						projectionValues.addToList(colIndx, interval.start, interval.end, 1);
  						leftover -= interval.end - interval.start;
  					}
  				}
  				projectionValues.addToList(colIndx, firstStart, firstStart + 1, leftover);	// Repeating first element leftover times
  			}
			}
		}
  }
  
  // Creating region to Value list
  List<LinkedList<DirtyVariableValuePairWithProjectionValues>> dirtyCliqueIdxToVarValuesList = new ArrayList<>(cliqueCount);
  for (int i = 0; i < cliqueCount; i++) {
      IntList colIndxs = arasuCliquesAsColIndxs.get(i);
      Partition partition = cliqueIdxtoPList.get(i);
  	HashMap<IntExpr, ProjectionValues> aggAndNonAggVarsToProjectionValues = cliqueWAggAndNonAggVarsToProjectionValues.get(i);
		
      LinkedList<DirtyVariableValuePairWithProjectionValues> varValuePairs = new LinkedList<>();
      
      for (int j = 0; j < partition.size(); j++) {
          String varname = "var" + i + "_" + j;
			IntExpr var = ctx.mkIntConst(varname);
          long rowcount = Long.parseLong(model.evaluate(var, true).toString());
          if (rowcount != 0) {
          	ProjectionValues projectionValues = aggAndNonAggVarsToProjectionValues.get(var);	// Could be null because of nonAggVars
              Region region = getTruncatedRegion(partition.at(j), colIndxs);
              DirtyVariableValuePairWithProjectionValues varValuePair = new DirtyVariableValuePairWithProjectionValues(region, rowcount, projectionValues);
              varValuePair.doSanityCheck(colIndxs);
              varValuePairs.add(varValuePair);
          }
      }
      dirtyCliqueIdxToVarValuesList.add(varValuePairs);
  }

  IntList dirtyMergedColIndxs = new IntArrayList();
  List<DirtyValueCombinationWithProjectionValues> dirtyMergedValueCombinations = new ArrayList<>();
  dirtyMergedColIndxs.addAll(arasuCliquesAsColIndxs.get(0));

  //Instantiating variables of first clique
  for (DirtyVariableValuePairWithProjectionValues varValuePair : dirtyCliqueIdxToVarValuesList.get(0)) {
      IntList columnValues = getFloorInstantiation(varValuePair.variable);
      DirtyValueCombinationWithProjectionValues valueCombination = new DirtyValueCombinationWithProjectionValues(columnValues, varValuePair.rowcount, varValuePair.getProjectionValues());
      dirtyMergedValueCombinations.add(valueCombination);
  }
  
  // merging with other cliques
  for (int i = 1; i < cliqueCount; i++) {
      dirtyMergeWithAlignment(dirtyMergedColIndxs, dirtyMergedValueCombinations, arasuCliquesAsColIndxs.get(i), dirtyCliqueIdxToVarValuesList.get(i));
  }
  
  
  for (ListIterator<DirtyValueCombinationWithProjectionValues> iter = dirtyMergedValueCombinations.listIterator(); iter.hasNext();) {
  	DirtyValueCombinationWithProjectionValues dirtyValueCombination = iter.next();
  	dirtyValueCombination = new DirtyValueCombinationWithProjectionValues(getReverseMappedValueCombination(dirtyValueCombination), dirtyValueCombination.getProjectionValues());
  	dirtyValueCombination = new DirtyValueCombinationWithProjectionValues(getExpandedValueCombination(dirtyValueCombination), dirtyValueCombination.getProjectionValues());
      iter.set(dirtyValueCombination);
  }
  
  // Verifying count per agg condition
  List<FormalCondition> allAggConditions = new ArrayList<>();
	for (FormalCondition formalCondition : conditions) {
		if (formalCondition instanceof FormalConditionAggregate)
			allAggConditions.add(formalCondition);
	}
	
	DirtyCode.debugSolvingErrorPerConditionForProjections(allAggConditions, dirtyMergedValueCombinations, sortedViewColumns);
	
  /*
  DirtyViewSolution viewSolution = new DirtyViewSolution(mergedValueCombinations);
  DirtyDatabaseSummary.getInstance().addSummary(viewname, viewSolution);
  /*
  
  // DIRTY END DIRTY END DIRTY END DIRTY END DIRTY END DIRTY END DIRTY END DIRTY END DIRTY END DIRTY END DIRTY END DIRTY END DIRTY END 
  ////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
*/
  ctx.close();
  
  
  
  
  
  
  return cliqueIdxToVarValuesList;

}

    
    private List<LinkedList<VariableValuePair>> formulateAndSolve(List<FormalCondition> conditions, List<Region> conditionRegions, FormalCondition consistencyConstraints[]
    		, ConsistencyMakerType consistencyMakerType) {
    	
    	// TODO : remove IntExpr with their original String names in projection code
    	
    	
    	HashMap<Set<String>, Set<String>> cliquesToFKeyCoverage = new HashMap<>();
    	
    	// USed by duplication code get fkeys in each clique knowledge
    	if(PostgresVConfig.fkeyToBorrowedAttr.containsKey(this.viewname)) {
    		Map<String, Set<String>> fkeyToB = PostgresVConfig.fkeyToBorrowedAttr.get(this.viewname);
        	
        	for(String fkey : fkeyToB.keySet()) {
        		Set<String> borrowedColumns = fkeyToB.get(fkey);
        		boolean okFlag = false;
        		for(Set<String> clique : arasuCliques) {
        		
        			Set<String> tempClique = new HashSet<>(borrowedColumns);
        			tempClique.removeAll(clique);
        			if(tempClique.isEmpty()) {
        				okFlag = true;
        				
        				if(!cliquesToFKeyCoverage.containsKey(clique)) {
        					cliquesToFKeyCoverage.put(clique, new HashSet<>());
        				}
        				cliquesToFKeyCoverage.get(clique).add(fkey);
        				if(cliquesToFKeyCoverage.get(clique).size() > 1) {
        					System.out.print("");
        				}
        				break;
        			}
        					
        		}
        		if(!okFlag) {
        			System.out.print("");
        		}
        	}
    	}
    	
    	
    	
    
    	
    	StopWatch onlyReductionSW = new StopWatch("LP-OnlyReduction" + viewname);
    	
        //STEP 1: For each clique find set of applicable conditions and call variable reduction
        

        for (int i = 0; i < cliqueCount; i++) {

            LongList bvalues = new LongArrayList();
            Set<String> clique = arasuCliques.get(i);   // set of columns
            List<Region> cRegions = new ArrayList<>();
            List<Pair<Integer, Boolean>> applicableConditions = new ArrayList<>();
            for (int j = 0; j < conditions.size(); j++) {      
            	FormalCondition curCondition = conditions.get(j);
                Set<String> appearingCols = new HashSet<>();
                getAppearingCols(appearingCols, curCondition);   // appearing columns will have columns appeared in current condition

                if (clique.containsAll(appearingCols)) {
                    cRegions.add(conditionRegions.get(j));
                    bvalues.add(curCondition.getOutputCardinality());
                    if (curCondition instanceof FormalConditionAggregate)
                    	applicableConditions.add(new Pair<>(j ,true));
                    else
                    	applicableConditions.add(new Pair<>(j ,false));
                } else if (curCondition instanceof FormalConditionAggregate) {
                	removeAggregateCols(appearingCols, curCondition);
                	if (clique.containsAll(appearingCols)) {
                        cRegions.add(conditionRegions.get(j));
                        bvalues.add(curCondition.getOutputCardinality());
                        applicableConditions.add(new Pair<>(j ,false));
                	}
                }
            }
            applicableConditionsOnClique.add(applicableConditions);

            //Adding extra cRegion for all 1's condition
            Region allOnesCRegion = new Region();
            BucketStructure subConditionBS = new BucketStructure();
            for (int j = 0; j < allTrueBS.size(); j++) {
                Bucket bucket = new Bucket();
                for (int k = 0; k < allTrueBS.get(j).length; k++) {
                    if (allTrueBS.get(j)[k]) {		// Is this check needed?
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
            //DebugHelper.printInfo("Bachaaaao!");
            //DebugHelper.printInfo(viewname + " " +clique + " " + cRegions);
            
            
             Set<String> fkeysList = cliquesToFKeyCoverage.get(clique);
           
             Set<String> borrowedAttr = new HashSet<>();
             if(PostgresVConfig.fkeyToBorrowedAttr.containsKey(viewname) && cliquesToFKeyCoverage.containsKey(clique)) {
             	
             	
             	Set<String> fkeys = cliquesToFKeyCoverage.get(clique);
             	for(String fkey : fkeys) {
             		borrowedAttr.addAll(PostgresVConfig.fkeyToBorrowedAttr.get(viewname).get(fkey));
             	}
            	 	 
            	
             }
           // Reducer reducer = new Reducer(allTrueBS, cRegions);
            Reducer reducer = new Reducer(allTrueBS, cRegions,borrowedAttr,clique,sortedViewColumns);
            //Map<IntList, Region> P = reducer.getMinPartition();

            //Added by Anupam for Skew Mimicking            
            reducer.refineRegionsforSkewMimicking();

            //Using varIds instead of old variable regions
            List<Region> oldVarList = new ArrayList<>();	// List of regions corresponding to below labels
            List<IntList> conditionIdxsList = new ArrayList<>();	// List of labels
            reducer.getVarsAndConditionsSimplified(oldVarList, conditionIdxsList);

            Partition cliqueP = new Partition(new ArrayList<>(oldVarList));
            cliqueIdxtoPList.add(cliqueP);

            cliqueIdxtoPSimplifiedList.add(conditionIdxsList);
        }
        onlyReductionSW.displayTimeAndDispose();

        
        /* 
         * Code for subhodeep for Finding regions satisfying set of CCs 
         * 
         */
        
        
        HashMap<String,List<String>> regionToCCMap = new HashMap<>();
        for (int i = 0; i < cliqueCount; i++) {
        	
           Set<String> clique = arasuCliques.get(i);
        	
        	Partition partition = cliqueIdxtoPList.get(i);
        	
        	for(int j=0; j < partition.size(); j++) {
        		
        		Region r = partition.at(j);
        		regionToCCMap.put("View " + this.viewname + "_Clique" + i + "_Region" + j, new ArrayList<>());
        		for(int c=0; c< conditions.size(); c++) {
        			 FormalCondition curCondition = conditions.get(c); 
        			 Set<String> appearingCols = new HashSet<>();
                     getAppearingCols(appearingCols, curCondition);
        			 if (clique.containsAll(appearingCols)) {
        				 
        				 if(checkCCSatifyRegion(r,appearingCols,curCondition)) {
        					
        					 //System.out.println("Clique_" + i + "Region" + j + " -> " + " CC_" + c);
        					 regionToCCMap.get("View " + this.viewname + "_Clique" + i + "_Region" + j).add("CC" + c);
        					 
        				 }
        				 
        			 }
        		}
        		
        		
        		
        	}
        	        	
        }
        
        for(String region : regionToCCMap.keySet()) {
        	//System.out.println(region + " ---> " + regionToCCMap.get(region));
        }
        
        
        
        
        if (consistencyMakerType == ConsistencyMakerType.BRUTEFORCE) {	// Further divide regions for consistency
	        for (int i = 0; i < cliqueCount; i++) {
	            for (int j = i + 1; j < cliqueCount; j++) {
	                IntList intersectingColIndices = getIntersectionColIndices(arasuCliques.get(i), arasuCliques.get(j));
	                if (intersectingColIndices.isEmpty()) {
	                    continue;
	                }
	                CliqueIntersectionInfo cliqueIntersectionInfo =
	                        replaceWithFreshVariablesToEnsureConsistency(cliqueIdxtoPList, cliqueIdxtoPSimplifiedList, i, j, intersectingColIndices);
	                cliqueIntersectionInfos.add(cliqueIntersectionInfo);
	            }
	        }
        }

        long varcountDR = 0;
        for (int i = 0; i < cliqueCount; i++) {
            varcountDR += cliqueIdxtoPList.get(i).getAll().size();
        }
        DebugHelper.printInfo("Number of variables after double reduction " + varcountDR);
        
       return formAndSolveLP(consistencyMakerType, consistencyConstraints, conditions,cliquesToFKeyCoverage);
        		
        		
     }
    
    
    

	private boolean checkCCSatifyRegion(Region r, Set<String> appearingCols, FormalCondition condition) {
		// TODO Auto-generated method stub
		r =getReverseMappedRegion(r);
        r =getExpandedRegion(r);
        IntList columnValues = getFloorInstantiation(r);
        ValueCombination valueCombination = new ValueCombination(columnValues, 0);//if you wish to get the valuecombination too
		List<String> sortedColumns = this.sortedViewColumns;
		if (condition instanceof FormalConditionSimpleInt && meetsSimple(valueCombination, (FormalConditionSimpleInt) condition, sortedColumns)   ) {
			return true;
		}else if (condition instanceof FormalConditionAnd && meetsAnd(valueCombination, (FormalConditionAnd) condition, sortedColumns)) {
           return true;
        } else if (condition instanceof FormalConditionOr && meetsOr(valueCombination, (FormalConditionOr) condition, sortedColumns)) {
            return true;
        } else if (!(condition instanceof FormalConditionSimpleInt || condition instanceof FormalConditionAnd
                || condition instanceof FormalConditionOr))
            throw new RuntimeException("Unrecognized condition " + condition + " of type " + condition.getClass());
		
		return false;
	}
	
	
	private static boolean meetsSimple(ValueCombination valueCombination, FormalConditionSimpleInt simpleCondition, List<String> sortedColumns) {
        String colname = simpleCondition.getColumnname();
        //String colname = PostgresVConfig.COLUMN_ID_MAP.get(columnId).getColname();
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
	
    private static boolean meetsAnd(ValueCombination valueCombination, FormalConditionAnd andCondition, List<String> sortedColumns) {
        for (FormalCondition condition : andCondition.getConditionList()) {
            if (condition instanceof FormalConditionSimpleInt && !meetsSimple(valueCombination, (FormalConditionSimpleInt) condition, sortedColumns))
                return false;
            else if (condition instanceof FormalConditionAnd && !meetsAnd(valueCombination, (FormalConditionAnd) condition, sortedColumns))
                return false;
            else if (condition instanceof FormalConditionOr && !meetsOr(valueCombination, (FormalConditionOr) condition, sortedColumns))
                return false;
            else if (!(condition instanceof FormalConditionSimpleInt || condition instanceof FormalConditionAnd || condition instanceof FormalConditionOr))
                throw new RuntimeException("Unrecognized condition " + condition + " of type " + condition.getClass());
        }
        return true;
    }
    private static boolean meetsOr(ValueCombination valueCombination, FormalConditionOr orCondition, List<String> sortedColumns) {
        for (FormalCondition condition : orCondition.getConditionList()) {
            if (condition instanceof FormalConditionSimpleInt && meetsSimple(valueCombination, (FormalConditionSimpleInt) condition, sortedColumns))
                return true;
            else if (condition instanceof FormalConditionAnd && meetsAnd(valueCombination, (FormalConditionAnd) condition, sortedColumns))
                return true;
            else if (condition instanceof FormalConditionOr && meetsOr(valueCombination, (FormalConditionOr) condition, sortedColumns))
                return true;
            else if (!(condition instanceof FormalConditionSimpleInt || condition instanceof FormalConditionAnd || condition instanceof FormalConditionOr))
                throw new RuntimeException("Unrecognized condition " + condition + " of type " + condition.getClass());
        }
        return false;
    }
	
	
    // changes by manish
	public List<LinkedList<VariableValuePair>> formAndSolveLP1(ConsistencyMakerType consistencyMakerType,FormalCondition[] consistencyConstraints, 
							List<FormalCondition> conditions, HashMap<Set<String>, Set<String>> cliquesToFKeyCoverage) {
		
			StopWatch onlyFormationSW = new StopWatch("ByMJ LP-OnlyFormation" + viewname);
			  
			  Map<String, String> contextmap = new HashMap<>();
			  contextmap.put("model", "true");
			  contextmap.put("unsat_core", "true");
			  Context ctx = new Context(contextmap);
			
			//Solver solver = ctx.mkSolver();
			  Optimize solver = ctx.mkOptimize();
			  			  
			  List<List<List<IntExpr>>> solverConstraintsRequiredForConsistency = new ArrayList<>();
			  int projectionVarsIndex = 0;
			  List<HashMap<String, ProjectionStuffInColumn>> cliqueWColumnWProjectionStuff = new ArrayList<>();
			  
			  // Create lp variables for cardinality constraints
			  for (int cliqueIndex = 0; cliqueIndex < cliqueCount; cliqueIndex++) {
			      LongList bvalues = cliqueIdxtoConditionBValuesList.get(cliqueIndex);
			      Partition partition = cliqueIdxtoPList.get(cliqueIndex);		// Partition is a list of regions corresponding to below labels
			      List<IntList> conditionIdxsList = cliqueIdxtoPSimplifiedList.get(cliqueIndex);	// Getting label list for this clique
			
			      HashMap<Integer, Integer> indexKeeper;
			      int solverConstraintSize;
			      
			      if (consistencyMakerType == ConsistencyMakerType.CONSISTENCYFILTERS) {
			      	indexKeeper = mappedIndexOfConsistencyConstraint.get(cliqueIndex);
			      	solverConstraintSize = bvalues.size() + indexKeeper.size();
			      }
			      else {
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
			       
			          //Adding non-negativity constraints
			          solver.Add(ctx.mkGe(ctx.mkIntConst(varname), ctx.mkInt(0)));
			
			          for (IntIterator iter = conditionIdxsList.get(blockIndex).iterator(); iter.hasNext();) {
			              int k = iter.nextInt();
			              solverConstraints.get(k).add(ctx.mkIntConst(varname));
			          }
			      }
			      //Adding normal constraints
			      for (int conditionIndex = 0; conditionIndex < bvalues.size(); conditionIndex++) {
			          long outputCardinality = bvalues.getLong(conditionIndex);
			          List<IntExpr> addList = solverConstraints.get(conditionIndex);
			          solver.Add(ctx.mkEq(ctx.mkAdd(addList.toArray(new ArithExpr[addList.size()])), ctx.mkInt(outputCardinality)));
			          solverStats.solverConstraintCount++;
			      }
			      
			///////////////// Start dk
			      if (consistencyMakerType == ConsistencyMakerType.CONSISTENCYFILTERS) {
			          List<List<IntExpr>> solverConstraintsToExport = new ArrayList<>(indexKeeper.size());
			          for(int j = bvalues.size(); j < solverConstraintSize; j++) {
			          	solverConstraintsToExport.add(solverConstraints.get(j));
			          }
			          solverConstraintsToExport.add(solverConstraints.get(bvalues.size() - 1));   // Clique size
			          solverConstraintsRequiredForConsistency.add(solverConstraintsToExport);
			      }
			  }
			
			///////////////// Start dk
			  DebugHelper.printInfo("variablesRequiredForProjection: " + projectionVarsIndex);
			  
			  // Consistency
			  List<ProjectionConsistencyInfoPair> projectionConsistencyInfoPairs = new LinkedList<>();
			  int countConsistencyConstraint = 0;
			  if (consistencyMakerType == ConsistencyMakerType.CONSISTENCYFILTERS) {
			      
			  	if(consistencyConstraints.length != 0 ) {
				        for (int c1index = 0; c1index < cliqueCount; c1index++) {
							HashMap<Integer, Integer> c1indexKeeper = mappedIndexOfConsistencyConstraint.get(c1index);
							if(c1indexKeeper.isEmpty())
								continue;
							List<List<IntExpr>> c1solverConstraints = solverConstraintsRequiredForConsistency.get(c1index);
							for (int c2index = c1index + 1; c2index < cliqueCount; c2index++) {
								HashMap<Integer, Integer> c2indexKeeper = mappedIndexOfConsistencyConstraint.get(c2index);
								if(c2indexKeeper.isEmpty())
									continue;
								List<List<IntExpr>> c2solverConstraints = solverConstraintsRequiredForConsistency.get(c2index);
								Set<Integer> applicableConsistencyConstraints = new HashSet<>(c1indexKeeper.keySet());
								applicableConsistencyConstraints.retainAll(c2indexKeeper.keySet());
								if(applicableConsistencyConstraints.isEmpty())
									continue;
								List<List<IntExpr>> c1ApplicableSolverConstraints = new ArrayList<>();
								List<List<IntExpr>> c2ApplicableSolverConstraints = new ArrayList<>();
								for (Integer originalConsistencyConstraintIndex : applicableConsistencyConstraints) {
									c1ApplicableSolverConstraints.add(c1solverConstraints.get(c1indexKeeper.get(originalConsistencyConstraintIndex)));
									c2ApplicableSolverConstraints.add(c2solverConstraints.get(c2indexKeeper.get(originalConsistencyConstraintIndex)));
								}
								
								c1ApplicableSolverConstraints.add(c1solverConstraints.get(c1solverConstraints.size() - 1));
								c2ApplicableSolverConstraints.add(c2solverConstraints.get(c2solverConstraints.size() - 1));
			
								HashMap<IntList, MutablePair<List<IntExpr>, List<IntExpr>>> conditionListToPairOfVarList = new HashMap<>();
								addTo_ConditionListToPairOfVarList(c1ApplicableSolverConstraints, conditionListToPairOfVarList);
								addTo_ConditionListToPairOfVarList(c2ApplicableSolverConstraints, conditionListToPairOfVarList);
								
								Set<String> commonCols = new HashSet<>(arasuCliques.get(c1index));
								commonCols.retainAll(arasuCliques.get(c2index));
								
								for (MutablePair<List<IntExpr>, List<IntExpr>> pair : conditionListToPairOfVarList.values()) {
									List<IntExpr> c1Set = pair.getFirst();
									List<IntExpr> c2Set = pair.getSecond();
									ArithExpr set1expr = ctx.mkAdd(c1Set.toArray(new ArithExpr[c1Set.size()]));
									ArithExpr set2expr = ctx.mkAdd(c2Set.toArray(new ArithExpr[c2Set.size()]));
									solver.Add(ctx.mkEq(set1expr, set2expr));
					                countConsistencyConstraint++;
			
					                // 1-D projection
					                collectProjectionConsistencyData(solver,ctx, c1Set, c2Set, c1index, c2index, commonCols, projectionConsistencyInfoPairs, cliqueWColumnWProjectionStuff);
								}
					        }
				        }
			      }
			  }
			///////////////// End dk
			
			  else if (consistencyMakerType == ConsistencyMakerType.BRUTEFORCE) {
			      for (CliqueIntersectionInfo cliqueIntersectionInfo : cliqueIntersectionInfos) {		// Create lp variables for consistency constraints
			
			          int i = cliqueIntersectionInfo.i;
			          int j = cliqueIntersectionInfo.j;
			          IntList intersectingColIndices = cliqueIntersectionInfo.intersectingColIndices;
			
			          Partition partitionI = cliqueIdxtoPList.get(i);
			          Partition partitionJ = cliqueIdxtoPList.get(j);
			
			          //Recomputing SplitRegions for every pair of intersecting cliques
			          //as the SplitRegions might have become more granular due to
			          //some other pair of intersecting cliques having its intersectingColIndices
			          //overlapping with this pair's intersectingColIndices
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
			
			              //Adding consistency constraints
			              solver.Add(ctx.mkEq(ctx.mkAdd(consistencyLHS.toArray(new ArithExpr[consistencyLHS.size()])),
			                      ctx.mkAdd(consistencyRHS.toArray(new ArithExpr[consistencyRHS.size()]))));
			              solverStats.solverConstraintCount++;
			              countConsistencyConstraint++;
			
			              // 1-D projection
			              collectProjectionConsistencyData(solver,ctx, consistencyLHS, consistencyRHS, i, j, commonCols, projectionConsistencyInfoPairs, cliqueWColumnWProjectionStuff);
			          }
			      }
			  }
			  else {
			  	ctx.close();
			  	throw new RuntimeException("Unknown consistency maker " + consistencyMakerType);
			  }
			  DebugHelper.printInfo("countConsistencyConstraint for " + viewname + " = " + countConsistencyConstraint);
			  
			/////////////// Start dk
			  // Consistency for projection: Phase 1
			  Set<IntExpr> allSlackVars = new HashSet<>();
			  for (int cliqueIndex = 0; cliqueIndex < cliqueWColumnWProjectionStuff.size(); ++cliqueIndex) {
			  	HashMap<String, ProjectionStuffInColumn> columnWProjectionStuff = cliqueWColumnWProjectionStuff.get(cliqueIndex);
			  	for (Entry<String, ProjectionStuffInColumn> entry : columnWProjectionStuff.entrySet()) {
			  		String columnname = entry.getKey();
			  		ProjectionStuffInColumn projectionStuff = entry.getValue();
			  		// All AggVars in an atomic set satisfy the same set of consistency constraints
						List<Set<IntExpr>> listOfAtomicSetOfNonAggVars = projectionStuff.doPartition_ConsistencyConstraintSetWiseNonAggVars();
						for (int j = 0; j < listOfAtomicSetOfNonAggVars.size(); ++j) {
							Set<IntExpr> atomicSetOfNonAggVars = listOfAtomicSetOfNonAggVars.get(j);
							IntExpr slackVar = ctx.mkIntConst(getSlackVarStringName(cliqueIndex, columnname, j));		// SlackVar value is the number of unique points from Atomic set vars
							solver.Add(ctx.mkGe(slackVar, ctx.mkInt(0)));
							solver.Add(ctx.mkGe(ctx.mkAdd(atomicSetOfNonAggVars.toArray(new ArithExpr[atomicSetOfNonAggVars.size()])), slackVar));
							
							allSlackVars.add(slackVar);
						}
					}
				}
			  
			  for (ProjectionConsistencyInfoPair projectionConsistencyInfoPair : projectionConsistencyInfoPairs) {
					String columnname = projectionConsistencyInfoPair.columnname;
					ProjectionConsistencyInfo c1ProjectionConsistencyInfo = projectionConsistencyInfoPair.getFirst();
					ProjectionConsistencyInfo c2ProjectionConsistencyInfo = projectionConsistencyInfoPair.getSecond();
					ProjectionStuffInColumn c1ProjectionStuff = cliqueWColumnWProjectionStuff.get(c1ProjectionConsistencyInfo.cindex).get(columnname);
					ProjectionStuffInColumn c2ProjectionStuff = cliqueWColumnWProjectionStuff.get(c2ProjectionConsistencyInfo.cindex).get(columnname);
					List<Integer> c1SlackVarsIndexs = c1ProjectionStuff.getSlackVarsIndexsContainedInNonAggVars(c1ProjectionConsistencyInfo.nonAggVars);
					List<Integer> c2SlackVarsIndexs = c2ProjectionStuff.getSlackVarsIndexsContainedInNonAggVars(c2ProjectionConsistencyInfo.nonAggVars);
					
					projectionConsistencyInfoPair.setSlackVarsIndexes(c1SlackVarsIndexs, c2SlackVarsIndexs);
					
					List<IntExpr> c1ProjVarsUnionSlackVar = new LinkedList<>(c1ProjectionConsistencyInfo.projVars);
					for (Integer index : c1SlackVarsIndexs) {
						c1ProjVarsUnionSlackVar.add(ctx.mkIntConst(getSlackVarStringName(c1ProjectionConsistencyInfo.cindex, columnname, index)));
					}
					List<IntExpr> c2ProjVarsUnionSlackVar = new LinkedList<>(c2ProjectionConsistencyInfo.projVars);
					for (Integer index : c2SlackVarsIndexs) {
						c2ProjVarsUnionSlackVar.add(ctx.mkIntConst(getSlackVarStringName(c2ProjectionConsistencyInfo.cindex, columnname, index)));
					}
					
					solver.Add(ctx.mkEq(ctx.mkAdd(c1ProjVarsUnionSlackVar.toArray(new ArithExpr[c1ProjVarsUnionSlackVar.size()])), ctx.mkAdd(c2ProjVarsUnionSlackVar.toArray(new ArithExpr[c2ProjVarsUnionSlackVar.size()]))));
				}
			  
			  // 1-D projection: This is not in report. The dVars maximize the difference between nonAggVars and ProjVars so that more slack is available
			  // While, at the same time, the sum of all slackVars is minimized to prevent generating extra unique points which were originally not required: proj1 + slack1 = proj2 + slack2; 1+1=2+0 is better then 1+2=2+1
			  int dVarIndex = 0;
			  List<IntExpr> allDVars = new ArrayList<>();
			  
			  for (ProjectionConsistencyInfoPair projectionConsistencyInfoPair : projectionConsistencyInfoPairs) {
					ProjectionConsistencyInfo c1ProjectionConsistencyInfo = projectionConsistencyInfoPair.getFirst();
					Set<IntExpr> projVars = c1ProjectionConsistencyInfo.projVars;
					if (projVars.size() != 0 && c1ProjectionConsistencyInfo.nonAggVars.size() != 0) {
						IntExpr dVar = ctx.mkIntConst("d_var" + dVarIndex++);
						allDVars.add(dVar);
						Set<IntExpr> nonAggVars = new HashSet<>(c1ProjectionConsistencyInfo.nonAggVars);
						ArithExpr nonAggVarsSum = ctx.mkAdd(nonAggVars.toArray(new ArithExpr[nonAggVars.size()]));
						ctx.mkEq(dVar, ctx.mkSub(nonAggVarsSum, ctx.mkAdd(projVars.toArray(new ArithExpr[projVars.size()]))));
					}
					
					ProjectionConsistencyInfo c2ProjectionConsistencyInfo = projectionConsistencyInfoPair.getFirst();
					projVars = c2ProjectionConsistencyInfo.projVars;
					if (projVars.size() != 0 && c2ProjectionConsistencyInfo.nonAggVars.size() != 0) {
						IntExpr dVar = ctx.mkIntConst("d_var" + dVarIndex++);
						allDVars.add(dVar);
						Set<IntExpr> nonAggVars = new HashSet<>(c2ProjectionConsistencyInfo.nonAggVars);
						ArithExpr nonAggVarsSum = ctx.mkAdd(nonAggVars.toArray(new ArithExpr[nonAggVars.size()]));
						ctx.mkEq(dVar, ctx.mkSub(nonAggVarsSum, ctx.mkAdd(projVars.toArray(new ArithExpr[projVars.size()]))));
					}
			  }
			  
			  ArithExpr objective = null;
			  if (allDVars.size() > 0) {
			  	objective = ctx.mkMul(ctx.mkInt(-1), ctx.mkAdd(allDVars.toArray(new ArithExpr[allDVars.size()])));
			  	if (allSlackVars.size() > 0)
			  		objective = ctx.mkAdd(objective, ctx.mkAdd(allSlackVars.toArray(new ArithExpr[allSlackVars.size()])));
			  }
			  
			  if (objective != null)
			  	solver.MkMinimize(objective);
			  
			///////////////// End dk			
			  List<String> allIntervalRegions = new ArrayList<>(); // List of all intervals
			  List<String> allIntervalisedRegions = new ArrayList<>(); // List of all intervalised regions
			  List<String> allDxValues = new ArrayList<>();
			
			  if(PostgresVConfig.hydraVersions.contains(PostgresVConfig.HydraTypes.duplicationHydra)) {
			  
			  // New variables
			 Map<String,List<String>> allIntervalRegionsVariables = new HashMap<>();			 
			 Map<String, List<String>> allDxValuesVariables = new HashMap<>();
			 Map<String, List<String>> allIntervalisedRegionsVariables = new HashMap<>();
			 Map<String, HashMap<String, List<Integer>>> varToIntervalMapPerFKey = new HashMap<>();
			 			  
			  if(PostgresVConfig.fkeyToBorrowedAttr.containsKey(viewname)) {
				  
				  				  
				  Map<String, Set<String>> fkeyToBorrowedAttr = PostgresVConfig.fkeyToBorrowedAttr.get(viewname);
			  
				  for(String fkey : fkeyToBorrowedAttr.keySet()) {
					  
					  allIntervalRegionsVariables.put(fkey, new ArrayList<>());
					  allDxValuesVariables.put(fkey, new ArrayList<>());
					  allIntervalisedRegionsVariables.put(fkey, new ArrayList<>());
					  varToIntervalMapPerFKey.put(fkey, new HashMap<>());
					  Set<String> currentClique = null; 
					  Integer currentCliqueIdx = null;
					  
					  for(int c=0; c <  this.arasuCliques.size(); c++ ) {
						  Set<String> clique = this.arasuCliques.get(c);
						  if(!cliquesToFKeyCoverage.containsKey(clique)) {
							  continue;
						  }
						  Set<String> fkeysCovered = cliquesToFKeyCoverage.get(clique);
						  if(fkeysCovered.contains(fkey)) {
							  currentClique = clique;
							  currentCliqueIdx = c;
							  break;
						  }						  
					  }					  
					  if(currentClique == null) {
						  throw new RuntimeException("Something wrong can't be possible");
					  }
					  
					  fkeyToCliqueIdx.put(fkey, currentCliqueIdx);
					  
					  Set<String> borrowedAttr = fkeyToBorrowedAttr.get(fkey);
					  List<String> sortedBorrowedAttr = new ArrayList<>(borrowedAttr);
					  List<Integer> borrowedAttrIdx = new ArrayList<>();
					  Collections.sort(sortedBorrowedAttr);
					  int c=0;
					  for(int i=0; i < sortedViewColumns.size(); i++) {
						  
						  if(sortedBorrowedAttr.get(c).contentEquals(sortedViewColumns.get(i))){
							  
							  borrowedAttrIdx.add(i);
							  c = c + 1;
						  }
						  if(c == sortedBorrowedAttr.size()) {
							  break;
						  }
						  
					  }
					  
					  int noOfIntervalRegions = 1;
					  List<List<Integer>> borrowedAttrIntervals  = new ArrayList<>();
					  Partition partition = cliqueIdxtoPList.get(currentCliqueIdx);
					  for(int bucket : borrowedAttrIdx) {
							
							Set<Integer> intervals = new HashSet<>();
							for(Region r : partition.getAll()) {
								
								for(BucketStructure bs : r.getAll()) {
									
									intervals.addAll((bs.at(bucket).getAll()));
									
								}
							}
							noOfIntervalRegions*=intervals.size();
							ArrayList<Integer> intervalsList = new ArrayList<>(intervals);
							Collections.sort(intervalsList);
							borrowedAttrIntervals.add(intervalsList);
							}
					  
					  List<List<Integer>> intervalRegions = new ArrayList<>();
					    for(int i=0; i < noOfIntervalRegions; i++) {
					    	
					    	intervalRegions.add(new ArrayList<>());					    	
					  }
					    
					    int count=0;
					    int row = 0;
					    while(count < noOfIntervalRegions) {
					    	
					    	int currentRowSize = borrowedAttrIntervals.get(row).size();
					    	
					    	if(count > 0) {
					    		
					    		int currentIndex=0;
								List<List<Integer>> copyofIntervalRegionList = new ArrayList<>();
								for(int i=0;i<intervalRegions.size();i++) {
									List<Integer> temp = new ArrayList<Integer>();
									copyofIntervalRegionList.add(temp);
									for(int j=0; j<intervalRegions.get(i).size(); j++) {
										  temp.add(intervalRegions.get(i).get(j));
									  }								
									
								}
								for(int j=0; j<currentRowSize; j++) {
									  Integer val = borrowedAttrIntervals.get(row).get(j);
									  for(int i=0;i<count;i++) {
										  List<Integer> w = new ArrayList<>(copyofIntervalRegionList.get(i));
										  w.add(val);
										  intervalRegions.set(currentIndex, w);
										  currentIndex++;
									  }
								}
								row = row + 1;
								count*=currentRowSize;
					    							    		
					    	}
					    	else {
					    		
					    		int currentIndex = 0;
					    		for(int j=0; j < currentRowSize; j++) {
					    			
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
					    for(int i=0; i< intervalRegions.size();i ++) {
					    	String intervalname =  fkey +  "_clique" + currentCliqueIdx + "interval" + i;
					    	allIntervalRegionsVariables.get(fkey).add(intervalname);
				    		Z3name.put(i, intervalname);
					    }
					    
					    
					    // Adding sum of all intervals to total tuple cout
					    ArithExpr[] sumOfIntervalRegions = new ArithExpr[intervalRegions.size()]; 
					    c = 0;
					    allIntervalRegionsPerFKey.put(fkey, intervalRegions);
					    for(Integer interval : Z3name.keySet()) {
					    	
					    	String intervalName = Z3name.get(interval);
					    	solver.Add(ctx.mkGe(ctx.mkIntConst(intervalName), ctx.mkInt(0)));
					    	allIntervalRegions.add(intervalName);
					    	sumOfIntervalRegions[c++] = ctx.mkIntConst(intervalName);
					    	
					    }
					    
					    c=0;
					    ArithExpr[] sumOfPartitionedRegions = new ArithExpr[partition.size()];
					    for(int r=0; r < partition.size(); r++){
					    	
					    	String varname = "var" + currentCliqueIdx + "_" + r;
					    	varToIntervalMapPerFKey.get(fkey).put(varname, new ArrayList<>());
					    	sumOfPartitionedRegions[c++] = ctx.mkIntConst(varname);
					    	
					    }
					    //    adding all vars = all clique intervals
					    solver.Add(ctx.mkEq(ctx.mkAdd(sumOfPartitionedRegions), ctx.mkAdd(sumOfIntervalRegions)));
					    
					    fkeyToActualInteervalisedRegMap.put(fkey,intervalisedRegionMap);
					    Map<Integer,List<String>> intervalRegionToPartionedRegionsMap = new HashMap<>();
					    for(int r=0; r < partition.size(); r++) {
					    	
					    	Region region = partition.at(r);
					    	String regionName =  "var" + currentCliqueIdx + "_" + r;
					    	List<String> regionPartitionList = new ArrayList<>();
					    	for(int i=0; i < intervalRegions.size(); i++) {
					    		
					    		List<Integer> intervalRegion = intervalRegions.get(i);
						    	boolean flag = false;
						    	int bsIdx = 0;
						    	
					    		for(BucketStructure bs : region.getAll()) {
					    			
					    			c = 0;
						    		for(int bucketIdx : borrowedAttrIdx) {
						    			Bucket bucket = bs.at(bucketIdx);
						    			if(bucket.contains(intervalRegion.get(c))) {
						    				c = c + 1;
						    			}
						    			else {
						    				
						    				break;
						    			}
						    		}
						    		
						    		if(c == borrowedAttrIdx.size()) {
						    			flag = true;
						    			break;
						    		}
						    		bsIdx++;
					    			
					    		}
					    		
					    		if(flag) {
					    			String intervalisedRegionName =fkey + "_var" + currentCliqueIdx + "_" + r + "_interval_" + i ;
					    			BucketStructure bucketStructure = region.at(bsIdx);
					    			BucketStructure bsNew  = new BucketStructure();
					    			
					    			int ci=0;
					    			for(int bi=0; bi < bucketStructure.size(); bi++) {
					    				
					    				Bucket bucket = new Bucket();
					    				if(bi == borrowedAttrIdx.get(ci)){
					    					bucket.add(intervalRegion.get(ci));
					    				}
					    				else {
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
					    			if(!intervalRegionToPartionedRegionsMap.containsKey(i)) {
					    				intervalRegionToPartionedRegionsMap.put(i, new ArrayList<>());
					    			}
					    			intervalRegionToPartionedRegionsMap.get(i).add(intervalisedRegionName);
					    			solver.Add(ctx.mkGe(ctx.mkIntConst(intervalisedRegionName), ctx.mkInt(0)));
						    	}
					    		
					    	}
					    	
					    	ArithExpr[] regionPartitionArray = new ArithExpr[regionPartitionList.size()];
					    	for(int i=0; i < regionPartitionList.size(); i++) {
					    		
					    		regionPartitionArray[i] = ctx.mkIntConst(regionPartitionList.get(i));
					    		
					    	}
					    	
					    	// sum  of intervalised regions = var
					    	solver.Add(ctx.mkEq(ctx.mkAdd(regionPartitionArray), ctx.mkIntConst(regionName)));
					    	
					    }					    
					    
					    System.out.print("");
					    
					    
					    for(int intervalIdx : intervalRegionToPartionedRegionsMap.keySet()) {
					    	
					    	
					    	List<String> regionNames =  intervalRegionToPartionedRegionsMap.get(intervalIdx);
					    	
					    	ArithExpr[] regionArray =  new ArithExpr[regionNames.size()];
					    	for(int i=0; i < regionNames.size(); i++) {
					    		regionArray[i] = ctx.mkIntConst(regionNames.get(i));
					    	}
					    	
					    	solver.Add(ctx.mkEq( ctx.mkAdd(regionArray), ctx.mkIntConst(Z3name.get(intervalIdx))));
					    					    	
					    }					    
					    
					    JSONArray dfVector = PostgresVConfig.fkeySkewVectors.getJSONObject(viewname).getJSONArray(fkey);
				    	JSONArray d = dfVector.getJSONArray(0);
						JSONArray f = dfVector.getJSONArray(1);
												
						for(Integer i = 0; i < intervalRegions.size(); i++) {
							ArithExpr[] dxSumm = new ArithExpr[d.length()];
							for(int d_i=0; d_i < d.length(); d_i++){
								
								 
								 String x = fkey + "_interval_" + i  + "_d_" + d_i;
								 solver.Add(ctx.mkGe(ctx.mkIntConst(x), ctx.mkInt(0)));
								 allDxValuesVariables.get(fkey).add(x);
								 allDxValues.add(x);
				    	    	 ArithExpr xd = ctx.mkMul(ctx.mkIntConst(x), ctx.mkInt(d.getInt(d_i)));
				    	    	 dxSumm[d_i] = xd;
								
							}
						String intervalname = Z3name.get(i);
							solver.Add(ctx.mkEq(ctx.mkAdd(dxSumm),ctx.mkIntConst(Z3name.get(i))));
						}
						
						for(int d_i=0; d_i < d.length(); d_i++) {
				    		
				    		ArithExpr[] xfSumm = new ArithExpr[intervalRegions.size()];
				    		for(int i=0; i < intervalRegions.size(); i++) {
				    			
				    			String x = fkey + "_interval_" + i  + "_d_" + d_i;
				    			xfSumm[i] = ctx.mkIntConst(x);
				    			
				    		}
				    		
				    	 solver.Add(ctx.mkEq(ctx.mkAdd(xfSumm),ctx.mkInt(f.getInt(d_i))));
				    	}
					}
									  
				  // Adding equations for CCs skew
				  
				  Map<String, Map<String, Set<String>>> fkeyToBR = PostgresVConfig.fkeyToBorrowedAttr;
				  for(FormalCondition condition : conditions) {
					  
					  Integer counter = condition.getCounter();
					  String queryname = condition.getQueryname();
					  List<FormalCondition> conditionList = new ArrayList<>();
					  conditionList.add(condition);
					  String fkey = findFkey(conditionList);	
					  // CC having no foreign key column
					  if(fkey == null) {
						  continue;
					  }
					  // No borrowed attr for fkey
					  if(!fkeyToBR.containsKey(fkey)) {
						  continue;
					  }
					  String actualFKey = PostgresVConfig.reverseColumnAnonyMap.get(fkey);
					  String dfVec = actualFKey  + "___" + counter + "_" + queryname;
					  
					  
					  DFvector dfvector = PostgresVConfig.ccsDFvectors.get(dfVec);
					  List<Long> dValues = dfvector.getD();
					  List<Long> fValues = dfvector.getF();
					  List<List<Integer>> intervalRegions = this.allIntervalRegionsPerFKey.get(fkey);
					  //String x = fkey + "_interval_" + i  + "_d_" + d_i;
					  
					  // find CCs intersecting with intervals
					  
					  Map<String, Region> intervalisedRegions = this.fkeyToActualInteervalisedRegMap.get(fkey);
					  Set<Integer> intersectingIntervals = findCCsIntersectingWithIntervals(condition,intervalisedRegions);
					  
					  
					  JSONArray fkeyBaseSkewVectors = PostgresVConfig.fkeySkewVectors.getJSONObject(viewname).getJSONArray(fkey);
					  JSONArray baseDValues = fkeyBaseSkewVectors.getJSONArray(0);
					  JSONArray baseFValues = fkeyBaseSkewVectors.getJSONArray(1);
					  
					  
					  
					  long fCount = 0;
					  for(int di=0; di < dValues.size(); di++) {
						  
						  Long fVal = fValues.get(di);
						  Long dVal = dValues.get(di);
						  ArithExpr[] dxArray =  new ArithExpr[intersectingIntervals.size()];
						  for(int bdi=0; bdi < baseDValues.length(); bdi++) {
							  long baseDval = baseDValues.getLong(bdi);
							  if(baseDval < dVal) {
								  break;
							  }
							  else {
								  
								  
								  int c=0;
								  for(int intervalIdx : intersectingIntervals) {
									  
									  dxArray[c] = ctx.mkIntConst(fkey + "_interval_" + intervalIdx  + "_d_" + di);
									  c = c + 1;
								  }
								  
							  }
							  
						  }
						 
						  
						 solver.Add(ctx.mkGe(ctx.mkAdd(dxArray),ctx.mkInt(fVal - fCount)));
						 fCount += fVal;
						  						  
					  }					  
					  System.out.print("");
				}
			}
			}
				  
			  onlyFormationSW.displayTimeAndDispose();
			  			  
			  //Dumping LP into a file -- Anupam
			  //start
//			  FileWriter fw;
//				try {
//					fw = new FileWriter("lpfile-"+viewname+".txt");
//					fw.write(solver.toString());
//			      fw.close();
//				} catch (IOException e) {
//					// TODO Auto-generated catch block
//					e.printStackTrace();
//				} 
//			  System.err.println(solver.toString());
			  //stop
			  
			  StopWatch onlySolvingSW = new StopWatch("ByMJ LP-OnlySolving" + viewname);
			  
			  Status solverStatus = solver.Check();
			  DebugHelper.printInfo("Solver Status: " + solverStatus);
			
			  if (!Status.SATISFIABLE.equals(solverStatus)) {
			  	ctx.close();
			      throw new RuntimeException("solverStatus is not SATISFIABLE");
			  }
			  			  
			  Model model = solver.getModel();
			  
			  onlySolvingSW.displayTimeAndDispose();
			  
			  List<LinkedList<VariableValuePair>> cliqueIdxToVarValuesList = new ArrayList<>(cliqueCount);
			  for (int i = 0; i < cliqueCount; i++) {
			
			      IntList colIndxs = arasuCliquesAsColIndxs.get(i);
			      Partition partition = cliqueIdxtoPList.get(i);
			      LinkedList<VariableValuePair> varValuePairs = new LinkedList<>();
			      for (int j = 0; j < partition.size(); j++) {
			          String varname = "var" + i + "_" + j;
			       
			  		  long rowcount = Long.parseLong(model.evaluate(ctx.mkIntConst(varname), true).toString());
			       
			          if (rowcount != 0) {
			              Region variable = getTruncatedRegion(partition.at(j), colIndxs);
			              VariableValuePair varValuePair = new VariableValuePair(variable, rowcount);
			              varValuePairs.add(varValuePair);
			          }
			      }
			      cliqueIdxToVarValuesList.add(varValuePairs);
			  }
			  
			  
			  if(PostgresVConfig.hydraVersions.contains(PostgresVConfig.HydraTypes.duplicationHydra)) {
				  long sumOfIntervalRegion = 0;
				  for(int i=0; i < allIntervalRegions.size(); i++) {
					  
					  // t17_c001_clique0interval8
					  long val = Long.parseLong(model.evaluate(ctx.mkIntConst(allIntervalRegions.get(i)), true).toString());
					  if(val==0) {
						  continue;
					  }
					  
					  String interval = allIntervalRegions.get(i);
					  String fkey = interval.split("_clique")[0];
					  
					  this.allIntervalRegionValueMap.put(allIntervalRegions.get(i), val);
					  sumOfIntervalRegion += val;
					  if(!this.fkeyToIntervalRegionMap.containsKey(fkey)) {
						  this.fkeyToIntervalRegionMap.put(fkey, new ArrayList<>());
					  }
					  this.fkeyToIntervalRegionMap.get(fkey).add(interval);					  
				  }				  
				  long sumOfIntervalisedRegion = 0;
				  				  
				  for(int i=0; i < allIntervalisedRegions.size(); i++ ) {
					  long val = Long.parseLong(model.evaluate(ctx.mkIntConst(allIntervalisedRegions.get(i)), true).toString());
					  if(val==0) {
						  continue;
					  }
					  
					  String intervalisedRegion = allIntervalisedRegions.get(i);
					  
					  this.allIntervalisedRegionsMap.put(allIntervalisedRegions.get(i), val);
					  sumOfIntervalisedRegion += val;
					  
					  String fkey =  intervalisedRegion.split("_var")[0];
					  String varname = intervalisedRegion.split("_")[2] + "_" + intervalisedRegion.split("_")[3]; 
					  
					  if(!varToIntervalisedRegionMapPerFkey.containsKey(fkey)) {
						  varToIntervalisedRegionMapPerFkey.put(fkey, new HashMap<>());
					  }
					  if(!varToIntervalisedRegionMapPerFkey.get(fkey).containsKey(varname)) {
						  varToIntervalisedRegionMapPerFkey.get(fkey).put(varname,new ArrayList<>());
					  }
					  varToIntervalisedRegionMapPerFkey.get(fkey).get(varname).add(intervalisedRegion);
										  
				  }
				  				  
				  for(int i=0; i < allDxValues.size(); i++) {
					  //t17_c018_interval_0_d_0
					  long val = Long.parseLong(model.evaluate(ctx.mkIntConst(allDxValues.get(i)), true).toString());
					  if(val==0) {
						  continue;
					  }
					  
					  this.allDxValuesMap.put(allDxValues.get(i), val);
					  String dxValue = allDxValues.get(i);
					  String fkey =  dxValue.split("_interval_")[0];
					  int intervalIdx = Integer.parseInt(dxValue.split("_")[3]) ;
					  if(!intervalToDxValuePerFkey.containsKey(fkey)) {
						  intervalToDxValuePerFkey.put(fkey, new HashMap<>());
					  }
					  if(!intervalToDxValuePerFkey.get(fkey).containsKey(intervalIdx)) {
						  intervalToDxValuePerFkey.get(fkey).put(intervalIdx, new ArrayList<>());
					  }
					  intervalToDxValuePerFkey.get(fkey).get(intervalIdx).add(dxValue);
					  
				  }
			  }
			  
			/*        
			  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
			  // DIRTY START DIRTY START DIRTY START DIRTY START DIRTY START DIRTY START DIRTY START DIRTY START DIRTY START DIRTY START DIRTY START 
			  
			  StopWatch onlyPhase2SW = new StopWatch("onlyPhase2SW " + viewname);
			  
			  HashMap<String, HashMap<Region, List<ProjectionConsistencyInfoPair>>> columnWSSPRegionToAllProjectionConsistencyInfoPairs = new HashMap<>();
			  for (ProjectionConsistencyInfoPair projectionConsistencyInfoPair : projectionConsistencyInfoPairs) {
			  	HashMap<Region, List<ProjectionConsistencyInfoPair>> sspRegionToAllProjectionConsistencyInfoPairs = columnWSSPRegionToAllProjectionConsistencyInfoPairs.get(projectionConsistencyInfoPair.columnname);
			  	if (sspRegionToAllProjectionConsistencyInfoPairs == null) {
			  		sspRegionToAllProjectionConsistencyInfoPairs = new HashMap<>();
			  		columnWSSPRegionToAllProjectionConsistencyInfoPairs.put(projectionConsistencyInfoPair.columnname, sspRegionToAllProjectionConsistencyInfoPairs);
			  	}
			  	IntExpr aVar = null;
			  	ProjectionConsistencyInfo c1ProjectionConsistencyInfo = projectionConsistencyInfoPair.getFirst();
			  	if (c1ProjectionConsistencyInfo.aggVars.size() != 0) {
			  		aVar = c1ProjectionConsistencyInfo.aggVars.iterator().next();
			  	} else if (c1ProjectionConsistencyInfo.nonAggVars.size() != 0) {
			  		aVar = c1ProjectionConsistencyInfo.nonAggVars.iterator().next();
			  	} else
			  		DirtyCode.throwError("Should not happen!");
			
			  	HashMap<Region, ProjectionStuffInSSPRegion> sspRegionToProjectionStuff = cliqueWColumnWProjectionStuff.get(projectionConsistencyInfoPair.getFirst().cindex).get(projectionConsistencyInfoPair.columnname).getMapSSPRegionToProjectionStuff();
			  	List<ProjectionConsistencyInfoPair> listOfProjectionConsistencyInfoPairs = getCorrespondingRegionList(sspRegionToAllProjectionConsistencyInfoPairs, sspRegionToProjectionStuff, aVar);
					listOfProjectionConsistencyInfoPairs.add(projectionConsistencyInfoPair);
				}
			  
			  for (int i = 0; i < cliqueCount; i++) {
			  	HashMap<String, ProjectionStuffInColumn> columnWiseProjectionStuff = cliqueWColumnWProjectionStuff.get(i);
					for (ProjectionStuffInColumn projectionStuffInColumn : columnWiseProjectionStuff.values()) {
						projectionStuffInColumn.updateAggVarToProjVarOfProjectionStuffInSSPRegion();
					}
			  }
			
				// Assigning intervals to projVars and finding MaxUniqePoints per sspRegion
			  List<HashMap<IntExpr, DirtyValueInterval>> cliqueWiseProjVarToInterval = new ArrayList<>();
			  HashMap<String, HashMap<Region, Long>> columnWSSPRegionToMaxUniqePoints = new HashMap<>();
			  
			  if (false)
			  // heuristic
			  	createProjVarToIntervalAndSSPRegionToMaxUniquePoints_hueristic(model, ctx, cliqueWiseProjVarToInterval, columnWSSPRegionToAllProjectionConsistencyInfoPairs, cliqueWColumnWProjectionStuff, columnWSSPRegionToMaxUniqePoints);
			  // sequential
			  else
			  	createProjVarToIntervalAndSSPRegionToMaxUniquePoints_sequential(model, ctx, cliqueWiseProjVarToInterval, cliqueWColumnWProjectionStuff, columnWSSPRegionToMaxUniqePoints);
			  
			  List<HashMap<IntExpr, ProjectionValues>> cliqueWAggAndNonAggVarsToProjectionValues= new ArrayList<>(cliqueCount);
			  for (int i = 0; i < cliqueCount; ++i)
			  	cliqueWAggAndNonAggVarsToProjectionValues.add(new HashMap<>());
			  
			  // Projection consistency Phase 2
			  for (Entry<String, HashMap<Region, List<ProjectionConsistencyInfoPair>>> outerEntry : columnWSSPRegionToAllProjectionConsistencyInfoPairs.entrySet()) {
					String columnname = outerEntry.getKey();
					HashMap<Region, List<ProjectionConsistencyInfoPair>> sspRegionToAllProjectionConsistencyInfoPairs = outerEntry.getValue();
					HashMap<Region, Long> sspRegionToMaxUniqePoints = columnWSSPRegionToMaxUniqePoints.get(columnname);
			  	int colIndx = sortedViewColumns.indexOf(columnname);
					for (Entry<Region, List<ProjectionConsistencyInfoPair>> innerEntry : sspRegionToAllProjectionConsistencyInfoPairs.entrySet()) {
						Region region = innerEntry.getKey();
						Long maxUniqePoints = sspRegionToMaxUniqePoints.get(region);
						if (maxUniqePoints == 0)
							continue;
						
						// TODO: Problem: LongIndexNeeded : Need to change this code because using long array indexes!
						long maxint = Integer.MAX_VALUE;
						if (maxUniqePoints.longValue() >= maxint)
							DirtyCode.throwError("problem");
						
						List<ProjectionConsistencyInfoPair> listProjectionConsistencyInfoPairs = innerEntry.getValue();
						
						Map<String, String> contextmapTemp = new HashMap<>();
				        contextmapTemp.put("model", "true");
				        contextmapTemp.put("unsat_core", "true");
				        Context ctxPhase2 = new Context(contextmapTemp);
				        Solver solverPhase2 = ctxPhase2.mkSolver();
				        
				        IntNum zero = ctxPhase2.mkInt(0);
				        
				        List<List<IntExpr>> c1PointWListOfNewVars = new ArrayList<>((int)maxUniqePoints.longValue());			// value of point - list of vars
				        List<List<IntExpr>> c2PointWListOfNewVars = new ArrayList<>((int)maxUniqePoints.longValue());			// value of point - list of vars
						for(int i = 0; i < (int)maxUniqePoints.longValue(); ++i) {
							c1PointWListOfNewVars.add(new ArrayList<>());
							c2PointWListOfNewVars.add(new ArrayList<>());
						}
						
				        for (ProjectionConsistencyInfoPair pInfoPair : listProjectionConsistencyInfoPairs) {
				        	ProjectionConsistencyInfo c1ProjectionConsistencyInfo = pInfoPair.getFirst();
				        	ProjectionConsistencyInfo c2ProjectionConsistencyInfo = pInfoPair.getSecond();
				        	createPointWiseConstraints(model, solverPhase2, ctxPhase2, c1ProjectionConsistencyInfo, cliqueWColumnWProjectionStuff, cliqueWiseProjVarToInterval, c1PointWListOfNewVars, columnname, maxUniqePoints);
				        	createPointWiseConstraints(model, solverPhase2, ctxPhase2, c2ProjectionConsistencyInfo, cliqueWColumnWProjectionStuff, cliqueWiseProjVarToInterval, c2PointWListOfNewVars, columnname, maxUniqePoints);
			
				    		for(int i = 0; i < (int)maxUniqePoints.longValue(); ++i) {
				    			List<IntExpr> c1NewVars = c1PointWListOfNewVars.get(i);
				    			List<IntExpr> c2NewVars = c2PointWListOfNewVars.get(i);
				    			
				    			if (c1NewVars.isEmpty() && c2NewVars.isEmpty())
				    				continue;
				    			if (c1NewVars.isEmpty() || c2NewVars.isEmpty()) {
				    				if (c1NewVars.isEmpty() && containsOnlySlacks(c2NewVars))
				    					c1NewVars.add(zero);
				    				else if (c2NewVars.isEmpty() && containsOnlySlacks(c1NewVars))
				    					c2NewVars.add(zero);
				    				else
				    					DirtyCode.throwError("Phase 2: No space to multiply points!");
				    			}
				    			
				    			solverPhase2.add(ctxPhase2.mkEq(ctxPhase2.mkAdd(c1NewVars.toArray(new ArithExpr[c1NewVars.size()])), ctxPhase2.mkAdd(c2NewVars.toArray(new ArithExpr[c2NewVars.size()]))));
				    		}
				        }
				        
				        /////
				        long numberOfVars = 0;
				        for (List<IntExpr> list : c1PointWListOfNewVars) {
							numberOfVars += list.size();
						}
				        for (List<IntExpr> list : c2PointWListOfNewVars) {
							numberOfVars += list.size();
						}
				        System.out.println("Number of variables for phase 2: " + numberOfVars + " , maxUniqePoints: " + maxUniqePoints);
				        /////
				        
						
						if (solverPhase2.check() != Status.SATISFIABLE)
							DirtyCode.throwError("Phase 2 Unsatisfiable!!");
						Model modelTemp = solverPhase2.getModel();
				        
						// Assigning projection intervals with number of occurrences (count) to regions (vars)
						// To AggVars
						for (int cindex = 0; cindex < cliqueCount; ++cindex) {
							ProjectionStuffInColumn projectionStuffInColumn = cliqueWColumnWProjectionStuff.get(cindex).get(columnname);
							if (projectionStuffInColumn == null)
								continue;
							ProjectionStuffInSSPRegion projectionStuffInSSPRegion = projectionStuffInColumn.getProjectionStuffInSSPRegion(region);
							HashMap<IntExpr, DirtyValueInterval> projVarToInterval = cliqueWiseProjVarToInterval.get(cindex);
							HashMap<IntExpr, ProjectionValues> varsToProjectionValues = cliqueWAggAndNonAggVarsToProjectionValues.get(cindex);
				        	createAggVarsToProjectionValues(model, ctxPhase2, modelTemp, projectionStuffInSSPRegion, projVarToInterval, columnname, maxUniqePoints, varsToProjectionValues, colIndx, cindex);
						}
						
						List<Set<Integer>> cliqueWSlackVarsIndexes = new ArrayList<>(cliqueCount);
						for (int i = 0; i < cliqueCount; ++i)
							cliqueWSlackVarsIndexes.add(new HashSet<>());
						
						for (ProjectionConsistencyInfoPair pInfoPair : listProjectionConsistencyInfoPairs) {
				        	ProjectionConsistencyInfo c1ProjectionConsistencyInfo = pInfoPair.getFirst();
				        	cliqueWSlackVarsIndexes.get(c1ProjectionConsistencyInfo.cindex).addAll(c1ProjectionConsistencyInfo.slackVarsIndexes);
				        	ProjectionConsistencyInfo c2ProjectionConsistencyInfo = pInfoPair.getSecond();
				        	cliqueWSlackVarsIndexes.get(c2ProjectionConsistencyInfo.cindex).addAll(c2ProjectionConsistencyInfo.slackVarsIndexes);
						}
						
						// To NonAggVars
						for (int cindex = 0; cindex < cliqueCount; ++cindex) {
							ProjectionStuffInColumn projectionStuffInColumn = cliqueWColumnWProjectionStuff.get(cindex).get(columnname);
							if (projectionStuffInColumn == null)
								continue;
							HashMap<IntExpr, ProjectionValues> varsToProjectionValues = cliqueWAggAndNonAggVarsToProjectionValues.get(cindex);
							Set<Integer> slackVarsIndexes = cliqueWSlackVarsIndexes.get(cindex);
							createNonAggVarsToProjectionValues(model, ctxPhase2, modelTemp, projectionStuffInColumn, slackVarsIndexes, columnname, maxUniqePoints, varsToProjectionValues, colIndx, cindex);
						}
					}
				}
			  
			  onlyPhase2SW.displayTimeAndDispose();
			  
			  // Assigning intervals to aggVars of those columns which have not taken part in any of the consistency constraints
			  Set<String> projColsTakingPartInConsistency = columnWSSPRegionToAllProjectionConsistencyInfoPairs.keySet();
			  Set<String> projColsNotTakingPartInConsistency = columnWSSPRegionToMaxUniqePoints.keySet();
			  projColsNotTakingPartInConsistency.removeAll(projColsTakingPartInConsistency);
			  for (int cIndex = 0; cIndex < cliqueCount; ++cIndex) {
			  	HashMap<String, ProjectionStuffInColumn> columnWProjectionStuff = cliqueWColumnWProjectionStuff.get(cIndex);
			  	HashMap<IntExpr, ProjectionValues> varsToProjectionValues = cliqueWAggAndNonAggVarsToProjectionValues.get(cIndex);
			  	HashMap<IntExpr, DirtyValueInterval> projVarToInterval = cliqueWiseProjVarToInterval.get(cIndex);
			  	for (String columnname : projColsNotTakingPartInConsistency) {
			  		ProjectionStuffInColumn projectionStuffInColumn = columnWProjectionStuff.get(columnname);
			  		if (projectionStuffInColumn == null)
			  			continue;
			  		int colIndx = sortedViewColumns.indexOf(columnname);
			  		for (Entry<IntExpr, List<IntExpr>> entry : projectionStuffInColumn.getAggVarsToProjVars().entrySet()) {
							IntExpr aggVar = entry.getKey();
			  			long rowcount = Long.parseLong(model.evaluate(aggVar, true).toString());
			  			if (rowcount > 0) {
			  				long leftover = rowcount;
			  				List<IntExpr> projVars = entry.getValue();
			  				ProjectionValues projectionValues = getOrAdd(varsToProjectionValues, aggVar);
			  				Iterator<IntExpr> it = projVars.iterator();
			  				DirtyValueInterval interval = null;
			  				do {
			  					interval = projVarToInterval.get(it.next());
			  				} while (interval == null);
			  				long firstStart = interval.start;
			  				long intervalSizeExceptFirstElement = interval.end - (interval.start + 1);		// Will repeat first element
			  				if (intervalSizeExceptFirstElement > 0) {
			  					projectionValues.addToList(colIndx, interval.start + 1, interval.end, 1);
			  					leftover -= intervalSizeExceptFirstElement;
			  				}
			  				while (it.hasNext()) {
			  					interval = projVarToInterval.get(it.next());
			  					if (interval != null) {
			  						projectionValues.addToList(colIndx, interval.start, interval.end, 1);
			  						leftover -= interval.end - interval.start;
			  					}
			  				}
			  				projectionValues.addToList(colIndx, firstStart, firstStart + 1, leftover);	// Repeating first element leftover times
			  			}
						}
					}
			  }
			  
			  // Creating region to Value list
			  List<LinkedList<DirtyVariableValuePairWithProjectionValues>> dirtyCliqueIdxToVarValuesList = new ArrayList<>(cliqueCount);
			  for (int i = 0; i < cliqueCount; i++) {
			      IntList colIndxs = arasuCliquesAsColIndxs.get(i);
			      Partition partition = cliqueIdxtoPList.get(i);
			  	HashMap<IntExpr, ProjectionValues> aggAndNonAggVarsToProjectionValues = cliqueWAggAndNonAggVarsToProjectionValues.get(i);
					
			      LinkedList<DirtyVariableValuePairWithProjectionValues> varValuePairs = new LinkedList<>();
			      
			      for (int j = 0; j < partition.size(); j++) {
			          String varname = "var" + i + "_" + j;
						IntExpr var = ctx.mkIntConst(varname);
			          long rowcount = Long.parseLong(model.evaluate(var, true).toString());
			          if (rowcount != 0) {
			          	ProjectionValues projectionValues = aggAndNonAggVarsToProjectionValues.get(var);	// Could be null because of nonAggVars
			              Region region = getTruncatedRegion(partition.at(j), colIndxs);
			              DirtyVariableValuePairWithProjectionValues varValuePair = new DirtyVariableValuePairWithProjectionValues(region, rowcount, projectionValues);
			              varValuePair.doSanityCheck(colIndxs);
			              varValuePairs.add(varValuePair);
			          }
			      }
			      dirtyCliqueIdxToVarValuesList.add(varValuePairs);
			  }
			
			  IntList dirtyMergedColIndxs = new IntArrayList();
			  List<DirtyValueCombinationWithProjectionValues> dirtyMergedValueCombinations = new ArrayList<>();
			  dirtyMergedColIndxs.addAll(arasuCliquesAsColIndxs.get(0));
			
			  //Instantiating variables of first clique
			  for (DirtyVariableValuePairWithProjectionValues varValuePair : dirtyCliqueIdxToVarValuesList.get(0)) {
			      IntList columnValues = getFloorInstantiation(varValuePair.variable);
			      DirtyValueCombinationWithProjectionValues valueCombination = new DirtyValueCombinationWithProjectionValues(columnValues, varValuePair.rowcount, varValuePair.getProjectionValues());
			      dirtyMergedValueCombinations.add(valueCombination);
			  }
			  
			  // merging with other cliques
			  for (int i = 1; i < cliqueCount; i++) {
			      dirtyMergeWithAlignment(dirtyMergedColIndxs, dirtyMergedValueCombinations, arasuCliquesAsColIndxs.get(i), dirtyCliqueIdxToVarValuesList.get(i));
			  }
			  
			  
			  for (ListIterator<DirtyValueCombinationWithProjectionValues> iter = dirtyMergedValueCombinations.listIterator(); iter.hasNext();) {
			  	DirtyValueCombinationWithProjectionValues dirtyValueCombination = iter.next();
			  	dirtyValueCombination = new DirtyValueCombinationWithProjectionValues(getReverseMappedValueCombination(dirtyValueCombination), dirtyValueCombination.getProjectionValues());
			  	dirtyValueCombination = new DirtyValueCombinationWithProjectionValues(getExpandedValueCombination(dirtyValueCombination), dirtyValueCombination.getProjectionValues());
			      iter.set(dirtyValueCombination);
			  }
			  
			  // Verifying count per agg condition
			  List<FormalCondition> allAggConditions = new ArrayList<>();
				for (FormalCondition formalCondition : conditions) {
					if (formalCondition instanceof FormalConditionAggregate)
						allAggConditions.add(formalCondition);
				}
				
				DirtyCode.debugSolvingErrorPerConditionForProjections(allAggConditions, dirtyMergedValueCombinations, sortedViewColumns);
				
			  /*
			  DirtyViewSolution viewSolution = new DirtyViewSolution(mergedValueCombinations);
			  DirtyDatabaseSummary.getInstance().addSummary(viewname, viewSolution);
			  /*
			  
			  // DIRTY END DIRTY END DIRTY END DIRTY END DIRTY END DIRTY END DIRTY END DIRTY END DIRTY END DIRTY END DIRTY END DIRTY END DIRTY END 
			  ////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
			*/
			  ctx.close();
			  return cliqueIdxToVarValuesList;
		
	}
	
	//changes by Manish starts for gurobi
	
	
	public List<LinkedList<VariableValuePair>> formAndSolveLP(ConsistencyMakerType consistencyMakerType,FormalCondition[] consistencyConstraints, 
			List<FormalCondition> conditions, HashMap<Set<String>, Set<String>> cliquesToFKeyCoverage) {
		
		StopWatch onlyFormationSW = new StopWatch("ByMJ LP-OnlyFormation" + viewname);
		
		Map<String, String> contextmap = new HashMap<>();
//		contextmap.put("model", "true");
//		contextmap.put("unsat_core", "true");
//		Context ctx = new Context(contextmap);

//		//Solver solver = ctx.mkSolver();
//		Optimize solver = ctx.mkOptimize();
		List<LinkedList<VariableValuePair>> cliqueIdxToVarValuesList = new ArrayList<>(cliqueCount);
		
		try {
			GRBEnv env = new GRBEnv();
			GRBModel model = new GRBModel(env);
	
			List<List<List<IntExpr>>> solverConstraintsRequiredForConsistency = new ArrayList<>();
			int projectionVarsIndex = 0;
			List<HashMap<String, ProjectionStuffInColumn>> cliqueWColumnWProjectionStuff = new ArrayList<>();
			int varsize = 0;
			for(int cliqueIndex = 0; cliqueIndex<cliqueCount; cliqueIndex++) {
				Partition partition = cliqueIdxtoPList.get(cliqueIndex);
				varsize+=partition.size();
			}
			GRBVar[] vars = new GRBVar[varsize];
			// Create lp variables for cardinality constraints
			for (int cliqueIndex = 0; cliqueIndex < cliqueCount; cliqueIndex++) {
				LongList bvalues = cliqueIdxtoConditionBValuesList.get(cliqueIndex);
				Partition partition = cliqueIdxtoPList.get(cliqueIndex);		// Partition is a list of regions corresponding to below labels
				List<IntList> conditionIdxsList = cliqueIdxtoPSimplifiedList.get(cliqueIndex);	// Getting label list for this clique
	
				HashMap<Integer, Integer> indexKeeper;
				int solverConstraintSize;
	  
				if (consistencyMakerType == ConsistencyMakerType.CONSISTENCYFILTERS) {
					indexKeeper = mappedIndexOfConsistencyConstraint.get(cliqueIndex);
					solverConstraintSize = bvalues.size() + indexKeeper.size();
					}
				else {
					indexKeeper = new HashMap<>();
					solverConstraintSize = bvalues.size() + cliqueWiseTotalSingleSplitPointRegions.get(cliqueIndex);
					}
	  
				List<List<GRBVar>> solverConstraints = new ArrayList<>(solverConstraintSize);
				for (int j = 0; j < solverConstraintSize; j++) {
					solverConstraints.add(new ArrayList<>());
				}
				
				
				for (int blockIndex = 0; blockIndex < partition.size(); blockIndex++) {
					String varname = "var" + cliqueIndex + "_" + blockIndex;
					solverStats.solverVarCount++;
	
				//Adding non-negativity constraints
	//				solver.Add(ctx.mkGe(ctx.mkIntConst(varname), ctx.mkInt(0)));
	
					
					vars[blockIndex] = model.addVar(0, GRB.INFINITY, 0, GRB.INTEGER, varname);
					for (IntIterator iter = conditionIdxsList.get(blockIndex).iterator(); iter.hasNext();) {
						int k = iter.nextInt();
						solverConstraints.get(k).add(vars[blockIndex]);
					}
					
				}
				//Adding normal constraints
				for (int conditionIndex = 0; conditionIndex < bvalues.size(); conditionIndex++) {
					long outputCardinality = bvalues.getLong(conditionIndex);
	//				List<IntExpr> addList = solverConstraints.get(conditionIndex);
	//				solver.Add(ctx.mkEq(ctx.mkAdd(addList.toArray(new ArithExpr[addList.size()])), ctx.mkInt(outputCardinality)));
					GRBLinExpr expr = new GRBLinExpr();
					for(int blockIndex = 0; blockIndex <solverConstraints.get(conditionIndex).size() ; blockIndex++ )
					{
						expr.addTerm(1, solverConstraints.get(conditionIndex).get(blockIndex));
					}
					model.addConstr(expr, GRB.EQUAL, outputCardinality, "" );
					solverStats.solverConstraintCount++;
				}
				onlyFormationSW.displayTimeAndDispose();
			///////////////// Start dk
//			if (consistencyMakerType == ConsistencyMakerType.CONSISTENCYFILTERS) {
//				List<List<IntExpr>> solverConstraintsToExport = new ArrayList<>(indexKeeper.size());
//				for(int j = bvalues.size(); j < solverConstraintSize; j++) {
//					solverConstraintsToExport.add(solverConstraints.get(j));
//				}
//				solverConstraintsToExport.add(solverConstraints.get(bvalues.size() - 1));   // Clique size
//				solverConstraintsRequiredForConsistency.add(solverConstraintsToExport);
//			}
		}
			StopWatch onlySolvingSW = new StopWatch("ByMJ LP-OnlySolving" + viewname);
			
			model.optimize();
			
			onlySolvingSW.displayTimeAndDispose();
			
//			for (int i =0; i<solverStats.solverVarCount; i++)
//			{	
//				System.out.println(vars[i].get(GRB.StringAttr.VarName)+ " " + vars[i].get(GRB.DoubleAttr.X));
//			}
			
//
//		///////////////// Start dk
//		DebugHelper.printInfo("variablesRequiredForProjection: " + projectionVarsIndex);
//
//		// Consistency
//		List<ProjectionConsistencyInfoPair> projectionConsistencyInfoPairs = new LinkedList<>();
//		int countConsistencyConstraint = 0;
//		if (consistencyMakerType == ConsistencyMakerType.CONSISTENCYFILTERS) {
//  
//			if(consistencyConstraints.length != 0 ) {
//				for (int c1index = 0; c1index < cliqueCount; c1index++) {
//					HashMap<Integer, Integer> c1indexKeeper = mappedIndexOfConsistencyConstraint.get(c1index);
//					if(c1indexKeeper.isEmpty())
//						continue;
//					List<List<IntExpr>> c1solverConstraints = solverConstraintsRequiredForConsistency.get(c1index);
//					for (int c2index = c1index + 1; c2index < cliqueCount; c2index++) {
//						HashMap<Integer, Integer> c2indexKeeper = mappedIndexOfConsistencyConstraint.get(c2index);
//						if(c2indexKeeper.isEmpty())
//							continue;
//						List<List<IntExpr>> c2solverConstraints = solverConstraintsRequiredForConsistency.get(c2index);
//						Set<Integer> applicableConsistencyConstraints = new HashSet<>(c1indexKeeper.keySet());
//						applicableConsistencyConstraints.retainAll(c2indexKeeper.keySet());
//						if(applicableConsistencyConstraints.isEmpty())
//							continue;
//						List<List<IntExpr>> c1ApplicableSolverConstraints = new ArrayList<>();
//						List<List<IntExpr>> c2ApplicableSolverConstraints = new ArrayList<>();
//						for (Integer originalConsistencyConstraintIndex : applicableConsistencyConstraints) {
//							c1ApplicableSolverConstraints.add(c1solverConstraints.get(c1indexKeeper.get(originalConsistencyConstraintIndex)));
//							c2ApplicableSolverConstraints.add(c2solverConstraints.get(c2indexKeeper.get(originalConsistencyConstraintIndex)));
//						}	
//				
//						c1ApplicableSolverConstraints.add(c1solverConstraints.get(c1solverConstraints.size() - 1));
//						c2ApplicableSolverConstraints.add(c2solverConstraints.get(c2solverConstraints.size() - 1));
//
//						HashMap<IntList, MutablePair<List<IntExpr>, List<IntExpr>>> conditionListToPairOfVarList = new HashMap<>();
//						addTo_ConditionListToPairOfVarList(c1ApplicableSolverConstraints, conditionListToPairOfVarList);
//						addTo_ConditionListToPairOfVarList(c2ApplicableSolverConstraints, conditionListToPairOfVarList);
//				
//						Set<String> commonCols = new HashSet<>(arasuCliques.get(c1index));
//						commonCols.retainAll(arasuCliques.get(c2index));
//				
//						for (MutablePair<List<IntExpr>, List<IntExpr>> pair : conditionListToPairOfVarList.values()) {
//							List<IntExpr> c1Set = pair.getFirst();
//							List<IntExpr> c2Set = pair.getSecond();
//							ArithExpr set1expr = ctx.mkAdd(c1Set.toArray(new ArithExpr[c1Set.size()]));
//							ArithExpr set2expr = ctx.mkAdd(c2Set.toArray(new ArithExpr[c2Set.size()]));
//							solver.Add(ctx.mkEq(set1expr, set2expr));
//							countConsistencyConstraint++;
//
//							// 1-D projection
//							collectProjectionConsistencyData(solver,ctx, c1Set, c2Set, c1index, c2index, commonCols, projectionConsistencyInfoPairs, cliqueWColumnWProjectionStuff);
//						}
//					}
//				}
//			}
//		}
//		///////////////// End dk
//
//		else if (consistencyMakerType == ConsistencyMakerType.BRUTEFORCE) {
//			for (CliqueIntersectionInfo cliqueIntersectionInfo : cliqueIntersectionInfos) {		// Create lp variables for consistency constraints
//
//				int i = cliqueIntersectionInfo.i;
//				int j = cliqueIntersectionInfo.j;
//				IntList intersectingColIndices = cliqueIntersectionInfo.intersectingColIndices;
//
//				Partition partitionI = cliqueIdxtoPList.get(i);
//				Partition partitionJ = cliqueIdxtoPList.get(j);
//
//				//Recomputing SplitRegions for every pair of intersecting cliques
//				//as the SplitRegions might have become more granular due to
//				//some other pair of intersecting cliques having its intersectingColIndices
//				//overlapping with this pair's intersectingColIndices
//				List<Region> splitRegions = getSplitRegions(partitionI, partitionJ, intersectingColIndices);
//      
//				Set<String> commonCols = new HashSet<>(arasuCliques.get(i));
//				commonCols.retainAll(arasuCliques.get(j));
//
//				for (Region splitRegion : splitRegions) {
//					List<IntExpr> consistencyLHS = new ArrayList<>();
//					for (int k = 0; k < partitionI.size(); k++) {
//						Region iVar = partitionI.at(k);
//						Region truncRegion = getTruncatedRegion(iVar, intersectingColIndices);
//						Region truncOverlap = truncRegion.intersection(splitRegion);
//						if (!truncOverlap.isEmpty()) {
//							String varname = "var" + i + "_" + k;
//							consistencyLHS.add(ctx.mkIntConst(varname));
//						}
//					}
//
//					List<IntExpr> consistencyRHS = new ArrayList<>();
//					for (int k = 0; k < partitionJ.size(); k++) {
//						Region jVar = partitionJ.at(k);
//						Region truncRegion = getTruncatedRegion(jVar, intersectingColIndices);
//						Region truncOverlap = truncRegion.intersection(splitRegion);
//						if (!truncOverlap.isEmpty()) {
//							String varname = "var" + j + "_" + k;
//							consistencyRHS.add(ctx.mkIntConst(varname));
//						}
//					}
//
//					//Adding consistency constraints
//					solver.Add(ctx.mkEq(ctx.mkAdd(consistencyLHS.toArray(new ArithExpr[consistencyLHS.size()])),
//							ctx.mkAdd(consistencyRHS.toArray(new ArithExpr[consistencyRHS.size()]))));
//					solverStats.solverConstraintCount++;
//					countConsistencyConstraint++;
//
//					// 1-D projection
//					collectProjectionConsistencyData(solver,ctx, consistencyLHS, consistencyRHS, i, j, commonCols, projectionConsistencyInfoPairs, cliqueWColumnWProjectionStuff);
//				}
//			}
//		}
//		else {
//			ctx.close();
//			throw new RuntimeException("Unknown consistency maker " + consistencyMakerType);
//		}
//		DebugHelper.printInfo("countConsistencyConstraint for " + viewname + " = " + countConsistencyConstraint);
//
//		/////////////// Start dk
//		// Consistency for projection: Phase 1
//		Set<IntExpr> allSlackVars = new HashSet<>();
//		for (int cliqueIndex = 0; cliqueIndex < cliqueWColumnWProjectionStuff.size(); ++cliqueIndex) {
//			HashMap<String, ProjectionStuffInColumn> columnWProjectionStuff = cliqueWColumnWProjectionStuff.get(cliqueIndex);
//			for (Entry<String, ProjectionStuffInColumn> entry : columnWProjectionStuff.entrySet()) {
//				String columnname = entry.getKey();
//				ProjectionStuffInColumn projectionStuff = entry.getValue();
//				// All AggVars in an atomic set satisfy the same set of consistency constraints
//				List<Set<IntExpr>> listOfAtomicSetOfNonAggVars = projectionStuff.doPartition_ConsistencyConstraintSetWiseNonAggVars();
//				for (int j = 0; j < listOfAtomicSetOfNonAggVars.size(); ++j) {
//					Set<IntExpr> atomicSetOfNonAggVars = listOfAtomicSetOfNonAggVars.get(j);
//					IntExpr slackVar = ctx.mkIntConst(getSlackVarStringName(cliqueIndex, columnname, j));		// SlackVar value is the number of unique points from Atomic set vars
//					solver.Add(ctx.mkGe(slackVar, ctx.mkInt(0)));
//					solver.Add(ctx.mkGe(ctx.mkAdd(atomicSetOfNonAggVars.toArray(new ArithExpr[atomicSetOfNonAggVars.size()])), slackVar));
//			
//					allSlackVars.add(slackVar);
//				}
//			}
//		}
//
//		for (ProjectionConsistencyInfoPair projectionConsistencyInfoPair : projectionConsistencyInfoPairs) {
//			String columnname = projectionConsistencyInfoPair.columnname;
//			ProjectionConsistencyInfo c1ProjectionConsistencyInfo = projectionConsistencyInfoPair.getFirst();
//			ProjectionConsistencyInfo c2ProjectionConsistencyInfo = projectionConsistencyInfoPair.getSecond();
//			ProjectionStuffInColumn c1ProjectionStuff = cliqueWColumnWProjectionStuff.get(c1ProjectionConsistencyInfo.cindex).get(columnname);
//			ProjectionStuffInColumn c2ProjectionStuff = cliqueWColumnWProjectionStuff.get(c2ProjectionConsistencyInfo.cindex).get(columnname);
//			List<Integer> c1SlackVarsIndexs = c1ProjectionStuff.getSlackVarsIndexsContainedInNonAggVars(c1ProjectionConsistencyInfo.nonAggVars);
//			List<Integer> c2SlackVarsIndexs = c2ProjectionStuff.getSlackVarsIndexsContainedInNonAggVars(c2ProjectionConsistencyInfo.nonAggVars);
//	
//			projectionConsistencyInfoPair.setSlackVarsIndexes(c1SlackVarsIndexs, c2SlackVarsIndexs);
//	
//			List<IntExpr> c1ProjVarsUnionSlackVar = new LinkedList<>(c1ProjectionConsistencyInfo.projVars);
//			for (Integer index : c1SlackVarsIndexs) {
//				c1ProjVarsUnionSlackVar.add(ctx.mkIntConst(getSlackVarStringName(c1ProjectionConsistencyInfo.cindex, columnname, index)));
//			}
//			List<IntExpr> c2ProjVarsUnionSlackVar = new LinkedList<>(c2ProjectionConsistencyInfo.projVars);
//			for (Integer index : c2SlackVarsIndexs) {
//				c2ProjVarsUnionSlackVar.add(ctx.mkIntConst(getSlackVarStringName(c2ProjectionConsistencyInfo.cindex, columnname, index)));
//			}
//	
//			solver.Add(ctx.mkEq(ctx.mkAdd(c1ProjVarsUnionSlackVar.toArray(new ArithExpr[c1ProjVarsUnionSlackVar.size()])), ctx.mkAdd(c2ProjVarsUnionSlackVar.toArray(new ArithExpr[c2ProjVarsUnionSlackVar.size()]))));
//		}
//
//		// 1-D projection: This is not in report. The dVars maximize the difference between nonAggVars and ProjVars so that more slack is available
//		// While, at the same time, the sum of all slackVars is minimized to prevent generating extra unique points which were originally not required: proj1 + slack1 = proj2 + slack2; 1+1=2+0 is better then 1+2=2+1
//		int dVarIndex = 0;
//		List<IntExpr> allDVars = new ArrayList<>();
//
//		for (ProjectionConsistencyInfoPair projectionConsistencyInfoPair : projectionConsistencyInfoPairs) {
//			ProjectionConsistencyInfo c1ProjectionConsistencyInfo = projectionConsistencyInfoPair.getFirst();
//			Set<IntExpr> projVars = c1ProjectionConsistencyInfo.projVars;
//			if (projVars.size() != 0 && c1ProjectionConsistencyInfo.nonAggVars.size() != 0) {
//				IntExpr dVar = ctx.mkIntConst("d_var" + dVarIndex++);
//				allDVars.add(dVar);
//				Set<IntExpr> nonAggVars = new HashSet<>(c1ProjectionConsistencyInfo.nonAggVars);
//				ArithExpr nonAggVarsSum = ctx.mkAdd(nonAggVars.toArray(new ArithExpr[nonAggVars.size()]));
//				ctx.mkEq(dVar, ctx.mkSub(nonAggVarsSum, ctx.mkAdd(projVars.toArray(new ArithExpr[projVars.size()]))));
//			}
//	
//			ProjectionConsistencyInfo c2ProjectionConsistencyInfo = projectionConsistencyInfoPair.getFirst();
//			projVars = c2ProjectionConsistencyInfo.projVars;
//			if (projVars.size() != 0 && c2ProjectionConsistencyInfo.nonAggVars.size() != 0) {
//				IntExpr dVar = ctx.mkIntConst("d_var" + dVarIndex++);
//				allDVars.add(dVar);
//				Set<IntExpr> nonAggVars = new HashSet<>(c2ProjectionConsistencyInfo.nonAggVars);
//				ArithExpr nonAggVarsSum = ctx.mkAdd(nonAggVars.toArray(new ArithExpr[nonAggVars.size()]));
//				ctx.mkEq(dVar, ctx.mkSub(nonAggVarsSum, ctx.mkAdd(projVars.toArray(new ArithExpr[projVars.size()]))));
//			}
//		}
//
//		ArithExpr objective = null;
//		if (allDVars.size() > 0) {
//			objective = ctx.mkMul(ctx.mkInt(-1), ctx.mkAdd(allDVars.toArray(new ArithExpr[allDVars.size()])));
//			if (allSlackVars.size() > 0)
//				objective = ctx.mkAdd(objective, ctx.mkAdd(allSlackVars.toArray(new ArithExpr[allSlackVars.size()])));
//		}
//
//		if (objective != null)
//			solver.MkMinimize(objective);
//
//		///////////////// End dk
//
//
//
//		List<String> allIntervalRegions = new ArrayList<>(); // List of all intervals
//		List<String> allIntervalisedRegions = new ArrayList<>(); // List of all intervalised regions
//		List<String> allDxValues = new ArrayList<>();
//
//		if(PostgresVConfig.hydraVersions.contains(PostgresVConfig.HydraTypes.duplicationHydra)) {
//
//			// New variables
//			Map<String,List<String>> allIntervalRegionsVariables = new HashMap<>();			 
//			Map<String, List<String>> allDxValuesVariables = new HashMap<>();
//			Map<String, List<String>> allIntervalisedRegionsVariables = new HashMap<>();
//			Map<String, HashMap<String, List<Integer>>> varToIntervalMapPerFKey = new HashMap<>();
//
//
//
//			if(PostgresVConfig.fkeyToBorrowedAttr.containsKey(viewname)) {
//  
//  				  
//				Map<String, Set<String>> fkeyToBorrowedAttr = PostgresVConfig.fkeyToBorrowedAttr.get(viewname);
//
//				for(String fkey : fkeyToBorrowedAttr.keySet()) {
//	  
//					allIntervalRegionsVariables.put(fkey, new ArrayList<>());
//					allDxValuesVariables.put(fkey, new ArrayList<>());
//					allIntervalisedRegionsVariables.put(fkey, new ArrayList<>());
//					varToIntervalMapPerFKey.put(fkey, new HashMap<>());
//					Set<String> currentClique = null; 
//					Integer currentCliqueIdx = null;
//	  
//					for(int c=0; c <  this.arasuCliques.size(); c++ ) {
//						Set<String> clique = this.arasuCliques.get(c);
//						if(!cliquesToFKeyCoverage.containsKey(clique)) {
//							continue;
//						}
//						Set<String> fkeysCovered = cliquesToFKeyCoverage.get(clique);
//						if(fkeysCovered.contains(fkey)) {
//							currentClique = clique;
//							currentCliqueIdx = c;
//							break;
//						}
//		  
//					}
//	  
//					if(currentClique == null) {
//						throw new RuntimeException("Something wrong can't be possible");
//					}
//	  
//					fkeyToCliqueIdx.put(fkey, currentCliqueIdx);
//	  
//					Set<String> borrowedAttr = fkeyToBorrowedAttr.get(fkey);
//					List<String> sortedBorrowedAttr = new ArrayList<>(borrowedAttr);
//					List<Integer> borrowedAttrIdx = new ArrayList<>();
//					Collections.sort(sortedBorrowedAttr);
//					int c=0;
//					for(int i=0; i < sortedViewColumns.size(); i++) {
//		  
//						if(sortedBorrowedAttr.get(c).contentEquals(sortedViewColumns.get(i))){
//			  
//							borrowedAttrIdx.add(i);
//							c = c + 1;
//						}
//						if(c == sortedBorrowedAttr.size()) {
//							break;
//						}
//		  
//					}
//					
//					int noOfIntervalRegions = 1;
//					List<List<Integer>> borrowedAttrIntervals  = new ArrayList<>();
//					Partition partition = cliqueIdxtoPList.get(currentCliqueIdx);
//					for(int bucket : borrowedAttrIdx) {
//			
//						Set<Integer> intervals = new HashSet<>();
//						for(Region r : partition.getAll()) {
//				
//							for(BucketStructure bs : r.getAll()) {
//					
//								intervals.addAll((bs.at(bucket).getAll()));
//					
//							}	
//						}
//						noOfIntervalRegions*=intervals.size();
//						ArrayList<Integer> intervalsList = new ArrayList<>(intervals);
//						Collections.sort(intervalsList);
//						borrowedAttrIntervals.add(intervalsList);
//			
//					}
//	  
//					List<List<Integer>> intervalRegions = new ArrayList<>();
//					for(int i=0; i < noOfIntervalRegions; i++) {
//						intervalRegions.add(new ArrayList<>());					    	
//					}
//	    
//					int count=0;
//					int row = 0;
//					while(count < noOfIntervalRegions) {
//	    	
//						int currentRowSize = borrowedAttrIntervals.get(row).size();
//	    	
//						if(count > 0) {
//	    		
//							int currentIndex=0;
//							List<List<Integer>> copyofIntervalRegionList = new ArrayList<>();
//							for(int i=0;i<intervalRegions.size();i++) {
//								List<Integer> temp = new ArrayList<Integer>();
//								copyofIntervalRegionList.add(temp);
//								for(int j=0; j<intervalRegions.get(i).size(); j++) {
//									temp.add(intervalRegions.get(i).get(j));
//								}								
//					
//							}
//							for(int j=0; j<currentRowSize; j++) {
//								Integer val = borrowedAttrIntervals.get(row).get(j);
//								for(int i=0;i<count;i++) {
//									List<Integer> w = new ArrayList<>(copyofIntervalRegionList.get(i));
//									w.add(val);
//									intervalRegions.set(currentIndex, w);
//									currentIndex++;
//								}
//							}
//							row = row + 1;
//							count*=currentRowSize;    		
//						}
//						else {
//	    		
//							int currentIndex = 0;
//							for(int j=0; j < currentRowSize; j++) {
//	    			
//								Integer val = borrowedAttrIntervals.get(row).get(j);
//								List<Integer> w = new ArrayList<>();
//								w.add(val);
//					  
//								intervalRegions.set(currentIndex, w);
//								currentIndex++;
//							}
//	    		
//							count = currentRowSize;
//							row = row + 1;
//	    			
//							}	
//						}
//	    
//	    
//					HashMap<Integer, String> Z3name = new HashMap<>();
//					for(int i=0; i< intervalRegions.size();i ++) {
//						String intervalname =  fkey +  "_clique" + currentCliqueIdx + "interval" + i;
//						allIntervalRegionsVariables.get(fkey).add(intervalname);
//						Z3name.put(i, intervalname);
//					}
//	    
//	    
//					// Adding sum of all intervals to total tuple cout
//					ArithExpr[] sumOfIntervalRegions = new ArithExpr[intervalRegions.size()]; 
//					c = 0;
//					allIntervalRegionsPerFKey.put(fkey, intervalRegions);
//					for(Integer interval : Z3name.keySet()) {
//	    	
//						String intervalName = Z3name.get(interval);
//						solver.Add(ctx.mkGe(ctx.mkIntConst(intervalName), ctx.mkInt(0)));
//						allIntervalRegions.add(intervalName);
//						sumOfIntervalRegions[c++] = ctx.mkIntConst(intervalName);
//						}
//	    
//					c=0;
//					ArithExpr[] sumOfPartitionedRegions = new ArithExpr[partition.size()];
//					for(int r=0; r < partition.size(); r++){
//	    	
//						String varname = "var" + currentCliqueIdx + "_" + r;
//						varToIntervalMapPerFKey.get(fkey).put(varname, new ArrayList<>());
//						sumOfPartitionedRegions[c++] = ctx.mkIntConst(varname);
//					}
//					//    adding all vars = all clique intervals
//					solver.Add(ctx.mkEq(ctx.mkAdd(sumOfPartitionedRegions), ctx.mkAdd(sumOfIntervalRegions)));
//	    
//					fkeyToActualInteervalisedRegMap.put(fkey,intervalisedRegionMap);
//					Map<Integer,List<String>> intervalRegionToPartionedRegionsMap = new HashMap<>();
//					for(int r=0; r < partition.size(); r++) {
//	    	
//						Region region = partition.at(r);
//						String regionName =  "var" + currentCliqueIdx + "_" + r;
//						List<String> regionPartitionList = new ArrayList<>();
//						for(int i=0; i < intervalRegions.size(); i++) {
//	    		
//							List<Integer> intervalRegion = intervalRegions.get(i);
//							boolean flag = false;
//							int bsIdx = 0;
//		    	
//							for(BucketStructure bs : region.getAll()) {
//	    			
//								c = 0;
//								for(int bucketIdx : borrowedAttrIdx) {
//									Bucket bucket = bs.at(bucketIdx);
//									if(bucket.contains(intervalRegion.get(c))) {
//										c = c + 1;
//									}
//									else {
//		    				
//										break;
//									}
//								}
//								if(c == borrowedAttrIdx.size()) {
//									flag = true;
//									break;
//								}
//								bsIdx++;
//							}
//	    		
//							if(flag) {
//								String intervalisedRegionName =fkey + "_var" + currentCliqueIdx + "_" + r + "_interval_" + i ;
//								BucketStructure bucketStructure = region.at(bsIdx);
//								BucketStructure bsNew  = new BucketStructure();
//	    			
//								int ci=0;
//								for(int bi=0; bi < bucketStructure.size(); bi++) {
//	    				
//									Bucket bucket = new Bucket();
//									if(bi == borrowedAttrIdx.get(ci)){
//										bucket.add(intervalRegion.get(ci));
//									}
//									else {
//										bucket = bucketStructure.at(bi);
//									}
//									bsNew.add(bucket);
//	    					
//									}
//	    			
//								Region newR = new Region();
//								newR.add(bsNew);
//	    			
//								intervalisedRegionMap.put(intervalisedRegionName, newR);
//								regionPartitionList.add(intervalisedRegionName);
//								allIntervalisedRegions.add(intervalisedRegionName);
//								allIntervalisedRegionsVariables.get(fkey).add(intervalisedRegionName);
//								varToIntervalMapPerFKey.get(fkey).get("var" + currentCliqueIdx + "_" + r).add(i);
//								if(!intervalRegionToPartionedRegionsMap.containsKey(i)) {
//									intervalRegionToPartionedRegionsMap.put(i, new ArrayList<>());
//								}
//								intervalRegionToPartionedRegionsMap.get(i).add(intervalisedRegionName);
//								solver.Add(ctx.mkGe(ctx.mkIntConst(intervalisedRegionName), ctx.mkInt(0)));
//							}
//	    		
//						}
//	    	
//						ArithExpr[] regionPartitionArray = new ArithExpr[regionPartitionList.size()];
//						for(int i=0; i < regionPartitionList.size(); i++) {
//	    		
//							regionPartitionArray[i] = ctx.mkIntConst(regionPartitionList.get(i));
//	    		
//						}
//	    	
//						// sum  of intervalised regions = var
//						solver.Add(ctx.mkEq(ctx.mkAdd(regionPartitionArray), ctx.mkIntConst(regionName)));
//	    	
//					}
//	    
//	    
//	    
//					System.out.print("");
//	    
//	    
//					for(int intervalIdx : intervalRegionToPartionedRegionsMap.keySet()) {
//	    	
//	    	
//						List<String> regionNames =  intervalRegionToPartionedRegionsMap.get(intervalIdx);
//	    	
//						ArithExpr[] regionArray =  new ArithExpr[regionNames.size()];
//						for(int i=0; i < regionNames.size(); i++) {
//							regionArray[i] = ctx.mkIntConst(regionNames.get(i));
//						}
//	    	
//						solver.Add(ctx.mkEq( ctx.mkAdd(regionArray), ctx.mkIntConst(Z3name.get(intervalIdx))));	
//						}   
//	    	    
//					JSONArray dfVector = PostgresVConfig.fkeySkewVectors.getJSONObject(viewname).getJSONArray(fkey);
//					JSONArray d = dfVector.getJSONArray(0);
//					JSONArray f = dfVector.getJSONArray(1);
//				
//					for(Integer i = 0; i < intervalRegions.size(); i++) {
//						ArithExpr[] dxSumm = new ArithExpr[d.length()];
//						for(int d_i=0; d_i < d.length(); d_i++){
//				
//				 
//							String x = fkey + "_interval_" + i  + "_d_" + d_i;
//							solver.Add(ctx.mkGe(ctx.mkIntConst(x), ctx.mkInt(0)));
//							allDxValuesVariables.get(fkey).add(x);
//							allDxValues.add(x);
//							ArithExpr xd = ctx.mkMul(ctx.mkIntConst(x), ctx.mkInt(d.getInt(d_i)));
//							dxSumm[d_i] = xd;
//				
//						}
//						String intervalname = Z3name.get(i);
//						solver.Add(ctx.mkEq(ctx.mkAdd(dxSumm),ctx.mkIntConst(Z3name.get(i))));
//					}
//		
//					for(int d_i=0; d_i < d.length(); d_i++) {
//    		
//						ArithExpr[] xfSumm = new ArithExpr[intervalRegions.size()];
//						for(int i=0; i < intervalRegions.size(); i++) {
//    			
//							String x = fkey + "_interval_" + i  + "_d_" + d_i;
//							xfSumm[i] = ctx.mkIntConst(x);
//    			
//						}
//    		
//						solver.Add(ctx.mkEq(ctx.mkAdd(xfSumm),ctx.mkInt(f.getInt(d_i))));
//    		
//					}	  
//				}
//	  
//
//  
//  
//				// Adding equations for CCs skew
//  
//				Map<String, Map<String, Set<String>>> fkeyToBR = PostgresVConfig.fkeyToBorrowedAttr;
//				for(FormalCondition condition : conditions) {
//	  
//					Integer counter = condition.getCounter();
//					String queryname = condition.getQueryname();
//					List<FormalCondition> conditionList = new ArrayList<>();
//					conditionList.add(condition);
//					String fkey = findFkey(conditionList);	
//					// CC having no foreign key column
//					if(fkey == null) {
//						continue;
//					}
//					// No borrowed attr for fkey
//					if(!fkeyToBR.containsKey(fkey)) {
//						continue;
//					}
//					String actualFKey = PostgresVConfig.reverseColumnAnonyMap.get(fkey);
//					String dfVec = actualFKey  + "___" + counter + "_" + queryname;
//	  
//	  
//					DFvector dfvector = PostgresVConfig.ccsDFvectors.get(dfVec);
//					List<Long> dValues = dfvector.getD();
//					List<Long> fValues = dfvector.getF();
//					List<List<Integer>> intervalRegions = this.allIntervalRegionsPerFKey.get(fkey);
//					//String x = fkey + "_interval_" + i  + "_d_" + d_i;
//	  
//					// find CCs intersecting with intervals
//	  
//					Map<String, Region> intervalisedRegions = this.fkeyToActualInteervalisedRegMap.get(fkey);
//					Set<Integer> intersectingIntervals = findCCsIntersectingWithIntervals(condition,intervalisedRegions);
//	  
//	  
//					JSONArray fkeyBaseSkewVectors = PostgresVConfig.fkeySkewVectors.getJSONObject(viewname).getJSONArray(fkey);
//					JSONArray baseDValues = fkeyBaseSkewVectors.getJSONArray(0);
//					JSONArray baseFValues = fkeyBaseSkewVectors.getJSONArray(1);
//	  
//	  
//	  
//					long fCount = 0;
//					for(int di=0; di < dValues.size(); di++) {
//		  
//						Long fVal = fValues.get(di);
//						Long dVal = dValues.get(di);
//						ArithExpr[] dxArray =  new ArithExpr[intersectingIntervals.size()];
//						for(int bdi=0; bdi < baseDValues.length(); bdi++) {
//							long baseDval = baseDValues.getLong(bdi);
//							if(baseDval < dVal) {
//								break;
//							}
//							else {
//								int c=0;
//								for(int intervalIdx : intersectingIntervals) {
//					  
//									dxArray[c] = ctx.mkIntConst(fkey + "_interval_" + intervalIdx  + "_d_" + di);
//									c = c + 1;
//								}
//							}
//						}
//		 
//		  
//						solver.Add(ctx.mkGe(ctx.mkAdd(dxArray),ctx.mkInt(fVal - fCount)));
//						fCount += fVal;  
//					}
//					System.out.print("");
//	  
//				}
//			}
//		}
//
//		onlyFormationSW.displayTimeAndDispose();
//		//Dumping LP into a file -- Anupam
//		//start
//		FileWriter fw;
//		try {
//			fw = new FileWriter("lpfile-"+viewname+".txt");
//			fw.write(solver.toString());
//			fw.close();
//		} catch (IOException e) {
//			// TODO Auto-generated catch block
//			e.printStackTrace();
//		} 
//		System.err.println(solver.toString());
//		//stop
//
//		StopWatch onlySolvingSW = new StopWatch("LP-OnlySolving" + viewname);
//
//		Status solverStatus = solver.Check();
//		DebugHelper.printInfo("Solver Status: " + solverStatus);
//
//		if (!Status.SATISFIABLE.equals(solverStatus)) {
//			ctx.close();
//			throw new RuntimeException("solverStatus is not SATISFIABLE");
//		}
//
//		Model model = solver.getModel();
//
		
		
		for (int i = 0; i < cliqueCount; i++) {
			IntList colIndxs = arasuCliquesAsColIndxs.get(i);
			Partition partition = cliqueIdxtoPList.get(i);
			LinkedList<VariableValuePair> varValuePairs = new LinkedList<>();
			for (int j = 0; j < partition.size(); j++) {
				String varname = "var" + i + "_" + j;
//      
//				//Variable to column indices mapping -- Anupam
//				//start
//				FileWriter fw1;
//				try {
//					fw1 = new FileWriter(viewname+"-var-to-colindices.txt", true);
//					fw1.write(varname+" "+colIndxs.toString()+ "\n");
//					fw1.close();
//				} catch (IOException e) {
//					// TODO Auto-generated catch block
//					e.printStackTrace();
//				} 
//				//stop
//				//System.err.println(varname+colIndxs.toString());
//				long rowcount = Long.parseLong(model.evaluate(ctx.mkIntConst(varname), true).toString());
				long rowcount = (long)vars[j].get(GRB.DoubleAttr.X);
				if (rowcount != 0) {
					Region variable = getTruncatedRegion(partition.at(j), colIndxs);
					VariableValuePair varValuePair = new VariableValuePair(variable, rowcount);
					varValuePairs.add(varValuePair);
				}
			}
			cliqueIdxToVarValuesList.add(varValuePairs);
		}
	
//
//
//		if(PostgresVConfig.hydraVersions.contains(PostgresVConfig.HydraTypes.duplicationHydra)) {
//			long sumOfIntervalRegion = 0;
//			for(int i=0; i < allIntervalRegions.size(); i++) {
//	  
//				// t17_c001_clique0interval8
//				long val = Long.parseLong(model.evaluate(ctx.mkIntConst(allIntervalRegions.get(i)), true).toString());
//				if(val==0) {
//					continue;
//				}
//	  
//				String interval = allIntervalRegions.get(i);
//				String fkey = interval.split("_clique")[0];
//	  
//				this.allIntervalRegionValueMap.put(allIntervalRegions.get(i), val);
//				sumOfIntervalRegion += val;
//				if(!this.fkeyToIntervalRegionMap.containsKey(fkey)) {
//					this.fkeyToIntervalRegionMap.put(fkey, new ArrayList<>());
//				}
//				this.fkeyToIntervalRegionMap.get(fkey).add(interval);
//			}
//  
//		long sumOfIntervalisedRegion = 0;
//  
//  
//		for(int i=0; i < allIntervalisedRegions.size(); i++ ) {
//	  
//		  
//		  long val = Long.parseLong(model.evaluate(ctx.mkIntConst(allIntervalisedRegions.get(i)), true).toString());
//		  if(val==0) {
//			  continue;
//		  }
//	  
//		  String intervalisedRegion = allIntervalisedRegions.get(i);
//	  
//		  this.allIntervalisedRegionsMap.put(allIntervalisedRegions.get(i), val);
//		  sumOfIntervalisedRegion += val;
//	  
//		  String fkey =  intervalisedRegion.split("_var")[0];
//		  String varname = intervalisedRegion.split("_")[2] + "_" + intervalisedRegion.split("_")[3]; 
//	  
//		  if(!varToIntervalisedRegionMapPerFkey.containsKey(fkey)) {
//			  varToIntervalisedRegionMapPerFkey.put(fkey, new HashMap<>());
//		  }
//		  if(!varToIntervalisedRegionMapPerFkey.get(fkey).containsKey(varname)) {
//		  varToIntervalisedRegionMapPerFkey.get(fkey).put(varname,new ArrayList<>());
//		  }
//		  varToIntervalisedRegionMapPerFkey.get(fkey).get(varname).add(intervalisedRegion);
//		}
//  
//  
//		for(int i=0; i < allDxValues.size(); i++) {
//			//t17_c018_interval_0_d_0
//			long val = Long.parseLong(model.evaluate(ctx.mkIntConst(allDxValues.get(i)), true).toString());
//			if(val==0) {
//				continue;
//			}
//	  
//			this.allDxValuesMap.put(allDxValues.get(i), val);
//			String dxValue = allDxValues.get(i);
//			String fkey =  dxValue.split("_interval_")[0];
//			int intervalIdx = Integer.parseInt(dxValue.split("_")[3]) ;
//			if(!intervalToDxValuePerFkey.containsKey(fkey)) {
//				intervalToDxValuePerFkey.put(fkey, new HashMap<>());
//			}
//			if(!intervalToDxValuePerFkey.get(fkey).containsKey(intervalIdx)) {
//				intervalToDxValuePerFkey.get(fkey).put(intervalIdx, new ArrayList<>());
//			}
//			intervalToDxValuePerFkey.get(fkey).get(intervalIdx).add(dxValue);
//	  
//		}
//		}
//		onlySolvingSW.displayTimeAndDispose();
//
//		ctx.close();
		
		model.dispose();
		env.dispose();
		}catch(GRBException e) {
			System.out.println("Error code: "+ e.getErrorCode() + ". " + e.getMessage());
		}
		return cliqueIdxToVarValuesList;

	}
	
	//changes by Manish Ends for Gurobi
	
	
	private Set<Integer> findCCsIntersectingWithIntervals(FormalCondition curCondition,
			Map<String, Region> intervalisedRegions) {
		// TODO Auto-generated method stub
		Set<Integer> intersectingIntervals = new HashSet<>();
		for(String regionName : intervalisedRegions.keySet()) {
			
			Region region = intervalisedRegions.get(regionName);
			int currentCliqueIdx = Integer.parseInt(regionName.split("var")[1].split("_")[0]);
			Set<String> currentClique = this.arasuCliques.get(currentCliqueIdx);
			Set<String> appearingCols = new HashSet<>();
            getAppearingCols(appearingCols, curCondition);
            
 			if (currentClique.containsAll(appearingCols)) {
 				 
 				 if(checkCCSatifyRegion(region,appearingCols,curCondition)) {
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
			int count=0;
			for(String attr : attrFound) {
				if(!attr.contains(viewname)) {
					break;
				}
				else {
					count++;
				}
			}
			if(count == attrFound.size()) {
				return null;
			}
			
			if(condition instanceof FormalConditionComposite) {
				return findFkey(((FormalConditionComposite) condition).getConditionList());
			}
			else if(condition instanceof FormalConditionSimpleInt) {
				
				FormalConditionSimpleInt conditionInt = (FormalConditionSimpleInt) condition;
				List<String> fkColumns = conditionInt.getFkColumnNames();
				return fkColumns.get(fkColumns.size() - 1);
			}
			else {
				
				throw new RuntimeException("Not expecting");
			}
		}
		
		
		throw new RuntimeException("Not expecting");
		
	
		
		
		
	}

	void areDisjointCheck(List<VariableValuePair> regions) {
        //every pair of Regions are disjoint
       
        //List<Region> regionList = new ArrayList<>(regions);
        int n = regions.size();
        for (int i = 0; i < n; i++) {
            Region regi=regions.get(i).variable;
            for (int j = i + 1; j < n; j++) {
               
                Region regj=regions.get(j).variable;
                if (!regi.intersection(regj).isEmpty())
                    throw new RuntimeException("Expected disjoint region but found overlapping regions");
            }
        }
    }

	private void createProjVarToIntervalAndSSPRegionToMaxUniquePoints_sequential(Model model, Context ctx, List<HashMap<IntExpr, DirtyValueInterval>> cliqueWiseProjVarToInterval, 
			List<HashMap<String, ProjectionStuffInColumn>> cliqueWColumnWProjectionStuff, HashMap<String, HashMap<Region, Long>> columnWSSPRegionToMaxUniqePoints) {
		for (int i = 0; i < cliqueCount; i++) {
        	HashMap<String, ProjectionStuffInColumn> columnWiseProjectionStuff = cliqueWColumnWProjectionStuff.get(i);
			HashMap<IntExpr, DirtyValueInterval> projVarToInterval = new HashMap<>();
			for (Entry<String, ProjectionStuffInColumn> entry : columnWiseProjectionStuff.entrySet()) {
				String columnname = entry.getKey();
				ProjectionStuffInColumn projectionStuffInColumn = entry.getValue();
				HashMap<Region, Long> sspRegionToMaxUniqePoints = columnWSSPRegionToMaxUniqePoints.get(columnname);
				if (sspRegionToMaxUniqePoints == null) {
					sspRegionToMaxUniqePoints = new HashMap<>();
					columnWSSPRegionToMaxUniqePoints.put(columnname, sspRegionToMaxUniqePoints);
				}
				for (Entry<Region, ProjectionStuffInSSPRegion> regionAndProjectionStuff : projectionStuffInColumn.getMapSSPRegionToProjectionStuff().entrySet()) {
					Region region = regionAndProjectionStuff.getKey();
					ProjectionStuffInSSPRegion projectionStuff = regionAndProjectionStuff.getValue();
					Set<IntExpr> projVarsInSSPRegion = projectionStuff.getAllProjVars();
					long start = 0;
					long end = 0;	// excluding end
					
					for (IntExpr projVar : projVarsInSSPRegion) {
						long count = Long.parseLong(model.evaluate(projVar, true).toString());
						if (count != 0) {
							end += count;
							projVarToInterval.put(projVar, new DirtyValueInterval(start, end));
							start = end;
						}
					}
					
					if(!sspRegionToMaxUniqePoints.containsKey(region))
						sspRegionToMaxUniqePoints.put(region, end);
					else {
						long maxEnd = sspRegionToMaxUniqePoints.get(region);
						if (end > maxEnd)
							sspRegionToMaxUniqePoints.put(region, end);
					}
					
					
					long maxint = Integer.MAX_VALUE;
					if (end >= maxint)	// Search "LongIndexNeeded" in this code
						DirtyCode.throwError("problem");
				}
			}
			cliqueWiseProjVarToInterval.add(projVarToInterval);
		}
	}

	private void createProjVarToIntervalAndSSPRegionToMaxUniquePoints_hueristic(Model model, Context ctx, List<HashMap<IntExpr, DirtyValueInterval>> cliqueWiseProjVarToInterval, HashMap<String, HashMap<Region,
			List<ProjectionConsistencyInfoPair>>> columnWSSPRegionToAllProjectionConsistencyInfoPairs, 
			List<HashMap<String, ProjectionStuffInColumn>> cliqueWColumnWProjectionStuff, HashMap<String, HashMap<Region, Long>> columnWSSPRegionToMaxUniqePoints) {
		HashMap<String, HashMap<Region, List<LinkedList<DirtyValueInterval>>>> columnWRegionWCliqueWAvailableIntervals = new HashMap<>();
		for (int i = 0; i < cliqueCount; ++i) {
			cliqueWiseProjVarToInterval.add(new HashMap<>());
		}
		
		// Assigning intervals to projVars which take part in any consistency constraint
        for (Entry<String, HashMap<Region, List<ProjectionConsistencyInfoPair>>> outerEntry : columnWSSPRegionToAllProjectionConsistencyInfoPairs.entrySet()) {
        	String columnname = outerEntry.getKey();
        	HashMap<Region, List<ProjectionConsistencyInfoPair>> sspRegionToAllProjectionConsistencyInfoPairs = outerEntry.getValue();
        	HashMap<Region, List<LinkedList<DirtyValueInterval>>> regionWCliqueWAvailableIntervals = new HashMap<>();
			for (Entry<Region, List<ProjectionConsistencyInfoPair>> innerEntry : sspRegionToAllProjectionConsistencyInfoPairs.entrySet()) {
				Region region = innerEntry.getKey();
				SimpleGraph<ProjectionConsistencyInfo, DefaultEdge> graph = new SimpleGraph<>(DefaultEdge.class);
				for (ProjectionConsistencyInfoPair projectionConsistencyInfoPair : innerEntry.getValue()) {
					ProjectionConsistencyInfo c1ProjectionConsistencyInfo = projectionConsistencyInfoPair.getFirst();
					ProjectionConsistencyInfo c2ProjectionConsistencyInfo = projectionConsistencyInfoPair.getSecond();

					graph.addVertex(c1ProjectionConsistencyInfo);
					graph.addVertex(c2ProjectionConsistencyInfo);
					graph.addEdge(c1ProjectionConsistencyInfo, c2ProjectionConsistencyInfo);
				}
				ConnectivityInspector<ProjectionConsistencyInfo, DefaultEdge> connectivityInspector = new ConnectivityInspector<>(graph);
				List<Set<ProjectionConsistencyInfo>> listOfConnectedProjectionConsistencyInfos = connectivityInspector.connectedSets();
				
				ArrayList<LinkedList<DirtyValueInterval>> cliqueWAvailableIntervals = new ArrayList<>(cliqueCount);
				for (int i = 0; i < cliqueCount; ++i) {
					LinkedList<DirtyValueInterval> temp = new LinkedList<>();
					temp.add(new DirtyValueInterval(0, relationCardinality));
					cliqueWAvailableIntervals.add(temp);
				}
				for (Set<ProjectionConsistencyInfo> connectedProjectionConsistencyInfos : listOfConnectedProjectionConsistencyInfos) {
					ProjectionConsistencyInfo infoWithZeroSlack = null;
					for (ProjectionConsistencyInfo projectionConsistencyInfo : connectedProjectionConsistencyInfos) {
						int cliqueIndex = projectionConsistencyInfo.cindex;
						long slackVarSum = 0;
						for (Integer slackVarIndex : projectionConsistencyInfo.slackVarsIndexes) {
							String slackVar = getSlackVarStringName(cliqueIndex, columnname, slackVarIndex);
							slackVarSum += Long.parseLong(model.evaluate(ctx.mkIntConst(slackVar), true).toString());
						}
						if (slackVarSum == 0) {
							infoWithZeroSlack = projectionConsistencyInfo;
							break;
						}
					}
					if (infoWithZeroSlack == null)
						DirtyCode.throwError("Wrong assumption");
					
					LinkedList<DirtyValueInterval> existingIntervalsAcrossOtherCliques = new LinkedList<>();
					for (ProjectionConsistencyInfo projectionConsistencyInfo : connectedProjectionConsistencyInfos) {
						if (projectionConsistencyInfo == infoWithZeroSlack)
							continue;
						HashMap<IntExpr, DirtyValueInterval> projVarToInterval = cliqueWiseProjVarToInterval.get(projectionConsistencyInfo.cindex);
						for (IntExpr projVar : projectionConsistencyInfo.projVars) {
							DirtyValueInterval interval = projVarToInterval.get(projVar);
							if (interval != null)
								DirtyCode.mergeValueInterval(existingIntervalsAcrossOtherCliques, interval);
						}
					}
					
					LinkedList<DirtyValueInterval> availableIntervalsOfInfoWithZeroSlack = cliqueWAvailableIntervals.get(infoWithZeroSlack.cindex);
					DirtyCode.intersectWithIntervals(existingIntervalsAcrossOtherCliques, availableIntervalsOfInfoWithZeroSlack, relationCardinality);

					HashMap<IntExpr, DirtyValueInterval> projVarToIntervalOfInfoWithZeroSlack = cliqueWiseProjVarToInterval.get(infoWithZeroSlack.cindex);
					for (IntExpr projVar : infoWithZeroSlack.projVars) {
						if (!projVarToIntervalOfInfoWithZeroSlack.containsKey(projVar)) {
							long count = Long.parseLong(model.evaluate(projVar, true).toString());
							if (count != 0 ) {
								DirtyValueInterval bestInterval = DirtyCode.getSuitableIntervalForProjVar(count, availableIntervalsOfInfoWithZeroSlack, existingIntervalsAcrossOtherCliques);
								DirtyCode.removeFromIntervals(bestInterval, existingIntervalsAcrossOtherCliques);
								DirtyCode.removeFromIntervals(bestInterval, availableIntervalsOfInfoWithZeroSlack);
								projVarToIntervalOfInfoWithZeroSlack.put(projVar, bestInterval);
							}
						}
					}
					
					LinkedList<DirtyValueInterval> existingIntervalsInInfoWithZeroSlack = new LinkedList<>();
					for (IntExpr projVar : infoWithZeroSlack.projVars) {
						DirtyValueInterval interval = projVarToIntervalOfInfoWithZeroSlack.get(projVar);
						if (interval != null) {
							DirtyCode.mergeValueInterval(existingIntervalsInInfoWithZeroSlack, interval);
						}
					}
					
					for (ProjectionConsistencyInfo projectionConsistencyInfo : connectedProjectionConsistencyInfos) {
						if (projectionConsistencyInfo == infoWithZeroSlack)
							continue;
						LinkedList<DirtyValueInterval> availableIntervals = cliqueWAvailableIntervals.get(projectionConsistencyInfo.cindex);
						HashMap<IntExpr, DirtyValueInterval> projVarToInterval = cliqueWiseProjVarToInterval.get(projectionConsistencyInfo.cindex);
						LinkedList<DirtyValueInterval> existingIntervals = DirtyCode.createCopyIntervals(existingIntervalsInInfoWithZeroSlack);
						DirtyCode.intersectWithIntervals(existingIntervals, availableIntervals, relationCardinality);
						for (IntExpr projVar : projectionConsistencyInfo.projVars) {
							if (!projVarToInterval.containsKey(projVar)) {
								long count = Long.parseLong(model.evaluate(projVar, true).toString());
								if (count != 0 ) {
									DirtyValueInterval bestInterval = DirtyCode.getSuitableIntervalForProjVar(count, availableIntervals, existingIntervals);
									DirtyCode.removeFromIntervals(bestInterval, existingIntervals);
									DirtyCode.removeFromIntervals(bestInterval, availableIntervals);
									projVarToInterval.put(projVar, bestInterval);
								}
							}
						}
					}
					
				}
				regionWCliqueWAvailableIntervals.put(region, cliqueWAvailableIntervals);
			}
			columnWRegionWCliqueWAvailableIntervals.put(columnname, regionWCliqueWAvailableIntervals);
		}
        
        // Assigning intervals to projVars which do not take part in any consistency constraint
		for (int cliqueIndex = 0; cliqueIndex < cliqueCount; cliqueIndex++) {
        	HashMap<String, ProjectionStuffInColumn> columnWiseProjectionStuff = cliqueWColumnWProjectionStuff.get(cliqueIndex);
			HashMap<IntExpr, DirtyValueInterval> projVarToInterval = cliqueWiseProjVarToInterval.get(cliqueIndex);
			for (Entry<String, ProjectionStuffInColumn> entry : columnWiseProjectionStuff.entrySet()) {
				String columnname = entry.getKey();
				ProjectionStuffInColumn projectionStuffInColumn = entry.getValue();
				for (Entry<Region, ProjectionStuffInSSPRegion> regionAndProjectionStuff : projectionStuffInColumn.getMapSSPRegionToProjectionStuff().entrySet()) {
					Region region = regionAndProjectionStuff.getKey();
					ProjectionStuffInSSPRegion projectionStuff = regionAndProjectionStuff.getValue();
					Set<IntExpr> projVarsInSSPRegion = projectionStuff.getAllProjVars();

					HashMap<Region, List<LinkedList<DirtyValueInterval>>> regionWCliqueWAvailableIntervals = columnWRegionWCliqueWAvailableIntervals.get(columnname);
					if (regionWCliqueWAvailableIntervals == null) {
						regionWCliqueWAvailableIntervals = new HashMap<>();
						columnWRegionWCliqueWAvailableIntervals.put(columnname, regionWCliqueWAvailableIntervals);
					}
					List<LinkedList<DirtyValueInterval>> cliqueWAvailableIntervals = regionWCliqueWAvailableIntervals.get(region);
					if (cliqueWAvailableIntervals == null) {
						cliqueWAvailableIntervals = new ArrayList<>(cliqueCount);
						for (int j = 0; j < cliqueCount; ++j) {
							LinkedList<DirtyValueInterval> temp = new LinkedList<>();
							temp.add(new DirtyValueInterval(0, relationCardinality));
							cliqueWAvailableIntervals.add(temp);
						}
						regionWCliqueWAvailableIntervals.put(region, cliqueWAvailableIntervals);
					}
					LinkedList<DirtyValueInterval> availableIntervals = cliqueWAvailableIntervals.get(cliqueIndex);
					
					for (IntExpr projVar : projVarsInSSPRegion) {
						if (!projVarToInterval.containsKey(projVar)) {
							long count = Long.parseLong(model.evaluate(projVar, true).toString());
							if (count != 0) {
								DirtyValueInterval bestInterval = DirtyCode.getSuitableIntervalForProjVar(count, availableIntervals, null);
								DirtyCode.removeFromIntervals(bestInterval, availableIntervals);
								projVarToInterval.put(projVar, bestInterval);
							}
						}
					}
				}
			}
		}
		
		// Finding MaxUniqePoints per sspRegion
		for (Entry<String, HashMap<Region, List<LinkedList<DirtyValueInterval>>>> outerEntry : columnWRegionWCliqueWAvailableIntervals.entrySet()) {
			String columnname = outerEntry.getKey();
			HashMap<Region, List<LinkedList<DirtyValueInterval>>> regionWCliqueWAvailableIntervals = outerEntry.getValue();
			HashMap<Region, Long> sspRegionToMaxUniqePoints = new HashMap<>();
			for (Entry<Region, List<LinkedList<DirtyValueInterval>>> innerEntry : regionWCliqueWAvailableIntervals.entrySet()) {
				Region region = innerEntry.getKey();
				List<LinkedList<DirtyValueInterval>> cliqueWAvailableIntervals = innerEntry.getValue();
				long maxEnd = 0;
				for (LinkedList<DirtyValueInterval> availableIntervals : cliqueWAvailableIntervals) {
					long end = availableIntervals.getLast().start;
					if (end > maxEnd)
						maxEnd = end;
				}
				sspRegionToMaxUniqePoints.put(region, maxEnd);
				
				long maxint = Integer.MAX_VALUE;
				if (maxEnd >= maxint)	// Search "LongIndexNeeded" in this code
					DirtyCode.throwError("problem");
			}
			columnWSSPRegionToMaxUniqePoints.put(columnname, sspRegionToMaxUniqePoints);
		}
	}

	private boolean containsOnlySlacks(List<IntExpr> c2NewVars) {
		for (IntExpr intExpr : c2NewVars) {
			if (!intExpr.toString().startsWith(slackVarNamePrefix))
				return false;
		}
		return true;
	}

	private void createNonAggVarsToProjectionValues(Model model, Context ctxPhase2, Model modelPhase2, ProjectionStuffInColumn projectionStuffInColumn, Set<Integer> slackVarsIndexes, 
			String columnname, Long maxUniqePoints, HashMap<IntExpr, ProjectionValues> varsToProjectionValues, int colIndx, int cindex) {
		List<Set<IntExpr>> listOfAtomicSetOfNonAggVars = projectionStuffInColumn.getListOfAtomicSetOfNonAggVars();
		for (Integer slackVarIndex : slackVarsIndexes) {
			Set<IntExpr> atomicSetOfNonAggVars = listOfAtomicSetOfNonAggVars.get(slackVarIndex);
    		long atomicSetRowCount = 0;
    		for (IntExpr nonAggVar : atomicSetOfNonAggVars) {
    			long rowcount = Long.parseLong(model.evaluate(nonAggVar, true).toString());
    			atomicSetRowCount += rowcount;
			}
    		if (atomicSetRowCount > 0) {
    			String slackVarName = getSlackVarStringName(cindex, columnname, slackVarIndex);
    			
    			Iterator<IntExpr> it = atomicSetOfNonAggVars.iterator();
				IntExpr curNonAggVar = null;
				long curNonAggVarUsableSize = 0;
				do {
					curNonAggVar = it.next();		// This should not throw error!
					curNonAggVarUsableSize = Long.parseLong(model.evaluate(curNonAggVar, true).toString());
				} while (curNonAggVarUsableSize == 0);
				ProjectionValues projectionValues = getOrAdd(varsToProjectionValues, curNonAggVar);		// projectionValues in one nonAggVar
				
				long prevOccurrence = -1;
				long startFrom = -1;
				long lastSeenI = -1;
				
				outerloop:
				for (long i = -1, curOccurrence = 0;;) {
					do {
						++i;
						if (i == maxUniqePoints)
							break;
						IntExpr intExpr = ctxPhase2.mkIntConst(slackVarName + "_" + i);
						curOccurrence = Long.parseLong(modelPhase2.evaluate(intExpr, true).toString());
					} while (curOccurrence == 0);

					if (i == maxUniqePoints)
						break;
					
					if (lastSeenI+1 != i) {		// If i's are not continuous then need to end interval
						if (prevOccurrence > 0) {
							projectionValues.addToList(colIndx, startFrom, lastSeenI+1, prevOccurrence);	// excluding i i.e. last point
						}
						
						boolean changed = false;
						while (curNonAggVarUsableSize == 0) {
							if (it.hasNext())
								curNonAggVar = it.next();
							else
								break outerloop;
							curNonAggVarUsableSize = Long.parseLong(model.evaluate(curNonAggVar, true).toString());
							changed = true;
						}
						if (changed)
							projectionValues = getOrAdd(varsToProjectionValues, curNonAggVar);
						prevOccurrence = -1;
						startFrom = -1;
					}
					
					if (curOccurrence == prevOccurrence) {
						if (curNonAggVarUsableSize >= curOccurrence) {
							curNonAggVarUsableSize -= curOccurrence;
						} else {
							// Saving previous points
							projectionValues.addToList(colIndx, startFrom, i, prevOccurrence);
							// Saving current point instances which can be accommodated in curNonAggVar
							projectionValues.addToList(colIndx, i, i+1, curNonAggVarUsableSize);
							curOccurrence -= curNonAggVarUsableSize;
							while (true) {
								do {
									if (it.hasNext())
										curNonAggVar = it.next();
									else
										break outerloop;
									curNonAggVarUsableSize = Long.parseLong(model.evaluate(curNonAggVar, true).toString());
								} while (curNonAggVarUsableSize == 0);
								projectionValues = getOrAdd(varsToProjectionValues, curNonAggVar);
								if (curNonAggVarUsableSize >= curOccurrence) {
									curNonAggVarUsableSize -= curOccurrence;		// space used by i'th value
									prevOccurrence = curOccurrence;
									startFrom = i;
									break;
								}
								else {
									projectionValues.addToList(colIndx, i, i+1, curNonAggVarUsableSize);
									curOccurrence -= curNonAggVarUsableSize;
								}
							}
						}
					} else {
						if (prevOccurrence > 0) {
							projectionValues.addToList(colIndx, startFrom, i, prevOccurrence);	// excluding i i.e. last point
						}
						if (curNonAggVarUsableSize >= curOccurrence) {
							curNonAggVarUsableSize -= curOccurrence;
						} else {		// curNonAggVarUsableSize can't accommodate curCount
							do {
								projectionValues.addToList(colIndx, i, i+1, curNonAggVarUsableSize);
								curOccurrence -= curNonAggVarUsableSize;
								do {
									if (it.hasNext())
										curNonAggVar = it.next();
									else
										break outerloop;
									curNonAggVarUsableSize = Long.parseLong(model.evaluate(curNonAggVar, true).toString());
								} while (curNonAggVarUsableSize == 0);
								projectionValues = getOrAdd(varsToProjectionValues, curNonAggVar);
							} while (curNonAggVarUsableSize < curOccurrence);
							curNonAggVarUsableSize -= curOccurrence;		// space used by i'th value
						}
						prevOccurrence = curOccurrence;
						startFrom = i;
					}
					
					if (curNonAggVarUsableSize == 0) {
						if (prevOccurrence > 0) {
							projectionValues.addToList(colIndx, startFrom, i+1, prevOccurrence);	// excluding i i.e. last point
						}
						prevOccurrence = -1;
						startFrom = -1;
						do {
							if (it.hasNext())
								curNonAggVar = it.next();
							else
								break outerloop;
							curNonAggVarUsableSize = Long.parseLong(model.evaluate(curNonAggVar, true).toString());
						} while (curNonAggVarUsableSize == 0);
						projectionValues = getOrAdd(varsToProjectionValues, curNonAggVar);
					}
					lastSeenI = i;
				}
				
//				if (i == maxUniqePoints) it.hasNext()
				
				if (prevOccurrence > 0)
					DirtyCode.throwError("Problem!");
//					projectionValues.addToList(colIndx, startFrom, lastSeenI+1, prevOccurrence);
				
				// Filling leftover space with default value
				if (curNonAggVarUsableSize != 0)
					DirtyCode.throwError("Problem!");
//					projectionValues.fillLeftoverSpaceWithDefault(colIndx, curNonAggVarUsableSize);
				
				// Filling leftover space of leftover nonAggVars with default value
				while (it.hasNext()) {
					DirtyCode.throwError("Problem!");
//					curNonAggVar = it.next();
//					curNonAggVarUsableSize = Long.parseLong(modelouuuuu.evaluate(curNonAggVar, true).toString());
//					if (curNonAggVarUsableSize != 0) {
//						projectionValues = getOrAdd(varsToProjectionValues, curNonAggVar);
//						projectionValues.fillLeftoverSpaceWithDefault(colIndx, curNonAggVarUsableSize);
//					}
				}
    		}
		}
		
		// sanity check: total projection values = count of selection values
		for (Entry<IntExpr, ProjectionValues> entry : varsToProjectionValues.entrySet()) {
			IntExpr var = entry.getKey();
			ProjectionValues values = entry.getValue();
			long rowcount = Long.parseLong(model.evaluate(var, true).toString());
			long projectionCount = values.getTotalCount(colIndx);
			if (projectionCount == -1)
				continue;
			if (rowcount != projectionCount)
				DirtyCode.throwError("Problem!");
		}
	}

	private void createAggVarsToProjectionValues(Model model, Context ctxPhase2, Model modelPhase2, ProjectionStuffInSSPRegion projectionStuffInSSPRegion, HashMap<IntExpr, DirtyValueInterval> projVarToInterval, 
			String columnname, Long maxUniqePoints, HashMap<IntExpr, ProjectionValues> varsToProjectionValues, int colIndx, int cindex) {
		
		for (Entry<IntExpr, List<IntExpr>> entry : projectionStuffInSSPRegion.getAggVarsToProjVars().entrySet()) {
			IntExpr aggVar = entry.getKey();
			List<IntExpr> projVars = entry.getValue();
			long rowcount = Long.parseLong(model.evaluate(aggVar, true).toString());
			if (rowcount == 0)
				continue;
			ProjectionValues projectionValues = getOrAdd(varsToProjectionValues, aggVar);		// projectionValues in one aggVar
			String aggVarName = aggVar.toString();
			for (IntExpr projVar : projVars) {		// Every interval is disjoint
				DirtyValueInterval interval = projVarToInterval.get(projVar);	// If interval was null then projVar value was 0
				if (interval != null) {
					long prevCount = -1;
					long startFrom = -1;
					for(long i = interval.start; i < interval.end; ++i) {
						IntExpr intExpr = ctxPhase2.mkIntConst("n_" + aggVarName + "_" + i);
						long curCount = Long.parseLong(modelPhase2.evaluate(intExpr, true).toString());
						if (curCount != prevCount) {
							if (prevCount != -1)
								projectionValues.addToList(colIndx, startFrom, i, prevCount);	// excluding i i.e. last point
							prevCount = curCount;
							startFrom = i;
						}
					}
					projectionValues.addToList(colIndx, startFrom, interval.end, prevCount);
				}
			}
		}
	}

	private void createPointWiseConstraints(Model model, Solver solverPhase2, Context ctxPhase2, ProjectionConsistencyInfo projectionConsistencyInfo, List<HashMap<String, ProjectionStuffInColumn>> cliqueWColumnWProjectionStuff, 
			List<HashMap<IntExpr, DirtyValueInterval>> cliqueWiseProjVarToInterval, 
			List<List<IntExpr>> pointWListOfNewVars, String columnname, long maxUniqePoints) {
		
		int cindex = projectionConsistencyInfo.cindex;
		ProjectionStuffInColumn projectionStuffInColumn = cliqueWColumnWProjectionStuff.get(cindex).get(columnname);
		HashMap<IntExpr, DirtyValueInterval> projVarToInterval = cliqueWiseProjVarToInterval.get(cindex);
		
    	HashMap<IntExpr, List<IntExpr>> aggVarsToProjVars = projectionStuffInColumn.getAggVarsToProjVars();
		Set<IntExpr> aggVars = projectionConsistencyInfo.aggVars;
    	for (IntExpr aggVar : aggVars) {
			long rowcount = Long.parseLong(model.evaluate(aggVar, true).toString());
			if (rowcount == 0)
				continue;
			String aggVarName = aggVar.toString();
			List<IntExpr> projVars = aggVarsToProjVars.get(aggVar);
			List<IntExpr> addList = new ArrayList<>();
			for (IntExpr projVar : projVars) {		// Every interval is disjoint
				DirtyValueInterval interval = projVarToInterval.get(projVar);	// If interval was null then projVar value was 0
				if (interval != null)
					for(long i = interval.start; i < interval.end; ++i) {
						IntExpr intExpr = ctxPhase2.mkIntConst("n_" + aggVarName + "_" + i);
						addList.add(intExpr);
						solverPhase2.add(ctxPhase2.mkGe(intExpr, ctxPhase2.mkInt(1)));		// Must be greater than 0
						pointWListOfNewVars.get((int)i).add(intExpr);
					}
			}
			solverPhase2.add(ctxPhase2.mkEq(ctxPhase2.mkAdd(addList.toArray(new ArithExpr[addList.size()])), ctxPhase2.mkInt(rowcount)));
		}

		List<Integer> slackVarsIndexes = projectionConsistencyInfo.slackVarsIndexes;
    	List<Set<IntExpr>> listOfAtomicSetOfNonAggVars = projectionStuffInColumn.getListOfAtomicSetOfNonAggVars();
    	
    	for (Integer slackVarIndex : slackVarsIndexes) {
    		Set<IntExpr> atomicSetOfNonAggVars = listOfAtomicSetOfNonAggVars.get(slackVarIndex);
    		long atomicSetRowCount = 0;
    		for (IntExpr nonAggVar : atomicSetOfNonAggVars) {
    			long rowcount = Long.parseLong(model.evaluate(nonAggVar, true).toString());
    			atomicSetRowCount += rowcount;
			}
    		if (atomicSetRowCount > 0) {
				List<IntExpr> addList = new ArrayList<>();
    			String slackVarName = getSlackVarStringName(cindex, columnname, slackVarIndex);
    			for(long j = 0; j < maxUniqePoints; ++j) {
					IntExpr intExpr = ctxPhase2.mkIntConst(slackVarName + "_" + j);
					addList.add(intExpr);
					solverPhase2.add(ctxPhase2.mkGe(intExpr, ctxPhase2.mkInt(0)));
					pointWListOfNewVars.get((int)j).add(intExpr);
				}
    			solverPhase2.add(ctxPhase2.mkEq(ctxPhase2.mkAdd(addList.toArray(new ArithExpr[addList.size()])), ctxPhase2.mkInt(atomicSetRowCount)));
    		}
    	}
	}

	private String getSlackVarStringName(int cliqueIndex, String columnname, int slackVarIndex) {
		return slackVarNamePrefix + cliqueIndex + "_" + columnname + "_" + slackVarIndex;
	}

	private List<ProjectionConsistencyInfoPair> getCorrespondingRegionList(HashMap<Region, List<ProjectionConsistencyInfoPair>> sspRegionToAllProjectionConsistencyInfoPairs, HashMap<Region, ProjectionStuffInSSPRegion> sspRegionToProjectionStuff, IntExpr aVar) {
		for (Entry<Region, ProjectionStuffInSSPRegion> entry : sspRegionToProjectionStuff.entrySet()) {
			Region region = entry.getKey();
			ProjectionStuffInSSPRegion projectionStuffInSSPRegion = entry.getValue();
			HashSet<IntExpr> unionAggAndNonAggVars = new HashSet<>(projectionStuffInSSPRegion.getAggVars());
			unionAggAndNonAggVars.addAll(projectionStuffInSSPRegion.getNonAggVars());
			if (unionAggAndNonAggVars.contains(aVar)) {
				List<ProjectionConsistencyInfoPair> listOfProjectionConsistencyInfoPairs = sspRegionToAllProjectionConsistencyInfoPairs.get(region);
				if (listOfProjectionConsistencyInfoPairs == null) {
					listOfProjectionConsistencyInfoPairs = new ArrayList<>();
					sspRegionToAllProjectionConsistencyInfoPairs.put(region, listOfProjectionConsistencyInfoPairs);
				}
				return listOfProjectionConsistencyInfoPairs;
			}
		}
		throw new RuntimeException("Corresponding SSP region of aVar not found!");
	}

	private void collectProjectionConsistencyData(Optimize solver, Context ctx, List<IntExpr> c1Vars, List<IntExpr> c2Vars,
			int c1index, int c2index, Set<String> commonCols, List<ProjectionConsistencyInfoPair> projectionConsistencyInfoPairs, List<HashMap<String, ProjectionStuffInColumn>> cliqueWColumnWProjectionStuff) {
		HashMap<String, ProjectionStuffInColumn> c1ColumnWProjectionStuffInColumn = cliqueWColumnWProjectionStuff.get(c1index);
		HashMap<String, ProjectionStuffInColumn> c2ColumnWProjectionStuffInColumn = cliqueWColumnWProjectionStuff.get(c2index);
		
		for (String columnname : commonCols) {
			ProjectionStuffInColumn c1ProjectionStuffInColumn = c1ColumnWProjectionStuffInColumn.get(columnname);
			ProjectionStuffInColumn c2ProjectionStuffInColumn = c2ColumnWProjectionStuffInColumn.get(columnname);
			if (c1ProjectionStuffInColumn == null && c2ProjectionStuffInColumn == null)		// No projection on this column
				continue;
			
			if (c1ProjectionStuffInColumn == null || c2ProjectionStuffInColumn == null)
				throw new RuntimeException("Must not happen! Code must have handled this!");
			
			// Clique 1
			Set<IntExpr> c1AggVars = new HashSet<>();
			Set<IntExpr> c1NonAggVars = new HashSet<>();
			Set<IntExpr> c1ProjVars = new HashSet<>();
			getProjectionRelatedVars(c1Vars, c1ProjectionStuffInColumn, c1AggVars, c1NonAggVars, c1ProjVars);
			
			// Clique 2
			Set<IntExpr> c2AggVars = new HashSet<>();
			Set<IntExpr> c2NonAggVars = new HashSet<>();
			Set<IntExpr> c2ProjVars = new HashSet<>();
			getProjectionRelatedVars(c2Vars, c2ProjectionStuffInColumn, c2AggVars, c2NonAggVars, c2ProjVars);
			
			ProjectionConsistencyInfoPair projectionConsistencyInfoPair = new ProjectionConsistencyInfoPair(c1index, c2index, c1ProjVars, c1AggVars, c1NonAggVars, c2ProjVars, c2AggVars, c2NonAggVars, columnname);
			projectionConsistencyInfoPairs.add(projectionConsistencyInfoPair);
			c1ColumnWProjectionStuffInColumn.get(columnname).getConsistencyConstraintSetWNonAggVars().add(c1NonAggVars);
			c2ColumnWProjectionStuffInColumn.get(columnname).getConsistencyConstraintSetWNonAggVars().add(c2NonAggVars);
		}
	}
	
	private void getProjectionRelatedVars(List<IntExpr> vars, ProjectionStuffInColumn projectionStuffInColumn, Set<IntExpr> aggVars, Set<IntExpr> nonAggVars, Set<IntExpr> projVars) {
		Set<IntExpr> allAggVars;
		allAggVars = new HashSet<>(projectionStuffInColumn.getAggVarsToProjVars().keySet());
		aggVars.addAll(vars);
		aggVars.retainAll(allAggVars);
		nonAggVars.addAll(vars);
		nonAggVars.removeAll(allAggVars);
		
		HashMap<IntExpr, List<IntExpr>> aggVarsToProjVars = projectionStuffInColumn.getAggVarsToProjVars();
		for (IntExpr aggVar : aggVars) {
			projVars.addAll(aggVarsToProjVars.get(aggVar));
		}
	}

	private void dirtyMergeWithAlignment(IntList lhsColIndxs, List<DirtyValueCombinationWithProjectionValues> lhsValueCombinations, IntList rhsColIndxs, LinkedList<DirtyVariableValuePairWithProjectionValues> rhsVarValuePairs) {
		
		// Raghav didn't used retainAll in original mergeWithAlignment maybe because ordering was getting changed!
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
        List<DirtyValueCombinationWithProjectionValues> mergedValueCombinations = new ArrayList<>();
        for (DirtyValueCombinationWithProjectionValues lhsValueCombination : lhsValueCombinations) {
            IntList lhsColValues = lhsValueCombination.getColValues();
            long lhsRowcount = lhsValueCombination.getRowcount();
            ProjectionValues lhsProjectionValues = lhsValueCombination.getProjectionValues();

            for (ListIterator<DirtyVariableValuePairWithProjectionValues> rhsIter = rhsVarValuePairs.listIterator(); rhsIter.hasNext();) {
                DirtyVariableValuePairWithProjectionValues rhsVarValuePair = rhsIter.next();
                Region rhsVariable = rhsVarValuePair.variable;
                long rhsRowcount = rhsVarValuePair.rowcount;

                BucketStructure rhsCompatibleBS = getCompatibleBS(posInLHS, lhsColValues, posInRHS, rhsVariable);
                if (rhsCompatibleBS != null) {
                	
                	ProjectionValues rhsProjectionValues = rhsVarValuePair.getProjectionValues();
//                	if (lhsProjectionValues == null ^ rhsProjectionValues == null)		// Can happen if there is no projection on shared column but projection on non common column of one of the cliques
//                		DirtyCode.throwError("Should not happen!");
                	
                    IntList mergedColValues = new IntArrayList(mergedColIndxsList.size());
                    for (int j = 0; j < mergedColIndxsList.size(); j++) {
                        if (fromLHS[j]) {
                            mergedColValues.add(lhsColValues.getInt(correspOriginalIndx[j]));
                        } else {
                            mergedColValues.add(rhsCompatibleBS.at(correspOriginalIndx[j]).at(0));
                        }
                    }
                    
                    ProjectionValues mergedProjectionvalues = null;
                    long minMergable = -1;
                    if (lhsRowcount <= rhsRowcount)
                		minMergable = lhsRowcount;
                	else
                		minMergable = rhsRowcount;
                    
                    if (lhsProjectionValues == null && rhsProjectionValues == null) {	// No projection on any of columns of any clique
                    } else {
                    	if (lhsProjectionValues == null || rhsProjectionValues == null) {	// No shared projection column
                        	mergedProjectionvalues = new ProjectionValues();
                    		if (lhsProjectionValues != null)
                    			mergedProjectionvalues.takeFrom(lhsProjectionValues, minMergable, null);
                    		else
                    			mergedProjectionvalues.takeFrom(rhsProjectionValues, minMergable, null);
                    	} else {
                    		Set<Integer> sharedProjectionCols = new HashSet<>(lhsProjectionValues.keySet());
                    		sharedProjectionCols.retainAll(rhsProjectionValues.keySet());
                    		if (sharedProjectionCols.size() == 0) {	// No shared projection column
                            	mergedProjectionvalues = new ProjectionValues();
                    			if (lhsProjectionValues != null)
                        			mergedProjectionvalues.takeFrom(lhsProjectionValues, minMergable, null);
                    			if (rhsProjectionValues != null)
                        			mergedProjectionvalues.takeFrom(rhsProjectionValues, minMergable, null);
                    		} else {	// Shared projection columns present
                    			mergedProjectionvalues = DirtyCode.getIntersectingProjectionValues(sharedColIndxs, lhsProjectionValues, rhsProjectionValues);	// Returns intersecting projection values for shared indexes and remove those values from lhsProjectionValues and rhsProjectionValues
                    			minMergable = mergedProjectionvalues.getTotalCount();
                    			if (minMergable > 0) {
                    				mergedProjectionvalues.takeFrom(lhsProjectionValues, minMergable, sharedProjectionCols);	// Getting projection values from lhsProjectionValues for those columns which were not present in sharedProjectionCols
                    				mergedProjectionvalues.takeFrom(rhsProjectionValues, minMergable, sharedProjectionCols);	// Getting projection values from rhsProjectionValues for those columns which were not present in sharedProjectionCols
                    			}
                    		}
                    	}
                    }
                    if (minMergable > 0) {
                    	DirtyValueCombinationWithProjectionValues mergedValueCombination = new DirtyValueCombinationWithProjectionValues(mergedColValues, minMergable, mergedProjectionvalues);
                        mergedValueCombinations.add(mergedValueCombination);
                        lhsValueCombination.reduceRowcount(minMergable);
                        lhsRowcount = lhsValueCombination.getRowcount();
                        rhsVarValuePair.rowcount -= minMergable;
                        if (rhsVarValuePair.rowcount == 0) {
                            rhsIter.remove();
                        }
                        if (lhsRowcount == 0)
                        	break;
                    }
                }
            }
        }
        
        boolean acceptErrorsWhenRegionMismatch = true;
        
        //if (DebugHelper.sanityChecksNeeded()) {
        for (DirtyValueCombinationWithProjectionValues lhsValueCombination : lhsValueCombinations) {
            if (lhsValueCombination.getRowcount() != 0) {
            	if (!acceptErrorsWhenRegionMismatch)
            		throw new RuntimeException("Found while merge ValueCombination " + lhsValueCombination + " in LHS with unmet rowcount");
            	Pair<DirtyVariableValuePairWithProjectionValues, BucketStructure> bestMatchPair = DirtyCode.findBestMatch(lhsValueCombination, rhsVarValuePairs, posInLHS, posInRHS);
            	if (bestMatchPair.getFirst() == null)
            		throw new RuntimeException("No rhs Var found with same rowcount and projectionValues!");
            	DirtyVariableValuePairWithProjectionValues bestMatchRHSVariableValuePair = bestMatchPair.getFirst();
            	BucketStructure bestMatchRHS_BS = bestMatchPair.getSecond();
            	long rowCount = lhsValueCombination.getRowcount();
            	IntList mergedColValues = new IntArrayList(mergedColIndxsList.size());
                for (int j = 0; j < mergedColIndxsList.size(); j++) {
                    if (fromLHS[j]) {
                        mergedColValues.add(lhsValueCombination.getColValues().getInt(correspOriginalIndx[j]));
                    } else {
                        mergedColValues.add(bestMatchRHS_BS.at(correspOriginalIndx[j]).at(0));
                    }
                }
                ProjectionValues mergedProjectionvalues = lhsValueCombination.getProjectionValues();
                mergedProjectionvalues.takeFrom(bestMatchRHSVariableValuePair.getProjectionValues(), rowCount, mergedProjectionvalues.keySet());
                
                
                DirtyValueCombinationWithProjectionValues mergedValueCombination = new DirtyValueCombinationWithProjectionValues(mergedColValues, rowCount, mergedProjectionvalues);
                mergedValueCombinations.add(mergedValueCombination);
            	lhsValueCombination.reduceRowcount(rowCount);
            	rhsVarValuePairs.remove(bestMatchRHSVariableValuePair);
            }
        }
        if (!rhsVarValuePairs.isEmpty())
            throw new RuntimeException("Found while merge RHS variables not getting exhausted");

        //Updating targetColIndxs
        lhsColIndxs.clear();
        lhsColIndxs.addAll(mergedColIndxsList);

        //Updating targetValueCombinations
        lhsValueCombinations.clear();
        lhsValueCombinations.addAll(mergedValueCombinations);
	}

	private ProjectionValues getOrAdd(HashMap<IntExpr, ProjectionValues> varsToProjectionValues, IntExpr key) {
		ProjectionValues value = varsToProjectionValues.get(key);
		if (value == null) {
			value = new ProjectionValues();
			varsToProjectionValues.put(key, value);
		}
		return value;
	}

	private ViewSolution mergeCliqueSolutions(List<LinkedList<VariableValuePair>> cliqueIdxToVarValuesList) {

        IntList mergedColIndxs = new IntArrayList();
        List<ValueCombination> mergedValueCombinations = new ArrayList<>();

        mergedColIndxs.addAll(arasuCliquesAsColIndxs.get(0));
        //Instantiating variables of first clique
        for (VariableValuePair varValuePair : cliqueIdxToVarValuesList.get(0)) {
            IntList columnValues = getFloorInstantiation(varValuePair.variable);
            ValueCombination valueCombination = new ValueCombination(columnValues, varValuePair.rowcount);
            mergedValueCombinations.add(valueCombination);
        }

        for (int i = 1; i < cliqueCount; i++) {		// merging with other cliques
            mergeWithAlignment(mergedColIndxs, mergedValueCombinations, arasuCliquesAsColIndxs.get(i), cliqueIdxToVarValuesList.get(i));
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
        //choose BS with min bucket floors
        BucketStructure leadingBS = variable.getLeadingBS();
        IntList columnValues = new IntArrayList(leadingBS.getAll().size());
        for (Bucket b : leadingBS.getAll()) {
            columnValues.add(b.min());
        }
        return columnValues;
    }

    /**
     * lhs has instantiated ValueCombinations. Each lhs ValueCombination is extended by widthwise appending instantiated tuples from appropriate BucketStructure of compatible rhs variable(s).
     *     lhsColIndxs and lhsValueCombinations get side effects.
     *     rhsColIndxs gets NO side effects.
     *     rhsVarValuePairs gets exhausted and becomes empty.
     * TODO: Could have been some smart alignment which prevents extra tuples to be added to primary view
     * @param lhsColIndxs
     * @param lhsValueCombinations
     * @param rhsColIndxs
     * @param sourceValueCombinations
     */
    private void mergeWithAlignment(IntList lhsColIndxs, List<ValueCombination> lhsValueCombinations, IntList rhsColIndxs,
            LinkedList<VariableValuePair> rhsVarValuePairs) {

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

        //if (DebugHelper.sanityChecksNeeded()) {
        for (ValueCombination lhsValueCombination : lhsValueCombinations) {
            if (lhsValueCombination.getRowcount() != 0)
                throw new RuntimeException("Found while merge ValueCombination " + lhsValueCombination + " in LHS with unmet rowcount");
        }
        if (!rhsVarValuePairs.isEmpty())
            throw new RuntimeException("Found while merge RHS variables not getting exhausted");

        //Updating targetColIndxs
        lhsColIndxs.clear();
        lhsColIndxs.addAll(mergedColIndxsList);

        //Updating targetValueCombinations
        lhsValueCombinations.clear();
        lhsValueCombinations.addAll(mergedValueCombinations);
    }

    private static BucketStructure getCompatibleBS(IntList posInLHS, IntList lhsColValues, IntList posInRHS, Region var) {
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
    
    private HashMap<String, ProjectionStuffInColumn> getColumnWiseAggAndNonAggVarsInSingleSplitPointRegion(Set<String> clique, List<List<IntExpr>> solverConstraints, HashMap<String, 
    		Set<IntExpr>> columnWiseVarsInAllAggregateConditions, Map<String, List<Region>> aggregateColumnsToSingleSplitPointRegions, int offsetForSingleSplitPointRegions, ArrayList<String> sortedAggCols) {
    	HashMap<String, ProjectionStuffInColumn> result = new HashMap<>();
        int tempIndex = 0;
        for (String columnname : sortedAggCols) {
			if (clique.contains(columnname)) {
				ProjectionStuffInColumn projectionStuffInColumn = new ProjectionStuffInColumn();
				
				Set<IntExpr> blocksInAllAggregateConditions = columnWiseVarsInAllAggregateConditions.getOrDefault(columnname, new HashSet<>()); // This clique might not have any aggregate condition on this column, hence getOrDefault
				List<Region> splitPointRegions = aggregateColumnsToSingleSplitPointRegions.get(columnname);
				for (int splitPointIndex = 0; splitPointIndex < splitPointRegions.size(); ++splitPointIndex) {
					// offsetForSingleSplitPointRegions + tempIndex is correct index because of consistent
					// ordering during multiple iterations of aggregateColumnsToSingleSplitPointRegions
					Set<IntExpr> aggBlocks = new HashSet<>(solverConstraints.get(offsetForSingleSplitPointRegions + tempIndex));
					Set<IntExpr> nonAggBlocks = new HashSet<>(aggBlocks);
					
					aggBlocks.retainAll(blocksInAllAggregateConditions);	// Only retain those blocks which are also in aggregate conditions
					nonAggBlocks.removeAll(aggBlocks);	// Remove those blocks which are in aggregate conditions
					
					projectionStuffInColumn.putProjectionStuffInSSPRegion(splitPointRegions.get(splitPointIndex), new ProjectionStuffInSSPRegion(aggBlocks, nonAggBlocks));
					tempIndex++;
				}
				result.put(columnname, projectionStuffInColumn);
			}
		}
		return result;
	}

	private HashMap<String, Set<IntExpr>> getColumnWiseAggVarsInAllAggregateConditions(List<FormalCondition> conditions, List<List<IntExpr>> solverConstraints, List<Pair<Integer, Boolean>> applicableConditions) {
		
    	HashMap<String, Set<IntExpr>> result = new HashMap<>();
        for (int i = 0; i < applicableConditions.size(); ++i) {
        	Pair<Integer, Boolean> applicableConditionInfo = applicableConditions.get(i);
        	if (applicableConditionInfo.getSecond()) {	// Is the condition applied with projection or without projection 
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
			throw new RuntimeException("one << 63 will overflow and won't work correctly because long is used. Change type of 'one' to BigInt or something like that!");
		long one = 1;
        for (int i = 0; i < (one << size); i++)
        {
        	List<IntExpr> newSet = new ArrayList<>();		// using list to save on memory because set properties are not required
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
        powerSet.remove(new ArrayList<>());		// removing empty set
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
     * cliqueIndextoPList stores current partition (set of variables) of every clique.
     * This method takes two (intersecting) cliques i and j as input and replaces
     *     cliqueIndextoPList[i] with a newer partition (a fresh set of variables)
     *     cliqueIndextoPList[j] with a newer partition (a fresh set of variables)
     * such that these newer variables of the two cliques can be used to frame consistency conditions later.
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
        Partition freshPartitionI = getFreshVariables(parentOldVarIdsI, partitionI, splitRegions, intersectingColIndices);
        cliqueIdxtoPList.set(i, freshPartitionI);
        List<IntList> sourceListI = cliqueIdxtoPSimplifiedList.get(i);
        List<IntList> freshListI = new ArrayList<>(freshPartitionI.size());
        for (int a = 0; a < freshPartitionI.size(); a++) {
            freshListI.add(sourceListI.get(parentOldVarIdsI.getInt(a)));
        }
        cliqueIdxtoPSimplifiedList.set(i, freshListI);

        IntArrayList parentOldVarIdsJ = new IntArrayList();
        Partition freshPartitionJ = getFreshVariables(parentOldVarIdsJ, partitionJ, splitRegions, intersectingColIndices);
        cliqueIdxtoPList.set(j, freshPartitionJ);
        List<IntList> sourceListJ = cliqueIdxtoPSimplifiedList.get(j);
        List<IntList> freshListJ = new ArrayList<>(freshPartitionJ.size());
        for (int a = 0; a < freshPartitionJ.size(); a++) {
            freshListJ.add(sourceListJ.get(parentOldVarIdsJ.getInt(a)));
        }
        cliqueIdxtoPSimplifiedList.set(j, freshListJ);

        CliqueIntersectionInfo cliqueIntersectionInfo = new CliqueIntersectionInfo(i, j, intersectingColIndices);
        //cliqueIntersectionInfo.splitRegions = splitRegions;
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
     * Returns a Partition with freshVariables and also populated parentOldVarIds of same length storing which oldVarId it came from
     * @param parentOldVarIds
     * @param oldPartition
     * @param splitRegions
     * @param intersectingColIndices
     * @return
     */
    private Partition getFreshVariables(IntList parentOldVarIds, Partition oldPartition, List<Region> splitRegions, IntList intersectingColIndices) {

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

                Region freshRegion = new Region(); //stores list of untruncated bs which come from intersection of oldRegion and splitRegion
                Region remainRegion = new Region(); //stores list of untruncated bs which come from oldRegion minus splitRegion
                for (BucketStructure oldBS : oldRegion.getAll()) { //need to do bs by bs so that untruncing is possible
                    Region oldSingleBSRegion = new Region();
                    oldSingleBSRegion.add(oldBS);
                    Region truncOldSingleBSRegion = getTruncatedRegion(oldSingleBSRegion, intersectingColIndices);
                    Region truncOverlap = truncOldSingleBSRegion.intersection(splitRegion);
                    if (truncOverlap.isEmpty()) {
                        remainRegion.add(oldBS);
                    } else {
                        Region untruncOverlap = getUntruncatedRegion(truncOverlap, oldSingleBSRegion, intersectingColIndices);
                        freshRegion.addAll(untruncOverlap.getAll());

                        Region remainTruncRegion = truncOldSingleBSRegion.minus(truncOverlap);
                        if (!remainTruncRegion.isEmpty()) {
                            Region remainUntruncRegion = getUntruncatedRegion(remainTruncRegion, oldSingleBSRegion, intersectingColIndices);
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
            throw new RuntimeException("Expected oldRegions to be empty here. oldRegions " + oldRegions.size() + " and oldRegionIds " + oldRegionIds.size());

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
            throw new RuntimeException("Can only untruncate Regions with single BucketStructure in donor but found " + donorRegion.getAll().size());

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
    
    private void addTo_ConditionListToPairOfVarList(List<List<IntExpr>> applicableSolverConstraints, HashMap<IntList, MutablePair<List<IntExpr>, List<IntExpr>>> conditionListToSetOfVarList) {
    	HashMap<IntExpr, IntList> varToConditionList = new HashMap<>();
		for (int i = 0; i < applicableSolverConstraints.size(); i++) {
			for (IntExpr var : applicableSolverConstraints.get(i)) {	// For every region which satisfy i'th condition
				if(!varToConditionList.containsKey(var))
					varToConditionList.put(var, new IntArrayList());
				varToConditionList.get(var).add(i);
			}
		}
		HashMap<IntList, List<IntExpr>> conditionListToVarList = new HashMap<>();
        for (Entry<IntExpr, IntList> entry : varToConditionList.entrySet()) {
        	IntExpr var = entry.getKey();
        	IntList conditionsList = entry.getValue();
			if(!conditionListToVarList.containsKey(conditionsList)) {
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
//			if(!conditionListToSetOfVarList.containsKey(entry.getKey())) {
//				conditionListToSetOfVarList.put(entry.getKey(), new ArrayList<>(2));
//			}
//			conditionListToSetOfVarList.get(entry.getKey()).add(entry.getValue());
		}
    }

	

	
}

class CliqueIntersectionInfo {
    final int     i;
    final int     j;
    final IntList intersectingColIndices;
    //List<Region> splitRegions;

    public CliqueIntersectionInfo(int i, int j, IntList intersectingColIndices) {
        this.i = i;
        this.j = j;
        this.intersectingColIndices = intersectingColIndices;
    }
}



class ProjectionConsistencyInfoPair {
	final Pair<ProjectionConsistencyInfo, ProjectionConsistencyInfo> pair;
	final String columnname;
	public ProjectionConsistencyInfoPair(int c1index, int c2index, Set<IntExpr> c1ProjVars, Set<IntExpr> c1AggVars, Set<IntExpr> c1NonAggVars, Set<IntExpr> c2ProjVars, Set<IntExpr> c2AggVars, Set<IntExpr> c2NonAggVars, String columnname) {
		ProjectionConsistencyInfo first = new ProjectionConsistencyInfo(c1index, c1ProjVars, c1AggVars, c1NonAggVars);
		ProjectionConsistencyInfo second = new ProjectionConsistencyInfo(c2index, c2ProjVars, c2AggVars, c2NonAggVars);
		this.columnname = columnname;
		pair = new Pair<ProjectionConsistencyInfo, ProjectionConsistencyInfo>(first, second);
	}
	
	public ProjectionConsistencyInfo getFirst() {
		return pair.getFirst();
	}
	
	public ProjectionConsistencyInfo getSecond() {
		return pair.getSecond();
	}
	
	public void setSlackVarsIndexes(List<Integer> c1SlackVarsIndexes, List<Integer> c2SlackVarsIndexes) {
		pair.getFirst().setSlackVarsIndexes(c1SlackVarsIndexes);
		pair.getSecond().setSlackVarsIndexes(c2SlackVarsIndexes);
	}
}

class ProjectionConsistencyInfo {
	final int cindex;
	final Set<IntExpr> projVars;
	final Set<IntExpr> aggVars;
	final Set<IntExpr> nonAggVars;
	List<Integer> slackVarsIndexes;
	public ProjectionConsistencyInfo(int cindex, Set<IntExpr> projVars, Set<IntExpr> aggVars, Set<IntExpr> nonAggVars) {
		this.cindex = cindex;
		this.projVars = projVars;
		this.aggVars = aggVars;
		this.nonAggVars = nonAggVars;
	}
	
	public void setSlackVarsIndexes(List<Integer> slackVarsIndexes) {
		this.slackVarsIndexes = slackVarsIndexes;
	}
	
	@Override
    public int hashCode() {
        final int prime = 31;
        int result = cindex;
        result = prime * result + aggVars.hashCode();
        result = prime * result + nonAggVars.hashCode();
        return result;
    }

    @Override
    public boolean equals(Object obj) {
    	if (this == obj) return true;
    	if (getClass() != obj.getClass())
    		return false;
    	@SuppressWarnings("unchecked")
    	ProjectionConsistencyInfo that = (ProjectionConsistencyInfo)obj;
    	if (!aggVars.equals(that.aggVars))
    		return false;
    	if (!nonAggVars.equals(that.nonAggVars))
    		return false;
    	
    	return true;
    }
}