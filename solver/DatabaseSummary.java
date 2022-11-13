package in.ac.iisc.cds.dsl.cdgvendor.solver;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileWriter;
import java.io.IOException;
import java.io.PrintWriter;
import java.math.BigInteger;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Calendar;
import java.util.Collections;
import java.util.Date;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.concurrent.Callable;
import java.util.concurrent.ConcurrentHashMap;
import java.util.concurrent.ExecutionException;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.Future;

import org.apache.commons.lang.StringUtils;
import org.json.JSONArray;
import org.json.JSONObject;

import in.ac.iisc.cds.dsl.cdgclient.constants.PostgresCConfig;
import in.ac.iisc.cds.dsl.cdgvendor.constants.PostgresVConfig;
import in.ac.iisc.cds.dsl.cdgvendor.constants.PostgresVConfig.Key;
import in.ac.iisc.cds.dsl.cdgvendor.model.ColumnInfo;
import in.ac.iisc.cds.dsl.cdgvendor.model.ColumnPathInfo;
import in.ac.iisc.cds.dsl.cdgvendor.model.SchemaInfo;
import in.ac.iisc.cds.dsl.cdgvendor.model.SolverViewStats;
import in.ac.iisc.cds.dsl.cdgvendor.model.TableInfo;
import in.ac.iisc.cds.dsl.cdgvendor.model.ValueCombination;
import in.ac.iisc.cds.dsl.cdgvendor.model.VariableValuePair;
import in.ac.iisc.cds.dsl.cdgvendor.model.ViewInfo;
import in.ac.iisc.cds.dsl.cdgvendor.model.ViewSolution;
import in.ac.iisc.cds.dsl.cdgvendor.model.ViewSolutionDiskBased;
import in.ac.iisc.cds.dsl.cdgvendor.model.ViewSolutionInMemory;
import in.ac.iisc.cds.dsl.cdgvendor.model.ViewSolutionRegion;
import in.ac.iisc.cds.dsl.cdgvendor.model.ViewSolutionWithSolverStats;
import in.ac.iisc.cds.dsl.cdgvendor.reducer.Bucket;
import in.ac.iisc.cds.dsl.cdgvendor.reducer.BucketStructure;
import in.ac.iisc.cds.dsl.cdgvendor.reducer.Region;
import in.ac.iisc.cds.dsl.cdgvendor.solver.DatabaseSummary.NewRegionIntersectionHelperByMultiThreading;
import in.ac.iisc.cds.dsl.cdgvendor.solver.Z3Solver.SpillType;
import in.ac.iisc.cds.dsl.cdgvendor.utils.DebugHelper;
import in.ac.iisc.cds.dsl.cdgvendor.utils.FileUtils;
import in.ac.iisc.cds.dsl.cdgvendor.utils.SharedBoolean;
import in.ac.iisc.cds.dsl.cdgvendor.utils.StopWatch;
import it.unimi.dsi.fastutil.ints.Int2DoubleOpenHashMap;
import it.unimi.dsi.fastutil.ints.Int2ObjectOpenHashMap;
import it.unimi.dsi.fastutil.ints.IntArrayList;
import it.unimi.dsi.fastutil.ints.IntIterator;
import it.unimi.dsi.fastutil.ints.IntList;
import it.unimi.dsi.fastutil.objects.Object2IntMap;
import it.unimi.dsi.fastutil.objects.Object2IntOpenHashMap;


/*
 *  TODO :  1. Make code for region union
 * 			2. Use Region union and minus code for assigning error cardinality as 1
 * 			3. Change name to projected from projected
 * 			4. Check code correctness!! 
 *  
 * 			5. MultiMap for 2 fk -> 1 pk // just check for it whether it's occuring or not
 * 			6. Assign [0] to fkColumns in pkView
 * 			7. region cardinality
 * 
 */

public class DatabaseSummary {

    private static final String             NEWLINE = "\n";
    private static final String             COMMA   = ",";

    //private static final String CURRENT_CONTEXT = "1GBHFOE";
    
    private final StopWatch                 databaseSummarySW;
    private final SpillType                 spillType;
    private final Map<String, ViewSolution> viewSolutions;
    //private final Map<String, ViewSolutionRegion> viewSolutionsRegion;
    private ConcurrentHashMap<String,ConcurrentHashMap<String, VariableValuePair>> seqNumberToVariableValuePairViewMap;  // For each View maps a seqNo to VariableValuePair of that view
    private ConcurrentHashMap<String,ConcurrentHashMap<String,Set<String>>> pkSeqNumtoFkSeqNumListforFKView; // maps for each fkView regions to pkView Regions using seqNumber mapping
    private ConcurrentHashMap<String,ConcurrentHashMap<String,Set<String>>> FkSeqNumtoPkSeqNumListforFKview; // maps the fk view region to list of pk view regions
    private Map<String,List<String>> pkViewToFkViewMap;  // maps a list of fkview corresponding to a pkview
    private Map<String,Integer> RegionIntervalMap; // key : region_seqno value: interval_start + " to " interval_end
    private Map<String,List<Long>> IntervalDomainMap;
    private Map<String,Integer> viewErrorCountMap;
    
    private Map<String,List<String>> OrderedRegionMapParallelToIntervalDomainMap;
    
    private boolean                         isConsistent;
    private boolean                         isCompressed;
    
    class FKeyClass {
    	
		String fkColumnName;  // column name of fk table
    	String pkColumnName;  // column name of pk table
    	List<String> pkRegionSeqNum;
    	
		public FKeyClass(List<String> pkRegionList, String pkColumnName, String fkColumnName) {
			
			this.fkColumnName = fkColumnName;
			this.pkColumnName = pkColumnName;
			this.pkRegionSeqNum = pkRegionList;
			
		}

    	
    }
    
    class RegionSummary{
    	
		String regionSeqnum;
    	List<FKeyClass> fkeysClassObjList;
    	
    	public RegionSummary(String fkRegionSeqnum) {
			this.regionSeqnum = fkRegionSeqnum;
			this.fkeysClassObjList = new ArrayList<>();
		}

		public void addFKey(FKeyClass fkObj) {
			
			fkeysClassObjList.add(fkObj);
			
		}

		
    	
    }
    
    class ViewSummary{
    	
		String viewName;
		List<String> viewNonKeys;
    	List<String> fkeys;
    	List<String> pkRelationList; // list of those pk relation whose value is referenced for fkeys
    	List<RegionSummary> regionSummaryList;
    	boolean fkeysSet = false;
    	public ViewSummary(String key, List<String> viewNonKeysList) {
			this.viewName = key;
			this.regionSummaryList = new ArrayList<>();
			this.viewNonKeys = viewNonKeysList;  
			this.fkeys = new ArrayList<>();
			this.pkRelationList = new ArrayList<>();
			
		}
		public void addRegionSummary(RegionSummary rs) {
			
			this.regionSummaryList.add(rs);
			if(!fkeysSet)
				addFkeys(rs);
			
			
		}
		private void addFkeys(RegionSummary rs) {
			
			for(FKeyClass fk : rs.fkeysClassObjList)
			{
				this.fkeys.add(fk.fkColumnName);
				this.pkRelationList.add(fk.pkColumnName.split("_")[0]);
			}
			fkeysSet = true;
			
		}
    }
    
    class RelationSummary{
    	
    	
		String relName;
    	List<String> tableNonKeys;
    	List<String> fkeys;
    	List<String> pkRelationList; // list of those pk relation whose value is referenced for fkeys
    	List<String> viewNonKeys;
    	List<RegionSummary> regionSummaryList;
    	long relationCardinality;
    	List<String> pkeysInRefrencedRelation;
    	int iterationOrderForRegionSummaryList[];
    	
    	public RelationSummary(String relName, ViewSummary viewSummary, List<String> tableNonKeys) {
    		
    		this.relName = relName;
    		this.tableNonKeys = tableNonKeys;
    		this.fkeys = viewSummary.fkeys;
    		this.viewNonKeys = viewSummary.viewNonKeys;
    		this.regionSummaryList = viewSummary.regionSummaryList;
    		this.pkRelationList = viewSummary.pkRelationList;
    		this.pkeysInRefrencedRelation = new ArrayList<>();
    		    		
    		this.iterationOrderForRegionSummaryList = new int[regionSummaryList.size()];
    		
    		Collections.sort(this.tableNonKeys);
    		Collections.sort(this.fkeys);
    		sortFkeysInRegionSummaryList();
    		
		}
		
		private void sortFkeysInRegionSummaryList() {
			
			boolean flag=true;
			for(RegionSummary rs : regionSummaryList)
			{
				List<FKeyClass> sorted_fkeysClassObjList = new ArrayList<>();
				for(String fkCol : fkeys)
				{
					
					for(FKeyClass fkClassObj : rs.fkeysClassObjList)
					{
						String fkColName = fkClassObj.fkColumnName;
						if(fkCol.contentEquals(fkColName))
						{
							FKeyClass obj = new FKeyClass(fkClassObj.pkRegionSeqNum,fkClassObj.pkColumnName,fkClassObj.fkColumnName);
							sorted_fkeysClassObjList.add(obj);
							
							if(flag) {
								this.pkeysInRefrencedRelation.add(fkClassObj.pkColumnName);
								
							//System.out.println("Adding :" + fkClassObj.pkColumnName );
							}
							
							break;
						}
						 
					}
					
				}
				flag=false;
				rs.fkeysClassObjList = sorted_fkeysClassObjList;
			}
		
		}
		
		

		//NEWEST CODE AFTER TARUN SENT FIX FOR HD 306 307 BUG VIA WHATSAPP
		
		public void addRegionCardinality(long regionCardinality) {
			
			this.relationCardinality = regionCardinality;
			generateIterOrderForRegionSummaryList();
			
            
		}
		
public void generateIterOrderForRegionSummaryList() {
			
			List<String> OrderedRegionMap = OrderedRegionMapParallelToIntervalDomainMap.get(relName);
        	
			//System.out.println("OrderedRegionMap size " + OrderedRegionMap.size());
			
			//System.out.println("iterationOrderForRegionSummaryList.length " + iterationOrderForRegionSummaryList.length);
			
			//System.out.println("regionSummaryList.size() " + regionSummaryList.size());
			
			//for(int k=0; k< iterationOrderForRegionSummaryList.length;k++) {
			//	System.out.println("iterationOrderForRegionSummaryList " + iterationOrderForRegionSummaryList[k]);
			//}
			
        	for(int r=0; r< regionSummaryList.size();r++) {
        		// creating iteration order for regionSummaryList
        		//System.out.println("regionSummaryList.get(r).regionSeqnum " + regionSummaryList.get(r).regionSeqnum);
    				
				for(int i=0; i< OrderedRegionMap.size();i++) {
					if(OrderedRegionMap.get(i).contentEquals(regionSummaryList.get(r).regionSeqnum))
					{
						iterationOrderForRegionSummaryList[i] = r;
					}
				}
				
        	}
		}
		


public JSONObject getJSONRelationSummary()
{

	StopWatch bugger = new StopWatch("JS");
	
	JSONObject obj = new JSONObject();
	obj.put("relName", relName);
	obj.put("tableNonKeys", tableNonKeys);
	obj.put("tableFkeys", fkeys);
	obj.put("relationPKRangeArray", IntervalDomainMap.get(relName));
	obj.put("relationCardinality", relationCardinality);
	
	obj.put("pkColumnNamesInReferecedRelation", this.pkeysInRefrencedRelation);
	
	
	List<List<Long>> fkRangeArrayList = new ArrayList<>();
	
	for(String pk : this.pkeysInRefrencedRelation)
	{
		List<Long> x = IntervalDomainMap.get(pk.split("_")[0]);
		fkRangeArrayList.add(x);
	}
	obj.put("fkRangeArrayList", fkRangeArrayList);
	
	
	
	//JSONArray regionsArray = new JSONArray();
	List<Integer> viewNonKeyIdx = new ArrayList<>();
	
	for(int s=0; s<viewNonKeys.size(); s++)
	{
		String viewNonKey = viewNonKeys.get(s);
		if(viewNonKey.contains(relName))
		{
			viewNonKeyIdx.add(s);
		}
	}
	
	int totalsize = iterationOrderForRegionSummaryList.length;
	int currentcount = 0;
	
	Map<String, String> columnDataTypeMap = PostgresVConfig.columnDataTypeMap;
	

	Set<String> tableNonkeysWhichHaveNonZeroValues = new HashSet<String>();

	long heapsize;
	
	try {
		File f = new File(PostgresVConfig.getProp(Key.DATABASESUMMARY_LOCATION) + "/" + relName+ "_regions/"+ PostgresVConfig.REGION_COUNT_INDEX);
		if(f.exists() && !f.isDirectory()) { 
			PrintWriter pw = new PrintWriter(f);
			pw.close();
		}
	} catch (FileNotFoundException e1) {
		// TODO Auto-generated catch block
		e1.printStackTrace();
	}
	
	for(int r_iter : iterationOrderForRegionSummaryList)
	{
		heapsize = Runtime.getRuntime().freeMemory();
		
		if(heapsize<10000000000L)
			System.gc();
		currentcount++;
		
		
		//System.out.println("Doing iterationOrderForRegionSummaryList : " + currentcount++ + " / " + totalsize + " heap now : " + heapsize );
		
		
		
		//System.out.print("Loop 1 : "); bugger.displayTime();
		
		RegionSummary rs = regionSummaryList.get(r_iter);
		JSONObject reg = new JSONObject();
		reg.put("regionName", rs.regionSeqnum);
		
		//regionsArray.put(reg);
		
		VariableValuePair vvp = seqNumberToVariableValuePairViewMap.get(relName).get(rs.regionSeqnum);
		Region r = vvp.variable;
		
		reg.put("regionCardinality", vvp.rowcount);
		
		
		List<ArrayList<Integer>> fkeysList = new ArrayList<>();
		List<FKeyClass> fkeysObjList = rs.fkeysClassObjList;
		int f=0;
		for(FKeyClass fk : fkeysObjList)
		{

			//System.out.print("Loop 2 : "); bugger.displayTime();
			
			
			ArrayList<Integer> fkeysRangeList = new ArrayList<Integer>();
			List<String> pkRegionSeqNumList =  fk.pkRegionSeqNum;
			for(String pkRegSeqnum : pkRegionSeqNumList)
			{
				if(relName.equals("t10")) {
					System.out.println(pkRegSeqnum +" " + RegionIntervalMap.get(pkRegSeqnum));
				}
					

				//System.out.print("Loop 3 : "); bugger.displayTime();
				
				String pkRelname = pkRegSeqnum.split("_")[0];
				if(pkRegSeqnum.contains("allRegions"))
				{	
					for(int i=0; i < IntervalDomainMap.get(pkRelname).size()-1;i++)
					{

						////System.out.print("Loop 4 : "); bugger.displayTime();
						
						fkeysRangeList.add(i);
					}
					
				}
				else
				{
					fkeysRangeList.add(RegionIntervalMap.get(pkRegSeqnum));
				}
				
				
				
			}
			
			fkeysList.add(fkeysRangeList);
			if(fkeysRangeList.size() >= fkRangeArrayList.get(f++).size())
			{
				System.out.println("Wrong fkeys maapping");
				throw new ArithmeticException("Wrong fkeys maapping");
			}
			
			
			
			
		}
		
		reg.put("fkeysList", fkeysList);
		List<ArrayList<ArrayList<Integer>>> tableNonKeysList = new ArrayList<>();
		
		
		
		// Assigning each bucketStructure cardinality on basis of volume
		long regionVolume = r.getVolume();
		int num_of_bs = r.size();
		int bs_counter = 0;
		long sum_of_bsCardinality = 0;
		List<Long> bsCardinalityList = new ArrayList<>();
		
		Set<String> bucketStructureStrings = new HashSet<String>();
		
		for(BucketStructure b : r.getAll())
		{

			//System.out.print("Loop 5 : "); bugger.displayTime();
			
			bs_counter++;
			Region tempRegion = new Region();
			tempRegion.add(b);
			long tempRegionVolume = tempRegion.getVolume();
			long bsCardinality = -1;
			if(num_of_bs == bs_counter)
				bsCardinality = vvp.rowcount - sum_of_bsCardinality;
			else
				bsCardinality = (long) (((tempRegionVolume*1.0)/regionVolume)* vvp.rowcount); 
			sum_of_bsCardinality += bsCardinality;
			bsCardinalityList.add(bsCardinality);
			
			int c=0;
			ArrayList<ArrayList<Integer>> bs_array = new ArrayList<>();
			for(String tableNonKey : tableNonKeys)
			{

				//System.out.print("Loop 6 : "); bugger.displayTime();
				
				ArrayList<Integer> columnBucket =  new ArrayList<>();
				if(!viewNonKeyIdx.isEmpty() && c<viewNonKeyIdx.size() && viewNonKeys.get(viewNonKeyIdx.get(c)).contains(tableNonKey))
				{
					tableNonkeysWhichHaveNonZeroValues.add(tableNonKey);

					Bucket x = b.at(viewNonKeyIdx.get(c));
					columnBucket.addAll(x.getAll());
					
					c++;
				}
				else
				{
					if(columnDataTypeMap.get(tableNonKey).contentEquals("integer"))
					{
						columnBucket.add(Integer.MIN_VALUE);
					}
					else
					{
						columnBucket.add(0);
					}
					//columnBucket.add(0);
				}
				
				bs_array.add(columnBucket);
				
			}
			
			if(!bucketStructureStrings.contains(bs_array.toString())) {
				tableNonKeysList.add(bs_array);
				bucketStructureStrings.add(bs_array.toString());
			}
			
			
			if(bs_array.size()!=tableNonKeys.size()) {
				System.out.println("Very Weird : " + relName + " " + bs_array.size() + " " +tableNonKeys.size());
			}
		}
		if(sum_of_bsCardinality != vvp.rowcount)
			System.out.print("error: should no be reaching here");
		reg.put("BucketStructures", tableNonKeysList);
		reg.put("BSCardinalityList", bsCardinalityList);
		
		//FileUtils.writeStringToFile("/home/dsladmin/multi-query-workspace/codd-data-gen/resources/cdgvendor/output/postgres/"+ CURRENT_CONTEXT + "/"+relName+"/allRegions/region_" + currentcount + ".json", reg.toString());
		FileUtils.writeStringToFile(PostgresVConfig.getProp(Key.DATABASESUMMARY_LOCATION) + "/" + relName + "_regions/region_" +  currentcount + ".json", reg.toString());
		FileUtils.writeStringToFile(PostgresVConfig.getProp(Key.DATABASESUMMARY_LOCATION) + "/" + relName+ "_regions", PostgresVConfig.REGION_COUNT_INDEX, "region_" +  currentcount + ".json"+"\n", 1); // System.out.println("Now
		
	}
	//obj.put("regions", regionsArray);

	obj.put("usableTableNonKeys", tableNonkeysWhichHaveNonZeroValues);
		
	//System.out.println(obj);
	
	return obj;
	
	}
	
    	
    }
    
    
    private Map<String,ViewSummary> viewSummaryMap;
    private Map<String,RelationSummary> relationSummaryMap;
    
    
public void dumpBeforeRI() {
		
		// Only need to dump ViewSolutions
		JSONObject obj = new JSONObject();
		JSONObject viewsObj = new JSONObject();
		obj.put("viewSolutions",viewsObj);
        for (Entry<String,ViewSolution> entry : this.viewSolutions.entrySet()) {
        	ViewSolution viewSolution = entry.getValue();
        	String viewName = entry.getKey();
        	JSONObject viewObj = new JSONObject();
        	viewsObj.put(viewName, viewObj);
        	if (viewSolution instanceof ViewSolutionInMemory) {
        		viewObj.put("type", "ViewSolutionInMemory");
        		viewObj.put("last_seen_pk",((ViewSolutionInMemory) viewSolution).getLastSeenPK());
            } else if (viewSolution instanceof ViewSolutionWithSolverStats) {
            	viewObj.put("type", "ViewSolutionWithSolverStats");
            	JSONArray regionsArray = new JSONArray();
            	viewObj.put("regions", regionsArray);
            	
            	long sum=0;
            	for( VariableValuePair vvp : viewSolution.getVariableValuePairs()) {
            		Region r = vvp.variable;
            		long rowcount = vvp.rowcount;
            		sum+=rowcount;
            		JSONObject regObj = new JSONObject();
            		regObj.put("rowCount", rowcount);
            		List<List<List<Integer>>> bs_array = new ArrayList<>();
            		for(BucketStructure bs : r.getAll() ) {
            			
            			List<List<Integer>> bucketStructures = new ArrayList<>();
            			for(Bucket b : bs.getAll()) {
            				
            				List<Integer> x = b.getAll();
            				bucketStructures.add(x);
            			}
            			bs_array.add(bucketStructures);
            		}
            		regObj.put("region", bs_array);
            		regionsArray.put(regObj);
            
            	}
            	viewObj.put("last_seen_pk",sum);
            }
            else {
            	viewObj.put("type", "ViewSolution");
            }
       
        }
        
        
        FileUtils.writeStringToFile(PostgresVConfig.getProp(Key.BEFORE_RI), obj.toString());
		
		
	}

/*

public void dumpInterRI() {
	
	
	
	
	
	JSONObject obj = new JSONObject();
	// ViewSolutions
	JSONObject viewsObj = new JSONObject();
	obj.put("viewSolutions",viewsObj);
    for (Entry<String,ViewSolution> entry : this.viewSolutions.entrySet()) {
    	ViewSolution viewSolution = entry.getValue();
    	String viewName = entry.getKey();
    	

    	System.out.println("Doing Inter RI Dump - ViewSol - " + viewName);
    	
    	JSONObject viewObj = new JSONObject();
    	viewsObj.put(viewName, viewObj);
    	if (viewSolution instanceof ViewSolutionInMemory) {
    		viewObj.put("type", "ViewSolutionInMemory");
    		viewObj.put("last_seen_pk",((ViewSolutionInMemory) viewSolution).getLastSeenPK());
        } else if (viewSolution instanceof ViewSolutionWithSolverStats) {
        	viewObj.put("type", "ViewSolutionWithSolverStats");
        	
        	
        	//JSONArray regionsArray = new JSONArray();
        	//viewObj.put("regions", regionsArray);
        	
        	long regionCount = 0;
        	
        	long sum=0;
        	for( VariableValuePair vvp : viewSolution.getVariableValuePairs()) {
        		Region r = vvp.variable;
        		long rowcount = vvp.rowcount;
        		sum+=rowcount;
        		JSONObject regObj = new JSONObject();
        		regObj.put("rowCount", rowcount);
        		List<List<List<Integer>>> bs_array = new ArrayList<>();
        		for(BucketStructure bs : r.getAll() ) {
        			
        			List<List<Integer>> bucketStructures = new ArrayList<>();
        			for(Bucket b : bs.getAll()) {
        				
        				List<Integer> x = b.getAll();
        				bucketStructures.add(x);
        			}
        			bs_array.add(bucketStructures);
        		}
        		regObj.put("region", bs_array);
        		

        		FileUtils.writeStringToFile("/home/dsladmin/multi-query-workspace/codd-data-gen/resources/cdgvendor/output/postgres/"+ CURRENT_CONTEXT + "/inter_ri/viewSol/"+viewName+"/allRegions/region_" + ++regionCount + ".json", regObj.toString());

                FileUtils.writeStringToFile(PostgresVConfig.getProp(Key.BEFORE_RI), obj.toString());
        		//regionsArray.put(regObj);
        
        	}
        	viewObj.put("last_seen_pk",sum);
        }
        else {
        	viewObj.put("type", "ViewSolution");
        }
   
    }
    
    if(Runtime.getRuntime().freeMemory() <10000000000L)
		System.gc();
    
    
    //seqNumberToVariableValuePairViewMap
    JSONObject seqNumberToVariableValuePairViewMapObj = new JSONObject();
	obj.put("seqNumberToVariableValuePairViewMap",seqNumberToVariableValuePairViewMapObj);
	for (Entry<String, ConcurrentHashMap<String, VariableValuePair>> view : this.seqNumberToVariableValuePairViewMap.entrySet()) {
		
		JSONObject viewObj = new JSONObject();
		seqNumberToVariableValuePairViewMapObj.put(view.getKey(),viewObj);
		
		String viewName = view.getKey();
		

    	System.out.println("Doing Inter RI Dump - seqVVP - " + viewName);
    	
    	
		//JSONArray regionsArray = new JSONArray();
		//viewObj.put("regions", regionsArray);
		long regionCount = 0;
    	
		for(Entry<String,VariableValuePair> region : view.getValue().entrySet()) {
		
			String regSeqnum = region.getKey();
			VariableValuePair vvp = region.getValue();
			Region r = vvp.variable;
    		long rowcount = vvp.rowcount;
    		JSONObject regObj = new JSONObject();
    		regObj.put("rowCount", rowcount);
    		List<List<List<Integer>>> bs_array = new ArrayList<>();
    		for(BucketStructure bs : r.getAll() ) {
    			
    			List<List<Integer>> bucketStructures = new ArrayList<>();
    			for(Bucket b : bs.getAll()) {
    				
    				List<Integer> x = b.getAll();
    				bucketStructures.add(x);
    			}
    			bs_array.add(bucketStructures);
    		}
    		regObj.put("region", bs_array);
    		regObj.put("regionSeqNum", regSeqnum);
    		
    		//regionsArray.put(regObj);
    		

FileUtils.writeStringToFile("/home/dsladmin/multi-query-workspace/codd-data-gen/resources/cdgvendor/output/postgres/"+ CURRENT_CONTEXT + "/inter_ri/seqVVP/"+viewName+"/allRegions/region_" + ++regionCount + ".json", regObj.toString());
		
		}
		
	}
	
	if(Runtime.getRuntime().freeMemory() <10000000000L)
		System.gc();
	    
	/*
	JSONObject FkSeqNumtoPkSeqNumListforFKviewObj = new JSONObject();
	obj.put("FkSeqNumtoPkSeqNumListforFKview", FkSeqNumtoPkSeqNumListforFKviewObj);
	for(Entry<String, ConcurrentHashMap<String, Set<String>>> view : FkSeqNumtoPkSeqNumListforFKview.entrySet()) {
		
		//JSONObject viewObj = new JSONObject();
		//FkSeqNumtoPkSeqNumListforFKviewObj.put(view.getKey(),viewObj);
		

    	System.out.println("Doing Inter RI Dump - Mapping - FkSeqNumtoPkSeqNumListforFKview -" + view.getKey());
    	
    	FileWriter fw = null;
        try {
            fw = new FileWriter(new File("/home/dsladmin/multi-query-workspace/codd-data-gen/resources/cdgvendor/output/postgres/" + CURRENT_CONTEXT + "/inter_ri/FkSeqNumtoPkSeqNumListforFKview_" + view.getKey()  + ".txt"));
        	
    	
        }catch (IOException ex) {
            throw new RuntimeException("Unable to open file FkSeqNumtoPkSeqNumListforFKview", ex);
        }
    	
		for(Entry<String,Set<String>> entry : view.getValue().entrySet()) {
			
			//viewObj.put(entry.getKey(), entry.getValue());
			
			try {
				fw.write(entry.getKey() + " : "+  entry.getValue() + "\n");
			} catch (IOException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			}
		}
		
		
		try {
	        fw.close();
	    } catch (Exception ex2) {}

		
	}
	
	
    
	
	if(Runtime.getRuntime().freeMemory() <10000000000L)
		System.gc();
	    
	
	
	JSONObject pkSeqNumtoFkSeqNumListforFKViewObj = new JSONObject();
	obj.put("pkSeqNumtoFkSeqNumListforFKView", pkSeqNumtoFkSeqNumListforFKViewObj);
	
	for(Entry<String, ConcurrentHashMap<String, Set<String>>> view : pkSeqNumtoFkSeqNumListforFKView.entrySet()) {
		
		//JSONObject viewObj = new JSONObject();
		//pkSeqNumtoFkSeqNumListforFKViewObj.put(view.getKey(),viewObj);
		//for(Entry<String,Set<String>> entry : view.getValue().entrySet()) {
		//	viewObj.put(entry.getKey(), entry.getValue());
		//}
		

    	//System.out.println("Doing Inter RI Dump - Mapping - pkSeqNumtoFkSeqNumListforFKView -" + view.getKey());
    	
    	FileWriter fw1 = null;
        try {
            fw1 = new FileWriter(new File("/home/dsladmin/multi-query-workspace/codd-data-gen/resources/cdgvendor/output/postgres/"+ CURRENT_CONTEXT + "/inter_ri/pkSeqNumtoFkSeqNumListforFKView_" + view.getKey() +".txt"));
        	
    	
        }catch (IOException ex) {
            throw new RuntimeException("Unable to open file FkSeqNumtoPkSeqNumListforFKview", ex);
        }
    	
		
		for(Entry<String,Set<String>> entry : view.getValue().entrySet()) {
			
			//viewObj.put(entry.getKey(), entry.getValue());
			
			try {
				fw1.write(entry.getKey() + " : "+  entry.getValue() + "\n");
			} catch (IOException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			}
		}
		try {
	        fw1.close();
	    } catch (Exception ex2) {}
		
		
		if(Runtime.getRuntime().freeMemory() <10000000000L)
			System.gc();
		    

	}
	
	 
		
	if(Runtime.getRuntime().freeMemory() <10000000000L)
		System.gc();
	    
    
    
	//FileUtils.writeStringToFile(PostgresVConfig.getProp(Key.INTER_RI), obj.toString());
	
	
}

*/

/*

public void dumpAfterRI() {
	
	
	JSONObject obj = new JSONObject();
	// ViewSolutions
	JSONObject viewsObj = new JSONObject();
	obj.put("viewSolutions",viewsObj);
    for (Entry<String,ViewSolution> entry : this.viewSolutions.entrySet()) {
    	ViewSolution viewSolution = entry.getValue();
    	String viewName = entry.getKey();
    	
    	System.out.println("Dump after RI -" + viewName);
    	
    	JSONObject viewObj = new JSONObject();
    	viewsObj.put(viewName, viewObj);
    	
    	if (viewSolution instanceof ViewSolutionInMemory) {
    		viewObj.put("type", "ViewSolutionInMemory");
    		viewObj.put("last_seen_pk",((ViewSolutionInMemory) viewSolution).getLastSeenPK());
        } else if (viewSolution instanceof ViewSolutionWithSolverStats) {
        	viewObj.put("type", "ViewSolutionWithSolverStats");
        	JSONArray regionsArray = new JSONArray();
        	viewObj.put("regions", regionsArray);
        	
        	long regionCount = 0;
        	
        	long sum=0;
        	for( VariableValuePair vvp : viewSolution.getVariableValuePairs()) {
        		Region r = vvp.variable;
        		long rowcount = vvp.rowcount;
        		sum+=rowcount;
        		JSONObject regObj = new JSONObject();
        		regObj.put("rowCount", rowcount);
        		List<List<List<Integer>>> bs_array = new ArrayList<>();
        		for(BucketStructure bs : r.getAll() ) {
        			
        			List<List<Integer>> bucketStructures = new ArrayList<>();
        			for(Bucket b : bs.getAll()) {
        				
        				List<Integer> x = b.getAll();
        				bucketStructures.add(x);
        			}
        			bs_array.add(bucketStructures);
        		}
        		regObj.put("region", bs_array);
        		regionsArray.put(regObj);
        
        		//FileUtils.writeStringToFile("/home/dsladmin/multi-query-workspace/codd-data-gen/resources/cdgvendor/output/postgres/"+ CURRENT_CONTEXT + "/after_ri/viewSol/"+viewName+"/allRegions/region_" + ++regionCount + ".json", regObj.toString());

        		if(Runtime.getRuntime().freeMemory() <10000000000L)
    				System.gc();
    			
        	}
        	viewObj.put("last_seen_pk",sum);
        	
        	if(Runtime.getRuntime().freeMemory() <10000000000L)
				System.gc();
			
        }
        else {
        	viewObj.put("type", "ViewSolution");
        }
   
    	if(Runtime.getRuntime().freeMemory() <10000000000L)
			System.gc();
		
    }
    
    
    //seqNumberToVariableValuePairViewMap
    JSONObject seqNumberToVariableValuePairViewMapObj = new JSONObject();
	obj.put("seqNumberToVariableValuePairViewMap",seqNumberToVariableValuePairViewMapObj);
	for (Entry<String, ConcurrentHashMap<String, VariableValuePair>> view : this.seqNumberToVariableValuePairViewMap.entrySet()) {
		
		JSONObject viewObj = new JSONObject();
		seqNumberToVariableValuePairViewMapObj.put(view.getKey(),viewObj);
		JSONArray regionsArray = new JSONArray();
		viewObj.put("regions", regionsArray);
		
		String viewName = view.getKey();
		
		long regionCount = 0;
		
		for(Entry<String,VariableValuePair> region : view.getValue().entrySet()) {
		
			String regSeqnum = region.getKey();
			VariableValuePair vvp = region.getValue();
			Region r = vvp.variable;
    		long rowcount = vvp.rowcount;
    		JSONObject regObj = new JSONObject();
    		regObj.put("rowCount", rowcount);
    		List<List<List<Integer>>> bs_array = new ArrayList<>();
    		for(BucketStructure bs : r.getAll() ) {
    			
    			List<List<Integer>> bucketStructures = new ArrayList<>();
    			for(Bucket b : bs.getAll()) {
    				
    				List<Integer> x = b.getAll();
    				bucketStructures.add(x);
    			}
    			bs_array.add(bucketStructures);
    		}
    		regObj.put("region", bs_array);
    		regObj.put("regionSeqNum", regSeqnum);
    		regionsArray.put(regObj);
    		
       		

    		//FileUtils.writeStringToFile("/home/dsladmin/multi-query-workspace/codd-data-gen/resources/cdgvendor/output/postgres/"+ CURRENT_CONTEXT + "/after_ri/seqVVP/"+viewName+"/allRegions/region_" + ++regionCount + ".json", regObj.toString());
    				
    			
    		if(Runtime.getRuntime().freeMemory() <10000000000L)
				System.gc();
			
		}
		
		if(Runtime.getRuntime().freeMemory() <10000000000L)
			System.gc();
		
	}
	
	
	JSONObject FkSeqNumtoPkSeqNumListforFKviewObj = new JSONObject();
	obj.put("FkSeqNumtoPkSeqNumListforFKview", FkSeqNumtoPkSeqNumListforFKviewObj);
	for(Entry<String, ConcurrentHashMap<String, Set<String>>> view : FkSeqNumtoPkSeqNumListforFKview.entrySet()) {
		
		JSONObject viewObj = new JSONObject();
		FkSeqNumtoPkSeqNumListforFKviewObj.put(view.getKey(),viewObj);
		
		//System.out.println("Doing After RI Dump - Mapping - FkSeqNumtoPkSeqNumListforFKview -" + view.getKey());
	    	
	    	FileWriter fw = null;
	        try {
	            fw = new FileWriter(new File("/home/dsladmin/multi-query-workspace/codd-data-gen/resources/cdgvendor/output/postgres/"+ CURRENT_CONTEXT + "/after_ri/FkSeqNumtoPkSeqNumListforFKview_" + view.getKey()  + ".txt"));
	        	
	    	
	        }catch (IOException ex) {
	            throw new RuntimeException("Unable to open file FkSeqNumtoPkSeqNumListforFKview", ex);
	        }
	        
	    	
	        
			for(Entry<String,Set<String>> entry : view.getValue().entrySet()) {

				//viewObj.put(entry.getKey(), entry.getValue());
				
				try {
					fw.write(entry.getKey() + " : "+  entry.getValue() + "\n");
				} catch (IOException e) {
					// TODO Auto-generated catch block
					e.printStackTrace();
				}
			}
			
			
			try {
		        fw.close();
		    } catch (Exception ex2) {}

		
		if(Runtime.getRuntime().freeMemory() <10000000000L)
			System.gc();
		
	}
    
	if(Runtime.getRuntime().freeMemory() <10000000000L)
		System.gc();
	
    
	FileUtils.writeStringToFile(PostgresVConfig.getProp(Key.AFTER_RI), obj.toString());
	
	if(Runtime.getRuntime().freeMemory() <10000000000L)
		System.gc();
	
	
} 
*/


public void dumpAfterRI() {
	
	
	JSONObject obj = new JSONObject();
	// ViewSolutions
	JSONObject viewsObj = new JSONObject();
	obj.put("viewSolutions",viewsObj);
    for (Entry<String,ViewSolution> entry : this.viewSolutions.entrySet()) {
    	ViewSolution viewSolution = entry.getValue();
    	String viewName = entry.getKey();
    	JSONObject viewObj = new JSONObject();
    	viewsObj.put(viewName, viewObj);
    	if (viewSolution instanceof ViewSolutionInMemory) {
    		viewObj.put("type", "ViewSolutionInMemory");
    		viewObj.put("last_seen_pk",((ViewSolutionInMemory) viewSolution).getLastSeenPK());
        } else if (viewSolution instanceof ViewSolutionWithSolverStats) {
        	viewObj.put("type", "ViewSolutionWithSolverStats");
        	JSONArray regionsArray = new JSONArray();
        	viewObj.put("regions", regionsArray);
        	
        	long sum=0;
        	for( VariableValuePair vvp : viewSolution.getVariableValuePairs()) {
        		Region r = vvp.variable;
        		long rowcount = vvp.rowcount;
        		sum+=rowcount;
        		JSONObject regObj = new JSONObject();
        		regObj.put("rowCount", rowcount);
        		List<List<List<Integer>>> bs_array = new ArrayList<>();
        		for(BucketStructure bs : r.getAll() ) {
        			
        			List<List<Integer>> bucketStructures = new ArrayList<>();
        			for(Bucket b : bs.getAll()) {
        				
        				List<Integer> x = b.getAll();
        				bucketStructures.add(x);
        			}
        			bs_array.add(bucketStructures);
        		}
        		regObj.put("region", bs_array);
        		regionsArray.put(regObj);
        
        	}
        	viewObj.put("last_seen_pk",sum);
        }
        else {
        	viewObj.put("type", "ViewSolution");
        }
   
    }
    
    
    //seqNumberToVariableValuePairViewMap
    JSONObject seqNumberToVariableValuePairViewMapObj = new JSONObject();
	obj.put("seqNumberToVariableValuePairViewMap",seqNumberToVariableValuePairViewMapObj);
	for (Entry<String, ConcurrentHashMap<String, VariableValuePair>> view : this.seqNumberToVariableValuePairViewMap.entrySet()) {
		
		JSONObject viewObj = new JSONObject();
		seqNumberToVariableValuePairViewMapObj.put(view.getKey(),viewObj);
		JSONArray regionsArray = new JSONArray();
		viewObj.put("regions", regionsArray);
		for(Entry<String,VariableValuePair> region : view.getValue().entrySet()) {
		
			String regSeqnum = region.getKey();
			VariableValuePair vvp = region.getValue();
			Region r = vvp.variable;
    		long rowcount = vvp.rowcount;
    		JSONObject regObj = new JSONObject();
    		regObj.put("rowCount", rowcount);
    		List<List<List<Integer>>> bs_array = new ArrayList<>();
    		for(BucketStructure bs : r.getAll() ) {
    			
    			List<List<Integer>> bucketStructures = new ArrayList<>();
    			for(Bucket b : bs.getAll()) {
    				
    				List<Integer> x = b.getAll();
    				bucketStructures.add(x);
    			}
    			bs_array.add(bucketStructures);
    		}
    		regObj.put("region", bs_array);
    		regObj.put("regionSeqNum", regSeqnum);
    		regionsArray.put(regObj);
		}
		
	}
	
	
	JSONObject FkSeqNumtoPkSeqNumListforFKviewObj = new JSONObject();
	obj.put("FkSeqNumtoPkSeqNumListforFKview", FkSeqNumtoPkSeqNumListforFKviewObj);
	for(Entry<String, ConcurrentHashMap<String, Set<String>>> view : FkSeqNumtoPkSeqNumListforFKview.entrySet()) {
		
		JSONObject viewObj = new JSONObject();
		FkSeqNumtoPkSeqNumListforFKviewObj.put(view.getKey(),viewObj);
		for(Entry<String,Set<String>> entry : view.getValue().entrySet()) {
			viewObj.put(entry.getKey(), entry.getValue());
		}
	}
    
    
    
	FileUtils.writeStringToFile(PostgresVConfig.getProp(Key.AFTER_RI), obj.toString());
	
	
	
}


	
public void readBeforeRIDump() {
		
		// Only useful information is fetched and dumped
        JSONObject obj = new JSONObject(FileUtils.readFileToString(PostgresVConfig.getProp(Key.BEFORE_RI)));
        JSONObject viewSolutionObj = obj.getJSONObject("viewSolutions");
        viewSolutions.clear();
        
        for(String key : viewSolutionObj.keySet()) {
        	List<VariableValuePair> vvpList = new ArrayList<>();
        	
        	
        	if(key.equals("t00"))
        		System.out.println(viewSolutionObj.getJSONObject(key));
        	
        	if(viewSolutionObj.getJSONObject(key).getString("type").contentEquals("ViewSolutionWithSolverStats")) {
	        	JSONArray regionsList = viewSolutionObj.getJSONObject(key).getJSONArray("regions");
	        	
	        	
	        	for(int r=0; r<regionsList.length();r++) {
	        		
	        		
	        		JSONArray bs_array = regionsList.getJSONObject(r).getJSONArray("region");
	        		
	        		Set<String> dupliBSPrevent = new HashSet<>();	        		
	        		
	        		Region reg = new Region();
	        		for(int bs=0; bs<bs_array.length();bs++) {
	        			JSONArray bucketStructure = bs_array.getJSONArray(bs);
	        			
	        			BucketStructure buckStr = new BucketStructure();
	        			
	        			for(int b=0; b<bucketStructure.length();b++) {
	        				JSONArray bucket = bucketStructure.getJSONArray(b);
	        				Bucket buck = new Bucket();
	        				for(int i=0; i <bucket.length(); i++) {
	        					buck.add(bucket.getInt(i));
	        				}
	        				buckStr.add(buck);
	        			}
	        			
	        			if(!dupliBSPrevent.contains(buckStr.toString())) {
	        				reg.add(buckStr);
	        				dupliBSPrevent.add(buckStr.toString());
	        				//System.out.println( key + "-  ");
	        			}else {
	        				System.out.println("Dupli BS found " + key +"  :  "+buckStr.toString());
	        			}
	        		}
	        		
	        		VariableValuePair vvp =  new VariableValuePair(reg,regionsList.getJSONObject(r).getLong("rowCount"));
	        		vvpList.add(vvp);
	        	}
	        	ViewSolutionInMemory viewSolution = new ViewSolutionInMemory(vvpList.size(),vvpList);
	        	viewSolution.setLastSeenPK(viewSolutionObj.getJSONObject(key).getLong("last_seen_pk"));
	        	viewSolutions.put(key,new ViewSolutionWithSolverStats(viewSolution, viewSolution.getVariableValuePairs() ,new SolverViewStats()));
        	}
        	else {
        		ViewSolutionInMemory viewSolution = new ViewSolutionInMemory(vvpList.size(),vvpList);
        		viewSolutions.put(key,viewSolution);
        		viewSolution.setLastSeenPK(viewSolutionObj.getJSONObject(key).getLong("last_seen_pk"));
            }
        	
        	
        }
        
       
	}
	

/*
public void readInterRIDump() {
		
		// Only useful information is fetched and dumped
        JSONObject obj = new JSONObject(FileUtils.readFileToString(PostgresVConfig.getProp(Key.INTER_RI)));
        JSONObject viewSolutionObj = obj.getJSONObject("viewSolutions");
        viewSolutions.clear();
       
        
        for(String key : viewSolutionObj.keySet()) {
        	List<VariableValuePair> vvpList = new ArrayList<>();
        	if(viewSolutionObj.getJSONObject(key).getString("type").contentEquals("ViewSolutionWithSolverStats")) {
	        	
        		String viewName = key;
        		
        		int regionsListLength = new File("/home/dsladmin/multi-query-workspace/codd-data-gen/resources/cdgvendor/output/postgres/"+ CURRENT_CONTEXT + "/inter_ri/viewSol/"+viewName+"/allRegions").list().length;

        		System.out.println("viewSol Total Regions of " + viewName + " : " + regionsListLength);
        		
        		//JSONArray regionsList = viewSolutionObj.getJSONObject(key).getJSONArray("regions");
	        	
	        	int j=0;
        		
	        	for(int r=0; r<regionsListLength ;r++) {
	        		
	        		JSONObject regionJSON = null;
	        		
	        		try {
	        				regionJSON = new JSONObject(new String(Files.readAllBytes(Paths.get("/home/dsladmin/multi-query-workspace/codd-data-gen/resources/cdgvendor/output/postgres/"+ CURRENT_CONTEXT + "/inter_ri/viewSol/"+viewName+"/allRegions/region_"+ ++j + ".json")), StandardCharsets.UTF_8));//"/home/dsladmin/sqlqueries/temp/anonymizedschema.info"));///home/dsladmin/TODI/ws_kk/codd-data-gen/resources/cdgvendor/input/postgres/anonymizedschema.info"));
	         	 	} catch (IOException e) {
	         			e.printStackTrace();
	         		} 
	            	
	        		//JSONArray bs_array = regionsList.getJSONObject(r).getJSONArray("region");
	        		JSONArray bs_array = regionJSON.getJSONArray("region");
	        		
	        		Region reg = new Region();
	        		for(int bs=0; bs<bs_array.length();bs++) {
	        			JSONArray bucketStructure = bs_array.getJSONArray(bs);
	        			BucketStructure buckStr = new BucketStructure();
	        			for(int b=0; b<bucketStructure.length();b++) {
	        				JSONArray bucket = bucketStructure.getJSONArray(b);
	        				Bucket buck = new Bucket();
	        				for(int i=0; i <bucket.length(); i++) {
	        					buck.add(bucket.getInt(i));
	        				}
	        				buckStr.add(buck);
	        			}
	        			reg.add(buckStr);
	        		}
	        		
	        		//VariableValuePair vvp =  new VariableValuePair(reg,regionsList.getJSONObject(r).getLong("rowCount"));
	        		VariableValuePair vvp =  new VariableValuePair(reg,regionJSON.getLong("rowCount"));
	        		vvpList.add(vvp);
	        		//System.out.println("vvp " + vvp);
	        	}
	        	ViewSolutionInMemory viewSolution = new ViewSolutionInMemory(vvpList.size(),vvpList);
	        	viewSolution.setLastSeenPK(viewSolutionObj.getJSONObject(key).getLong("last_seen_pk"));
	        	viewSolutions.put(key,new ViewSolutionWithSolverStats(viewSolution, viewSolution.getVariableValuePairs() ,new SolverViewStats()));
        	
        	if(key.equals("t10"))
	        	System.out.println("vs " + viewSolutions.get(key).getVariableValuePairs());
        	}
        	else {
        		ViewSolutionInMemory viewSolution = new ViewSolutionInMemory(vvpList.size(),vvpList);
        		viewSolutions.put(key,viewSolution);
        		viewSolution.setLastSeenPK(viewSolutionObj.getJSONObject(key).getLong("last_seen_pk"));
            }
        	
        	
        }
        
        if(Runtime.getRuntime().freeMemory() <10000000000L)
			System.gc();
        
        
        JSONObject seqNumberToVariableValuePairViewMapObj = obj.getJSONObject("seqNumberToVariableValuePairViewMap");
        seqNumberToVariableValuePairViewMap.clear();
        
        
        for(String key : seqNumberToVariableValuePairViewMapObj.keySet()) {
        	
        	
        	String viewName = key;
    		
    		int regionsListLength = new File("/home/dsladmin/multi-query-workspace/codd-data-gen/resources/cdgvendor/output/postgres/"+ CURRENT_CONTEXT + "/inter_ri/seqVVP/"+viewName+"/allRegions").list().length;

    		System.out.println("seqVVP Total Regions of " + viewName + " : " + regionsListLength);
    		
    		//JSONArray regionsList = viewSolutionObj.getJSONObject(key).getJSONArray("regions");
        	
        	int j=0;
    		
        		
	        	//JSONArray regionsList = seqNumberToVariableValuePairViewMapObj.getJSONObject(key).getJSONArray("regions");
	        	
	        	ConcurrentHashMap<String,VariableValuePair> seqNumberToVariableValuePair = new ConcurrentHashMap<>();
	        	//for(int r=0; r<regionsList.length();r++) {
	        		for(int r=0; r<regionsListLength ;r++) {
	                	
	        		
	        			JSONObject regionJSON = null;
		        		
		        		try {
		        				regionJSON = new JSONObject(new String(Files.readAllBytes(Paths.get("/home/dsladmin/multi-query-workspace/codd-data-gen/resources/cdgvendor/output/postgres/"+ CURRENT_CONTEXT + "/inter_ri/seqVVP/"+viewName+"/allRegions/region_"+ ++j + ".json")), StandardCharsets.UTF_8));//"/home/dsladmin/sqlqueries/temp/anonymizedschema.info"));///home/dsladmin/TODI/ws_kk/codd-data-gen/resources/cdgvendor/input/postgres/anonymizedschema.info"));
		         	 	} catch (IOException e) {
		         			e.printStackTrace();
		         		} 
		            	
	        			
		        		//JSONArray bs_array = regionsList.getJSONObject(r).getJSONArray("region");
		        		JSONArray bs_array = regionJSON.getJSONArray("region");
		        		
	        		Region reg = new Region();
	        		for(int bs=0; bs<bs_array.length();bs++) {
	        			JSONArray bucketStructure = bs_array.getJSONArray(bs);
	        			BucketStructure buckStr = new BucketStructure();
	        			for(int b=0; b<bucketStructure.length();b++) {
	        				JSONArray bucket = bucketStructure.getJSONArray(b);
	        				Bucket buck = new Bucket();
	        				for(int i=0; i <bucket.length(); i++) {
	        					buck.add(bucket.getInt(i));
	        				}
	        				
	        			
	        				buckStr.add(buck);
	        			}
	        			reg.add(buckStr);
	        		}
	        		//VariableValuePair vvp =  new VariableValuePair(reg,regionsList.getJSONObject(r).getLong("rowCount"));
	        		//seqNumberToVariableValuePair.put(regionsList.getJSONObject(r).getString("regionSeqNum"),vvp);
	        		VariableValuePair vvp =  new VariableValuePair(reg,regionJSON.getLong("rowCount"));
	        		seqNumberToVariableValuePair.put(regionJSON.getString("regionSeqNum"),vvp);
	        	}
	        	
	        	
	        	seqNumberToVariableValuePairViewMap.put(key, seqNumberToVariableValuePair);
        }
        
        if(Runtime.getRuntime().freeMemory() <10000000000L)
			System.gc();
        
        
        JSONObject FkSeqNumtoPkSeqNumListforFKviewObj = obj.getJSONObject("FkSeqNumtoPkSeqNumListforFKview");
        FkSeqNumtoPkSeqNumListforFKview.clear();
        
        ArrayList<String> allKeys = new ArrayList<String>(Arrays.asList("t00","t01","t02","t03","t04","t10","t12","t15","t16","t17","t20","t21","t22","t23"));
        

        for(String key : FkSeqNumtoPkSeqNumListforFKviewObj.keySet()) {
        //for(String key : allKeys) {
        	ConcurrentHashMap<String,Set<String>> map = new ConcurrentHashMap<>();
        	
        	String viewName = key;
        	
        	//System.out.println("Doing fkMaps of " + viewName );
    		
        	
        	List<String> lines = FileUtils.readLines("/home/dsladmin/multi-query-workspace/codd-data-gen/resources/cdgvendor/output/postgres/"+ CURRENT_CONTEXT + "/inter_ri/FkSeqNumtoPkSeqNumListforFKview_" + viewName  + ".txt");
        	
        	
        	for(String line : lines) {
        		String[] fragment = line.split(" : ");
        		
        		
        		Set<String> regSeqNumList = new HashSet<>();
        		
        		fragment[1] = fragment[1].substring(1,fragment[1].length()-1);
        		
        		String[] subFragments = fragment[1].split(", ");
        		
        	
        		for(String t : subFragments) {
        			regSeqNumList.add(t);
        		}
        		
        		if(key.contentEquals("t10"))
            		System.out.println(fragment[0] + " " + regSeqNumList);
            		

            		if(fragment[1].contains("t10_0")) 
            			System.out.println("Problem 1 " + key +" "+ fragment[1]);
            		
            		
            		if(fragment[1].contains("[")) 
            			System.out.println("Problem 2 " + key +" "+ fragment[1]);
            		
        		
        		map.put(fragment[0], regSeqNumList);
        	}
        	
        	
        	
        	
        	FkSeqNumtoPkSeqNumListforFKview.put(key,map);
        	
        	
        	if(Runtime.getRuntime().freeMemory() <10000000000L)
    			System.gc();
            
        	
        }
        
        
        JSONObject pkSeqNumtoFkSeqNumListforFKViewObj = obj.getJSONObject("pkSeqNumtoFkSeqNumListforFKView");
        pkSeqNumtoFkSeqNumListforFKView.clear();
 
        ArrayList<String> allKeys1 = new ArrayList<String>(Arrays.asList("t02","t03","t04","t10","t08","t16","t17","t21","t22"));
        

        for(String key : FkSeqNumtoPkSeqNumListforFKviewObj.keySet()) {
        //for(String key : allKeys1) {
        	ConcurrentHashMap<String,Set<String>> map = new ConcurrentHashMap<>();
        	
        	String viewName = key;

        	//System.out.println("Doing pkMaps of " + viewName );
    		
        	
        	List<String> lines = FileUtils.readLines("/home/dsladmin/multi-query-workspace/codd-data-gen/resources/cdgvendor/output/postgres/"+ CURRENT_CONTEXT + "/inter_ri/pkSeqNumtoFkSeqNumListforFKView_" + viewName  + ".txt");
        	
        	for(String line : lines) {
        		String[] fragment = line.split(" : ");
        		
        		
        		Set<String> regSeqNumList = new HashSet<>();
        		
        		fragment[1] = fragment[1].substring(1,fragment[1].length()-1);
        		
        		String[] subFragments = fragment[1].split(", ");
        		
        	
        		for(String t : subFragments) {
        			regSeqNumList.add(t);
        			
        			if(Runtime.getRuntime().freeMemory() <10000000000L)
            			System.gc();
                    
        		}
        		
        		map.put(fragment[0], regSeqNumList);
        		
        		if(Runtime.getRuntime().freeMemory() <10000000000L)
        			System.gc();
                
        	}
        	
        	
        	pkSeqNumtoFkSeqNumListforFKView.put(key,map);
        	
        	if(Runtime.getRuntime().freeMemory() <10000000000L)
    			System.gc();
            
        }
	}

*/
	
/*

public void readAfterRIDump() {
	
	// Only useful information is fetched and dumped
    JSONObject obj = new JSONObject(FileUtils.readFileToString(PostgresVConfig.getProp(Key.AFTER_RI)));
    JSONObject viewSolutionObj = obj.getJSONObject("viewSolutions");
    viewSolutions.clear();
    
    for(String key : viewSolutionObj.keySet()) {
    	List<VariableValuePair> vvpList = new ArrayList<>();
    	
    	if(key.contentEquals("t00"))
    		System.out.println(" readAfter t00 " + viewSolutionObj.getJSONObject(key));
    	
    	if(viewSolutionObj.getJSONObject(key).getString("type").contentEquals("ViewSolutionWithSolverStats")) {
        	JSONArray regionsList = viewSolutionObj.getJSONObject(key).getJSONArray("regions");
        	
        	
        	for(int r=0; r<regionsList.length();r++) {
        		
        		
        		JSONArray bs_array = regionsList.getJSONObject(r).getJSONArray("region");
        		
        		Region reg = new Region();
        		for(int bs=0; bs<bs_array.length();bs++) {
        			JSONArray bucketStructure = bs_array.getJSONArray(bs);
        			BucketStructure buckStr = new BucketStructure();
        			for(int b=0; b<bucketStructure.length();b++) {
        				JSONArray bucket = bucketStructure.getJSONArray(b);
        				Bucket buck = new Bucket();
        				for(int i=0; i <bucket.length(); i++) {
        					buck.add(bucket.getInt(i));
        				}
        				buckStr.add(buck);
        			}
        			reg.add(buckStr);
        		}
        		
        		VariableValuePair vvp =  new VariableValuePair(reg,regionsList.getJSONObject(r).getLong("rowCount"));
        		vvpList.add(vvp);
        	}
        	ViewSolutionInMemory viewSolution = new ViewSolutionInMemory(vvpList.size(),vvpList);
        	viewSolution.setLastSeenPK(viewSolutionObj.getJSONObject(key).getLong("last_seen_pk"));
        	viewSolutions.put(key,new ViewSolutionWithSolverStats(viewSolution, viewSolution.getVariableValuePairs() ,new SolverViewStats()));
    	}
    	else {
    		ViewSolutionInMemory viewSolution = new ViewSolutionInMemory(vvpList.size(),vvpList);
    		viewSolutions.put(key,viewSolution);
    		viewSolution.setLastSeenPK(viewSolutionObj.getJSONObject(key).getLong("last_seen_pk"));
        }
    	
    	  
        if(Runtime.getRuntime().freeMemory() <10000000000L)
    		System.gc();
        
        
    }
    
    JSONObject seqNumberToVariableValuePairViewMapObj = obj.getJSONObject("seqNumberToVariableValuePairViewMap");
    seqNumberToVariableValuePairViewMap.clear();
    for(String key : seqNumberToVariableValuePairViewMapObj.keySet()) {
    	
    	
        	JSONArray regionsList = seqNumberToVariableValuePairViewMapObj.getJSONObject(key).getJSONArray("regions");
        	
        	ConcurrentHashMap<String,VariableValuePair> seqNumberToVariableValuePair = new ConcurrentHashMap<>();
        	for(int r=0; r<regionsList.length();r++) {
        		
        		JSONArray bs_array = regionsList.getJSONObject(r).getJSONArray("region");
        		
        		Region reg = new Region();
        		for(int bs=0; bs<bs_array.length();bs++) {
        			JSONArray bucketStructure = bs_array.getJSONArray(bs);
        			BucketStructure buckStr = new BucketStructure();
        			for(int b=0; b<bucketStructure.length();b++) {
        				JSONArray bucket = bucketStructure.getJSONArray(b);
        				Bucket buck = new Bucket();
        				for(int i=0; i <bucket.length(); i++) {
        					buck.add(bucket.getInt(i));
        				}
        				
        			
        				buckStr.add(buck);
        			}
        			reg.add(buckStr);
        		}
        		VariableValuePair vvp =  new VariableValuePair(reg,regionsList.getJSONObject(r).getLong("rowCount"));
        		seqNumberToVariableValuePair.put(regionsList.getJSONObject(r).getString("regionSeqNum"),vvp);
        	}
        	
        	
        	seqNumberToVariableValuePairViewMap.put(key, seqNumberToVariableValuePair);
        	
        	  
            if(Runtime.getRuntime().freeMemory() <10000000000L)
        		System.gc();
            
            
    }
    
    if(Runtime.getRuntime().freeMemory() <10000000000L)
		System.gc();
    
    
    JSONObject FkSeqNumtoPkSeqNumListforFKviewObj = obj.getJSONObject("FkSeqNumtoPkSeqNumListforFKview");
    FkSeqNumtoPkSeqNumListforFKview.clear();
    for(String key : FkSeqNumtoPkSeqNumListforFKviewObj.keySet()) {
    	ConcurrentHashMap<String,Set<String>> map = new ConcurrentHashMap<>();
    	
    	
    	

    	String viewName = key;
    	
    	//System.out.println("Doing fkMaps of " + viewName );
    	
    	List<String> lines = FileUtils.readLines("/home/dsladmin/multi-query-workspace/codd-data-gen/resources/cdgvendor/output/postgres/"+ CURRENT_CONTEXT + "/after_ri/FkSeqNumtoPkSeqNumListforFKview_" + viewName  + ".txt");
    	
    	
    	for(String line : lines) {
    		String[] fragment = line.split(" : ");
    		
    		Set<String> regSeqNumList = new HashSet<>();
    		
    		fragment[1] = fragment[1].substring(1,fragment[1].length()-1);
    		
    		String[] subFragments = fragment[1].split(", ");
    		
    	
    		for(String t : subFragments) {
    			regSeqNumList.add(t);
    		}
    		
    		//if(key.contentEquals("t10"))
        	///	System.out.println(fragment[0] + " " + regSeqNumList);
        		

        	//	if(fragment[1].contains("t10_0")) 
        	//		System.out.println("Problem 1 " + key +" "+ fragment[1]);
        		
        		
        	//	if(fragment[1].contains("[")) 
        	//		System.out.println("Problem 2 " + key +" "+ fragment[1]);
        		
    		
    		map.put(fragment[0], regSeqNumList);
    	}
    	
    	
    	
    	FkSeqNumtoPkSeqNumListforFKview.put(key,map);
    	
    	if(Runtime.getRuntime().freeMemory() <10000000000L)
			System.gc();
        
    	
    	
    }
}

*/
	public DatabaseSummary(StopWatch databaseSummarySW, SpillType spillType, Map<String, ViewSolution> viewSolutions) {
        this.databaseSummarySW = databaseSummarySW;
        this.spillType = spillType;
        isConsistent = isCompressed = false;
        this.viewSolutions = viewSolutions;

        this.seqNumberToVariableValuePairViewMap = new ConcurrentHashMap<>(); 
        this.pkSeqNumtoFkSeqNumListforFKView = new ConcurrentHashMap<>();  // 2
        this.FkSeqNumtoPkSeqNumListforFKview = new ConcurrentHashMap<>();  // 3
        this.pkViewToFkViewMap = new HashMap<>();  // 4
        this.viewSummaryMap = new HashMap<>();
        this.RegionIntervalMap = new HashMap<>();
        this.relationSummaryMap = new HashMap<>();
        this.IntervalDomainMap = new HashMap<>();
        this.viewErrorCountMap = new HashMap<>();
        this.OrderedRegionMapParallelToIntervalDomainMap = new HashMap<>();
        
        if(Runtime.getRuntime().freeMemory() <10000000000L)
			System.gc();
        
        for (ViewSolution viewSolution : viewSolutions.values()) {
            if (viewSolution instanceof ViewSolutionInMemory) {
                ((ViewSolutionInMemory) viewSolution).prepareForSearch();
            } else if (viewSolution instanceof ViewSolutionWithSolverStats) {
                ((ViewSolutionWithSolverStats) viewSolution).prepareForSearch();
            }
        }

        makeAllViewRegionsConsistent();
        // Assigns sequence number to each VariableValuePair for all view
        for(Entry<String, ViewSolution> entry : viewSolutions.entrySet())
        {
        	ConcurrentHashMap<String, VariableValuePair> seqToVarValuePairMap = new ConcurrentHashMap<>();
        	long viewCardinality=0;
        	String viewName = entry.getKey();
        	seqNumberToVariableValuePairViewMap.put(viewName, seqToVarValuePairMap);
        	if(entry.getValue().getVariableValuePairs() == null)
        	{
        		continue;
        	}
        	for(Integer i=0; i<entry.getValue().getVariableValuePairs().size(); i++)
        	{
        		VariableValuePair vvp = entry.getValue().getVariableValuePairs().get(i);
        		vvp.variable.mergeBS();
        		seqToVarValuePairMap.put(viewName+ "_" + i.toString(), vvp);
        		viewCardinality+=vvp.rowcount;
        		
        	}
        	
        }
        
    }

public DatabaseSummary(StopWatch databaseSummarySW, SpillType spillType, Map<String, ViewSolution> viewSolutions, 
		Map<String, List<VariableValuePair>> viewToVVPMap) {
        this.databaseSummarySW = databaseSummarySW;
        this.spillType = spillType;
        isConsistent = isCompressed = false;
        this.viewSolutions = viewSolutions;

        this.seqNumberToVariableValuePairViewMap = new ConcurrentHashMap<>(); 
        this.pkSeqNumtoFkSeqNumListforFKView = new ConcurrentHashMap<>();  // 2
        this.FkSeqNumtoPkSeqNumListforFKview = new ConcurrentHashMap<>();  // 3
        this.pkViewToFkViewMap = new HashMap<>();  // 4
        this.viewSummaryMap = new HashMap<>();
        this.RegionIntervalMap = new HashMap<>();
        this.relationSummaryMap = new HashMap<>();
        this.IntervalDomainMap = new HashMap<>();
        this.viewErrorCountMap = new HashMap<>();
        this.OrderedRegionMapParallelToIntervalDomainMap = new HashMap<>();
        
        if(Runtime.getRuntime().freeMemory() <10000000000L)
			System.gc();
        
        for (ViewSolution viewSolution : viewSolutions.values()) {
            if (viewSolution instanceof ViewSolutionInMemory) {
                ((ViewSolutionInMemory) viewSolution).prepareForSearch();
            } else if (viewSolution instanceof ViewSolutionWithSolverStats) {
                ((ViewSolutionWithSolverStats) viewSolution).prepareForSearch();
            }
        }

        unifiedmakeAllViewRegionsConsistent(viewToVVPMap);
//        // Assigns sequence number to each VariableValuePair for all view
//        for(Entry<String, ViewSolution> entry : viewSolutions.entrySet())
//        {
//        	ConcurrentHashMap<String, VariableValuePair> seqToVarValuePairMap = new ConcurrentHashMap<>();
//        	long viewCardinality=0;
//        	String viewName = entry.getKey();
//        	seqNumberToVariableValuePairViewMap.put(viewName, seqToVarValuePairMap);
//        	if(entry.getValue().getVariableValuePairs() == null)
//        	{
//        		continue;
//        	}
//        	for(Integer i=0; i<entry.getValue().getVariableValuePairs().size(); i++)
//        	{
//        		VariableValuePair vvp = entry.getValue().getVariableValuePairs().get(i);
//        		vvp.variable.mergeBS();
//        		seqToVarValuePairMap.put(viewName+ "_" + i.toString(), vvp);
//        		viewCardinality+=vvp.rowcount;
//        		
//        	}
//        	
//        }
        
        for(Entry<String, List<VariableValuePair>> entry : viewToVVPMap.entrySet())
        {
        	ConcurrentHashMap<String, VariableValuePair> seqToVarValuePairMap = new ConcurrentHashMap<>();
//	        	long viewCardinality=0;
        	String viewName = entry.getKey();
        	seqNumberToVariableValuePairViewMap.put(viewName, seqToVarValuePairMap);
        	if(entry.getValue().get(0) == null)
        	{
        		continue;
        	}
        	for(Integer j=0; j<entry.getValue().size(); j++)
        	{
        		VariableValuePair vvp = entry.getValue().get(j);
        		vvp.variable.mergeBS();
        		seqToVarValuePairMap.put(viewName+ "_" + j.toString(), vvp);
//	        		viewCardinality+=vvp.rowcount;
        		
        	}
        	
        }
        
    }
	
public DatabaseSummary(StopWatch databaseSummarySW, SpillType spillType,String cond) {
	this.databaseSummarySW = databaseSummarySW;
    this.spillType = spillType;
    isConsistent = isCompressed = false;
    this.viewSolutions = new HashMap<>();
    this.seqNumberToVariableValuePairViewMap = new ConcurrentHashMap<>(); 
    this.FkSeqNumtoPkSeqNumListforFKview = new ConcurrentHashMap<>();
    this.pkSeqNumtoFkSeqNumListforFKView = new ConcurrentHashMap<>();  // 2
    this.FkSeqNumtoPkSeqNumListforFKview = new ConcurrentHashMap<>();  // 3
    this.pkViewToFkViewMap = new HashMap<>();  // 4
    this.viewSummaryMap = new HashMap<>();
    this.RegionIntervalMap = new HashMap<>();
    this.relationSummaryMap = new HashMap<>();
    this.IntervalDomainMap = new HashMap<>();
    this.viewErrorCountMap = new HashMap<>();
    this.OrderedRegionMapParallelToIntervalDomainMap = new HashMap<>();
    if(cond.contentEquals("BEFORE_RI")) {
    	this.readBeforeRIDump();
    	for(Entry<String, ViewSolution> entry : viewSolutions.entrySet())
        {
    		ConcurrentHashMap<String, VariableValuePair> seqToVarValuePairMap = new ConcurrentHashMap<>();
        	long viewCardinality=0;
        	String viewName = entry.getKey();
        	seqNumberToVariableValuePairViewMap.put(viewName, seqToVarValuePairMap);
        	if(entry.getValue().getVariableValuePairs() == null)
        	{
        		continue;
        	}
        	for(Integer i=0; i<entry.getValue().getVariableValuePairs().size(); i++)
        	{
        		VariableValuePair vvp = entry.getValue().getVariableValuePairs().get(i);
        		vvp.variable.mergeBS();
        		seqToVarValuePairMap.put(viewName+ "_" + i.toString(), vvp);
        		viewCardinality+=vvp.rowcount;
        		
        	}
        	
        }
    }
    else if(cond.contentEquals("AFTER_RI")){
    	this.readAfterRIDump();
    }
    else if(cond.contentEquals("INTER_RI")){
    	this.readInterRIDump();
    	//updateMappingAndViewSolution();
    }
    else {
    	System.out.println("Wrong Option");
    	System.exit(0);
    }
    
   
}
    
    private void readInterRIDump() {
	// TODO Auto-generated method stub
    	throw new RuntimeException("Uncomment the commented function");
    }

	private void readAfterRIDump() {
	// TODO Auto-generated method stub
		 throw new RuntimeException("Uncomment the commented function");
	}

	//BEFORE MATERIALIZATION CODE FROM TARUN
    //public DatabaseSummary(StopWatch databaseSummarySW, SpillType spillType, Map<String, ViewSolution> viewSolutions) {
    /*public DatabaseSummary(StopWatch databaseSummarySW, SpillType spillType, Map<String, ViewSolution> viewSolutions) {
        this.databaseSummarySW = databaseSummarySW;
        this.spillType = spillType;
        isConsistent = isCompressed = false;
        this.viewSolutions = viewSolutions;
        this.seqNumberToVariableValuePairViewMap = new ConcurrentHashMap<>();
        this.pkSeqNumtoFkSeqNumListforFKView = new ConcurrentHashMap<>();
        this.FkSeqNumtoPkSeqNumListforFKview = new ConcurrentHashMap<>();
        this.pkViewToFkViewMap = new HashMap<>();
        this.viewSummaryMap = new HashMap<>();
        this.RegionIntervalMap = new HashMap<>();
        this.relationSummaryMap = new HashMap<>();
        this.IntervalDomainMap = new HashMap<>();
        this.viewErrorCountMap = new HashMap<>();
        
        this.OrderedRegionMapParallelToIntervalDomainMap = new HashMap<>();
        
        makeAllViewRegionsConsistent();
        
        System.gc();
        // Assigns sequence number to each VariableValuePair for all view
        for(Entry<String, ViewSolution> entry : viewSolutions.entrySet())
        {
        	ConcurrentHashMap<String, VariableValuePair> seqToVarValuePairMap = new ConcurrentHashMap<String, VariableValuePair>();
        	long viewCardinality=0;
        	String viewName = entry.getKey();
        	seqNumberToVariableValuePairViewMap.put(viewName, seqToVarValuePairMap);
        	if(entry.getValue().getVariableValuePairs() == null)
        	{
        		continue;
        	}
        	
        	//if(!viewName.equals("t22")) {
        		//System.out.println("VVP : "  + viewName +  " " + entry.getValue().getVariableValuePairs());
        	//}
        	
        	for(Integer i=0; i<entry.getValue().getVariableValuePairs().size(); i++)
        	{
        		VariableValuePair vvp = entry.getValue().getVariableValuePairs().get(i);
        		seqToVarValuePairMap.put(viewName+ "_" + i.toString(), vvp);
        		viewCardinality+=vvp.rowcount;
        		
        		//if(viewName.equals("t08")) {
            		//System.out.println("VVP : "  + vvp);
            	//}
        		
        	}
        	
        	
        	
        }
       
        
    } */

    /**
     * Traverses summaryByView in topological order and adds an extra valueCombination
     * to the primary key viewSolution whenever required
     */
    public void makeFKeyConsistency() {
        if (isConsistent) {
            DebugHelper.printError("Received extra call to makeViewConsistency while it is already made consistent");
            return;
        }
        
        //Temp commented by shadab
        
        for (ViewSolution viewSolution : viewSolutions.values()) {
            if (viewSolution instanceof ViewSolutionInMemory) {
                ((ViewSolutionInMemory) viewSolution).prepareForSearch();
            } else if (viewSolution instanceof ViewSolutionWithSolverStats) {
                ((ViewSolutionWithSolverStats) viewSolution).prepareForSearch();
            }
        }
        
        
        Map<String, ViewInfo> viewInfos = PostgresVConfig.ANONYMIZED_VIEWINFOs;
        List<String> topoViewnames = PostgresVConfig.VIEWNAMES_TOPO;

        //Checking Views in topological order and adding extra tuple to fkeyViews whenever needed
        for (int i = 0; i < topoViewnames.size() - 1; i++) { //Last one won't require addition of any extra tuple to its children because it doesn't have any!
            String fkViewname = topoViewnames.get(i);
            ViewInfo fkViewInfo = viewInfos.get(fkViewname);
            List<String> fkSortedColumns = new ArrayList<>(fkViewInfo.getViewNonkeys());
            Collections.sort(fkSortedColumns);
            //ViewSolution fkViewSolution = viewSolutions.get(fkViewname);
            ViewSolution fkViewSolution = viewSolutions.get(fkViewname);

            DebugHelper.printDebug("Ensuring view consistency for pkviews of " + fkViewname);

            for (String pkViewname : fkViewInfo.getFkeyViews()) {
                ViewInfo pkViewInfo = viewInfos.get(pkViewname);
                List<String> sortedCommonColumns = new ArrayList<>(pkViewInfo.getViewNonkeys()); //All columns of pkViewInfo should infact be the common columns between it and viewInfo
                Collections.sort(sortedCommonColumns);

                //DebugHelper.printDebug("\tEnsuring view consistency for pkview " + pkViewname);

                IntList posOfCommonColumns = new IntArrayList(sortedCommonColumns.size());
                for (int j = 0; j < fkSortedColumns.size(); j++) {
                    if (sortedCommonColumns.contains(fkSortedColumns.get(j))) {
                        posOfCommonColumns.add(j);
                    }
                }

//                ViewSolution pkViewSolution = viewSolutions.get(pkViewname);
                ViewSolution pkViewSolution = viewSolutions.get(pkViewname);
                
                //Commented by Shadab to do Ref Integrity regionwise
//                for (ValueCombination fkValueCombination : fkViewSolution) {
//                    IntList seekedValuesInCombination = new IntArrayList(posOfCommonColumns.size());
//                    for (IntIterator iter = posOfCommonColumns.iterator(); iter.hasNext();) {
//                        int pos = iter.nextInt();
//                        seekedValuesInCombination.add(fkValueCombination.getColValues().getInt(pos));
//                    }
//
//                    if (!pkViewSolution.contains(seekedValuesInCombination)) {
//                        ValueCombination toaddValueCombination = new ValueCombination(seekedValuesInCombination, 1); //Adding extra valueCombination with count 1
//                        pkViewSolution.addValueCombination(toaddValueCombination);
//                    }
//
//                }
            
                List<Region> projectedRegionsFV=new ArrayList<>();
                for (VariableValuePair fkVar : fkViewSolution.getVariableValuePairs()) {
                    //IntList seekedValuesInCombination = new IntArrayList(posOfCommonColumns.size());
                	Region projectedRegion=new Region();
                	Region fkRegion=fkVar.variable;
                	for (int j =0;j<fkRegion.size();j++) {
                		
                		BucketStructure projectedBS=new BucketStructure();
                		for (IntIterator iter = posOfCommonColumns.iterator(); iter.hasNext();) {
                			int pos = iter.nextInt();
                			projectedBS.add(fkRegion.at(i).at(pos));                       
                        }
                		projectedRegion.add(projectedBS);
                    }
                	projectedRegionsFV.add(projectedRegion);                	
             }
            
            
            }
        }
        isConsistent = true;
        

//        if (DebugHelper.viewConsistencyErrorCheckNeeded()) {
//            if (databaseSummarySW != null) {
//                databaseSummarySW.pause();
//            }
//            DebugHelper.debugSummaryRowcounts(viewSolutions);
//            if (databaseSummarySW != null) {
//                databaseSummarySW.resume();
//            }
//        }
    }
    
    
    
    
    /**
     * Traverses summaryByView in topological order and adds an extra valueCombination
     * to the primary key viewSolution whenever required
     */
    // Added by tarun for Region consistency
    public void makeRegionConsistent() {
        if (isConsistent) {
            DebugHelper.printError("Received extra call to makeViewConsistency while it is already made consistent");
            return;
        }

     	 //System.out.println("viewSol t00" + ((ViewSolutionInMemory)this.viewSolutions.get("t00")).getLastSeenPK());
        
     	 /*

        for (ViewSolution viewSolution : viewSolutions.values()) {
            if (viewSolution instanceof ViewSolutionInMemory) {
                ((ViewSolutionInMemory) viewSolution).prepareForSearch();
            } else if (viewSolution instanceof ViewSolutionWithSolverStats) {
                ((ViewSolutionWithSolverStats) viewSolution).prepareForSearch();
            }
        }
        */

     	 //System.out.println("viewSol t00" + ((ViewSolutionInMemory)this.viewSolutions.get("t00")).getLastSeenPK());
        


        Map<String, ViewInfo> viewInfos = PostgresVConfig.ANONYMIZED_VIEWINFOs;
        List<String> topoViewnames = PostgresVConfig.VIEWNAMES_TOPO;
        
        int N_CONSUMERS = Runtime.getRuntime().availableProcessors();
      	ExecutorService service = Executors.newFixedThreadPool(N_CONSUMERS);
      	
      	 //System.out.println("viewSol t00" + ((ViewSolutionInMemory)this.viewSolutions.get("t00")).getLastSeenPK());
         

        //Checking Views in topological order and adding extra tuple to fkeyViews whenever needed
        for (int i = 0; i < topoViewnames.size() - 1; i++) { //Last one won't require addition of any extra tuple to its children because it doesn't have any!
            String fkViewname = topoViewnames.get(i);
            
            StopWatch regionCons = new StopWatch("Region-consistency for : "+ fkViewname);
    	    
            
            ViewInfo fkViewInfo = viewInfos.get(fkViewname);
            List<String> fkSortedColumns = new ArrayList<>(fkViewInfo.getViewNonkeys());
            Collections.sort(fkSortedColumns);

            DebugHelper.printDebug("Ensuring region consistency for pkviews of " + fkViewname);
            DebugHelper.printDebug("RAJfkViewInfo.getFkeyViews() " + fkViewInfo.getFkeyViews() + "fkSortedCols : " + fkSortedColumns);

            for (String pkViewname : fkViewInfo.getFkeyViews()) {
                ViewInfo pkViewInfo = viewInfos.get(pkViewname);
                List<String> pkViewSortedColumns = new ArrayList<>(pkViewInfo.getViewNonkeys()); //All columns of pkViewInfo should infact be the common columns between it and viewInfo
                Collections.sort(pkViewSortedColumns);
                
                // Now iterate over each column of fkView and find out column having pk-fk edge
                // pk-fk edge can be determine by seeing column path information of that column
                List<Integer> commonAttrFKIdxList = new ArrayList<>();
                List<Integer> commonAttrPKIdxList = new ArrayList<>();
                
                for(int fki=0; fki < fkSortedColumns.size(); fki++)
                {
                	String fkColumn = fkSortedColumns.get(fki);
                	Map<String, ColumnPathInfo> columnIdtoColumnPathMap = PostgresVConfig.COLUMN_ID_MAP;
                	
                    DebugHelper.printDebug("RAJcolumnIdtoColumnPathMap " + columnIdtoColumnPathMap);
                	
                	if(columnIdtoColumnPathMap.containsKey(fkColumn))
                	{
                		List<String> fkColPath = columnIdtoColumnPathMap.get(fkColumn).getColPath();
                		// search for pk-fk edge in column path

                        DebugHelper.printDebug("fkColPath" + fkColPath + " " +"fkColPath.size() " + fkColPath.size());
                        //DebugHelper.printDebug("fkColPath.get(fkColPath.size()-2) " + fkColPath.get(fkColPath.size()-2));
                        //DebugHelper.printDebug("fkColPath.get(fkColPath.size()-1) " + fkColPath.get(fkColPath.size()-1));
                    	
                		if(fkColPath.size() > 1 && 
                				fkColPath.get(fkColPath.size()-2).contentEquals(pkViewname)  &&
                				fkColPath.get(fkColPath.size()-1).contentEquals(fkViewname) )
                		{
                			
                			String[] fkColNameSplit = fkColumn.split("_");  // exp of fkColumn : t19_c003_3618624
                			
                			String pkColumn = fkColNameSplit[0] + "_" + fkColNameSplit[1] + "_" + fkColPath.subList(0, fkColPath.size()-1).hashCode();
                			
                			System.out.println("Joingg : " + pkColumn + " " + pkViewSortedColumns.indexOf(pkColumn));
                			System.out.println("Joingg : " + pkViewSortedColumns);
                			System.out.println("Joingg : " + fkColumn );
                			
              
                		
                			
                			//SPLITINTOMNWORK - ADD THIS LINE TO AVOID EXCEPTIONS
                			if(pkViewSortedColumns.indexOf(pkColumn)==-1)
                				continue;
                			
                			
                			//commonAttrPKList.add(pkColumn);
                			commonAttrPKIdxList.add(pkViewSortedColumns.indexOf(pkColumn));
                			//commonAttrFKList.add(fkColumn);
                    		commonAttrFKIdxList.add(fki);
                			
                		}
                		                	
                	}
                	
                }
                
               // System.out.println("commonAttrPkIdxList " + commonAttrPKIdxList);

                // Create a function Iterate over each region of fk and maps fk regions to pk regions
                // Add error cardinality(1) to the regions which don't have any associated region in pkView
                // Intersection between pk and fk regions are used to map pk-fk regions
                // It helps to keep region consistency and also will help to generate summary in later stages
                
                if(!commonAttrPKIdxList.isEmpty())
                {
 
                	if(!pkViewToFkViewMap.containsKey(pkViewname))
                	{
                		pkViewToFkViewMap.put(pkViewname,new ArrayList<String>());
                	}
                	pkViewToFkViewMap.get(pkViewname).add(fkViewname);
                	
                	mapFKRegionsToPKRegions(service, commonAttrFKIdxList,commonAttrPKIdxList,fkViewname,pkViewname);
                
                	
                	
                	
                	if(Runtime.getRuntime().freeMemory() <10000000000L)
            			System.gc();
                }
                else
                {
                	// iterate over each fk region and map it with all true region of pkRegion
                	ConcurrentHashMap<String, VariableValuePair> fkSeqToVarValPairMap = seqNumberToVariableValuePairViewMap.get(fkViewname);
                	
                	
                	ConcurrentHashMap<String,Set<String>> temp;
            		if(FkSeqNumtoPkSeqNumListforFKview.containsKey(fkViewname))
            		{
            			temp = FkSeqNumtoPkSeqNumListforFKview.get(fkViewname);
            		}
            		else
            		{
            			temp = new ConcurrentHashMap<String,Set<String>>();
            			FkSeqNumtoPkSeqNumListforFKview.put(fkViewname,temp);
            		}
            		

            		for(Entry<String, VariableValuePair> s : fkSeqToVarValPairMap.entrySet())
            		{
            			if(!temp.containsKey(s.getKey()))
            			{
            				Set<String> l = new HashSet<String>();
            				l.add(pkViewname + "_" + "allRegions");
            				temp.put(s.getKey(),l);
            			}
            			else
            			{
            				temp.get(s.getKey()).add(pkViewname + "_" + "allRegions");
            			}
            			
            		}                }
                
                if(Runtime.getRuntime().freeMemory() <10000000000L)
        			System.gc();
 
            }
            
          //HACK TO GET JASON OE GOING
            
            /*
        	if( fkViewInfo.getFkeyViews().size()>0) {
        		
        		if(!(fkViewname.contentEquals("t08") || fkViewname.contentEquals("t04") )) {
        			System.out.println("Deleting started for fk : " + fkViewname + " with pkViews : " + fkViewInfo.getFkeyViews() );
            		
        		seqNumberToVariableValuePairViewMap.remove(fkViewname);
        		//System.gc();
        		
        		this.viewSolutions.remove(fkViewname);
        		System.gc();
        		
        		System.out.println("Deleting ended for fk : " + fkViewname + " with pkViews : " + fkViewInfo.getFkeyViews() );
        		
        		}
        	}
        	
        	*/
        	
            regionCons.displayTimeAndDispose();
        }
        
        service.shutdown();
        
        /*
        ConcurrentHashMap<String, VariableValuePair> item = seqNumberToVariableValuePairViewMap.get("t11");
        
        long cardtotal = 0;
        long counter = 0;
        for(Entry<String, VariableValuePair> eb : item.entrySet()) {
        	VariableValuePair vvvp = eb.getValue();
        	cardtotal = cardtotal + vvvp.getRowcount();
        	System.out.println("Item card after RI " + counter++ + " " + vvvp.getRowcount() + " " + cardtotal);
        }
        */
        //dumpInterRI() ;
        
        //System.out.println("All entries : " + this.viewSolutions.keySet());
        //System.out.println("All entries : " + this.seqNumberToVariableValuePairViewMap.keySet());
		

        //System.out.println("viewSol t00" + ((ViewSolutionInMemory)this.viewSolutions.get("t00")).getLastSeenPK());
        
        StopWatch createFKMapandUpdateViewSol = new StopWatch("createFKMapandUpdateViewSol");
	    
        
        System.out.println("Started createFKRegiontoPKRegionListMap");
               
        createFKRegiontoPKRegionListMap();
        
        System.out.println("Finished createFKRegiontoPKRegionListMap");

        //System.out.println("viewSol t00" + ((ViewSolutionInMemory)this.viewSolutions.get("t00")).getLastSeenPK());
        
        
        System.out.println("Started updateViewSolutionsMap");
    
        //HACK TO GET JASON OE GOING
    	    updateViewSolutionsMap();
        
        System.out.println("Ended updateViewSolutionsMap");
        
        createFKMapandUpdateViewSol.displayTimeAndDispose();

       // System.out.println("viewSol t00" + ((ViewSolutionInMemory)this.viewSolutions.get("t00")).getLastSeenPK());
        
        isConsistent = true;
        
        //System.out.println("viewSol t00" + this.viewSolutions.get("t00"));
       
    }

    
    public void unifiedmakeRegionConsistent(HashMap<String, HashMap<String,Set<String>>> viewToprojectedFKRegionMap, ConcurrentHashMap<String,ConcurrentHashMap<String,Set<String>>> pkSeqNumtoFkSeqNumListforFKView,
    		ConcurrentHashMap<String,ConcurrentHashMap<String,Set<String>>> FkSeqNumtoPkSeqNumListforFKview) {
        if (isConsistent) {
            DebugHelper.printError("Received extra call to makeViewConsistency while it is already made consistent");
            return;
        }

     	 //System.out.println("viewSol t00" + ((ViewSolutionInMemory)this.viewSolutions.get("t00")).getLastSeenPK());
        
     	 /*

        for (ViewSolution viewSolution : viewSolutions.values()) {
            if (viewSolution instanceof ViewSolutionInMemory) {
                ((ViewSolutionInMemory) viewSolution).prepareForSearch();
            } else if (viewSolution instanceof ViewSolutionWithSolverStats) {
                ((ViewSolutionWithSolverStats) viewSolution).prepareForSearch();
            }
        }
        */

     	 //System.out.println("viewSol t00" + ((ViewSolutionInMemory)this.viewSolutions.get("t00")).getLastSeenPK());
        


        Map<String, ViewInfo> viewInfos = PostgresVConfig.ANONYMIZED_VIEWINFOs;
        List<String> topoViewnames = PostgresVConfig.VIEWNAMES_TOPO;
        
        int N_CONSUMERS = Runtime.getRuntime().availableProcessors();
      	ExecutorService service = Executors.newFixedThreadPool(N_CONSUMERS);
      	
      	 //System.out.println("viewSol t00" + ((ViewSolutionInMemory)this.viewSolutions.get("t00")).getLastSeenPK());
         

        //Checking Views in topological order and adding extra tuple to fkeyViews whenever needed
        for (int i = 0; i < topoViewnames.size() - 1; i++) { //Last one won't require addition of any extra tuple to its children because it doesn't have any!
            String fkViewname = topoViewnames.get(i);
            
            StopWatch regionCons = new StopWatch("Region-consistency for : "+ fkViewname);
    	    
            
            ViewInfo fkViewInfo = viewInfos.get(fkViewname);
            List<String> fkSortedColumns = new ArrayList<>(fkViewInfo.getViewNonkeys());
            Collections.sort(fkSortedColumns);

            DebugHelper.printDebug("Ensuring region consistency for pkviews of " + fkViewname);
            DebugHelper.printDebug("RAJfkViewInfo.getFkeyViews() " + fkViewInfo.getFkeyViews() + "fkSortedCols : " + fkSortedColumns);

            for (String pkViewname : fkViewInfo.getFkeyViews()) {
                ViewInfo pkViewInfo = viewInfos.get(pkViewname);
                List<String> pkViewSortedColumns = new ArrayList<>(pkViewInfo.getViewNonkeys()); //All columns of pkViewInfo should infact be the common columns between it and viewInfo
                Collections.sort(pkViewSortedColumns);
                
                // Now iterate over each column of fkView and find out column having pk-fk edge
                // pk-fk edge can be determine by seeing column path information of that column
                List<Integer> commonAttrFKIdxList = new ArrayList<>();
                List<Integer> commonAttrPKIdxList = new ArrayList<>();
                
                for(int fki=0; fki < fkSortedColumns.size(); fki++)
                {
                	String fkColumn = fkSortedColumns.get(fki);
                	Map<String, ColumnPathInfo> columnIdtoColumnPathMap = PostgresVConfig.COLUMN_ID_MAP;
                	
//                    DebugHelper.printDebug("RAJcolumnIdtoColumnPathMap " + columnIdtoColumnPathMap);
                	
                	if(columnIdtoColumnPathMap.containsKey(fkColumn))
                	{
                		List<String> fkColPath = columnIdtoColumnPathMap.get(fkColumn).getColPath();
                		// search for pk-fk edge in column path

                        DebugHelper.printDebug("fkColPath" + fkColPath + " " +"fkColPath.size() " + fkColPath.size());
                        //DebugHelper.printDebug("fkColPath.get(fkColPath.size()-2) " + fkColPath.get(fkColPath.size()-2));
                        //DebugHelper.printDebug("fkColPath.get(fkColPath.size()-1) " + fkColPath.get(fkColPath.size()-1));
                    	
                		if(fkColPath.size() > 1 && 
                				fkColPath.get(fkColPath.size()-2).contentEquals(pkViewname)  &&
                				fkColPath.get(fkColPath.size()-1).contentEquals(fkViewname) )
                		{
                			
                			String[] fkColNameSplit = fkColumn.split("_");  // exp of fkColumn : t19_c003_3618624
                			
                			String pkColumn = fkColNameSplit[0] + "_" + fkColNameSplit[1] + "_" + fkColPath.subList(0, fkColPath.size()-1).hashCode();
                			
                			System.out.println("Joingg : " + pkColumn + " " + pkViewSortedColumns.indexOf(pkColumn));
                			System.out.println("Joingg : " + pkViewSortedColumns);
                			System.out.println("Joingg : " + fkColumn );
                			
              
                		
                			
                			//SPLITINTOMNWORK - ADD THIS LINE TO AVOID EXCEPTIONS
                			if(pkViewSortedColumns.indexOf(pkColumn)==-1)
                				continue;
                			
                			
                			//commonAttrPKList.add(pkColumn);
                			commonAttrPKIdxList.add(pkViewSortedColumns.indexOf(pkColumn));
                			//commonAttrFKList.add(fkColumn);
                    		commonAttrFKIdxList.add(fki);
                			
                		}
                		                	
                	}
                	
                }
                
               // System.out.println("commonAttrPkIdxList " + commonAttrPKIdxList);

                // Create a function Iterate over each region of fk and maps fk regions to pk regions
                // Add error cardinality(1) to the regions which don't have any associated region in pkView
                // Intersection between pk and fk regions are used to map pk-fk regions
                // It helps to keep region consistency and also will help to generate summary in later stages
                
                if(!commonAttrPKIdxList.isEmpty())
                {
 
                	if(!pkViewToFkViewMap.containsKey(pkViewname))
                	{
                		pkViewToFkViewMap.put(pkViewname,new ArrayList<String>());
                	}
                	pkViewToFkViewMap.get(pkViewname).add(fkViewname);
                	
                	unifiedmapFKRegionsToPKRegions(viewToprojectedFKRegionMap, FkSeqNumtoPkSeqNumListforFKview, 
                			pkSeqNumtoFkSeqNumListforFKView, seqNumberToVariableValuePairViewMap,service, commonAttrFKIdxList,
                			commonAttrPKIdxList,fkViewname,pkViewname);
                
                	
                	
                	
                	if(Runtime.getRuntime().freeMemory() <10000000000L)
            			System.gc();
                }
                //PKR - commented else part
                else
                {
                	// iterate over each fk region and map it with all true region of pkRegion
                	ConcurrentHashMap<String, VariableValuePair> fkSeqToVarValPairMap = seqNumberToVariableValuePairViewMap.get(fkViewname);
                	
                	
                	ConcurrentHashMap<String,Set<String>> temp;
            		if(FkSeqNumtoPkSeqNumListforFKview.containsKey(fkViewname))
            		{
            			temp = FkSeqNumtoPkSeqNumListforFKview.get(fkViewname);
            		}
            		else
            		{
            			temp = new ConcurrentHashMap<String,Set<String>>();
            			FkSeqNumtoPkSeqNumListforFKview.put(fkViewname,temp);
            		}
            		

//            		if(fkSeqToVarValPairMap!=null) {
            			
            		
            		for(Entry<String, VariableValuePair> s : fkSeqToVarValPairMap.entrySet())
            		{
            			if(!temp.containsKey(s.getKey()))
            			{
            				Set<String> l = new HashSet<String>();
            				l.add(pkViewname + "_" + "allRegions");
            				temp.put(s.getKey(),l);
            			}
            			else
            			{
            				temp.get(s.getKey()).add(pkViewname + "_" + "allRegions");
            			}
            			
            		}  
            		}
//            		}
                
                if(Runtime.getRuntime().freeMemory() <10000000000L)
        			System.gc();
 
            }
            
          //HACK TO GET JASON OE GOING
            
            /*
        	if( fkViewInfo.getFkeyViews().size()>0) {
        		
        		if(!(fkViewname.contentEquals("t08") || fkViewname.contentEquals("t04") )) {
        			System.out.println("Deleting started for fk : " + fkViewname + " with pkViews : " + fkViewInfo.getFkeyViews() );
            		
        		seqNumberToVariableValuePairViewMap.remove(fkViewname);
        		//System.gc();
        		
        		this.viewSolutions.remove(fkViewname);
        		System.gc();
        		
        		System.out.println("Deleting ended for fk : " + fkViewname + " with pkViews : " + fkViewInfo.getFkeyViews() );
        		
        		}
        	}
        	
        	*/
        	
            regionCons.displayTimeAndDispose();
        }
        
        service.shutdown();
        
        /*
        ConcurrentHashMap<String, VariableValuePair> item = seqNumberToVariableValuePairViewMap.get("t11");
        
        long cardtotal = 0;
        long counter = 0;
        for(Entry<String, VariableValuePair> eb : item.entrySet()) {
        	VariableValuePair vvvp = eb.getValue();
        	cardtotal = cardtotal + vvvp.getRowcount();
        	System.out.println("Item card after RI " + counter++ + " " + vvvp.getRowcount() + " " + cardtotal);
        }
        */
        //dumpInterRI() ;
        
        //System.out.println("All entries : " + this.viewSolutions.keySet());
        //System.out.println("All entries : " + this.seqNumberToVariableValuePairViewMap.keySet());
		

        //System.out.println("viewSol t00" + ((ViewSolutionInMemory)this.viewSolutions.get("t00")).getLastSeenPK());
        
        StopWatch createFKMapandUpdateViewSol = new StopWatch("createFKMapandUpdateViewSol");
	    
        
        System.out.println("Started createFKRegiontoPKRegionListMap");
               
        createFKRegiontoPKRegionListMap();
        
        System.out.println("Finished createFKRegiontoPKRegionListMap");

        //System.out.println("viewSol t00" + ((ViewSolutionInMemory)this.viewSolutions.get("t00")).getLastSeenPK());
        
        
        System.out.println("Started updateViewSolutionsMap");
    
        //HACK TO GET JASON OE GOING
    	    updateViewSolutionsMap();
        
        System.out.println("Ended updateViewSolutionsMap");
        
        createFKMapandUpdateViewSol.displayTimeAndDispose();

       // System.out.println("viewSol t00" + ((ViewSolutionInMemory)this.viewSolutions.get("t00")).getLastSeenPK());
        
        isConsistent = true;
        
        //System.out.println("viewSol t00" + this.viewSolutions.get("t00"));
       
    }

    
 private void updateViewSolutionsMap() {
		
    	for(Entry<String, ConcurrentHashMap<String, Set<String>>> view : FkSeqNumtoPkSeqNumListforFKview.entrySet()) {
    	
    		List<VariableValuePair> newRegionsList = new ArrayList<>();
    		for(Entry<String, Set<String>> region : view.getValue().entrySet()) {
    			
    			VariableValuePair vvp = seqNumberToVariableValuePairViewMap.get(view.getKey()).get(region.getKey());
    			newRegionsList.add(vvp);
    			
    			
    		}
    		
    		viewSolutions.get(view.getKey()).setVariableValuePairs(newRegionsList);
    		
    		if(Runtime.getRuntime().freeMemory() <10000000000L)
				System.gc();
			
    	}
		
	}

	private void createFKRegiontoPKRegionListMap() {
		
    	for(Entry<String, ConcurrentHashMap<String, Set<String>>> e  : pkSeqNumtoFkSeqNumListforFKView.entrySet())
    	{
    		ConcurrentHashMap<String, Set<String>> temp;
    		if(FkSeqNumtoPkSeqNumListforFKview.containsKey(e.getKey()))
    		{
    			temp = FkSeqNumtoPkSeqNumListforFKview.get(e.getKey());
    		}
    		else
    		{
    			temp = new ConcurrentHashMap<String,Set<String>>();
    			FkSeqNumtoPkSeqNumListforFKview.put(e.getKey(),temp);
    		}
    		
    		for(Entry<String, Set<String>> s : pkSeqNumtoFkSeqNumListforFKView.get(e.getKey()).entrySet())
    		{
    			for(String regno : s.getValue())
    			{
    				if(!temp.containsKey(regno))
        			{
        				Set<String> l = new HashSet<String>();
        				l.add(s.getKey());
        				temp.put(regno,l);
        			}
        			else
        			{
        				temp.get(regno).add(s.getKey());
        			}
    			}
    			
    			
    		}
    		if(Runtime.getRuntime().freeMemory() <10000000000L)
				System.gc();
			
    		
    	}
	}

    
	
	//COMMENTED ON 27 NOV TO CHECK IF THERE IS ANY BUG FROM BEFORE_RI TO AFTER_RI
	
	/*
    public void updateMappingAndViewSolution() {
    	
    	 //dumpInterRI();
         
         System.out.println("Started createFKRegiontoPKRegionListMap");
                
         createFKRegiontoPKRegionListMap();
         
         System.out.println("Finished createFKRegiontoPKRegionListMap");
         
         
         System.out.println("Started updateViewSolutionsMap");
     
         //HACK TO GET JASON OE GOING
     	    updateViewSolutionsMap();
         
         System.out.println("Ended updateViewSolutionsMap");
         
         
         isConsistent = true;
    }

    private void updateViewSolutionsMap() {
       
        for(Entry<String, ConcurrentHashMap<String, Set<String>>> view : FkSeqNumtoPkSeqNumListforFKview.entrySet()) {
       
        	//if(this.viewSolutions.keySet().contains(view.getKey())) {
        	//if(!view.getKey().equals("t10"))continue;
        	
        	 if(view.getKey().equals("t10"))
                 System.out.println("uvs " +viewSolutions.get(view.getKey()).getVariableValuePairs());
                 
    		
        	System.out.println("Inside updateViewSolMap, started for " + view.getKey());
        	
        	if(view.getKey().equals("t10"))
                System.out.println("All  " + seqNumberToVariableValuePairViewMap.get(view.getKey()));
      
        	 List<VariableValuePair> newRegionsList = new ArrayList<>();
            for(Entry<String, Set<String>> region : view.getValue().entrySet()) {
               
            	if(view.getKey().equals("t10"))
                    System.out.println("region.getKey() " + region.getKey() );
            	
              	
                VariableValuePair vvp = seqNumberToVariableValuePairViewMap.get(view.getKey()).get(region.getKey());
                newRegionsList.add(vvp);
                
                            
            }
           
            viewSolutions.get(view.getKey()).setVariableValuePairs(newRegionsList);
            
            if(view.getKey().equals("t10"))
            System.out.println("uvs " +viewSolutions.get(view.getKey()).getVariableValuePairs());
            
            
            System.out.println("Inside updateViewSolMap, ended for " + view.getKey());
        	
        	//}
           
        }
       
    }

	private void createFKRegiontoPKRegionListMap() {
		
		System.out.println("t10 vvp" + this.viewSolutions.get("t10").getVariableValuePairs());
		
    	for(Entry<String,ConcurrentHashMap<String,Set<String>>> e  : pkSeqNumtoFkSeqNumListforFKView.entrySet())
    	{
    		System.out.println("Inside createFKRegiontoPKRegionListMap, started for " + e.getKey());
        	
    		
    		//if(!e.getKey().equals("t10"))continue;
    		
    		ConcurrentHashMap<String,Set<String>> temp;
    		if(FkSeqNumtoPkSeqNumListforFKview.containsKey(e.getKey()))
    		{
    			temp = FkSeqNumtoPkSeqNumListforFKview.get(e.getKey());
    		}
    		else
    		{
    			temp = new ConcurrentHashMap<String,Set<String>>();
    			FkSeqNumtoPkSeqNumListforFKview.put(e.getKey(),temp);
    		}
    		
    		for(Entry<String, Set<String>> s : pkSeqNumtoFkSeqNumListforFKView.get(e.getKey()).entrySet())
    		{
    			for(String regno : s.getValue())
    			{
    				if(!temp.containsKey(regno))
        			{
        				Set<String> l = new HashSet<String>();
        				l.add(s.getKey());
        				temp.put(regno,l);
        			}
        			else
        			{
        				temp.get(regno).add(s.getKey());
        			}
    				
    				//if(regno.contains("t10_0")) System.out.println("Debugggg + " + regno );
    				
    				//System.out.println("regno " + regno + " " + temp.get(regno)) ;
    			}
    			
    			
    		}
    		
    		System.gc();
    		
    		System.out.println("Inside createFKRegiontoPKRegionListMap, ended for " + e.getKey());
        	
    	}
	}
	
	*/
	
private void mapFKRegionsToPKRegions(ExecutorService service, List<Integer> commonAttrFKIdxList, List<Integer> commonAttrPKIdxList, String fkViewname, String pkViewname) {
    	
    	
    	Map<String, VariableValuePair> fkSeqToVarValPairMap = seqNumberToVariableValuePairViewMap.get(fkViewname);
    	Map<String, VariableValuePair> pkSeqToVarValPairMap = seqNumberToVariableValuePairViewMap.get(pkViewname);
    	HashMap<String,Set<String>> projectedFKRegionMap = new HashMap<>();
    	// Iterating over VariableValuePair(Region of fk)
    	int count = 0;
		int total = fkSeqToVarValPairMap.size();
		
		boolean printFlagForDebugging = false;
		
    	for(Entry<String, VariableValuePair> vvp : fkSeqToVarValPairMap.entrySet() )
    	{
    		// Map pkSeqno to fkseqno
    		// divide pk region if required and add both regions and remove entry for old region
    		
    		Region fkRegion = vvp.getValue().variable;
    		String fkSeqNum = vvp.getKey();
    		if(fkSeqNum.contains("allRegions"))
    			continue;
    		if(!pkSeqNumtoFkSeqNumListforFKView.containsKey(fkViewname))
    		{
    			pkSeqNumtoFkSeqNumListforFKView.put(fkViewname,new ConcurrentHashMap<String,Set<String>>());
    		}   
    		
    		
    		
    		//System.out.println("Doing : " + fkViewname + " " +pkViewname + " " + count++ + " " + total);
    		count++;
    			
    		//if(!fkViewname.equals("t10")) continue;
    			
    		
    		//findIntersectingRegion(fkRegion,pkSeqToVarValPairMap,commonAttrFKIdxList,commonAttrPKIdxList,pkViewname,fkViewname,fkSeqNum);
    		Region projectedFKRegion = projectRegion(fkRegion,commonAttrFKIdxList);
    		Set<String> pkRegionsSeqnum = null;
    		if(projectedFKRegionMap.containsKey(projectedFKRegion.toString())) {
    			pkRegionsSeqnum = projectedFKRegionMap.get(projectedFKRegion.toString());
    			
    		}
    		else {
    			//System.err.println("ACTUALLY DOING : " + fkViewname + " " +pkViewname + " " + count + " " + total);
    			//System.err.println("Region : " + projectedFKRegion.toString());
        		
        		
     		   pkRegionsSeqnum = newfindIntersectingRegion(service, projectedFKRegion,pkSeqToVarValPairMap,commonAttrFKIdxList,commonAttrPKIdxList,pkViewname,fkViewname,fkSeqNum, printFlagForDebugging, count, total);
     		   projectedFKRegionMap.put(projectedFKRegion.toString(),pkRegionsSeqnum);
     		   for(String pkReg : pkRegionsSeqnum ) {
 	    		   for(Entry<String,Set<String>> e : projectedFKRegionMap.entrySet()) {
 	    				 
 	    				 Set<String> regSeqNumSet =  e.getValue();
 	    				 
 	    				
 	    				 if(regSeqNumSet.contains(pkReg.subSequence(0, pkReg.length()-2))) {
 	    					 
 	    					 regSeqNumSet.remove(pkReg.subSequence(0, pkReg.length()-2)); // removing older name
 	    					 regSeqNumSet.add(pkReg);  // intersecting part
 	    					 if(pkSeqToVarValPairMap.containsKey(pkReg.subSequence(0, pkReg.length()-2) + "_1")) {
 	    						 regSeqNumSet.add(pkReg.subSequence(0, pkReg.length()-2) + "_1"); // non intersecting part
 	    					 }
 	    					 
 	    					 
 	    				 }
 	    			 }
     		   }
     		   
     		   
     		}
    		
    		
    		
    		
    		
    		for(String pkReg : pkRegionsSeqnum ) {
  			   
      			 if(pkSeqNumtoFkSeqNumListforFKView.get(fkViewname).containsKey(pkReg))
     				 {
     					pkSeqNumtoFkSeqNumListforFKView.get(fkViewname).get(pkReg).add(fkSeqNum);
     				 }
      			 else {
      				 Set<String> l = new HashSet<String>();
    				     l.add(fkSeqNum);
        			     pkSeqNumtoFkSeqNumListforFKView.get(fkViewname).put(pkReg,l);
      			 }
      			   
      		   }
    		
    	
    	}
    	System.out.println("STATS FOR THIS VIEW : " + fkViewname + " " + pkViewname + ", Actual VVP size: " + fkSeqToVarValPairMap.entrySet().size() +", Unique VVP size: " + projectedFKRegionMap.size() );
    	
	}

	
private void unifiedmapFKRegionsToPKRegions(HashMap<String, HashMap<String,Set<String>>> viewToprojectedFKRegionMap, 
		ConcurrentHashMap<String,ConcurrentHashMap<String,Set<String>>> FkSeqNumtoPkSeqNumListforFKview, 
		ConcurrentHashMap<String,ConcurrentHashMap<String,Set<String>>> pkSeqNumtoFkSeqNumListforFKView, 
		ConcurrentHashMap<String,ConcurrentHashMap<String, VariableValuePair>> seqNumberToVariableValuePairViewMap, 
		ExecutorService service, List<Integer> commonAttrFKIdxList, List<Integer> commonAttrPKIdxList, String fkViewname, String pkViewname) {
    	
    	
    	Map<String, VariableValuePair> fkSeqToVarValPairMap = seqNumberToVariableValuePairViewMap.get(fkViewname);
    	Map<String, VariableValuePair> pkSeqToVarValPairMap = seqNumberToVariableValuePairViewMap.get(pkViewname);
    	HashMap<String,Set<String>> projectedFKRegionMap = new HashMap<>();
    	// Iterating over VariableValuePair(Region of fk)
    	int count = 0;
    	int total = 0;
    	if(fkSeqToVarValPairMap != null)
    		total = fkSeqToVarValPairMap.size();
		
		boolean printFlagForDebugging = false;
		
		//PKR
		if(fkSeqToVarValPairMap != null) {
			
		
    	for(Entry<String, VariableValuePair> vvp : fkSeqToVarValPairMap.entrySet() )
    	{
    		// Map pkSeqno to fkseqno
    		// divide pk region if required and add both regions and remove entry for old region
    		
    		Region fkRegion = vvp.getValue().variable;
    		String fkSeqNum = vvp.getKey();
    		if(fkSeqNum.contains("allRegions"))
    			continue;
    		if(!pkSeqNumtoFkSeqNumListforFKView.containsKey(fkViewname))
    		{
    			pkSeqNumtoFkSeqNumListforFKView.put(fkViewname,new ConcurrentHashMap<String,Set<String>>());
    		}   
    		
    		
    		
    		//System.out.println("Doing : " + fkViewname + " " +pkViewname + " " + count++ + " " + total);
    		count++;
    			
    		//if(!fkViewname.equals("t10")) continue;
    			
    		
    		//findIntersectingRegion(fkRegion,pkSeqToVarValPairMap,commonAttrFKIdxList,commonAttrPKIdxList,pkViewname,fkViewname,fkSeqNum);
    		Region projectedFKRegion = projectRegion(fkRegion,commonAttrFKIdxList);
    		Set<String> pkRegionsSeqnum = null;
    		if(projectedFKRegionMap.containsKey(projectedFKRegion.toString())) {
    			pkRegionsSeqnum = projectedFKRegionMap.get(projectedFKRegion.toString());
    			
    		}
    		else {
    			//System.err.println("ACTUALLY DOING : " + fkViewname + " " +pkViewname + " " + count + " " + total);
    			//System.err.println("Region : " + projectedFKRegion.toString());
        		
        		
     		   pkRegionsSeqnum = unifiednewfindIntersectingRegion(FkSeqNumtoPkSeqNumListforFKview, 
     				   pkSeqNumtoFkSeqNumListforFKView, service, projectedFKRegion,pkSeqToVarValPairMap,
     				   commonAttrFKIdxList,commonAttrPKIdxList,pkViewname,fkViewname,
     				   fkSeqNum, printFlagForDebugging, count, total);
     		   projectedFKRegionMap.put(projectedFKRegion.toString(),pkRegionsSeqnum);
     		   for(String pkReg : pkRegionsSeqnum ) {
 	    		   for(Entry<String,Set<String>> e : projectedFKRegionMap.entrySet()) {
 	    				 
 	    				 Set<String> regSeqNumSet =  e.getValue();
 	    				 
 	    				
 	    				 if(regSeqNumSet.contains(pkReg.subSequence(0, pkReg.length()-2))) {
 	    					 
 	    					 regSeqNumSet.remove(pkReg.subSequence(0, pkReg.length()-2)); // removing older name
 	    					 regSeqNumSet.add(pkReg);  // intersecting part
 	    					 if(pkSeqToVarValPairMap.containsKey(pkReg.subSequence(0, pkReg.length()-2) + "_1")) {
 	    						 regSeqNumSet.add(pkReg.subSequence(0, pkReg.length()-2) + "_1"); // non intersecting part
 	    					 }
 	    					 
 	    					 
 	    				 }
 	    			 }
     		   }
     		   
     		   
     		}
    		
    		
    		
    		
    		
    		for(String pkReg : pkRegionsSeqnum ) {
  			   
      			 if(pkSeqNumtoFkSeqNumListforFKView.get(fkViewname).containsKey(pkReg))
     				 {
     					pkSeqNumtoFkSeqNumListforFKView.get(fkViewname).get(pkReg).add(fkSeqNum);
     				 }
      			 else {
      				 Set<String> l = new HashSet<String>();
    				     l.add(fkSeqNum);
        			     pkSeqNumtoFkSeqNumListforFKView.get(fkViewname).put(pkReg,l);
      			 }
      			   
      		   }
    		
    	
    	}
		
    	System.out.println("STATS FOR THIS VIEW : " + fkViewname + " " + pkViewname + ", Actual VVP size: " + fkSeqToVarValPairMap.entrySet().size() +", Unique VVP size: " + projectedFKRegionMap.size() );
		
    	//PKR
    	viewToprojectedFKRegionMap.put(fkViewname, projectedFKRegionMap);
		
		}
	}

	
	//OLD CODE BEFORE INDEX OUT OF BOUND EXCEPTION
	/*private void mapFKRegionsToPKRegions(ExecutorService service, List<Integer> commonAttrFKIdxList, List<Integer> commonAttrPKIdxList, String fkViewname, String pkViewname) {

		ConcurrentHashMap<String, VariableValuePair> fkSeqToVarValPairMap = seqNumberToVariableValuePairViewMap.get(fkViewname);
		ConcurrentHashMap<String, VariableValuePair> pkSeqToVarValPairMap = seqNumberToVariableValuePairViewMap.get(pkViewname);
    	
		
		//System.out.println("seqNumberToVariableValuePairViewMap " + seqNumberToVariableValuePairViewMap);
		
		int count = 0;
		int total = fkSeqToVarValPairMap.size();
		boolean printFlagForDebugging = false;
		
		Set<String> uniqueFKRegions = new HashSet<>();
    			
		//System.out.println("total " + total);
    	
    	// Iterating over VariableValuePair(Region of fk)
    	for(Entry<String, VariableValuePair> vvp : fkSeqToVarValPairMap.entrySet() )
    	{
    		// Map pkSeqno to fkseqno
    		// divide pk region if required and add both regions and remove entry for old region
    		
    		
    		Region fkRegion = vvp.getValue().variable;
    		String fkSeqNum = vvp.getKey();
    		
    		//System.out.println("Fkviewname , pkViewname, fkSeqNum " + fkViewname + " " + pkViewname +  " " + fkSeqNum);

    		
    		if(fkSeqNum.contains("allRegions"))
    			continue;
    		if(!pkSeqNumtoFkSeqNumListforFKView.containsKey(fkViewname))
    		{
    			pkSeqNumtoFkSeqNumListforFKView.put(fkViewname,new ConcurrentHashMap<String,Set<String>>());
    		}    	
    		
    		System.err.println("Doing : " + fkViewname + " " +pkViewname + " " + count++ + " " + total);
    		
    		
    		Region projectedFKRegion = projectRegion(fkRegion,commonAttrFKIdxList);  // projectedFKRegion only contains columns that are in pkView
    		
    		String projectedFKRegionString = projectedFKRegion.toString();
    		
    		if(!uniqueFKRegions.contains(projectedFKRegionString)) {
    			
    			System.err.println("ACTUALLY DOING : " + fkViewname + " " +pkViewname + " " + count + " " + total);
        		
    			
    			System.err.println("Region : " + projectedFKRegionString);
        		
    			
    			findIntersectingRegion(service, fkRegion,pkSeqToVarValPairMap,commonAttrFKIdxList,commonAttrPKIdxList,pkViewname,fkViewname,fkSeqNum, printFlagForDebugging);
        		
    			System.gc();
        		
    			uniqueFKRegions.add(projectedFKRegionString);
    		}
    		
    		//if(!(fkViewname.equals("t17") && pkViewname.equals("t07"))) continue;
    		
    		//if(count<302) continue;
		 	
    		//if(fkViewname.equals("t22") && pkViewname.equals("t20") && count>301 && count<500)
    		//	printFlagForDebugging = true;
    		//else 
    		//	printFlagForDebugging = false;
    		
    		
    		//findIntersectingRegion(service, fkRegion,pkSeqToVarValPairMap,commonAttrFKIdxList,commonAttrPKIdxList,pkViewname,fkViewname,fkSeqNum, printFlagForDebugging);
    		
    		//System.gc();
    		//Runtime.getRuntime().gc();
    			
    		//all view search
    	
    	}
    	
    	System.out.println("STATS FOR THIS VIEW : " + fkViewname + " " + pkViewname + ", Actual VVP size: " + fkSeqToVarValPairMap.entrySet().size() +", Unique VVP size: " + uniqueFKRegions.size() );
	}
	
	*/
	

public class NewRegionIntersectionHelperByMultiThreading implements Callable<Boolean> {

	String pkSeqNum;
	Map<String, VariableValuePair> pkSeqToVarValPairMap;
	Region projectedFKRegion;
	List<Integer> commonAttrPKIdxList;
	String pkViewname;
	String fkViewname;
	String fkSeqNum;
	boolean intersectionExist;
	boolean printFlagForDebugging;
	ConcurrentHashMap interesectionPKRegionsSeqnumHashSet;
	
	
	public NewRegionIntersectionHelperByMultiThreading(String pkSeqNumString, Map<String, VariableValuePair> pkSeqToVarValPairMap,
			Region projectedFKRegion, List<Integer> commonAttrPKIdxList, String pkViewname, String fkViewname,
			String fkSeqNum, ConcurrentHashMap<String, String> interesectionPKRegionsSeqnumHashSet, boolean printFlagForDebugging) {
		super();
		this.pkSeqNum = pkSeqNumString;
		this.pkSeqToVarValPairMap = pkSeqToVarValPairMap;
		this.projectedFKRegion = projectedFKRegion;
		this.commonAttrPKIdxList = commonAttrPKIdxList;
		this.pkViewname = pkViewname;
		this.fkViewname = fkViewname;
		this.fkSeqNum = fkSeqNum;
		this.intersectionExist = false;
		this.interesectionPKRegionsSeqnumHashSet = interesectionPKRegionsSeqnumHashSet;
		this.printFlagForDebugging = printFlagForDebugging;
	}





	@Override
	public Boolean call() throws Exception {

		VariableValuePair pkVariableValuePair = pkSeqToVarValPairMap.get(pkSeqNum);
		Region pkRegion = pkVariableValuePair.variable;
		
		long regionCardinality = pkVariableValuePair.rowcount;
		
		Region projectedPKRegion = projectRegion(pkRegion,commonAttrPKIdxList);
		
		//projectedPKRegion.deleteDuplicateBucketStructure("1");
		Region intersectingProjectedRegion = null;
		try{
			intersectingProjectedRegion = projectedFKRegion.intersection(projectedPKRegion);
		}catch(Exception e) {
			System.out.println("commonAttrPKIdxList : " + commonAttrPKIdxList);
			System.out.println("projectedPKRegion : " + projectedPKRegion);
			System.out.println("projectedFKRegion : " + projectedFKRegion);
			
		}

		
		//intersectingProjectedRegion.deleteDuplicateBucketStructure("2");
		
		if(intersectingProjectedRegion.isEmpty()) {

			//continue;
		
		}else
		{
			intersectionExist = true;
			Region intersectingPKRegion = getExpandedRegion(intersectingProjectedRegion,pkRegion, commonAttrPKIdxList);
			
			//intersectingPKRegion.deleteDuplicateBucketStructure("3");
			
			Region nonIntersectingPKRegion = pkRegion.minus(intersectingPKRegion);
			
			//nonIntersectingPKRegion.deleteDuplicateBucketStructure("4");
			
			//RAJKUMAR ADDED THIS LINE - BUG CAUSING ITEM CARDINALITY TO GO NEGATIVE IN NEW WORKLOAD
			//long nonIntersectingRegionRowCount = findRegionCardinalityUniformlyByComputingVolume(pkViewname, pkRegion,nonIntersectingPKRegion,regionCardinality);
			
			//ACTUAL LINE CALCULATES VOL BASED ON SIZE
			long nonIntersectingRegionRowCount = findRegionCardinalityUniformly(pkRegion,nonIntersectingPKRegion,regionCardinality);
			
			
			long IntersectingRegionRowCount = regionCardinality - nonIntersectingRegionRowCount;
			VariableValuePair intersectingVarValPair =  new VariableValuePair(intersectingPKRegion,IntersectingRegionRowCount);
			String pkSeqNumForIntersectingRegion = pkSeqNum + "_0";
			
			pkSeqToVarValPairMap.put(pkSeqNumForIntersectingRegion, intersectingVarValPair);
			List<String> newSeqNumList = new ArrayList<String>();
			newSeqNumList.add(pkSeqNumForIntersectingRegion);
			interesectionPKRegionsSeqnumHashSet.put(pkSeqNumForIntersectingRegion, pkSeqNumForIntersectingRegion);
			
			
			//if(pkViewname.equals("t11") || fkViewname.equals("t11")) {
				
				if(nonIntersectingRegionRowCount < 0)
					System.err.println("Culprit, pk fk viewname = nonIntersectingRegionRowCount " + pkViewname + " " + fkViewname + " "+ nonIntersectingRegionRowCount + " rcard " + regionCardinality);
				if(IntersectingRegionRowCount < 0)
					System.err.println("Culprit, pk fk viewname =  IntersectingRegionRowCount " + pkViewname + " " + fkViewname + " "+ IntersectingRegionRowCount+ " rcard " + regionCardinality);
			//}
			
			
			// Non-Intersecting region only adds when it's not empty and it's region cardinality is more than 0.
			if((!nonIntersectingPKRegion.isEmpty()) && nonIntersectingRegionRowCount>0)
			{
				String pkSeqNumForNonIntersectingRegion = pkSeqNum + "_1";
				VariableValuePair nonIntersectingVarValPair = new VariableValuePair(nonIntersectingPKRegion,nonIntersectingRegionRowCount);
				pkSeqToVarValPairMap.put(pkSeqNumForNonIntersectingRegion, nonIntersectingVarValPair);
				newSeqNumList.add(pkSeqNumForNonIntersectingRegion);
				
			}
			if(Runtime.getRuntime().freeMemory() <10000000000L)
				System.gc();
			// Replace old sequence number with new sequence numbers whenever a region breaks one more time
			maintainpkfkSeqNumMapping(pkViewname,pkSeqNum,newSeqNumList);
			
			// Remove sequence number for 
			pkSeqToVarValPairMap.remove(pkSeqNum,pkVariableValuePair);
		}

	return intersectionExist;
	}

	
}


private Set<String> newfindIntersectingRegion(ExecutorService service, Region projectedFKRegion,
		Map<String, VariableValuePair> pkSeqToVarValPairMap, List<Integer> commonAttrFKIdxList,
		List<Integer> commonAttrPKIdxList, String pkViewname, String fkViewname, String fkSeqNum, boolean printFlagForDebugging, int countFk, int countFkTotal){
	Set<String> interesectionPKRegionsSeqnum = new HashSet<>();
	
	ConcurrentHashMap<String,String> interesectionPKRegionsSeqnumHashSet = new ConcurrentHashMap<>();	
	// Creating a list of sequence number to be iterated on to map fkRegion
	Set<String> pkSeqNumSet = pkSeqToVarValPairMap.keySet();
	ArrayList<String> pkSeqNumList = new ArrayList<>();
	for(String s : pkSeqNumSet)
	{
		pkSeqNumList.add(s);
	}
	
	Collections.sort(pkSeqNumList);
	
	boolean intersectionExist = false;
	
	//Region projectedFKRegion = projectRegion(fkRegion,commonAttrFKIdxList);  // projectedFKRegion only contains columns that are in pkView
	
	List<Future<Boolean>> allFutures = new ArrayList<Future<Boolean>>();
	

	long pkCount = 0;
	long pkCountTotal = pkSeqNumList.size();
	
	for(String pkSeqNum : pkSeqNumList)
	{
		
		//System.out.println("Doing fk:" + fkViewname +" pk: "+ pkViewname + " : "+ countFk +" / " + countFkTotal +" pkNumber : " + pkCount++ + " / " + pkCountTotal);
		
		if(pkSeqNum.contains("allRegions"))
			continue;

		Region projectedFKRegionDeepCopy = projectedFKRegion.getDeepCopy();
		
		//projectedFKRegionDeepCopy.deleteDuplicateBucketStructure("5");

		Future<Boolean> future = service.submit(new NewRegionIntersectionHelperByMultiThreading(pkSeqNum, pkSeqToVarValPairMap, projectedFKRegionDeepCopy,
				commonAttrPKIdxList, pkViewname, fkViewname,fkSeqNum, interesectionPKRegionsSeqnumHashSet, printFlagForDebugging));
		
		allFutures.add(future);
		
	}
	
	
	
	
	for(Future<Boolean> f : allFutures) {
		
			Boolean result;
			try {
				result = f.get();
				intersectionExist = intersectionExist || result ;
			} catch (InterruptedException | ExecutionException e) {
				e.printStackTrace();
			}

	}
	
	for(String str : interesectionPKRegionsSeqnumHashSet.keySet())	
		interesectionPKRegionsSeqnum.add(str);
	
	Integer colCount=0; // Helps to find to error like if empty Region got added to SeqNum to Region map.

	if(!intersectionExist)
	while(!pkSeqNumList.isEmpty()  && colCount==0 )
	{
		
		String pkSeqNum = pkSeqNumList.get(0);
		
		pkSeqNumList.remove(0);
		if(pkSeqNum.contains("allRegions"))
			continue;
		
		if(pkSeqToVarValPairMap.containsKey(pkSeqNum)) {
		VariableValuePair pkVariableValuePair = pkSeqToVarValPairMap.get(pkSeqNum);
		Region pkRegion = pkVariableValuePair.variable;
		colCount = pkRegion.at(0).size(); // Number of columns in pkRegion // using it for error check. if error here means empty region is pushed.
		}
		
	}
	
	if(!intersectionExist)
	{
		Region zeroCardinalityRegion =getPKCompatibleRegion(projectedFKRegion,colCount,commonAttrPKIdxList,pkViewname);
		//zeroCardinalityRegion.deleteDuplicateBucketStructure();
		Integer len = pkSeqToVarValPairMap.size();
		VariableValuePair errorVarValPair = new VariableValuePair(zeroCardinalityRegion,1);
		String newSeqNum = pkViewname+ "_" +len.toString();
		pkSeqToVarValPairMap.put(newSeqNum,errorVarValPair);
		interesectionPKRegionsSeqnum.add(newSeqNum);
		//pkSeqNumtoFkSeqNumListforFKView.get(fkViewname).put(newSeqNum,fkSeqNum);
		Set<String> l = new HashSet<String>();
		l.add(fkSeqNum);
		pkSeqNumtoFkSeqNumListforFKView.get(fkViewname).put(newSeqNum,l);
		
		if(this.viewErrorCountMap.containsKey(pkViewname)) {
			Integer count = this.viewErrorCountMap.get(pkViewname);
			this.viewErrorCountMap.put(pkViewname,count+1);
			
		}
		else {
			this.viewErrorCountMap.put(pkViewname, 1);
		}
			
		
		/*
		//ADD THE BELOW PART ENCLOSED WITHIN "//" 
		
		//
		JSONObject regObj = new JSONObject();
		regObj.put("rowCount", 1);
		List<List<List<Integer>>> bs_array = new ArrayList<>();
		for(BucketStructure bs : zeroCardinalityRegion.getAll() ) {
			
			List<List<Integer>> bucketStructures = new ArrayList<>();
			for(Bucket b : bs.getAll()) {
				
				List<Integer> x = b.getAll();
				bucketStructures.add(x);
			}
			bs_array.add(bucketStructures);
		}
		regObj.put("region", bs_array);
		
		
		FileUtils.writeStringToFile("/home/dsladmin/multi-query-workspace/codd-data-gen/resources/cdgvendor/output/postgres/"+ CURRENT_CONTEXT + "/inter_ri/intersection/" + pkViewname + "_" + fkViewname + "_" + newSeqNum+".json", regObj.toString());
		
		//System.out.println("Written intersection ans " + pkViewname + "_" + fkViewname + "_" + newSeqNum+".json");
		//
		*/
	}
	
	if(Runtime.getRuntime().freeMemory() <10000000000L)
		System.gc();
			
	return interesectionPKRegionsSeqnum;
	
}

	private Set<String> unifiednewfindIntersectingRegion(ConcurrentHashMap<String,ConcurrentHashMap<String,Set<String>>> FkSeqNumtoPkSeqNumListforFKview, 
		ConcurrentHashMap<String,ConcurrentHashMap<String,Set<String>>> pkSeqNumtoFkSeqNumListforFKView, ExecutorService service, 
		Region projectedFKRegion, Map<String, VariableValuePair> pkSeqToVarValPairMap, List<Integer> commonAttrFKIdxList,
		List<Integer> commonAttrPKIdxList, String pkViewname, String fkViewname, String fkSeqNum, boolean printFlagForDebugging, int countFk, int countFkTotal){
	Set<String> interesectionPKRegionsSeqnum = new HashSet<>();
	
	ConcurrentHashMap<String,String> interesectionPKRegionsSeqnumHashSet = new ConcurrentHashMap<>();	
	// Creating a list of sequence number to be iterated on to map fkRegion
	Set<String> pkSeqNumSet = pkSeqToVarValPairMap.keySet();
	ArrayList<String> pkSeqNumList = new ArrayList<>();
	for(String s : pkSeqNumSet)
	{
		pkSeqNumList.add(s);
	}
	
	Collections.sort(pkSeqNumList);
	
	boolean intersectionExist = false;
	
	//Region projectedFKRegion = projectRegion(fkRegion,commonAttrFKIdxList);  // projectedFKRegion only contains columns that are in pkView
	
	List<Future<Boolean>> allFutures = new ArrayList<Future<Boolean>>();
	

	long pkCount = 0;
	long pkCountTotal = pkSeqNumList.size();
	
	for(String pkSeqNum : pkSeqNumList)
	{
		
		//System.out.println("Doing fk:" + fkViewname +" pk: "+ pkViewname + " : "+ countFk +" / " + countFkTotal +" pkNumber : " + pkCount++ + " / " + pkCountTotal);
		
		if(pkSeqNum.contains("allRegions"))
			continue;

		Region projectedFKRegionDeepCopy = projectedFKRegion.getDeepCopy();
		
		//projectedFKRegionDeepCopy.deleteDuplicateBucketStructure("5");

		Future<Boolean> future = service.submit(new NewRegionIntersectionHelperByMultiThreading(pkSeqNum, pkSeqToVarValPairMap, projectedFKRegionDeepCopy,
				commonAttrPKIdxList, pkViewname, fkViewname,fkSeqNum, interesectionPKRegionsSeqnumHashSet, printFlagForDebugging));
		
		allFutures.add(future);
		
	}
	
	
	
	
	for(Future<Boolean> f : allFutures) {
		
			Boolean result;
			try {
				result = f.get();
				intersectionExist = intersectionExist || result ;
			} catch (InterruptedException | ExecutionException e) {
				e.printStackTrace();
			}

	}
	
	for(String str : interesectionPKRegionsSeqnumHashSet.keySet())	
		interesectionPKRegionsSeqnum.add(str);
	
	Integer colCount=0; // Helps to find to error like if empty Region got added to SeqNum to Region map.

	if(!intersectionExist)
	while(!pkSeqNumList.isEmpty()  && colCount==0 )
	{
		
		String pkSeqNum = pkSeqNumList.get(0);
		
		pkSeqNumList.remove(0);
		if(pkSeqNum.contains("allRegions"))
			continue;
		
		if(pkSeqToVarValPairMap.containsKey(pkSeqNum)) {
		VariableValuePair pkVariableValuePair = pkSeqToVarValPairMap.get(pkSeqNum);
		Region pkRegion = pkVariableValuePair.variable;
		colCount = pkRegion.at(0).size(); // Number of columns in pkRegion // using it for error check. if error here means empty region is pushed.
		}
		
	}
	
	if(!intersectionExist)
	{
		Region zeroCardinalityRegion = getPKCompatibleRegion(projectedFKRegion,colCount,commonAttrPKIdxList,pkViewname);
		//zeroCardinalityRegion.deleteDuplicateBucketStructure();
		Integer len = pkSeqToVarValPairMap.size();
		VariableValuePair errorVarValPair = new VariableValuePair(zeroCardinalityRegion,1);
		String newSeqNum = pkViewname+ "_" +len.toString();
		pkSeqToVarValPairMap.put(newSeqNum,errorVarValPair);
		interesectionPKRegionsSeqnum.add(newSeqNum);
		//pkSeqNumtoFkSeqNumListforFKView.get(fkViewname).put(newSeqNum,fkSeqNum);
		Set<String> l = new HashSet<String>();
		l.add(fkSeqNum);
		pkSeqNumtoFkSeqNumListforFKView.get(fkViewname).put(newSeqNum,l);
		
		//PKR: commented if-else
//		if(this.viewErrorCountMap.containsKey(pkViewname)) {
//			Integer count = this.viewErrorCountMap.get(pkViewname);
//			this.viewErrorCountMap.put(pkViewname,count+1);
//			
//		}
//		else {
//			this.viewErrorCountMap.put(pkViewname, 1);
//		}
		//	
		
		/*
		//ADD THE BELOW PART ENCLOSED WITHIN "//" 
		
		//
		JSONObject regObj = new JSONObject();
		regObj.put("rowCount", 1);
		List<List<List<Integer>>> bs_array = new ArrayList<>();
		for(BucketStructure bs : zeroCardinalityRegion.getAll() ) {
			
			List<List<Integer>> bucketStructures = new ArrayList<>();
			for(Bucket b : bs.getAll()) {
				
				List<Integer> x = b.getAll();
				bucketStructures.add(x);
			}
			bs_array.add(bucketStructures);
		}
		regObj.put("region", bs_array);
		
		
		FileUtils.writeStringToFile("/home/dsladmin/multi-query-workspace/codd-data-gen/resources/cdgvendor/output/postgres/"+ CURRENT_CONTEXT + "/inter_ri/intersection/" + pkViewname + "_" + fkViewname + "_" + newSeqNum+".json", regObj.toString());
		
		//System.out.println("Written intersection ans " + pkViewname + "_" + fkViewname + "_" + newSeqNum+".json");
		//
		*/
	}
	
	if(Runtime.getRuntime().freeMemory() <10000000000L)
		System.gc();
			
	return interesectionPKRegionsSeqnum;
	
}

//OLD INTERSECTON PARALLEL CODE PRIOR TO INDEX OUT OF BOUND EXCEPTION, POST DASFAA DEADLINE EXTENSION

	public class RegionIntersectionHelperByMultiThreading implements Callable<Boolean> {

		String pkSeqNum;
		Map<String, VariableValuePair> pkSeqToVarValPairMap;
		Region projectedFKRegion;
		List<Integer> commonAttrPKIdxList;
		String pkViewname;
		String fkViewname;
		String fkSeqNum;
		boolean intersectionExist;
		boolean printFlagForDebugging;
		
		
		public RegionIntersectionHelperByMultiThreading(String pkSeqNumString, Map<String, VariableValuePair> pkSeqToVarValPairMap,
				Region projectedFKRegion, List<Integer> commonAttrPKIdxList, String pkViewname, String fkViewname,
				String fkSeqNum, boolean printFlagForDebugging) {
			super();
			this.pkSeqNum = pkSeqNumString;
			this.pkSeqToVarValPairMap = pkSeqToVarValPairMap;
			this.projectedFKRegion = projectedFKRegion;
			this.commonAttrPKIdxList = commonAttrPKIdxList;
			this.pkViewname = pkViewname;
			this.fkViewname = fkViewname;
			this.fkSeqNum = fkSeqNum;
			this.intersectionExist = false;
			this.printFlagForDebugging = printFlagForDebugging;
		}



		@Override
		public Boolean call() throws Exception {
			//System.out.println(Thread.currentThread().getName() + " pkSeqNumString: " + pkSeqNum);
			
			VariableValuePair pkVariableValuePair = pkSeqToVarValPairMap.get(pkSeqNum);
			Region pkRegion = pkVariableValuePair.variable;
			long regionCardinality = pkVariableValuePair.rowcount;
			//colCount = pkRegion.at(0).size(); // Number of columns in pkRegion // using it for error check. if error here means empty region is pushed.
			
			// make both region compatible			
			Region projectedPKRegion = projectRegion(pkRegion,commonAttrPKIdxList);  // projectedPKRegion contains all column of pkView
			//projectedPKRegion.deleteDuplicateBucketStructure("1");
			
			//System.gc();
			
			if(printFlagForDebugging)
				System.out.println("projectedPKRegion for this run ; " + projectedPKRegion);
			
			
			// Intersection of regions
			Region intersectingProjectedRegion = projectedFKRegion.intersection(projectedPKRegion);
			
			//intersectingProjectedRegion.deleteDuplicateBucketStructure("2");
			

			if(printFlagForDebugging)
				System.out.println("Intersection ans for this run ; " + intersectingProjectedRegion);
			
			
			//System.gc();
			
			// If Regions didn't intersect, check for next region until all regions are not checked
			if(intersectingProjectedRegion.isEmpty())
				return false;
			else
			{
				intersectionExist = true;
				//intersectingProjectedRegion.deleteDuplicateBucketStructure();
				
				if(printFlagForDebugging)
					System.out.println("Intersection ans for this run ; " + intersectingProjectedRegion);
				
				
				Region intersectingPKRegion = getExpandedRegion(intersectingProjectedRegion,pkRegion, commonAttrPKIdxList);				
				
				//if(printFlagForDebugging)
				//	System.err.println("intersectingPKRegion for this run with duplicate ; " + intersectingPKRegion);
				
				//intersectingPKRegion.deleteDuplicateBucketStructure("3");
				//intersectingPKRegion.deleteDuplicateBucketStructure();
				

				if(printFlagForDebugging)
					System.out.println("intersectingPKRegion for this run without duplicate; " + intersectingPKRegion);
				
				Region nonIntersectingPKRegion = pkRegion.minus(intersectingPKRegion);
				
				//if(printFlagForDebugging)
				//	System.err.println("nonIntersectingPKRegion ans for this run with duplicate; " + nonIntersectingPKRegion);
				
				
				
				//nonIntersectingPKRegion.deleteDuplicateBucketStructure("4");
				
				if(printFlagForDebugging)
					System.out.println("nonIntersectingPKRegion ans for this run without duplicate; " + nonIntersectingPKRegion);
				
				
				//System.gc();
				
				// Assign both(intersecting and non-intersecting) region cardinalities
				// floor value will be assigned to non-intersecting region
				// ceil value will be assigned to intersecting region
				// reason : to maintain cardinality=1 for intersecting region (in the case, where region cardinality=1 for pkRegion)
				long nonIntersectingRegionRowCount = findRegionCardinalityUniformly(pkRegion,nonIntersectingPKRegion,regionCardinality);
				long IntersectingRegionRowCount = regionCardinality - nonIntersectingRegionRowCount;
							
				VariableValuePair intersectingVarValPair =  new VariableValuePair(intersectingPKRegion,IntersectingRegionRowCount);
					
						
				// Adding intersecting region in pkSeqToVarValPairMap with new Sequence number.
				String pkSeqNumForIntersectingRegion = pkSeqNum + "_0";
				//if(pkSeqNumForIntersectingRegion.contentEquals("t11_37_0_0_0"))
				//	System.out.print("");
				pkSeqToVarValPairMap.put(pkSeqNumForIntersectingRegion, intersectingVarValPair);
				List<String> newSeqNumList = new ArrayList<String>();
				newSeqNumList.add(pkSeqNumForIntersectingRegion);
				
				// Non-Intersecting region only adds when it's not empty and it's region cardinality is more than 0.
				if((!nonIntersectingPKRegion.isEmpty()) && nonIntersectingRegionRowCount>0)
				{
					String pkSeqNumForNonIntersectingRegion = pkSeqNum + "_1";
					VariableValuePair nonIntersectingVarValPair = new  VariableValuePair(nonIntersectingPKRegion,nonIntersectingRegionRowCount);
					pkSeqToVarValPairMap.put(pkSeqNumForNonIntersectingRegion, nonIntersectingVarValPair);
					newSeqNumList.add(pkSeqNumForNonIntersectingRegion);
					
				}
				
				//System.gc();
					
				// Replace old sequence number with new sequence numbers whenever a region breaks one more time
				maintainpkfkSeqNumMapping(pkViewname,pkSeqNum,newSeqNumList);
				
				
				
				// Remove sequence number for 
				pkSeqToVarValPairMap.remove(pkSeqNum,pkVariableValuePair);			
				if(pkSeqNumtoFkSeqNumListforFKView.get(fkViewname).containsKey(pkSeqNumForIntersectingRegion))
				{
					
					pkSeqNumtoFkSeqNumListforFKView.get(fkViewname).get(pkSeqNumForIntersectingRegion).add(fkSeqNum);
				}
				else
				{
					Set<String> l = new HashSet<String>();
					l.add(fkSeqNum);
					pkSeqNumtoFkSeqNumListforFKView.get(fkViewname).put(pkSeqNumForIntersectingRegion,l);
				}
				 
				//System.gc();
							
			}

			//System.gc();
			
			
			return intersectionExist;
		
		}



	
		
		
	}
	
	private long findRegionCardinalityUniformly(Region pkRegion, Region nonIntersectingPKRegion,
			long regionCardinality) {
		// TODO Auto-generated method stub
			
			long projectedPKRegionSpace = regionSpace(pkRegion);
			long nonIntersectingPKRegionSpace = regionSpace(nonIntersectingPKRegion);
			
			if(projectedPKRegionSpace < 0)
				System.err.println("projectedPKRegionSpace " + projectedPKRegionSpace + " rcard " + regionCardinality);
			if(nonIntersectingPKRegionSpace < 0)
				System.err.println("nonIntersectingPKRegionSpace " + nonIntersectingPKRegionSpace + " rcard " + regionCardinality);
		
			if(projectedPKRegionSpace < nonIntersectingPKRegionSpace)
				return (long) (regionCardinality/2);
			
			return (nonIntersectingPKRegionSpace*regionCardinality/projectedPKRegionSpace);
		
	}
	
	
	//OLD INTERSECTON PARALLEL CODE PRIOR TO INDEX OUT OF BOUND EXCEPTION, POST DASFAA DEADLINE EXTENSION

	private void findIntersectingRegion(ExecutorService service, Region fkRegion, Map<String, VariableValuePair> pkSeqToVarValPairMap,
			List<Integer> commonAttrFKIdxList, List<Integer> commonAttrPKIdxList, String pkViewname, String fkViewname, String fkSeqNum, boolean printFlagForDebugging) {
		
		// Creating a list of sequence number to be iterated on to map fkRegion
		Set<String> pkSeqNumSet = pkSeqToVarValPairMap.keySet();
		ArrayList<String> pkSeqNumList = new ArrayList<>();
		for(String s : pkSeqNumSet)
		{
			pkSeqNumList.add(s);
		}
		
		Collections.sort(pkSeqNumList);
		
		//if(fkViewname.contains("t18") && pkViewname.contains("t07"))
		//	System.out.print("");
		//if(pkViewname.contains("t13"))
		//	System.out.print("");
		//System.out.println(pkViewname);
		boolean intersectionExist = false;
		
		Region projectedFKRegion = projectRegion(fkRegion,commonAttrFKIdxList);  // projectedFKRegion only contains columns that are in pkView
		//projectedFKRegion.deleteDuplicateBucketStructure("5"); // after projection regions can duplicate BS. that's why duplicate BS

		if(Runtime.getRuntime().freeMemory() <10000000000L)
			System.gc();

		//System.out.println("pkSeqNumList ; " + pkSeqNumList);
		
		if(printFlagForDebugging)
		System.out.println("projectedFKRegion for this run ; " + projectedFKRegion);
		
		List<Future<Boolean>> allFutures = new ArrayList<Future<Boolean>>();
		
		//while(!pkSeqNumList.isEmpty())
		for(String pkSeqNum : pkSeqNumList)
		{
			if(pkSeqNum.contains("allRegions"))
    			continue;
			
			//long heapSize = Runtime.getRuntime().totalMemory()/(1024); 

            // Get maximum size of heap in bytes. The heap cannot grow beyond this size.// Any attempt will result in an OutOfMemoryException.
            //long heapMaxSize = Runtime.getRuntime().maxMemory();

             // Get amount of free memory within the heap in bytes. This size will increase // after garbage collection and decrease as new objects are created.
            //long heapFreeSize = Runtime.getRuntime().freeMemory()/(1024); 
            
            //System.out.println("Used, free : " + (heapSize-heapFreeSize) + " "  + " " + heapFreeSize);
		 	
			
			//String pkSeqNum = pkSeqNumList.get(0);
			Region projectedFKRegionDeepCopy = projectedFKRegion.getDeepCopy();
			//System.out.println(pkViewname + " : " + pkSeqNum);

			Future<Boolean> future = service.submit(new RegionIntersectionHelperByMultiThreading(pkSeqNum, pkSeqToVarValPairMap, projectedFKRegionDeepCopy,
					commonAttrPKIdxList, pkViewname, fkViewname,fkSeqNum, printFlagForDebugging));
			
			allFutures.add(future);
			

		}
		
		int count = 0;
		
		//System.gc();
		
		//while(count < pkSeqNumList.size())
		for(Future<Boolean> f : allFutures) {
			
			//Boolean result = null;
				//while(!f.isDone());
				
				Boolean result;
				try {
					result = f.get();
					//System.out.println("RESULT : "+result + "  " +count++ + " " + pkSeqNumList.size());
					intersectionExist = intersectionExist || result ;
				} catch (InterruptedException | ExecutionException e) {
					// TODO Auto-generated catch block
					e.printStackTrace();
				}
				//count++;
		}
			if(printFlagForDebugging)
			System.out.println("intersectionExist" + intersectionExist);
		
		
		//System.gc();
		
		Integer colCount=0; // Helps to find to error like if empty Region got added to SeqNum to Region map.

		if(printFlagForDebugging)
			System.out.println("pkSeqToVarValPairMap " + pkSeqToVarValPairMap  + pkSeqNumList) ;
		
		if(!intersectionExist)
		while(!pkSeqNumList.isEmpty()  && colCount==0 )
		{
			
			String pkSeqNum = pkSeqNumList.get(0);
			//if(pkSeqNum.contains("t13_0"))
			//	System.out.print("");
			//System.out.println(pkViewname + " : " + pkSeqNum);
			pkSeqNumList.remove(0);
			if(pkSeqNum.contains("allRegions"))
    			continue;
			
			if(pkSeqToVarValPairMap.containsKey(pkSeqNum)) {
			VariableValuePair pkVariableValuePair = pkSeqToVarValPairMap.get(pkSeqNum);
			Region pkRegion = pkVariableValuePair.variable;
			colCount = pkRegion.at(0).size(); // Number of columns in pkRegion // using it for error check. if error here means empty region is pushed.
			}
			
		}
		
		//System.gc();
		if(printFlagForDebugging)
			System.out.println("colcount ; " + colCount);
		
		
		// if no intersection occurs create a region and assign cardinality=1
		// doubt here what should be the region
		// Region zeroCardinalityRegion = findZeroCardinalityCompatibleRegion(pkSeqToVarValPairMap,colCount,fkRegion,commonAttrFKIdxList,commonAttrPKIdxList);
		if(!intersectionExist)
		{
			Region zeroCardinalityRegion = getPKCompatibleRegion(projectedFKRegion,colCount,commonAttrPKIdxList,pkViewname);
			
			//zeroCardinalityRegion.deleteDuplicateBucketStructure("6");
			
			Integer len = pkSeqToVarValPairMap.size();
			VariableValuePair errorVarValPair = new VariableValuePair(zeroCardinalityRegion,1);
			String newSeqNum = pkViewname+ "_" +len.toString();
			pkSeqToVarValPairMap.put(newSeqNum,errorVarValPair);
			//pkSeqNumtoFkSeqNumListforFKView.get(fkViewname).put(newSeqNum,fkSeqNum);
			Set<String> l = new HashSet<String>();
			l.add(fkSeqNum);
			pkSeqNumtoFkSeqNumListforFKView.get(fkViewname).put(newSeqNum,l);
			
			
			if(this.viewErrorCountMap.containsKey(pkViewname)) {
				Integer count2 = this.viewErrorCountMap.get(pkViewname);
				this.viewErrorCountMap.put(pkViewname,count2+1);
				
			}
			else {
				this.viewErrorCountMap.put(pkViewname, 1);
			}
			
			if(printFlagForDebugging)
				System.err.println("Putting in ; " + newSeqNum + " " + errorVarValPair);
		
			if(printFlagForDebugging)
				System.err.println("fkViewname , l ,pkSeqNumtoFkSeqNumListforFKView ; " + fkViewname + " " + l + " " +pkSeqNumtoFkSeqNumListforFKView);
		}
	
		if(printFlagForDebugging)
		System.out.println("coming out " );
		
		if(Runtime.getRuntime().freeMemory() <10000000000L)
			System.gc();
		
		
		
	}
	
	
	private Region getExpandedRegion(Region intersectingProjectedRegion, Region pkRegion, List<Integer> commonAttrPKIdxList) {
		Set<String> x = new HashSet<>();
		Region expandedRegion = new Region();
		for(BucketStructure bs1 : intersectingProjectedRegion.getAll())
		{
			for(BucketStructure bs2 : pkRegion.getAll())
			{
				BucketStructure tempBs = bs2.projectBS(commonAttrPKIdxList);
				if(!bs1.intersection(tempBs).isEmpty()) {
					BucketStructure expandedBS = new BucketStructure();
					int k=0;
					for(int i=0;i<bs2.size();i++)
					{
						if(commonAttrPKIdxList.contains(i))
						{
							expandedBS.add(bs1.at(k++));
						}
						else
						{
			            	expandedBS.add(bs2.at(i));
						}
							
					}
					if(!x.contains(expandedBS.toString()))
					{
						x.add(expandedBS.toString());
						expandedRegion.add(expandedBS);
					}
					
					
				}
			}
			
		}

		return expandedRegion;
	}

	//CODE BEFORE TARUN SENT VIA WHATSAPP
	/*
	private Region getExpandedRegion(Region intersectingProjectedRegion, Region pkRegion, List<Integer> commonAttrPKIdxList) {
		Region expandedRegion = new Region();
		for(BucketStructure bs1 : intersectingProjectedRegion.getAll())
		{
			for(BucketStructure bs2 : pkRegion.getAll())
			{
				BucketStructure tempBs = bs2.projectBS(commonAttrPKIdxList);
				if(!bs1.intersection(tempBs).isEmpty()) {
					BucketStructure expandedBS = new BucketStructure();
					int k=0;
					for(int i=0;i<bs2.size();i++)
					{
						if(commonAttrPKIdxList.contains(i))
						{
							expandedBS.add(bs1.at(k++));
						}
						else
						{
			            	expandedBS.add(bs2.at(i));
						}
							
					}
					expandedRegion.add(expandedBS);
					
				}
			}
			
		}
		
		//System.gc();

		return expandedRegion;
	}
	*/
		
	
	private Region getPKCompatibleRegion(Region projectedFKRegion, Integer colCount, List<Integer> commonAttrPKIdxList, String pkViewname) {
		
		Set<String> x = new HashSet<>();
		Map<String, ViewInfo> viewInfos = PostgresVConfig.ANONYMIZED_VIEWINFOs;
		ViewInfo viewInfo = viewInfos.get(pkViewname);
		List<String> viewNonkeys = new ArrayList<>(viewInfo.getViewNonkeys());
		Map<String, String> columnDataTypeMap = PostgresVConfig.columnDataTypeMap;
		Collections.sort(viewNonkeys);
		Region expandedRegion =  new Region();
		for(BucketStructure bs : projectedFKRegion.getAll())
		{
			
			
			BucketStructure expandedBS = new BucketStructure();
			int k=0;
			for(int i=0;i<colCount;i++)
			{
				if(commonAttrPKIdxList.contains(i))
				{
					expandedBS.add(bs.at(k++));
				}
				else
				{

					Bucket b=new Bucket();
					if(columnDataTypeMap.get(viewNonkeys.get(i)).contentEquals("integer"))
					{
						b.add(Integer.MIN_VALUE);
					}
					else
					{
						b.add(0);
					}
	            	expandedBS.add(b);
				}
					
			}
			
			
			if(!x.contains(expandedBS.toString()))
			{
				x.add(expandedBS.toString());
				expandedRegion.add(expandedBS);
			}
			//expandedRegion.add(expandedBS);
		}
		
		return expandedRegion;
	}
	
	
	//CODE FROM TARUN BEFORE NEWEST CODE SENT BY WHATSAPP
	/*
	private Region getPKCompatibleRegion(Region projectedFKRegion, Integer colCount, List<Integer> commonAttrPKIdxList, String pkViewname) {
        
        Map<String, ViewInfo> viewInfos = PostgresVConfig.ANONYMIZED_VIEWINFOs;
        ViewInfo viewInfo = viewInfos.get(pkViewname);
        List<String> viewNonkeys = new ArrayList<>(viewInfo.getViewNonkeys());
        Map<String, String> columnDataTypeMap = PostgresVConfig.columnDataTypeMap;
        Collections.sort(viewNonkeys);
        Region expandedRegion =  new Region();
        for(BucketStructure bs : projectedFKRegion.getAll())
        {
            BucketStructure expandedBS = new BucketStructure();
            int k=0;
            for(int i=0;i<colCount;i++)
            {
                if(commonAttrPKIdxList.contains(i))
                {
                    expandedBS.add(bs.at(k++));
                }
                else
                {



                    Bucket b=new Bucket();
                    if(columnDataTypeMap.get(viewNonkeys.get(i)).contentEquals("integer"))
                    {
                        b.add(Integer.MIN_VALUE);
                    }
                    else
                    {
                        b.add(0);
                    }
                    expandedBS.add(b);
                }
                    
            }
            expandedRegion.add(expandedBS);
        }
        
        return expandedRegion;
    }
	
	*/
	
	//BEFORE CHANGING INT ANONY WAY
	private Region getPKCompatibleRegion(Region projectedFKRegion, Integer colCount, List<Integer> commonAttrPKIdxList) {
			
			Region expandedRegion =  new Region();
			for(BucketStructure bs : projectedFKRegion.getAll())
			{
				BucketStructure expandedBS = new BucketStructure();
				int k=0;
				for(int i=0;i<colCount;i++)
				{
					if(commonAttrPKIdxList.contains(i))
					{
						expandedBS.add(bs.at(k++));
					}
					else
					{
						Bucket b=new Bucket();
		            	b.add(0);
		            	expandedBS.add(b);
					}
						
				}
				expandedRegion.add(expandedBS);
			}
			
			//System.gc();
			
			return expandedRegion;
		}
		

/*

	private long findRegionCardinalityUniformlyByComputingVolume(String pkViewname, Region pkRegion,
			Region nonIntersectingPKRegion, long regionCardinality) {
		// TODO Auto-generated method stub
		SchemaInfo schemaInfo = PostgresVConfig.ANONYMIZED_SCHEMAINFO;
        
        	TableInfo tableVal = schemaInfo.getTableInfo(pkViewname);
        	
        	List<String> sortedBucketsToColumnNameMapping = new ArrayList<String>();
    		Set<String> usableTableNonKeys = new HashSet<String>();
    		
    		
    		//System.out.println("PostgresVConfig.allBucketFloors.get(pkViewname) + && " + PostgresVConfig.allBucketFloors.get(pkViewname));      	
        	
    				for(Entry<String,ColumnInfo> c : tableVal.getColumns().entrySet()) {
        		String colName = c.getKey();
        		ColumnInfo colInfo = c.getValue();
        		
        		sortedBucketsToColumnNameMapping.add(colName);        			
    			
        		if((colInfo.getColumnType().equals("integer") || colInfo.getColumnType().equals("numeric")) ){
        			
        			usableTableNonKeys.add(colName);
        		}
        	}
        	
        	//System.out.println("sortedBuck " + pkViewname + " " +sortedBucketsToColumnNameMapping);
        	
        	
        	VariableValuePair newVVP1 = new VariableValuePair(pkRegion, -1);
			newVVP1.setRegionValuesToComputeVolume(newVVP1.getVariable().calculateVolumeForRegion(pkViewname, sortedBucketsToColumnNameMapping, usableTableNonKeys, PostgresVConfig.reverseNumberMap, PostgresVConfig.reverseStringMap, PostgresVConfig.reverseDateMap, null, PostgresVConfig.allBucketFloors, PostgresVConfig.anonymizedschema));
			newVVP1.getRegionValuesToComputeVolume().accumulate();
			
			long projectedPKRegionSpace = 1;
			List<Double> d1 = newVVP1.getRegionValuesToComputeVolume().bucketStructuresIndividualVolume;
	
			for(Double d : d1) {
				projectedPKRegionSpace = (long) (projectedPKRegionSpace * d); 
			}
			
			VariableValuePair newVVP2 = new VariableValuePair(nonIntersectingPKRegion, -1);
			newVVP2.setRegionValuesToComputeVolume(newVVP2.getVariable().calculateVolumeForRegion(pkViewname, sortedBucketsToColumnNameMapping, usableTableNonKeys, PostgresVConfig.reverseNumberMap, PostgresVConfig.reverseStringMap, PostgresVConfig.reverseDateMap, null, PostgresVConfig.allBucketFloors, PostgresVConfig.anonymizedschema));
			newVVP2.getRegionValuesToComputeVolume().accumulate();
			
			long nonIntersectingPKRegionSpace = 1;
			List<Double> d2 = newVVP2.getRegionValuesToComputeVolume().bucketStructuresIndividualVolume;
	

			for(Double d : d2) {
				nonIntersectingPKRegionSpace = (long) (nonIntersectingPKRegionSpace * d); 
			}
			
			if(d2.size() > d1.size()) {
				projectedPKRegionSpace = (long) (projectedPKRegionSpace * ((float)d2.size()/(float)d1.size()));
			}
			
			if(projectedPKRegionSpace < nonIntersectingPKRegionSpace) {
				System.out.println("OMG " + projectedPKRegionSpace + " " + nonIntersectingPKRegionSpace);
				System.out.println("d1 " + d1);
				System.out.println("d2 " + d2);
				System.out.println("\npkRegion " + pkRegion);
				System.out.println("\nnonIntersectingPKRegion " + nonIntersectingPKRegion);
				System.out.println("\n\n\n" );
				
				
			}
			
			return (nonIntersectingPKRegionSpace*regionCardinality/projectedPKRegionSpace);
        			
        }
	
	

	private long findRegionCardinalityUniformly(Region projectedPKRegion, Region nonIntersectingPKRegion,
			long regionCardinality) {
		
		long projectedPKRegionSpace = regionSpace(projectedPKRegion);
		long nonIntersectingPKRegionSpace = regionSpace(nonIntersectingPKRegion);
		
		if(projectedPKRegionSpace < 0)
			System.err.println("projectedPKRegionSpace " + projectedPKRegionSpace + " rcard " + regionCardinality);
		if(nonIntersectingPKRegionSpace < 0)
			System.err.println("nonIntersectingPKRegionSpace " + nonIntersectingPKRegionSpace + " rcard " + regionCardinality);
	
		if(projectedPKRegionSpace < nonIntersectingPKRegionSpace)
			return (long) (regionCardinality/2);
		
		return (nonIntersectingPKRegionSpace*regionCardinality/projectedPKRegionSpace);
	}
	*/
	
	/* Returns volumetric space size */
	private long regionSpace(Region r)
	{
		long rSpace = 0;
		for(BucketStructure bs : r.getAll())
		{
			long temp = 1;
			//int temp = 1;
			for(Bucket b : bs.getAll())
			{
				temp*=b.size();
			}
			rSpace += temp;
		}
		
		//System.gc();
		return rSpace;
	}

	private void maintainpkfkSeqNumMapping(String pkViewname, String oldSeqNum, List<String> newSeqNumList) {
		
		// create a map or something which find out fkView for corresponding pkView
		List<String> fkViews = pkViewToFkViewMap.get(pkViewname);
		for(String fkView : fkViews)
		{
			if(pkSeqNumtoFkSeqNumListforFKView.containsKey(fkView))
			{
				if(pkSeqNumtoFkSeqNumListforFKView.get(fkView).containsKey(oldSeqNum))
				{
					Set<String> fkSeqNumList = pkSeqNumtoFkSeqNumListforFKView.get(fkView).get(oldSeqNum);
					pkSeqNumtoFkSeqNumListforFKView.get(fkView).put(newSeqNumList.get(0),fkSeqNumList);
					if(newSeqNumList.size()==2)
						pkSeqNumtoFkSeqNumListforFKView.get(fkView).put(newSeqNumList.get(1),fkSeqNumList);
					pkSeqNumtoFkSeqNumListforFKView.get(fkView).remove(oldSeqNum);
					
				}
			}
		}
		
		//System.gc();
	}

	private Region projectRegion(Region fkRegion, List<Integer> commonAttrFKIdxList) {
		Region projectedFkRegion =  new Region();
		Set<String> x = new HashSet<>();
		for(BucketStructure bs : fkRegion.getAll() )
		{
			BucketStructure tempBS = new BucketStructure();
			
			for(int b=0; b<bs.size(); b++)
			{
				
				if(commonAttrFKIdxList.contains(b))
				{
					tempBS.add(bs.at(b));
				}
				
			}
			if(!x.contains(tempBS.toString()))
			{
				x.add(tempBS.toString());
				projectedFkRegion.add(tempBS);
			}
			
			
		}
		return projectedFkRegion;
	}
	
	
	//CODE BEFORE TARUN SENT NW ONE VIA WHATSAPP
	/*
	private Region projectRegion(Region fkRegion, List<Integer> commonAttrFKIdxList) {
		Region projectedFkRegion =  new Region();
		for(BucketStructure bs : fkRegion.getAll() )
		{
			BucketStructure tempBS = new BucketStructure();
			for(int b=0; b<bs.size(); b++)
			{
				
				if(commonAttrFKIdxList.contains(b))
				{
					tempBS.add(bs.at(b));
				}
				
			}
			projectedFkRegion.add(tempBS);
		}
		
		//System.gc();
		
		return projectedFkRegion;
	}
	*/



	/**
     * Traverses summaryByView in topological order and replaces the fkeyColumnValueCombinations in the ValueCombinations.
     * A given foreign value combination is replaced by corresponding foreign key column
     * whose value is equal to the cumulative sum of rowCounts in the fkeyView until that value combination
     *
     * For each viewname we now have the compressed list as List<ValueCombination>
     * First few entries will be the fkey columnValues corresponding to the fKeyViews in the order returned by the viewInfo.getFkeyViews which is the sortedOrder of fkeyViewnames
     * After that there will be entries corresponding to viewInfo.getTableNonkeys in sortedOrder
     */
    public void compressSummaryByAddingFkeys() {

        Map<String, ViewInfo> viewInfos = PostgresVConfig.ANONYMIZED_VIEWINFOs;
        List<String> topoViewnames = PostgresVConfig.VIEWNAMES_TOPO;
        
        //Checking Views in topological order and compressing their tuples width wise
        for (int i = 0; i < topoViewnames.size(); i++) {
            String fkViewname = topoViewnames.get(i);
            ViewInfo fkViewInfo = viewInfos.get(fkViewname);
            List<String> sortedFKViewNonkeyColumns = new ArrayList<>(fkViewInfo.getViewNonkeys());
            Collections.sort(sortedFKViewNonkeyColumns);
            List<String> sortedFKTableNonkeyColumns = new ArrayList<>(fkViewInfo.getTableNonkeys());
            Collections.sort(sortedFKTableNonkeyColumns);
            ViewSolution fkViewSolution = viewSolutions.get(fkViewname);

            DebugHelper.printDebug("Compressing ViewSolution for view " + fkViewname);
            ViewSolution fkCompressedViewSolution = getEmptyViewSolutionBasedOnSpillType(fkViewname, fkViewSolution.getCountOfValueCombinations(),
                    getCompressedValueCombinationSizeInBytes(fkViewname));

            for (ValueCombination fkValueCombination : fkViewSolution) {

                Object2IntMap<String> pkViewnameToFKValue = new Object2IntOpenHashMap<>();
                //for each childView
                for (String pkViewname : fkViewInfo.getFkeyViews()) {
                    ViewInfo pkViewInfo = viewInfos.get(pkViewname);
                    List<String> sortedCommonColumns = new ArrayList<>(pkViewInfo.getViewNonkeys()); //All columns of pkViewInfo should infact be the common columns in it and viewInfo
                    Collections.sort(sortedCommonColumns);

                    //DebugHelper.printDebug("\tCompressing using ViewSolution for pkview " + pkViewname);

                    //finding referenced commonValues
                    IntList commonValues = new IntArrayList();
                    for (int j = 0; j < sortedFKViewNonkeyColumns.size(); j++) {
                        if (sortedCommonColumns.contains(sortedFKViewNonkeyColumns.get(j))) {
                            commonValues.add(fkValueCombination.getColValues().get(j));
                        }
                    }

                    if (commonValues.isEmpty())
                        throw new RuntimeException("Should not be reaching here");

                    ViewSolution pkValueCombinations = viewSolutions.get(pkViewname);
                    //NOTE: Allowing pkValue to go negative in databaseSummary as it would impact only in cosmetically large (scaled) table sizes
                    //Fixing this requires creating a separate data structure ValueCombination2 for summary which has long keys and int colValues
                    int pkValue = (int) pkValueCombinations.getPK(commonValues);
                    pkViewnameToFKValue.put(pkViewname, pkValue);
                }

                //For originalColumns we pick the unchanged valueCombination
                //while we insert fkeyValue for each pkView referenced
                IntList compressedValuesInCombination = new IntArrayList(fkViewInfo.getFkeyViews().size());
                for (String pkViewname : fkViewInfo.getFkeyViews()) {
                    compressedValuesInCombination.add(pkViewnameToFKValue.get(pkViewname));
                }
                for (int j = 0; j < sortedFKViewNonkeyColumns.size(); j++) {
                    String viewNonkeyColumnname = sortedFKViewNonkeyColumns.get(j);
                    if (sortedFKTableNonkeyColumns.contains(viewNonkeyColumnname)) {
                        compressedValuesInCombination.add(fkValueCombination.getColValues().get(j));
                    }
                }

                ValueCombination compressedValueCombination = new ValueCombination(compressedValuesInCombination, fkValueCombination.getRowcount());
                fkCompressedViewSolution.addValueCombination(compressedValueCombination);

            }
            fkViewSolution.close();
            viewSolutions.put(fkViewname, fkCompressedViewSolution);
        }
        
        isCompressed = true;
    }

    //    private List<ValueCombination> getEmptyViewSolutionBasedOnSpillType(String viewname, int expectedCapacity, int entrySizeInBytes) {
    //        switch (spillType) {
    //            case INMEMORY:
    //                return new ArrayList<>(expectedCapacity);
    //            case MAPDBBACKED:
    //                return MapDBUtils.createIndexTreeList(viewname, new ValueCombinationSerializer());
    //            case FILEBACKED:
    //                return new BigArrayList<>(viewname, new ValueCombinationReaderWriter(entrySizeInBytes), expectedCapacity);
    //            default:
    //                throw new RuntimeException("Unsupported SpillType " + spillType.name());
    //        }
    //    }

    private ViewSolution getEmptyViewSolutionBasedOnSpillType(String viewname, int expectedCapacity, int entrySizeInBytes) {
        switch (spillType) {
            case INMEMORY:
                return new ViewSolutionInMemory(expectedCapacity);
            case FILEBACKED_FKeyedBased:
                if (PostgresVConfig.ANONYMIZED_VIEWINFOs.get(viewname).getIsNeverFKeyed())
                    return new ViewSolutionDiskBased(viewname + "_comp", entrySizeInBytes);
                // TODO: Is next line correct?
                return new ViewSolutionInMemory(expectedCapacity);
            default:
                throw new RuntimeException("Unsupported SpillType " + spillType.name());
        }
    }

    private int getCompressedValueCombinationSizeInBytes(String viewname) {
        ViewInfo viewInfo = PostgresVConfig.ANONYMIZED_VIEWINFOs.get(viewname);
        IntList colValues = new IntArrayList(viewInfo.getTableNonkeys().size() + viewInfo.getFkeyViews().size());
        for (int i = viewInfo.getTableNonkeys().size() + viewInfo.getFkeyViews().size() - 1; i >= 0; i--) {
            colValues.add(0);
        }
        ValueCombination compressedValueCombination = new ValueCombination(colValues, -1);
        return compressedValueCombination.getSizeInBytes();
    }

    public Map<String, ViewSolution> getSummaryByView() {
        if (!isConsistent)
            throw new RuntimeException("Trying to get summaryByView which is not yet made consistent");
        if (!isCompressed)
            throw new RuntimeException("Trying to get summaryByView which is not yet compressed");
        return viewSolutions;
    }

    public Map<String, ViewSolution> getUncompressedSummaryByView() {
        //if (!isConsistent) //TEMPORARILY COMMENTED - TARUN ASKED TO DO SO
        //    throw new RuntimeException("Trying to get summaryByView which is not yet made consistent");
        //if (!isCompressed) //TEMPORARILY COMMENTED - TARUN ASKED TO DO SO
        //    throw new RuntimeException("Trying to get uncompressed summaryByView when it is already compressed");
        return viewSolutions;
    }

    public Map<String, ViewSolution> getDuplicateUncompressedSummaryByView() {
        Map<String, ViewSolution> uncompressedSummary = getUncompressedSummaryByView();
        return deepClone(uncompressedSummary);
    }

    private static Map<String, ViewSolution> deepClone(Map<String, ViewSolution> summary) {
        Map<String, ViewSolution> cloneSummary = new HashMap<>(summary.keySet().size());
        for (Entry<String, ViewSolution> entry : summary.entrySet()) {
            String viewname = entry.getKey();
            ViewSolution viewSolution = entry.getValue();
            cloneSummary.put(viewname, viewSolution.clone());
        }
        return cloneSummary;
    }

    public void dumpDatabaseSummary() {
        Map<String, ViewSolution> summaryByView = getSummaryByView();
        Map<String, ViewInfo> viewInfos = PostgresVConfig.ANONYMIZED_VIEWINFOs;

        StringBuilder sbindex = new StringBuilder();
        for (Entry<String, ViewSolution> entry : summaryByView.entrySet()) {
            String viewname = entry.getKey();
            ViewSolution viewSolution = entry.getValue();

            DebugHelper.printDebug("Writing database summary for view " + viewname);

            sbindex.append(viewname).append(NEWLINE);
            //Finding relation rowCount which might be different than viewInfos.get(viewname).getRowcount() because of view consistency tuples
            long rowcount = 0;
            for (ValueCombination valueCombination : viewSolution) {
                rowcount += valueCombination.getRowcount();
            }
            String firstRow = viewSolution.getCountOfValueCombinations() + COMMA + (viewInfos.get(viewname).getNonPkeyColCount() + 1) + COMMA + rowcount; //+1 as each row also has tuple count

            FileWriter fw = null;
            try {
                fw = new FileWriter(new File(PostgresVConfig.getProp(Key.DATABASESUMMARY_LOCATION), viewname));
                fw.write(firstRow + NEWLINE);
                for (ValueCombination valueCombination : viewSolution) {
                    fw.write(valueCombination.toStringFileDump() + NEWLINE);
                }
            } catch (IOException ex) {
                throw new RuntimeException("Unable to write database summary for view " + viewname, ex);
            } finally {
                try {
                    fw.close();
                } catch (Exception ex2) {}
            }
        }
        try {
            FileUtils.writeStringToFile(PostgresVConfig.getProp(Key.DATABASESUMMARY_LOCATION), PostgresVConfig.DATABASESUMMARY_INDEX, sbindex.toString());
        } catch (Exception ex) {
            throw new RuntimeException("Unable to write database summary index", ex);
        }
    }

	public void decodeAndDumpDatabaseSummary(HashMap<String, Int2DoubleOpenHashMap> reverseNumberMap, HashMap<String, Int2ObjectOpenHashMap<String>> reverseStringMap, HashMap<String, Int2ObjectOpenHashMap<Date>> reverseDateMap, HashMap<String, String> reverseTablesMap) {
		Map<String, ViewSolution> summaryByView = getSummaryByView();
        SchemaInfo schemaInfo = PostgresVConfig.ANONYMIZED_SCHEMAINFO;
        
        final String DEFAULT_STRING = " ";
        
        Calendar calender = Calendar.getInstance();
        calender.set(-1990, 1, 1);
        final Date DEFAULT_DATE = calender.getTime();

        StringBuilder sbindex = new StringBuilder();
        for (Entry<String, ViewSolution> entry : summaryByView.entrySet()) {		// For each table
            String viewname = entry.getKey();
            ViewSolution viewSolution = entry.getValue();
            TableInfo tableInfo = schemaInfo.getTableInfo(viewname);

            String origViewName = reverseTablesMap.get(viewname);
            DebugHelper.printDebug("Writing database summary for view " + origViewName);

            sbindex.append(viewname).append(NEWLINE);
            //Finding relation rowCount which might be different than viewInfos.get(viewname).getRowcount() because of view consistency tuples
            long rowcount = 0;
            for (ValueCombination valueCombination : viewSolution) {
                rowcount += valueCombination.getRowcount();
            }

            List<Integer> columnPositionMapping = tableInfo.getColumnPositionMapping();
//            int noOfGeneratedCols = viewInfos.get(viewname).getNonPkeyColCount() + 1;	 //+1 as each row also has tuple count
            int positionOfPk = columnPositionMapping.get(0);		// columnPositionMapping.get(0) is position of PK
            String firstRow = viewSolution.getCountOfValueCombinations() + COMMA + columnPositionMapping.size() + COMMA + rowcount + COMMA + positionOfPk + COMMA + "0"; // 0 is unconstrained velocity

            FileWriter fw = null;
            try {
                try {
					fw = new FileWriter(new File(PostgresVConfig.getProp(Key.DATABASESUMMARY_LOCATION), origViewName.toUpperCase()));
	                fw.write(firstRow + NEWLINE);
				} catch (IOException e) {
					e.printStackTrace();
				}
                
                int noOfPKs = 0;	// TODO
                int noOfKeys = noOfPKs + tableInfo.getFkeyTables().size();
                
                List<String> nonKeyColumnnames = new ArrayList<>(tableInfo.columnsNames());
                nonKeyColumnnames.removeAll(tableInfo.getKeys());
                Collections.sort(nonKeyColumnnames);
                
                String values[] = new String[columnPositionMapping.size()];
                
                for (ValueCombination valueCombination : viewSolution) {
                	
                	values[positionOfPk] = Long.toString(valueCombination.getRowcount());
                	
                	int i = 1;
                	String value;
                	for (IntIterator iter = valueCombination.getColValues().iterator(); iter.hasNext();) {
                		int encodedVal = iter.nextInt();
                		
                		if(i > noOfKeys) {
                			String colName = nonKeyColumnnames.get(i - noOfKeys - 1);
                    		String colType = tableInfo.getColumns().get(colName).getColumnType();
                    		
                			if(colType.equals("integer")) {
                				if(encodedVal == 0) {
                					value = Integer.toString(Integer.MIN_VALUE);
                    			} else if(reverseNumberMap.get(colName).containsKey(encodedVal)) {
                    				value = getIntFromDouble(reverseNumberMap.get(colName).get(encodedVal)).toString();
                    			} else if(reverseNumberMap.get(colName).containsKey(encodedVal - 1)) {
                    				value = getIntFromDouble(reverseNumberMap.get(colName).get(encodedVal - 1) + 1).toString();
                    			} else
                    				throw new RuntimeException("Unknown encoded value : " + encodedVal);
                    		}
                			else if(colType.equals("integer") || colType.equals("numeric")) {
                				if(encodedVal == 0) {
                					if(colType.equals("integer"))
                						value = Integer.toString(Integer.MIN_VALUE);
                					else
                						value = Double.toString(Double.MIN_VALUE);
                    			} else if(reverseNumberMap.get(colName).containsKey(encodedVal)) {
                    				value = Double.toString(reverseNumberMap.get(colName).get(encodedVal));
                    			} else if(reverseNumberMap.get(colName).containsKey(encodedVal - 1)) {
                    				if(colType.equals("integer"))
                    					value = Double.toString(reverseNumberMap.get(colName).get(encodedVal - 1) + 1);
                    				else
                    					value = Double.toString(reverseNumberMap.get(colName).get(encodedVal - 1) + 0.00001);
                    			} else
                    				throw new RuntimeException("Unknown encoded value : " + encodedVal);
                    		}
                    		
                    		else if(colType.startsWith("character")) {
                    			if(encodedVal == 0) {
                    				value = "\"" + DEFAULT_STRING + "\"";
                    			} else if(reverseStringMap.get(colName).containsKey(encodedVal)) {
                    				value = "\"" + reverseStringMap.get(colName).get(encodedVal) + "\"";
                    			} else 
                    				throw new RuntimeException("Unknown encoded value : " + encodedVal);
                    		}
                    		
                    		else if(colType.equals("date")) {
                    			if(encodedVal == 0) {
                    				value = DEFAULT_DATE.toString();
                    			} else if(reverseDateMap.get(colName).containsKey(encodedVal)) {
                    				value = reverseDateMap.get(colName).get(encodedVal).toString();
                    			} else if(reverseDateMap.get(colName).containsKey(encodedVal - 1)) {
                    				value = getNextDate(calender, reverseDateMap.get(colName).get(encodedVal - 1)).toString();
                    			} else
                    				throw new RuntimeException("Unknown encoded value : " + encodedVal);
                    		}
                    		else if(colType.startsWith("time")) {
                    			if(encodedVal == 0)
                    				value = "00:00:00";
                    			else
                    				throw new RuntimeException("Not handled");
                    		}
                    		else {
//                    			DebugHelper.printError("Unknown column type: " + colType);
                    			throw new RuntimeException("Unknown column type: " + colType);
                    		}
                		} else {
                			value = Integer.toString(encodedVal);
                		}
                		values[columnPositionMapping.get(i)] = value;
                		i++;
                	}
                	for(int j = i; j < columnPositionMapping.size(); ++j)
                		values[columnPositionMapping.get(j)] = "-1";
                	String s = StringUtils.join(values, COMMA);
					fw.write(s + NEWLINE);
                }
            } catch (Exception ex) {
                throw new RuntimeException("Unable to write database summary for view " + origViewName + NEWLINE + ex.toString(), ex);
            } finally {
                try {
                    fw.close();
                } catch (Exception ex2) {}
            }
        }
        try {
            FileUtils.writeStringToFile(PostgresVConfig.getProp(Key.DATABASESUMMARY_LOCATION), PostgresVConfig.DATABASESUMMARY_INDEX, sbindex.toString());
        } catch (Exception ex) {
            throw new RuntimeException("Unable to write database summary index", ex);
        }
	}
	
	private Integer getIntFromDouble(Double value) {
		return Integer.valueOf((int) Math.round(value));
	}

    private Date getNextDate(Calendar calender, Date date) {
    	calender.setTime(date);
    	calender.add(Calendar.DATE, 1);  // number of days to add
		return calender.getTime();
	}

	public void dumpAllStaticRelations() {
        Map<String, ViewSolution> summaryByView = getSummaryByView();
        List<String> dumpViewnames = new ArrayList<>(summaryByView.keySet());
        Collections.sort(dumpViewnames);
        dumpStaticRelations(dumpViewnames);
    }

    public void dumpStaticRelations(List<String> dumpViewnames) {
        Map<String, ViewSolution> summaryByView = getSummaryByView();

        StringBuilder sbindex = new StringBuilder();
        for (String viewname : dumpViewnames) {
            ViewSolution viewSolution = summaryByView.get(viewname);

            DebugHelper.printDebug("Writing static database dump for view " + viewname);

            sbindex.append(viewname).append(NEWLINE);

            FileWriter fw = null;
            try {
                fw = new FileWriter(new File(PostgresVConfig.getProp(Key.DATABASESTATICDUMP_LOCATION), viewname));
                long pk = 0;
                for (ValueCombination valueCombination : viewSolution) {
                    for (long i = 0; i < valueCombination.getRowcount(); i++) {
                        fw.write(pk++ + COMMA + valueCombination.toStringStaticDump() + NEWLINE);
                    }
                }
            } catch (IOException ex) {
                throw new RuntimeException("Unable to write static database dump for view " + viewname, ex);
            } finally {
                try {
                    fw.close();
                } catch (Exception ex2) {}
            }
        }
        try {
            FileUtils.writeStringToFile(PostgresVConfig.getProp(Key.DATABASESTATICDUMP_LOCATION), PostgresVConfig.DATABASESUMMARY_INDEX, sbindex.toString());
        } catch (Exception ex) {
            throw new RuntimeException("Unable to write static database dump index", ex);
        }
    }
    
    public List<String> decodeAndDumpStaticRelations(HashMap<String, Int2DoubleOpenHashMap> reverseNumberMap, HashMap<String, Int2ObjectOpenHashMap<String>> reverseStringMap, HashMap<String, Int2ObjectOpenHashMap<Date>> reverseDateMap,
    		Map<String, String> TABLES_MAP, List<String> dumpViewnames, String outputLocation, SharedBoolean doWork) {
		Map<String, ViewSolution> summaryByView = getSummaryByView();
        SchemaInfo schemaInfo = PostgresVConfig.ANONYMIZED_SCHEMAINFO;
        
        final String DEFAULT_STRING = " ";
        
        Calendar calender = Calendar.getInstance();
        calender.set(-1990, 1, 1);
        final Date DEFAULT_DATE = calender.getTime();
        
        List<String> doneViews = new ArrayList<>();

        StringBuilder sbindex = new StringBuilder();
        for (String origViewName : dumpViewnames) {
            String viewname = TABLES_MAP.get(origViewName);
            ViewSolution viewSolution = summaryByView.get(viewname);
            TableInfo tableInfo = schemaInfo.getTableInfo(viewname);
            DebugHelper.printDebug("Writing static database dump for view " + origViewName);

            sbindex.append(origViewName).append(NEWLINE);

            List<Integer> columnPositionMapping = tableInfo.getColumnPositionMapping();
            int positionOfPk = columnPositionMapping.get(0);		// columnPositionMapping.get(0) is position of PK

            FileWriter fw = null;
            try {
				fw = new FileWriter(new File(outputLocation, origViewName.toUpperCase()));
                
                int noOfPKs = 0;	// TODO
                int noOfKeys = noOfPKs + tableInfo.getFkeyTables().size();
                
                List<String> nonKeyColumnnames = new ArrayList<>(tableInfo.columnsNames());
                nonKeyColumnnames.removeAll(tableInfo.getKeys());
                Collections.sort(nonKeyColumnnames);
                
                String values[] = new String[columnPositionMapping.size()];
                long pk = 0;

                for (ValueCombination valueCombination : viewSolution) {
//                	values[positionOfPk] = Long.toString(valueCombination.getRowcount());
                	
                	int i = 1;
                	String value;
                	for (IntIterator iter = valueCombination.getColValues().iterator(); iter.hasNext();) {
                		int encodedVal = iter.nextInt();
                		
                		if(i > noOfKeys) {
                			String colName = nonKeyColumnnames.get(i - noOfKeys - 1);
                    		String colType = tableInfo.getColumns().get(colName).getColumnType();
                    		
                			if(colType.equals("integer")) {
                				if(encodedVal == 0) {
                					value = Integer.toString(Integer.MIN_VALUE);
                    			} else if(reverseNumberMap.get(colName).containsKey(encodedVal)) {
                    				value = getIntFromDouble(reverseNumberMap.get(colName).get(encodedVal)).toString();
                    			} else if(reverseNumberMap.get(colName).containsKey(encodedVal - 1)) {
                    				value = getIntFromDouble(reverseNumberMap.get(colName).get(encodedVal - 1) + 1).toString();
                    			} else
                    				throw new RuntimeException("Unknown encoded value : " + encodedVal);
                    		}
                			else if(colType.equals("integer") || colType.equals("numeric")) {
                				if(encodedVal == 0) {
                					if(colType.equals("integer"))
                						value = Integer.toString(Integer.MIN_VALUE);
                					else
                						value = Double.toString(Double.MIN_VALUE);
                    			} else if(reverseNumberMap.get(colName).containsKey(encodedVal)) {
                    				value = Double.toString(reverseNumberMap.get(colName).get(encodedVal));
                    			} else if(reverseNumberMap.get(colName).containsKey(encodedVal - 1)) {
                    				if(colType.equals("integer"))
                    					value = Double.toString(reverseNumberMap.get(colName).get(encodedVal - 1) + 1);
                    				else
                    					value = Double.toString(reverseNumberMap.get(colName).get(encodedVal - 1) + 0.00001);
                    			} else
                    				throw new RuntimeException("Unknown encoded value : " + encodedVal);
                    		}
                    		
                    		else if(colType.startsWith("character")) {
                    			if(encodedVal == 0) {
                    				value = "\"" + DEFAULT_STRING + "\"";
                    			} else if(reverseStringMap.get(colName).containsKey(encodedVal)) {
                    				value = "\"" + reverseStringMap.get(colName).get(encodedVal) + "\"";
                    			} else 
                    				throw new RuntimeException("Unknown encoded value : " + encodedVal);
                    		}
                    		
                    		else if(colType.equals("date")) {
                    			if(encodedVal == 0) {
                    				value = DEFAULT_DATE.toString();
                    			} else if(reverseDateMap.get(colName).containsKey(encodedVal)) {
                    				value = reverseDateMap.get(colName).get(encodedVal).toString();
                    			} else if(reverseDateMap.get(colName).containsKey(encodedVal - 1)) {
                    				value = getNextDate(calender, reverseDateMap.get(colName).get(encodedVal - 1)).toString();
                    			} else
                    				throw new RuntimeException("Unknown encoded value : " + encodedVal);
                    		}
                    		else if(colType.startsWith("time")) {
                    			if(encodedVal == 0)
                    				value = "00:00:00";
                    			else
                    				throw new RuntimeException("Not handled");
                    		}
                    		else {
                    			DebugHelper.printError("Unknown column type: " + colType);
                    			throw new RuntimeException("Unknown column type: " + colType);
                    		}
                		} else {
                			value = Integer.toString(encodedVal);
                		}
                		values[columnPositionMapping.get(i)] = value;
                		i++;
                	}
                	for(int j = i; j < columnPositionMapping.size(); ++j)
                		values[columnPositionMapping.get(j)] = "-1";
                	for (long k = 0; k < valueCombination.getRowcount(); ++k) {
                		if (!doWork.value)
                			return doneViews;
                		String curValues[] = createCopy(values);
                		curValues[positionOfPk] = Long.toString(pk++);
                		String s = StringUtils.join(curValues, COMMA);
    					fw.write(s + NEWLINE);
                	}
                }
                doneViews.add(origViewName);
            } catch (Exception ex) {
                throw new RuntimeException("Unable to write static database dump for view " + origViewName + NEWLINE + ex.toString(), ex);
            } finally {
                try {
                    fw.close();
                } catch (Exception ex2) {}
            }
        }
        try {
            FileUtils.writeStringToFile(PostgresVConfig.getProp(Key.DATABASESUMMARY_LOCATION), PostgresVConfig.DATABASESUMMARY_INDEX, sbindex.toString());
        } catch (Exception ex) {
        	throw new RuntimeException("Unable to write static database dump index", ex);
        }
        return doneViews;
	}

	private String[] createCopy(String[] values) {
		String curValues[] = new String[values.length];
		for (int i = 0; i < values.length; ++i)
			curValues[i] = values[i];
		return curValues;
	}

	public void compressSummaryUsingRegionMapping() {
		
		
		
		// ViewSummarisation		
		Map<String, ViewInfo> viewInfos = PostgresVConfig.ANONYMIZED_VIEWINFOs;
		Map<String, ColumnPathInfo> columnIdMap = PostgresVConfig.COLUMN_ID_MAP;
		Map<String,String> fkPkMap = PostgresVConfig.FKPKMap;
		
		for(Entry<String,ConcurrentHashMap<String,Set<String>>> e : FkSeqNumtoPkSeqNumListforFKview.entrySet())		{
			String viewName = e.getKey();
			
			StopWatch compressSummaryUsingRegionMappingLoop1 = new StopWatch("compressSummaryUsingRegionMappingLoop1--" + viewName );
			   
			
			//System.out.println("Inside compressSummary - FkSeqNumtoPkSeqNumListforFKview " + viewName);
			
			Set<String> viewNonKeysSet = viewInfos.get(viewName).getViewNonkeys();
			List<String> viewNonKeysList = new ArrayList<>();
			for(String s : viewNonKeysSet)
				viewNonKeysList.add(s);
			Collections.sort(viewNonKeysList);				
			ViewSummary vs = new ViewSummary(viewName, viewNonKeysList);
			viewSummaryMap.put(viewName, vs);
			// Iterate over each fk regions'
			
			/*
			 *  Taking care of views which didn't appear in query workload
			 */
			
			//System.out.println("Inside compressSummary - Stage 2 " + viewName);
			
			if(e.getValue().isEmpty())
			{
				
				
				String fkRegionSeqnum = viewName + "_" + "allRegions"; // create a fake region sequence number
				ViewSolutionInMemory viewSolution = (ViewSolutionInMemory) viewSolutions.get(viewName);
				// adding a fake region for the view
				// fake region = [[[]]]
				Bucket b = new Bucket();
				BucketStructure bs = new BucketStructure();
				bs.add(b);
				Region r = new Region();
				r.add(bs);
				seqNumberToVariableValuePairViewMap.get(viewName).put(fkRegionSeqnum,new VariableValuePair(r,viewSolution.getLastSeenPK()));
				
				RegionSummary rs = new RegionSummary(fkRegionSeqnum);
				for(Entry<String,String> fk : fkPkMap.entrySet())
				{
					if(fk.getKey().contains(viewName))
					{
						String pkColumnName =  fk.getValue();
						String fkColumnName = fk.getKey();
						
						List<String> pkRegionList = new ArrayList<>();
						String pkRegionSeqNum = pkColumnName + "_" + "allRegions";
						pkRegionList.add(pkRegionSeqNum);
						FKeyClass fkObj = new FKeyClass(pkRegionList,pkColumnName,fkColumnName);
						rs.addFKey(fkObj);
						
					}
					
					//System.out.println("RELNAME FKPK " + fk);
				}
				
				vs.addRegionSummary(rs);
				continue;
				
			}
			
			//System.out.println("Inside compressSummary - Stage 3 " + viewName);
			
		
			for(Entry<String, Set<String>> region : e.getValue().entrySet())
			{
			
				String fkRegionSeqnum = region.getKey();
				RegionSummary rs = new RegionSummary(fkRegionSeqnum);
				
				ViewInfo viewInfo = viewInfos.get(e.getKey());
				Set<String> viewNonKeys = new HashSet<String>(viewInfo.getViewNonkeys());
				viewNonKeys.removeAll(viewInfo.getTableNonkeys());
				List<String> fkeyColumnTracker = new ArrayList<String>();
				List<String> pkeyColumnTracker = new ArrayList<String>();
				// Iterate over viewNonkeys to find fkeys for borrowed attributes
				//if(viewName.contains("t02"))
				//	System.out.print("");
			
				for(String col : viewNonKeys)
				{
					
					List<String> fkColumnNames = columnIdMap.get(col).getFKColumnNames();
					List<String> pkColumnNames = columnIdMap.get(col).getPKColumnNames();
					String pkColumnName = null;
					String fkColumnName = null;
					
					
					for(int j=0; j<pkColumnNames.size();j++)
					{
						pkColumnName = pkColumnNames.get(j);
						fkColumnName = fkColumnNames.get(j);
						
						if(!fkColumnName.contains(viewName))
							continue;
						
						if(pkColumnName.contentEquals(""))
							continue;
						
						if(pkeyColumnTracker.contains(pkColumnName) && fkeyColumnTracker.contains(fkColumnName)) {
							continue;
						}
						
						
						String pkTableName = pkColumnName.split("_")[0];
						boolean pkflag=false;
						List<String> pkRegionList = new ArrayList<String>();
						for(String pkRegionSeqNum : region.getValue())
						{
							if(pkRegionSeqNum.contains(pkTableName))
							{
								pkRegionList.add(pkRegionSeqNum);
								pkflag=true;
							}
						}
						if(pkflag) {
							
							fkeyColumnTracker.add(fkColumnName);
							pkeyColumnTracker.add(pkColumnName);
							FKeyClass fkObj = new FKeyClass(pkRegionList,pkColumnName,fkColumnName);
							rs.addFKey(fkObj);
							
						}
						
						
					}
					
				}
				
				
				// adding fkeys for pk relation whose pk-fk edge is not present in query workload, but present in schema
				for(String pkRegionSeqNum : region.getValue())
				{
					if(pkRegionSeqNum.contains("allRegions"))
					{
						String pkRelName = pkRegionSeqNum.split("_")[0];
						String fkRelName = fkRegionSeqnum.split("_")[0];
						List<String> pkRegionList = new ArrayList<>();
						pkRegionList.add(pkRegionSeqNum);
						for(Entry<String,String> k : fkPkMap.entrySet())
						{
							if(k.getKey().contains(fkRelName) &&  k.getValue().contains(pkRelName))
							{
								String pkColumnName =  k.getValue();
								String fkColumnName = k.getKey();
								boolean cflag = false;
								for(int i=0;i<pkeyColumnTracker.size();i++)
								{
									
									if(pkeyColumnTracker.get(i).contentEquals(pkColumnName) && fkeyColumnTracker.get(i).contentEquals(fkColumnName) )
									{
										cflag = true;
										break;
									}
									
								}
								if(cflag)
									continue;
								FKeyClass fkObj = new FKeyClass(pkRegionList,pkColumnName,fkColumnName);
								rs.addFKey(fkObj);
								
								
								fkeyColumnTracker.add(fkColumnName);
								pkeyColumnTracker.add(pkColumnName);
							
								
							}
						}
						
					}
								
				}
				
				// Adding those fkeys which have pk-fk edge in workload for the pk-fk relation but with other fkey(s)
				HashMap<String,String> tempFKPKMap = new HashMap<>();
				for(Entry<String,String> fkpk : fkPkMap.entrySet())
				{
					if(!fkpk.getKey().contains(viewName))
						continue;
					
					String fkColname  = fkpk.getKey();
					String pkColname =  fkpk.getValue();
					tempFKPKMap.put(fkColname,pkColname);
					
				}
				// remove entries from tempPKFKMap
				for(int p=0; p<pkeyColumnTracker.size();p++)
				{
					if(tempFKPKMap.containsKey(fkeyColumnTracker.get(p)))
					{
						tempFKPKMap.remove(fkeyColumnTracker.get(p));
					}
				}
				//if(viewName.contains("t02"))
				//	System.out.print("");
				for(Entry<String,String> fkpk : tempFKPKMap.entrySet())
				{
					List<String> pkRegionList = new ArrayList<>();
					pkRegionList.add(fkpk.getValue().split("_")[0]  + "_allRegions");		
				
					
					FKeyClass fkObj = new FKeyClass(pkRegionList,fkpk.getValue(),fkpk.getKey());
					rs.addFKey(fkObj);
					fkeyColumnTracker.add(fkpk.getKey());
					pkeyColumnTracker.add(fkpk.getValue());
				}
				
				
				
				vs.addRegionSummary(rs);
				
			}
			
			//System.out.println("Inside compressSummary - Stage 4 " + viewName);
			
			compressSummaryUsingRegionMappingLoop1.displayTimeAndDispose();
		}
		
		// Adding pk Relations in viewSummary
	    List<String> topoViewnames = PostgresVConfig.VIEWNAMES_TOPO;
	    for(String viewName : topoViewnames)
	    {
	    	
	    	StopWatch compressSummaryUsingRegionMappingLoop2 = new StopWatch("compressSummaryUsingRegionMappingLoop2--" + viewName );
			
	    	//if(viewName.contentEquals("t10"))
	    	//	System.out.println("");
	    	if(viewSummaryMap.containsKey(viewName))
	    		continue;
	    	Set<String> viewNonKeysSet = viewInfos.get(viewName).getViewNonkeys();
			List<String> viewNonKeysList = new ArrayList<>();
			for(String s : viewNonKeysSet)
				viewNonKeysList.add(s);
			Collections.sort(viewNonKeysList);
	    	ViewSummary viewSummary = new ViewSummary(viewName,viewNonKeysList);

	    	viewSummaryMap.put(viewName, viewSummary);
	    	if(viewName.contains("t09"))
	    		System.out.print("");
	    	if(!FkSeqNumtoPkSeqNumListforFKview.containsKey(viewName))
	    	{
	    		if(seqNumberToVariableValuePairViewMap.get(viewName).entrySet().isEmpty())
	    		{
	    			ViewSolutionInMemory viewSolution = (ViewSolutionInMemory) viewSolutions.get(viewName);
					// adding a fake region for the view
					// fake region = [[[]]]
					Bucket b = new Bucket();
					BucketStructure bs = new BucketStructure();
					bs.add(b);
					Region r = new Region();
					r.add(bs);
					seqNumberToVariableValuePairViewMap.get(viewName).put(viewName + "_" + "allRegions",new VariableValuePair(r,viewSolution.getLastSeenPK()));
	    		}
	    		for(Entry<String,VariableValuePair> region : seqNumberToVariableValuePairViewMap.get(viewName).entrySet() )
	    		{
	    			RegionSummary rs = new RegionSummary(region.getKey());
	    			viewSummary.addRegionSummary(rs);
	    		}
	    		
	    	}
	    	
	    	compressSummaryUsingRegionMappingLoop2.displayTimeAndDispose();
	    }
	    	
		
		System.out.println("MIDWAY");
		
		
		// Relation Summarisation
		for(Entry<String,ViewSummary> view  : viewSummaryMap.entrySet())
		{
			String relName = view.getKey();
			StopWatch compressSummaryUsingRegionMappingLoop3 = new StopWatch("compressSummaryUsingRegionMappingLoop3--" + relName );
			
			ViewSummary viewSummary = view.getValue();
			Set<String> tableNonKeysSet = viewInfos.get(relName).getTableNonkeys();
			List<String> tableNonKeys = new ArrayList<>();
			tableNonKeys.addAll(tableNonKeysSet);
			Collections.sort(tableNonKeys);
			RelationSummary relSumm = new RelationSummary(relName,viewSummary,tableNonKeys);
			relationSummaryMap.put(relName, relSumm);
	    	
			compressSummaryUsingRegionMappingLoop3.displayTimeAndDispose();
						
		}
		
		if(Runtime.getRuntime().freeMemory() <10000000000L)
			System.gc();
		
		StopWatch assignIntervalstoViewRegions = new StopWatch("assignIntervalstoViewRegions" );
		
		
		assignIntervalstoViewRegions();
		
		assignIntervalstoViewRegions.displayTimeAndDispose();
		System.out.println("HALFWAY");
		
		
		// Just for printing things
		//for(Entry<String,ViewSummary> view  : viewSummaryMap.entrySet())
		//{
		//	String relName = view.getKey();
		//	relationSummaryMap.get(relName).generateRelationSummary();
		//}
		
		if(Runtime.getRuntime().freeMemory() <10000000000L)
			System.gc();
		
		
		try {
			File f = new File(PostgresVConfig.getProp(Key.DATABASESUMMARY_LOCATION) + "/" + PostgresVConfig.RELATION_NAMES_INDEX);
			if(f.exists() && !f.isDirectory()) { 
				PrintWriter pw = new PrintWriter(f);
				pw.close();
			}
		} catch (FileNotFoundException e1) {
			// TODO Auto-generated catch block
			e1.printStackTrace();
		}
		
		// Dump json file
		JSONObject dbSummJSON = new JSONObject();
		for(Entry<String,ViewSummary> view  : viewSummaryMap.entrySet())
		{
			String relName = view.getKey();
			
			StopWatch writeSummary = new StopWatch("writeSummary--" + relName );
			
			
			//if(!(relName.equals("t19")))continue;// || relName.equals("t17")  || relName.equals("t16") ) ) continue;
			//if(!(relName.equals("t21")))continue;
			
			//if(relName.equals("t00") || relName.equals("t01") || relName.equals("t03")  || relName.equals("t10")    ) continue;
			//if(relName.equals("t20") || relName.equals("t14") || relName.equals("t12")  || relName.equals("t11")    ) continue;
			
			//if(relName.equals("t21") || relName.equals("t16") || relName.equals("t23")  || relName.equals("t22") ) continue;
			
			//if(!(relName.equals("t06") || relName.equals("t08")  || relName.equals("t09") ) ) continue;
			
			//System.out.println("Check : Stage 0 " + relName + "Entering rel summary");
			
			JSONObject obj = relationSummaryMap.get(relName).getJSONRelationSummary();
			
			//FileUtils.writeStringToFile("/home/dsladmin/multi-query-workspace/codd-data-gen/resources/cdgvendor/output/postgres/"+ CURRENT_CONTEXT + "/dBSummary"+ CURRENT_CONTEXT + "_" + relName + ".json", obj.toString());

			FileUtils.writeStringToFile(PostgresVConfig.getProp(Key.DATABASESUMMARY_LOCATION) + "/dbSummary_"+relName+ ".json", obj.toString()); 
			//dbSummJSON.put(relName, obj);

			FileUtils.writeStringToFile(PostgresVConfig.getProp(Key.DATABASESUMMARY_LOCATION),
					PostgresVConfig.RELATION_NAMES_INDEX, relName + "\n", 1); // System.out.println("Now
	
			//System.out.println("Check : Stage 0 " + relName + "Exiting rel summary");
			writeSummary.displayTimeAndDispose();
			
			if(Runtime.getRuntime().freeMemory() <10000000000L)
				System.gc();
		}
		
		
		//System.out.println(dbSummJSON);
		FileUtils.writeStringToFile(PostgresVConfig.getProp(Key.DB_SUMMARY_DUMP), dbSummJSON.toString());
		
		System.out.println("Error Cardinality viewWise added :" + this.viewErrorCountMap);
		
		
		
		isCompressed = true;
		
	}

	//NEWEST CODE AFTER TARUN SENT FINAL FIX VIA WHATSAPP FOR HD 306 307 BUG
private void assignIntervalstoViewRegions() {
		
		
		for(Entry<String, ConcurrentHashMap<String, VariableValuePair>> view : seqNumberToVariableValuePairViewMap.entrySet())
		{
			long start = 0;
			ArrayList<Long> bg = new ArrayList<Long>();
			ArrayList<String> regionSeqNumList = new ArrayList<>();
			this.IntervalDomainMap.put(view.getKey(),bg);
			this.OrderedRegionMapParallelToIntervalDomainMap.put(view.getKey(),regionSeqNumList);
			
			
			Integer index=0;
		
			for(Entry<String,VariableValuePair> region : view.getValue().entrySet())
			{
				long rowcount = region.getValue().rowcount;
				bg.add(start);
				regionSeqNumList.add(region.getKey());
				RegionIntervalMap.put(region.getKey(),index);
				index++;
				start = start + rowcount;
				System.out.print("");
				
			}
			
			
			if(!view.getValue().isEmpty())
			{
				bg.add(start);
				regionSeqNumList.add(view + "allRegions");
				relationSummaryMap.get(view.getKey()).addRegionCardinality(start);
			}
			else 
			{
				bg.add(start);
				regionSeqNumList.add(view + "allRegions");
				ViewSolutionInMemory viewSolution = (ViewSolutionInMemory) viewSolutions.get(view.getKey());
				bg.add(viewSolution.getLastSeenPK());
				relationSummaryMap.get(view.getKey()).addRegionCardinality(viewSolution.getLastSeenPK());
				
			}
			
			
		}
	}
	
	//CODE BEFORE TARUN SENT FINAL FIX VIA WHATSAPP FOR HD 306 307 BUG
	/*
	private void assignIntervalstoViewRegions() {
		
		
		for(Entry<String,ConcurrentHashMap<String,VariableValuePair>> view : seqNumberToVariableValuePairViewMap.entrySet())		{
			long start = 0;
			ArrayList<Long> bg = new ArrayList<Long>();
			IntervalDomainMap.put(view.getKey(),bg);
			
			Integer index=0;
		
			for(Entry<String,VariableValuePair> region : view.getValue().entrySet())
			{
				long rowcount = region.getValue().rowcount;
				bg.add(start);
				RegionIntervalMap.put(region.getKey(),index);
				index++;
				start = start + rowcount;
				System.out.print("");
				
			}
			
			
			if(!view.getValue().isEmpty())
			{
				bg.add(start);
				relationSummaryMap.get(view.getKey()).addRegionCardinality(start);
			}
			else 
			{
				bg.add(start);
				ViewSolutionInMemory viewSolution = (ViewSolutionInMemory) viewSolutions.get(view.getKey());
				bg.add(viewSolution.getLastSeenPK());
				relationSummaryMap.get(view.getKey()).addRegionCardinality(viewSolution.getLastSeenPK());
			}
			
			
		}

		
		
	}*/
	
	
	
	
	//Symmetric regions code
	private List<Region> makeSymmetric(Region region, List<String> commonColumn, List<String> sortedViewColumns) {
        // method to make regions symmetric along a commonColumn
        List<Region> symmetricRegions = new ArrayList<>();
        Map<List<Bucket>, Region> commonColumnBucketsToRegion = new HashMap<>();
        for (BucketStructure bs : region.getAll()) {
            List<Bucket> commonColumnBuckets = getBucketsForcommonColumn(bs, commonColumn, sortedViewColumns);
            if (!commonColumnBucketsToRegion.containsKey(commonColumnBuckets))
                commonColumnBucketsToRegion.put(commonColumnBuckets, new Region());
            commonColumnBucketsToRegion.get(commonColumnBuckets).add(bs);

 

        }
        for (Region reg : commonColumnBucketsToRegion.values()) {
            //if( reg.size()>1)
                //System.out.print(reg);
            symmetricRegions.add(reg);
        }
        return symmetricRegions;
    }

 

    private List<Bucket> getBucketsForcommonColumn(BucketStructure bs, List<String> commonColumn,List<String> sortedViewColumns) {
        List<Bucket> buckets = new ArrayList<>();
        List<Integer> idx = new ArrayList<>();

        

        for (String column : commonColumn) {
            idx.add(sortedViewColumns.indexOf(column));
        }
        for (Integer id : idx)
            buckets.add(bs.at(id));
        return buckets;
    }
    
    public void makeAllViewRegionsConsistent() {
    	
    	Map<String, ViewInfo> viewInfos = PostgresVConfig.ANONYMIZED_VIEWINFOs;
        List<String> topoViewnames = PostgresVConfig.VIEWNAMES_TOPO;
    	for (int i = 0; i < topoViewnames.size() - 1; i++) {
    		String fkViewname = topoViewnames.get(i);
            ViewInfo fkViewInfo = viewInfos.get(fkViewname);
            
            List<String> fkNonKeyColumns = new ArrayList<>(fkViewInfo.getViewNonkeys());
          
            List<String> sortedViewColumns = new ArrayList<>(fkViewInfo.getViewNonkeys());
            Collections.sort(sortedViewColumns);
    		for (String pkViewname : fkViewInfo.getFkeyViews()) {
    			ViewInfo pkViewInfo = viewInfos.get(pkViewname);
    			List<String> pkNonKeysCol = new ArrayList<>(pkViewInfo.getViewNonkeys());
    			if(pkNonKeysCol.isEmpty())
    				continue;
    			Collections.sort( pkNonKeysCol);
    			fkNonKeyColumns.retainAll(pkNonKeysCol);
    			List<VariableValuePair> regionsList = viewSolutions.get(fkViewname).getVariableValuePairs();
    			if(regionsList == null)
    				continue;
    			List<VariableValuePair> newRegionsList = new ArrayList<>();
    			for( VariableValuePair vvp : regionsList) {
    				List<Region> newRegions = makeSymmetric(vvp.variable,fkNonKeyColumns,sortedViewColumns);
    				long totalVolume = vvp.variable.getVolume();
    				long rowcount = vvp.rowcount;
    				long leftRowCount = vvp.rowcount;
    				for(int r=0; r<newRegions.size()-1; r++)
    				{
    					long volume = newRegions.get(r).getVolume();
    					long newRowCount = volume*rowcount/totalVolume;
    					VariableValuePair newVVP = new VariableValuePair(newRegions.get(r),newRowCount);
    					newRegionsList.add(newVVP);
    					leftRowCount = leftRowCount - newRowCount;
    				}
    				
    				if(leftRowCount<1)
    					throw new RuntimeException("Negative row count");
    				
    				VariableValuePair newVVP = new VariableValuePair(newRegions.get(newRegions.size()-1),leftRowCount);
					newRegionsList.add(newVVP);
    			}
    			
    			viewSolutions.get(fkViewname).setVariableValuePairs(newRegionsList);
    		}
    	}
    }
	
	
    public void unifiedmakeAllViewRegionsConsistent(Map<String, List<VariableValuePair>> viewToVVPMap) {
    	
    	Map<String, ViewInfo> viewInfos = PostgresVConfig.ANONYMIZED_VIEWINFOs;
        List<String> topoViewnames = PostgresVConfig.VIEWNAMES_TOPO;
    	for (int i = 0; i < topoViewnames.size() - 1; i++) {
    		String fkViewname = topoViewnames.get(i);
            ViewInfo fkViewInfo = viewInfos.get(fkViewname);
            
            List<String> fkNonKeyColumns = new ArrayList<>(fkViewInfo.getViewNonkeys());
          
            List<String> sortedViewColumns = new ArrayList<>(fkViewInfo.getViewNonkeys());
            Collections.sort(sortedViewColumns);
    		for (String pkViewname : fkViewInfo.getFkeyViews()) {
    			ViewInfo pkViewInfo = viewInfos.get(pkViewname);
    			List<String> pkNonKeysCol = new ArrayList<>(pkViewInfo.getViewNonkeys());
    			if(pkNonKeysCol.isEmpty())
    				continue;
    			Collections.sort( pkNonKeysCol);
    			fkNonKeyColumns.retainAll(pkNonKeysCol);
    			//PKR
    			List<VariableValuePair> regionsList = new LinkedList<>();
    			if(viewToVVPMap.containsKey(fkViewname))
    				regionsList = viewToVVPMap.get(fkViewname);
    			if(regionsList == null)
    				continue;
    			List<VariableValuePair> newRegionsList = new LinkedList<>();
    			for( VariableValuePair vvp : regionsList) {
    				List<Region> newRegions = makeSymmetric(vvp.variable,fkNonKeyColumns,sortedViewColumns);
    				long totalVolume = vvp.variable.getVolume();
    				long rowcount = vvp.rowcount;
    				long leftRowCount = vvp.rowcount;
    				for(int r=0; r<newRegions.size()-1; r++)
    				{
    					long volume = newRegions.get(r).getVolume();
    					long newRowCount = volume*rowcount/totalVolume;
    					VariableValuePair newVVP = new VariableValuePair(newRegions.get(r),newRowCount);
    					newRegionsList.add(newVVP);
    					leftRowCount = leftRowCount - newRowCount;
    				}
    				
    				//PKR
//    				if(leftRowCount<1)
//    					throw new RuntimeException("Negative row count");
    				
    				VariableValuePair newVVP = new VariableValuePair(newRegions.get(newRegions.size()-1),leftRowCount);
					newRegionsList.add(newVVP);
    			}
    			viewToVVPMap.remove(fkViewname);
    			if(!newRegionsList.isEmpty())
    				viewToVVPMap.put(fkViewname, newRegionsList);
    		}
    	}
    }

	
	
	
	
	
	
	
	
	
	
	
	
	
	
}