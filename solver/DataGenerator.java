package in.ac.iisc.cds.dsl.cdgvendor.solver;

import java.io.BufferedWriter;
import java.io.File;
import java.io.FileReader;
import java.io.FileWriter;
import java.io.IOException;
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
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.concurrent.ConcurrentHashMap;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;

import org.apache.commons.lang.mutable.MutableInt;
import org.json.JSONArray;
import org.json.JSONObject;
import org.json.simple.parser.JSONParser;
import org.json.simple.parser.ParseException;

import in.ac.iisc.cds.dsl.cdgclient.constants.PostgresCConfig;
import in.ac.iisc.cds.dsl.cdgvendor.constants.PostgresVConfig;
import in.ac.iisc.cds.dsl.cdgvendor.constants.PostgresVConfig.Key;
import in.ac.iisc.cds.dsl.cdgvendor.model.VariableValuePair;
import in.ac.iisc.cds.dsl.cdgvendor.reducer.Bucket;
import in.ac.iisc.cds.dsl.cdgvendor.reducer.BucketStructure;
import in.ac.iisc.cds.dsl.cdgvendor.reducer.Region;
import in.ac.iisc.cds.dsl.cdgvendor.utils.CustomCollator;
import in.ac.iisc.cds.dsl.cdgvendor.utils.FileUtils;
import in.ac.iisc.cds.dsl.cdgvendor.utils.Pair;
import it.unimi.dsi.fastutil.ints.Int2DoubleOpenHashMap;
import it.unimi.dsi.fastutil.ints.Int2ObjectOpenHashMap;
import it.unimi.dsi.fastutil.ints.IntList;

public class DataGenerator {
	

    
    public static void materializeAllRelationsFromJSONSummary(){
    	
    	/*
    	Object object=null;
		try {
			object = new JSONParser().parse(new FileReader("/home/dsladmin/multi-query-workspace/codd-data-gen/resources/cdgvendor/input/postgres/anonymizedschema.info"));//"/home/dsladmin/sqlqueries/temp/anonymizedschema.info"));///home/dsladmin/TODI/ws_kk/codd-data-gen/resources/cdgvendor/input/postgres/anonymizedschema.info"));
		} catch (IOException | ParseException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		} 
        
		
		  
		 org.json.simple.JSONObject jo = (org.json.simple.JSONObject) object; 
		 */
    	//FileUtils.writeStringToFile(PostgresCConfig.getProp(Key.EXPANALYZE_LOCATION), PostgresCConfig.EXPANALYZE_INDEX, "metadataPlans/"+ fileName.toString() + "\n", 1); // System.out.println("Now
    	List<String> relationNameList = FileUtils.readLines(PostgresVConfig.getProp(Key.DATABASESUMMARY_LOCATION), PostgresVConfig.RELATION_NAMES_INDEX);
        
    	//ArrayList<String> relationNameArray = new ArrayList<>(Arrays.asList("t00","t01","t02","t03","t04","t05","t06","t07","t08","t09","t10","t11","t12","t13","t14","t15","t16","t17","t18","t19","t20","t21","t22","t23"));
    	//ArrayList<String> relationNameArray = new ArrayList<>(Arrays.asList("t16","t21"));//,"t02","t03","t04","t05","t06","t07","t08","t09","t10","t11","t12","t13","t14","t15","t17","t18","t19","t20","t22","t23"));
    	
    	for(String relName : relationNameList) {
    	
    	JSONObject jsonDump=null;
 		//jsonDump = new JSONObject(FileUtils.readFileToString(PostgresVConfig.getProp(Key.DB_SUMMARY_DUMP)));
		//jsonDump = new JSONObject(new String(Files.readAllBytes(Paths.get("/home/dsladmin/multi-query-workspace/codd-data-gen/resources/cdgvendor/output/postgres/dBSummary.json")), StandardCharsets.UTF_8));//"/home/dsladmin/sqlqueries/temp/anonymizedschema.info"));///home/dsladmin/TODI/ws_kk/codd-data-gen/resources/cdgvendor/input/postgres/anonymizedschema.info"));
		//jsonDump = new JSONObject(new String(Files.readAllBytes(Paths.get("/home/dsladmin/multi-query-workspace/codd-data-gen/resources/cdgvendor/output/postgres/" + CURRENT_CONTEXT + "/dBSummary" + CURRENT_CONTEXT + "_"+relationName+".json")), StandardCharsets.UTF_8));//"/home/dsladmin/sqlqueries/temp/anonymizedschema.info"));///home/dsladmin/TODI/ws_kk/codd-data-gen/resources/cdgvendor/input/postgres/anonymizedschema.info")); 
		jsonDump = new JSONObject(new String(FileUtils.readFileToString(PostgresVConfig.getProp(Key.DATABASESUMMARY_LOCATION) + "/dbSummary_"+relName+ ".json"))); 
		
		//System.out.println("jsonDump " + jsonDump );

 		//System.out.println("reverseDateMap.get(t07_c005)" + reverseDateMap.get("t07_c005"));
 		//for(String a : jsonDump.keySet()) {
 			
		int N_CONSUMERS = Runtime.getRuntime().availableProcessors();
      	ExecutorService service = Executors.newFixedThreadPool(N_CONSUMERS);
      	
		
		JSONObject relationDump = jsonDump;//(JSONObject) jsonDump.get(a); //UNCOMMENT THIS FOR WHOLE DBSUMMARY
   	
    	//String relName = relationDump.getString("relName");
    	

    	//Checkpoint
    	
    	//if(!(relName.equals("t08") || relName.equals("t18") || relName.equals("t20") || relName.equals("t22"))) continue;
    	//if(!(relName.equals("t07") || relName.equals("t08") || relName.equals("t15") || relName.equals("t17"))) continue;
    	//if(!relationName.equals("t07")) continue;
    	
    	//if(!relName.equals("t23")) continue;
    	//if(!relName.equals("t07")) continue;
    	
    	
    	//if(!relName.equals("t07")) continue;
    	//if(!relName.equals("t14")) continue;
    	
    	
    	//if(relName.equals("t00") || relName.equals("t01") || relName.equals("t02")) continue;
    	
    	
    	//if(!( relName.equals("t16") || relName.equals("t21") )) continue;
    	
    	
    	//if(!( relName.equals("t02") || relName.equals("t22")  || relName.equals("t16") ) ) continue;
    	//if(!( relName.equals("t06") || relName.equals("t08")  || relName.equals("t09") || relName.equals("t19")) ) continue;
    	
    	
    	
    	
    	//hd_306_307_bug
    	//if(!( relName.equals("t19")  || relName.equals("t17")|| relName.equals("t08") || relName.equals("t09")) ) continue;
    	//if(!( relName.equals("t15") || relName.equals("t17")  || relName.equals("t08") || relName.equals("t18")) ) continue;
    	
    	
    	
    	
    	//t04 t05 t08 t09
    	
    	//if((relName.contentEquals("t15") || relName.contentEquals("t17") || relName.contentEquals("t08") || relName.contentEquals("t18"))) {
    	//if(relName.contentEquals("t07")) {// || relName.contentEquals("t17") || relName.contentEquals("t08") || relName.contentEquals("t18")) {
    	//    		FileUtils.writeStringToFile("/home/dsladmin/EquationsAndQueries/metadata_paper_relation_summaries/tempDumpJson_"+relName+".json",relationDump.toString() );
    	//		///System.out.println(relationDump);
    	//}
    	//else continue;
    		

		PostgresVConfig.loadDataForRegionVolumeComputation(relName);
		
    	FileWriter fw = null;
        try {
            fw = new FileWriter(PostgresVConfig.getProp(PostgresVConfig.Key.DEANONYMIZED_DATA_DUMP_LOCATION) + "_" + relName + ".txt");      	  			
        }catch (IOException ex) {
            throw new RuntimeException("Unable to open file " + relName, ex);
        }
    	
    	JSONArray fkRangeArrayListObj = (JSONArray) relationDump.get("fkRangeArrayList");
    	JSONArray tableNonKeysObj = relationDump.getJSONArray("tableNonKeys");
    	//JSONArray viewNonKeysObj = relationDump.getJSONArray("viewNonKeys");
    	//JSONArray usefulTableNonKeysObj = relationDump.getJSONArray("usefulTableNonKeys");
    	
    	List<List<Long>> fkRangeArrayList = new ArrayList<>();
    	//JSONArray viewNonKeyIdxObj = (JSONArray) relationDump.get("viewNonKeyIdx");// viewNonKeyIdx);
    	JSONArray usableTableNonKeysObj = (JSONArray) relationDump.get("usableTableNonKeys");// viewNonKeyIdx);

    	//List<String> viewNonKeys = new ArrayList<String>();
    	
    	
    	
    	List<String> tableNonKeys = new ArrayList<String>();
    	//List<String> usefulTableNonKeys = new ArrayList<String>();
    	//List<Integer> viewNonKeyIdx = new ArrayList<Integer>();
    	Set<String> usableTableNonKeys = new HashSet<String>();

    	for(int i = 0 ; i < tableNonKeysObj.length() ; i++){
    		tableNonKeys.add((String) tableNonKeysObj.get(i));//.getString("interestKey"));
    	}

    				
    	
    	//for(int i = 0 ; i < viewNonKeysObj.length() ; i++){
    	//	viewNonKeys.add((String) viewNonKeysObj.get(i));//.getString("interestKey"));
    	//}
    	
    	//for(int i = 0 ; i < viewNonKeyIdxObj.length() ; i++){
    	//	viewNonKeyIdx.add(viewNonKeyIdxObj.getInt(i));//.getString("interestKey"));
    	//}
    	
    	for(int i = 0 ; i < usableTableNonKeysObj.length() ; i++){
    		usableTableNonKeys.add(usableTableNonKeysObj.getString(i));//.getString("interestKey"));
    	}
    	
    	
    	 List<String> sortedBucketsToColumnNameMapping = new ArrayList<String>(tableNonKeys);//viewNonKeys);
         Collections.sort(sortedBucketsToColumnNameMapping, new CustomCollator());
   	  
       List<String> sortedUseableKeys = new ArrayList<>();
			
			for(String s : usableTableNonKeys)
				sortedUseableKeys.add(s);
			Collections.sort(sortedUseableKeys, new CustomCollator());
			
			
			System.out.println("All useable keys for " + relName);

			for(String s : usableTableNonKeys) {
				String dataType = PostgresVConfig.dataTypesForAllAnonymizedCols.get(s);
				if(dataType.equals("integer") || dataType.equals("numeric") ) {
					System.out.println(s);
				}
			}
			
    	for(int j = 0 ; j < fkRangeArrayListObj.length() ; j++){
    		
    		JSONArray currentPKList = fkRangeArrayListObj.getJSONArray(j);
    		
    		List<Long> currentFkRangeArrayListElements = new ArrayList<>();
    		
    		//add all elements
    		for(int i = 0 ; i < currentPKList.length() ; i++){
    			currentFkRangeArrayListElements.add(currentPKList.getLong(i));//.getString("interestKey"));
        	}
        	
    		
    		fkRangeArrayList.add(currentFkRangeArrayListElements);
    	}
    	
    	
    	List<Long> pkRanges = new ArrayList<Long>();
    	
    	JSONArray relationPKRangeArray = relationDump.getJSONArray("relationPKRangeArray");
    	
    	for(int j=0; j< relationPKRangeArray.length();j++) {
    		 pkRanges.add(relationPKRangeArray.getLong(j));
    	}
    	
    	List<String> regionsList = FileUtils.readLines(PostgresVConfig.getProp(Key.DATABASESUMMARY_LOCATION) + "/" + relName + "_regions", PostgresVConfig.REGION_COUNT_INDEX);
		
		//JSONArray regionsArray = (JSONArray) relationDump.get("regions");		
    	//int regionsListLength = new File("/home/dsladmin/multi-query-workspace/codd-data-gen/resources/cdgvendor/output/postgres/" + CURRENT_CONTEXT + "/"+relName+"/allRegions").list().length;

		JSONObject obj = new JSONObject();
		

		
		//Object object22=null;
		//try {
		//	object22 = new JSONParser().parse(new FileReader("/home/dsladmin/multi-query-workspace/codd-data-gen/resources/cdgvendor/input/postgres/anonymizedschema.info"));//"/home/dsladmin/sqlqueries/temp/anonymizedschema.info"));///home/dsladmin/TODI/ws_kk/codd-data-gen/resources/cdgvendor/input/postgres/anonymizedschema.info"));
		//} catch (IOException | ParseException e) {
			// TODO Auto-generated catch block
		//	e.printStackTrace();
		//} 
		
		//JSONObject anonymizedschema = (JSONObject) object22;
        
        // typecasting obj to JSONObject 
        //JSONObject jo = (JSONObject) obj; 
        
		
		//Map<String, Map<String, IntList>> allBucketFloors= (Map<String, Map<String, IntList>>) FileUtils.readObjectFromFile("/home/dsladmin/EquationsAndQueries/BucketFloorsByColumns.dat");

		//Map<String, Map<String, IntList>> allBucketFloors= (Map<String, Map<String, IntList>>) FileUtils.readObjectFromFile("/home/dsladmin/multi-query-workspace/codd-data-gen/resources/cdgvendor/input/postgres/BucketFloorsByColumns.dat");
		
		//if(!(relName.equals("t04") || relName.equals("t05"))) continue;
		
		//Map<String, String> minMap = new HashMap<String, String>();
		
		//for(String tableNonKey : tableNonKeys){
		//	String minVal = "";//QueryToExplainAnalyzePostgres.getMinValForThisAttributeFromDB(tableNonKey).strip();
		//	minMap.put(tableNonKey,minVal);
		//}
		
		int totalRegions =  regionsList.size();//regionsListLength;//regionsArray.length();
         
        long pkCounter = 0;
		 
        ConcurrentHashMap<Integer, List<String>> CollectAllData = new ConcurrentHashMap<>();
 		
         //List<Future<List<String>>> allFutures = new ArrayList<Future<List<String>>>();
         
		for(int regionIdentifier=0; regionIdentifier<totalRegions; regionIdentifier++) {
			
			JSONObject currentRegion = new JSONObject(new String(FileUtils.readFileToString(PostgresVConfig.getProp(Key.DATABASESUMMARY_LOCATION) + "/" + relName + "_regions/region_" + (regionIdentifier+1) + ".json"))); 
    		
    	Region originalRegion = new Region();
		String regionName = currentRegion.getString("regionName");

		JSONArray BSArray = (JSONArray) currentRegion.get("BucketStructures");
		
		long regionCardinality = currentRegion.getLong("regionCardinality");

		List<ArrayList<Integer>> fkeysList = new ArrayList<>();
		
		JSONArray fkeysListObj = (JSONArray) currentRegion.get("fkeysList");
		
		
		for(int j2 = 0 ; j2 < fkeysListObj.length() ; j2++){
    		
    		JSONArray currentPKList2 = fkeysListObj.getJSONArray(j2);
    		
    		ArrayList<Integer> currentFkRangeArrayListElements2 = new ArrayList<>();
    		
    		//add all elements
    		for(int i = 0 ; i < currentPKList2.length() ; i++){
    			currentFkRangeArrayListElements2.add(currentPKList2.getInt(i));//.getString("interestKey"));
        	}
        	
    		
    		fkeysList.add(currentFkRangeArrayListElements2);
    	}
    	
		for(int k=0; k<BSArray.length(); k++) {
				
				BucketStructure newBS = new BucketStructure();
				
				JSONArray bucketArray = BSArray.getJSONArray(k);
				
				for(int l=0; l<bucketArray.length(); l++) {

					
					Bucket newBucket = new Bucket();
					
					JSONArray bucketValListArray = bucketArray.getJSONArray(l);
					
					for(int m=0; m<bucketValListArray.length(); m++)
					newBucket.add(bucketValListArray.getInt(m));
		    		//add all elements

					newBS.add(newBucket);						
				}
				
				originalRegion.add(newBS);
				
			}  
		
		
		System.out.println("\nGenerating tuples for : "+ relName  + " , Doing for region number : "+ regionIdentifier + " / " + totalRegions  + " card : " + regionCardinality);//) + "  viewNonKeys:" + viewNonKeys + "\ntableNonKeys : " + tableNonKeys + "\nfkeysList : " + fkeysList.size() + " fkeysList.size() : " + fkeysList.size() + "\n");
		
		int fkOffset = fkeysList.size(); 
		Calendar calender = Calendar.getInstance();
        calender.set(1990, 1, 1);
        int dateOffset = 10; //Date diff from 1 Jan 1900 till 26 Sep 2020
      
        List<Integer> bucketStructureCardinalityList = new ArrayList<Integer>();
		
        
        VolumeCompute volcomp =  new VolumeCompute(originalRegion, sortedBucketsToColumnNameMapping,
    			sortedUseableKeys, fkeysList, fkRangeArrayList,
    			bucketStructureCardinalityList, tableNonKeys, pkRanges,
    			PostgresVConfig.minValsForAllAnonymizedCols, PostgresVConfig.bucketFloorColumnViewWise, relName, regionName, regionCardinality, fkOffset, regionIdentifier, dateOffset,
    			usableTableNonKeys, PostgresVConfig.reverseNumberAnonyMap, PostgresVConfig.reverseStringAnonyMap, 
    			PostgresVConfig.reverseDateAnonyMap, calender, fw);
        
        Region volumeRegion = volcomp.calculateVolumeForRegion();
        volcomp.accumulateRegion(volumeRegion);
        
        //newVVP.setRegionValuesToComputeVolume(newVVP.getVariable().calculateVolumeForRegion(relName, sortedBucketsToColumnNameMapping, usableTableNonKeys, reverseNumberMap, reverseStringMap, reverseDateMap, minMaxOfAllCols, allBucketFloors, anonymizedschema));
		
		///newVVP.getRegionValuesToComputeVolume().accumulate();
    	
    	//newVVP.getRegionValuesToComputeVolume().createNewRegionWithValuesDistributedAccordingToProbability(newRegion, relName,  sortedBucketsToColumnNameMapping, 
    			//sortedUseableKeys, allBucketFloors, regionName, newVVP.getRowcount(), fkeysList,  fkRangeArrayList, bucketStructureCardinalityList,	
    			//minMap, tableNonKeys, fkOffset, pkRanges, regionIdentifier,		calender, dateOffset, usableTableNonKeys, reverseNumberMap,		reverseStringMap,reverseDateMap, anonymizedschema, fw);
    	
    	
		
        DataGeneratorRandomized dgrm =  new DataGeneratorRandomized(originalRegion, relName, regionName, regionCardinality,
		fkOffset, dateOffset, regionIdentifier, calender, usableTableNonKeys, sortedBucketsToColumnNameMapping, sortedUseableKeys,
		fkeysList, fkRangeArrayList, bucketStructureCardinalityList, tableNonKeys, pkRanges, PostgresVConfig.bucketFloorColumnViewWise, PostgresVConfig.minValsForAllAnonymizedCols,
		PostgresVConfig.reverseNumberAnonyMap, PostgresVConfig.reverseStringAnonyMap, PostgresVConfig.reverseDateAnonyMap, fw);
        
		dgrm.createNewRegionWithValuesDistributedAccordingToProbability(volumeRegion);
        
        
		long heapFreeSize = Runtime.getRuntime().freeMemory();

		if(heapFreeSize < 35000000000L)
			System.gc();
		
		
 		
 		service.shutdown();
 		} //UNCOMMENT THIS FOR WHOLE DB SUMMARY
		try {
			fw.close();
        } catch (Exception ex2) {}
        //} 
		
    	}
    }
    
	
	//TO BE DELETED

	public DataGenerator(Map<String, String> minMap, List<String> tableNonKeys,
			List<ArrayList<Integer>> fkeysList, List<List<Long>> fkRangeArrayList, List<Long> pkRanges,
			Set<String> usableTableNonKeys, Region newRegion, int regionCardinality, String relName, String regionName,
			HashMap<String, Int2DoubleOpenHashMap> reverseNumberMap,
			HashMap<String, Int2ObjectOpenHashMap<String>> reverseStringMap,
			HashMap<String, Int2ObjectOpenHashMap<Date>> reverseDateMap, int regionIdentifier,
			ConcurrentHashMap<Integer, List<String>> collectAllData, Map<String, Map<String, IntList>> allBucketFloors,
			List<String> sortedBucketsToColumnNameMapping, List<String> sortedUseableKeys, JSONObject anonymizedschema,
			FileWriter fw) {
		// TODO Auto-generated constructor stub
		
		
		
				

			//System.out.println("New Region " + relName + "  "+ newRegion);
			
			//if(!relName.equals("t17") && !relName.equals("t16") && !relName.equals("t02") && !relName.equals("t12") && !relName.equals("t15")) {
			 
			//if(!relName.equals("t07")) continue;
			//System.out.println("View non keys " + viewNonKeys);
			
			//if(relName.equals("RAJKUMAR SANTHANAM")){   // && !relName.equals("t17") ) {
			
			List<Integer> bucketStructureCardinalityList = new ArrayList<Integer>();
			
			
			// List<String> sortedBucketsToColumnNameMapping = new ArrayList<String>(tableNonKeys);//viewNonKeys);
	        // Collections.sort(sortedBucketsToColumnNameMapping, new CustomCollator());
	   	     
	        Map<String, Pair<String, String>> minMaxOfAllCols = null;//QueryToExplainAnalyzePostgres.fetchMinMaxForAttributes(tableNonKeys);//viewNonKeys);
	            
			VariableValuePair newVVP = new VariableValuePair(newRegion, regionCardinality);
			//RAJKUMAR ADDED THIS CODE FOR TUPLE GENERATION FOR DATABASE SUMMARY FILE.
	        	//System.out.println("Current REgion " + relName + " " + r);
			
			//System.out.println("Point 1");
			
			//Takes a anonymized region as input, and gives a new region containing de-anonymized values corresponding to each of the bucket of the anonymized region.
			//newVVP.variable now contains original anonymized region from the relation summary
			//newVVP.RegionValuesToComputeVolume contains deanonymized region from the relation summary
			
			
			
			
			//newVVP.setRegionValuesToComputeVolume(newVVP.getVariable().calculateVolumeForRegion(relName, sortedBucketsToColumnNameMapping, usableTableNonKeys, reverseNumberMap, reverseStringMap, reverseDateMap, minMaxOfAllCols, allBucketFloors, anonymizedschema));
			
			
			
			
			//long heapFreeSize = Runtime.getRuntime().freeMemory();

			//if(heapFreeSize < 10000000000L)
	 		//System.gc();
			
	 		//System.out.println("1");
			//Takes the deanonymized region containing deanonymized values of buckets and then adds them up at bucket and bucketStructure level to populate volume values.
			//Bucket level => values are added, and returned to parent bucketstructure and stored in a list. So a Buketstructure will have a arraylist of volumes of its buckets
			//Bucket structure level => values across buckets are multiplied and returned to parent region and stored in a list.  So a Region will have a arraylist of volumes of its Buketst						//newVVP.RegionValuesToComputeVolume contains deanonymized region from the relation summary
			//System.out.println("Point 2");
			
			//newVVP.RegionValuesToComputeVolume.bucketStructureVolumes contains individual bucketStructure volumes of deanonymized vvp.RegionValuesToComputeVolume
			
			
			
			
			
			
			
			//newVVP.getRegionValuesToComputeVolume().accumulate();
			
			
			
			
			
			
			
			
			
			
			
			//System.out.println("2");
			
			//heapFreeSize = Runtime.getRuntime().freeMemory();

			//if(heapFreeSize < 10000000000L)
	 		//System.gc();

	 		
			//List<String> sortedUseableKeys = new ArrayList<>();
			
			//for(String s : usableTableNonKeys)
			//	sortedUseableKeys.add(s);
			//Collections.sort(sortedUseableKeys, new CustomCollator());
			
			//Map<String, Map<String, IntList>> allBucketFloors= (Map<String, Map<String, IntList>>) FileUtils.readObjectFromFile("/home/dsladmin/multi-query-workspace/codd-data-gen/resources/cdgvendor/input/postgres/BucketFloorsByColumns.dat");
			//System.out.println("Point 3");
			
			int fkOffset = fkeysList.size(); 
			Calendar calender = Calendar.getInstance();
	        calender.set(1990, 1, 1);
	        int dateOffset = 10; //Date diff from 1 Jan 1900 till 26 Sep 2020
	      
			
	    	//Region output = 
	    	
	    	
	        
	        
	        
	        
	        //newVVP.getRegionValuesToComputeVolume().createNewRegionWithValuesDistributedAccordingToProbability(newRegion, relName,  sortedBucketsToColumnNameMapping, 
	    	//		sortedUseableKeys, allBucketFloors, regionName, newVVP.getRowcount(), fkeysList,  fkRangeArrayList, bucketStructureCardinalityList,	
	    	//		minMap, tableNonKeys, fkOffset, pkRanges, regionIdentifier,			calender, dateOffset, usableTableNonKeys, reverseNumberMap,reverseStringMap,			reverseDateMap, anonymizedschema, fw);
	    	
	    	
	        
	        
	        
	        
	        
	        
	        
	        //System.out.println("Point 4");
			
	    	//heapFreeSize = Runtime.getRuntime().freeMemory();

			//if(heapFreeSize < 10000000000L)
	 		//System.gc();

			//System.out.println("3");
	    	//for(int mn=1; mn<bucketStructureCardinalityCumulativeList.size() ; mn++)
	    	//	bucketStructureCardinalityCumulativeList.set(mn, bucketStructureCardinalityCumulativeList.get(mn-1) + bucketStructureCardinalityCumulativeList.get(mn));
	    	//bucketStructureCardinalityCumulativeList.add((int) newVVP.getRowcount());
	    	
			//if(relName.equals("t13")) {
	    	//
	    	//	System.out.println("bucketStructureCardinalityCumulativeList" + bucketStructureCardinalityCumulativeList); 
			//	System.out.println("newRegion " + newRegion);
			//	//System.out.println("output " +output);
			//}
			
			//GENERATING DB SUMMARY FILE
			
			//long regionVolume = r.getVolume();
			//int num_of_bs = r.size();
			//int bs_counter = 0;
			//long sum_of_bsCardinality = 0;
			//List<Long> bsCardinalityList = new ArrayList<>();
			
			
			  
	        
				
	        
	        
	      	    
			 //System.out.println("jo_ : " + jo);
			
	        
			 Region output = new Region();
			 
			 //int fkOffset = fkeysList.size();
			
			     //long pkCounter = 0;
	                //for (ValueCombination valueCombination : viewSolution) {
	                //    for (long i = 0; i < valueCombination.getRowcount(); i++) {
	                //    }
	                //}
	      int bucketStructureCountCorrespondingToActualRegion = 0;
	      int rowCountOfThisBucketStructure = bucketStructureCardinalityList.get(0);
	      int bucketStructureCardinalityListPointer = 0;
	      
			 
	      //String allTuplesInThisRegion = "";
	      
	      List<String> allRowTuples  = new ArrayList<String>();
	      
	      Long startPkIndex = pkRanges.get(regionIdentifier);
	      
			for(BucketStructure b : output.getAll())
			{
				//pkCounter++;
				
				double rand = Math.random();
				
				while(rand==0.0 || rand==1.0) 
					rand = Math.random();
				
				
				rowCountOfThisBucketStructure--;
				
				if(rowCountOfThisBucketStructure<0) {
					bucketStructureCountCorrespondingToActualRegion++;
					bucketStructureCardinalityListPointer++;
					rowCountOfThisBucketStructure = bucketStructureCardinalityList.get(bucketStructureCardinalityListPointer);
				}
				
				int bs_counter = 0;
				 
				 int bucketCountCorrespondingToActualRegion = -1;

				 //if(pkCounter%10000==0)
				//		System.out.println("CURRENT BS " +  " " + relName + " " +pkCounter);
					
				//System.out.println("CURRENT BS " + b);
				
				//Region tempRegion = new Region();
				//tempRegion.add(b);
				//long tempRegionVolume = tempRegion.getVolume();
				//long bsCardinality = -1;
				//if(num_of_bs == bs_counter)
				//bsCardinality = vvp.rowcount - sum_of_bsCardinality;
				//else
				//bsCardinality = (long) (((tempRegionVolume*1.0)/regionVolume)* vvp.rowcount);
				//sum_of_bsCardinality += bsCardinality;
				//bsCardinalityList.add(bsCardinality);
				
				//System.out.println(relName + " " + "viewNonKeys " + viewNonKeys + "  \ntableNonKeys" + tableNonKeys  + "\n usableTableNonKeys :" + usableTableNonKeys );
				
				
				String rowTuple= String.valueOf(startPkIndex);
				//startPkIndex++;
				
				
				//ADDING FKEYS
				while(bs_counter < fkOffset) {
					
					Bucket y = b.at(bs_counter);//fkOffset + viewNonKeyIdx.get(c));
					bs_counter++;
					rowTuple = rowTuple + "," + String.valueOf(y.at(0));
					
					//continue;
				}
				//System.out.println("rowTuple " + relName + " : " +rowTuple);
				
				
				int c=0;
				//ArrayList<ArrayList<Integer>> bs_array = new ArrayList<>();
				for(String tableNonKey : tableNonKeys)
				{
					bucketCountCorrespondingToActualRegion++;
					
					String[] nameSplit = tableNonKey.split("_");	

					//org.json.simple.JSONObject ae = (org.json.simple.JSONObject) jo.get(nameSplit[0]); ////System.out.println("ae_ : " + ae);
					//org.json.simple.JSONObject bc = (org.json.simple.JSONObject) ae.get("columns");////System.out.println("b_ : " + b);
						
					//org.json.simple.JSONObject cd = (org.json.simple.JSONObject) bc.get(nameSplit[0] + "_" +nameSplit[1]);//anonymousTableAndColumnName); //System.out.println("c_ : " + c);
					//String colType = (String) cd.get("columnType"); ////System.out.println("d_ : " + dataType);
					
					
					String colType = PostgresVConfig.dataTypesForAllAnonymizedCols.get(nameSplit[0] + "_" + nameSplit[1]);//(String) cd.get("columnType"); ////System.out.println("d_ : " + dataType);
					
					//System.out.println("Col " + nameSplit[0] + "_" +nameSplit[1] + " : " + colType);
					
					
					//if(pkCounter%1000000==0)// || relName.contentEquals("t12"))
					//System.out.println(relName + " " + b.getAll() + " fkOffset:" +fkOffset + " \n"+ b.getAll().size() + " " + b);
					
					//ArrayList<Integer> columnBucket =  new ArrayList<>();
					//if(!viewNonKeyIdx.isEmpty() && c<viewNonKeyIdx.size() && viewNonKeys.get(viewNonKeyIdx.get(c)).contains(tableNonKey))
					if(usableTableNonKeys.contains(tableNonKey))
					{
						Bucket x = b.at(fkOffset + c);
						
						//String
						if(colType.equals("integer")) {// || colType.equals("numeric"))) {
							
						
							if(x.getValList().size()>0)	
								rowTuple = rowTuple + "," +  String.valueOf(x.at(0));
							else
								rowTuple = rowTuple + ","; //NULL ASSIGNMENT
								
								
									
							/*
						
							//if(x.getValList().size()>0)	
							if(x.getDeanonymizedTupleValueList()!=null && x.getDeanonymizedTupleValueList().size()>0)	
								rowTuple = rowTuple + "," +   String.valueOf(x.getDeanonymizedTupleValueList().get(0)); // String.valueOf(x.at(0));
							else
								rowTuple = rowTuple + ","; //NULL ASSIGNMENT
								
							*/
							
						}else if(colType.equals("numeric")) {
							
							//if(x.getValList().size()>0)	
								if(x.getDeanonymizedTupleValueList()!=null && x.getDeanonymizedTupleValueList().size()>0)	
									rowTuple = rowTuple + "," +   String.valueOf(x.getDeanonymizedTupleValueList().get(0)); // String.valueOf(x.at(0));
								else
									rowTuple = rowTuple + ","; //NULL ASSIGNMENT
									
							
						}
						else if(colType.startsWith("character")) {
								
							if(reverseStringMap.containsKey(tableNonKey)) {
								
								x = newRegion.at(bucketStructureCountCorrespondingToActualRegion).at(bucketCountCorrespondingToActualRegion);
								
								
								
								
								List<Integer> possibleValues = new ArrayList<Integer>();
								
								for(int t : x.getValList()) {
									if(t%2==0)
										possibleValues.add(t);
								}
								
								if(possibleValues.contains(0))
									possibleValues.remove(0);
								
								//System.out.println("Actual region bucket for string : " + possibleValues);
								
								
								//System.out.println("Chosen reverseStringMap " +  possibleValues + " " + reverseStringMap.get(tableNonKey));

								if(possibleValues.size()==0)
									rowTuple = rowTuple + ",\"\"";
								else if(possibleValues.size()==1) {
									rowTuple = rowTuple + "," + String.valueOf(reverseStringMap.get(tableNonKey).get(possibleValues.get(0)));
								
									//System.out.println("tableNonkey : "  + tableNonKey);
									//System.out.println("Chosen reverseStringMap.get(tableNonKey) (size 1) " +  possibleValues.get(0) + " " + reverseStringMap.get(tableNonKey).get(possibleValues.get(0)));
									
								}
								else {
									//System.out.println("tableNonkey : "  + tableNonKey);
									//System.out.println("reverseStringMap.get(tableNonKey)" + x.getValList() + " " +reverseStringMap.get(tableNonKey));
									
									int noOfEntriesInThisBucket = possibleValues.size();
									
									//double randomNumber = Math.random();
									//int chosenIndex = (int)(randomNumber * noOfEntriesInThisBucket);
									
									int chosenIndex = (int)(rand * noOfEntriesInThisBucket);
									
									rowTuple = rowTuple + "," + String.valueOf(reverseStringMap.get(tableNonKey).get(possibleValues.get(chosenIndex)));     
									//System.out.println("Chosen reverseStringMap.get(tableNonKey) (size n) " +chosenIndex + " "+ possibleValues.get(chosenIndex) + " " + reverseStringMap.get(tableNonKey).get(possibleValues.get(chosenIndex)));
									
								}
								
								/*
								if(x.getValList().size()==1 && x.getValList().get(0)==0)
									rowTuple = rowTuple + ",\"\"";//"," + String.valueOf(reverseStringMap.get(tableNonKey).get(2));
								else if(x.getValList().size()==1  && x.getValList().get(0)==1)
									rowTuple = rowTuple + "," + String.valueOf(reverseStringMap.get(tableNonKey).get(2));
								else {
									
									List<Integer> possibleValues = x.getValList();
									
									if(possibleValues.contains(0)) 
										possibleValues.remove(0);
									
									int noOfEntriesInThisBucket = possibleValues.size();
									
									double randomNumber = Math.random();
								
									int chosenIndex = (int)(randomNumber * noOfEntriesInThisBucket);
									
									rowTuple = rowTuple + "," + String.valueOf(reverseStringMap.get(tableNonKey).get(possibleValues.get(chosenIndex)));     
								}*/
								
								
							}else
								rowTuple = rowTuple + ",\"\"";
								
						}else if(colType.equals("date")) {
							
							if(reverseDateMap.containsKey(tableNonKey)) {
								
								x = newRegion.at(bucketStructureCountCorrespondingToActualRegion).at(bucketCountCorrespondingToActualRegion);
								
								
								//System.err.println("x " +  x);
								
								List<Integer> possibleValues = new ArrayList<Integer>();
								
								for(int t : x.getValList()) {
									if(t%2==0)
										possibleValues.add(t);
								}
								
								//System.err.println("possibleValues " +  possibleValues);
								
								//if(x.contains(74) || x.contains(76) ||x.contains(78) ||x.contains(80) ||x.contains(82) || x.contains(75) || x.contains(77) ||x.contains(79) ||x.contains(81) ||x.contains(82)) {
								//	System.out.println("possibleValues " +  possibleValues + " " + regionCardinality);
								//	System.out.println("x " +  x + " " + regionCardinality);
								//}
								
								if(possibleValues.contains(0))
									possibleValues.remove(0);
								
								//System.out.println("Chosen reverseDateMap.get(tableNonKey) (size 1) " +  possibleValues + " " + " " + reverseDateMap.get(tableNonKey));
								
								
								if(possibleValues.size()==0) {
									rowTuple = rowTuple + "," + String.valueOf(calender.getTime());
								
									//System.out.println("No vals found for date");
									
								}else if(possibleValues.size()==1) {
									
									int valChosen = possibleValues.get(0);
									
									//if(valChosen%2==1 && reverseDateMap.get(tableNonKey).get(valChosen-1)==null) {
									//	System.err.println("tbl " + tableNonKey + " " + (valChosen-1)+ " " +reverseDateMap.get(tableNonKey).get(valChosen-1));
									//	throw new RuntimeException("stop");
									//}
									
									if(valChosen%2==1) {
										rowTuple = rowTuple + "," + String.valueOf(reverseDateMap.get(tableNonKey).get(valChosen-1));     
										
									}else
										rowTuple = rowTuple + "," + String.valueOf(reverseDateMap.get(tableNonKey).get(valChosen));     
									
									
									
									//rowTuple = rowTuple + "," + String.valueOf(reverseDateMap.get(tableNonKey).get(possibleValues.get(0)));
									
								}
								else {

									int noOfEntriesInThisBucket = possibleValues.size();
									
									//double randomNumber = Math.random();
									//int chosenIndex = (int)(randomNumber * noOfEntriesInThisBucket);
									
									int chosenIndex = (int)(rand * noOfEntriesInThisBucket);
									
									int valChosen = possibleValues.get(chosenIndex);
									
									//if(valChosen%2==1 && reverseDateMap.get(tableNonKey).get(valChosen-1)==null) {
									//	System.err.println("tbl " + tableNonKey + " " + (valChosen-1)+ " " +reverseDateMap.get(tableNonKey).get(valChosen-1));
									//	throw new RuntimeException("stop");
									//}
									
									if(valChosen%2==1) {
										rowTuple = rowTuple + "," + String.valueOf(reverseDateMap.get(tableNonKey).get(valChosen-1));     
										
									}else
										rowTuple = rowTuple + "," + String.valueOf(reverseDateMap.get(tableNonKey).get(valChosen));     
									
									
									//rowTuple = rowTuple + "," + String.valueOf(reverseDateMap.get(tableNonKey).get(possibleValues.get(chosenIndex)));     
									
								}
								
								/*
								
								if(x.getValList().size()==1)
									rowTuple = rowTuple + "," + String.valueOf(reverseDateMap.get(tableNonKey).get(2));
								else {
									
									List<Integer> possibleValues = x.getValList();
									
									if(possibleValues.contains(0)) 
										possibleValues.remove(0);
									
									int noOfEntriesInThisBucket = possibleValues.size();
									
									double randomNumber = Math.random();
								
									int chosenIndex = (int)(randomNumber * noOfEntriesInThisBucket);
									
									rowTuple = rowTuple + "," + String.valueOf(reverseDateMap.get(tableNonKey).get(possibleValues.get(chosenIndex)));     
								
								}
								*/
								
								//if(rowTuple.contains("null"))
								//	System.err.println("culprit here");
								
							}else				
								rowTuple = rowTuple + "," + String.valueOf(calender.getTime());
						}else { //INTEGER
							
							System.out.println("Here : " + colType);
							
							if(x.getValList().size()>0) {						
								rowTuple = rowTuple + "," +   String.valueOf(x.getValList());
								System.out.println("BucketVal " + x);
							}else
								rowTuple = rowTuple + ","; //NULL ASSIGNMENT
							
							
							
							if(x.getDeanonymizedTupleValueList()!=null && x.getDeanonymizedTupleValueList().size()>0) {	
								rowTuple = rowTuple + "," +   String.valueOf(x.getDeanonymizedTupleValueList().get(0)); // String.valueOf(x.at(0));
								System.out.println("BucketVal " + x.getDeanonymizedTupleValueList());
								
							}else
								rowTuple = rowTuple + ","; //NULL ASSIGNMENT
							
							
						}
							
						
						//columnBucket.addAll(x.getAll());
						
						c++;
					}
					else
					{
						//Date
						if(colType.equals("date")) {
							
							//double random2 = Math.random();
							//int randomOffset = (int)(random2 * dateOffset);
						    
						    MutableInt noOfLeapDaysCounter = new MutableInt(0);
						    
						    int randomOffset = (int)(rand * dateOffset);
						    
						    
							
							rowTuple = rowTuple + "," + String.valueOf(getDateAfterManyDays(calender, calender.getTime(), randomOffset ,noOfLeapDaysCounter));//calender.getTime());
						
							//if(rowTuple.contains("null"))
							//	System.err.println("culprit here 2");
						}else if(colType.startsWith("character")) {
							
							

							//String minVal = QueryToExplainAnalyzePostgres.getMinValForThisAttributeFromDB(tableNonKey).strip();
							
							//double random2 = String.valueOf(Math.random()).substring(1,minMap.get(tableNonKey).length());
							//int ran = (int) (random2);
							
							//String rando = String.valueOf(Math.random()).substring(2);
							String rando = String.valueOf(rand).substring(2);
							
							
							rowTuple = rowTuple + "," + rando.substring(0,Math.min(rando.length(), minMap.get(tableNonKey).length()));//String.valueOf((ran));
							
							//System.out.println(rando.substring(0,Math.min(rando.length(), minMap.get(tableNonKey).length())));
							//rowTuple = rowTuple + ",\"\"";// + String.valueOf(x.at(0));
						}else {
							
							//double random2 = Math.random() * 1000;
							//int ran = (int) (random2);
							
							//int ran = (int) (random2);
							rowTuple = rowTuple + "," + String.valueOf((rand*1000));
							
							
							//rowTuple = rowTuple + ",0";// + String.valueOf(x.at(0));
						}
						
						
					}
					//bs_array.add(columnBucket);
				}
				
				
				//if(pkCounter%1000000==0)
				//System.out.println("rowTuple " + relName + "  "+ rowTuple);
				
				//allTuplesInThisRegion = allTuplesInThisRegion + rowTuple + "\n";
				//fw.write(rowTuple + "\n");
				//tableNonKeysList.add(bs_array);
				
				
				//allRowTuples.add(rowTuple);
				try {
					fw.write(rowTuple + "\n");
				} catch (IOException e) {
					// TODO Auto-generated catch block
					e.printStackTrace();
				}
				
						
								//for(String s : result)
				//try {
				
				//} catch (IOException e) {
								// TODO Auto-generated catch block
				//	e.printStackTrace();
				//}
							
				//CollectAllData.put(regionIdentifier, allRowTuples);
				//long heapFreeSize = Runtime.getRuntime().freeMemory();

				//if(heapFreeSize < 30000000000L)
		 		
			}
			
			
			//System.gc();	
			
		
	}



	private static Date getDateAfterManyDays(Calendar calender, Date date, int n, MutableInt noOfLeapDaysCounter) {
    	
		//System.out.println("Days offset " + n);
		//System.out.println("Date " + date);
		
		
		calender.setTime(date);
    	calender.add(Calendar.DATE, n + noOfLeapDaysCounter.intValue());  // number of days to add
    	
    	//System.out.println(calender.getTime());
    	//System.out.println(calender.getTime().getMonth() + " " + calender.getTime().getDate() );
    	
    	//THERE IS A LEAP YEAR BUG, IT DOESNT CALCULATE LEAP YEARS WRONGLY, AND HENCE POSTGRES THROWS ERROR LIKE 
    	//ERROR:  date/time field value out of range: "Tue Feb 29 22:12:23 IST 2021"
    	if(calender.getTime().getMonth()==1 && calender.getTime().getDate()==29) {
    		noOfLeapDaysCounter.increment();// = noOfLeapDaysCounter + 1;
    		
    		calender.setTime(date);
        	calender.add(Calendar.DATE, n + noOfLeapDaysCounter.intValue());
    	}
		return calender.getTime();
	}
	
}