package in.ac.iisc.cds.dsl.cdgvendor.solver;

import java.io.BufferedWriter;
import java.io.File;
import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.FileReader;
import java.io.FileWriter;
import java.io.IOException;
import java.io.ObjectInputStream;
import java.io.ObjectOutputStream;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.Date;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import in.ac.iisc.cds.dsl.cdgvendor.constants.Constants;
import in.ac.iisc.cds.dsl.cdgvendor.constants.PostgresVConfig;
import in.ac.iisc.cds.dsl.cdgvendor.model.Alqp;
import in.ac.iisc.cds.dsl.cdgvendor.model.ColumnPathInfo;
import in.ac.iisc.cds.dsl.cdgvendor.reducer.Bucket;
import in.ac.iisc.cds.dsl.cdgvendor.reducer.BucketStructure;
import in.ac.iisc.cds.dsl.cdgvendor.reducer.Partition;
import in.ac.iisc.cds.dsl.cdgvendor.reducer.Region;
import in.ac.iisc.cds.dsl.cdgvendor.solver.DoubleReductionBasedViewSolver;
import in.ac.iisc.cds.dsl.cdgvendor.utils.CustomCollator;
import in.ac.iisc.cds.dsl.cdgvendor.utils.FileUtils;
import in.ac.iisc.cds.dsl.cdgclient.constants.PostgresCConfig;
import in.ac.iisc.cds.dsl.cdgclient.constants.PostgresCConfig.Key;
import in.ac.iisc.cds.dsl.cdgclient.preprocess.DDLGenerator;
import in.ac.iisc.cds.dsl.cdgclient.preprocess.ExplainAnalyzeToAlqpPostgres;
import in.ac.iisc.cds.dsl.cdgclient.preprocess.QueryToExplainAnalyzePostgres;
import it.unimi.dsi.fastutil.doubles.Double2IntFunction;
import it.unimi.dsi.fastutil.doubles.Double2IntMap;
import it.unimi.dsi.fastutil.doubles.Double2IntOpenHashMap;
import it.unimi.dsi.fastutil.doubles.DoubleArrayList;
import it.unimi.dsi.fastutil.doubles.DoubleList;
import it.unimi.dsi.fastutil.doubles.DoubleOpenHashSet;
import it.unimi.dsi.fastutil.ints.Int2DoubleMap;
import it.unimi.dsi.fastutil.ints.Int2DoubleOpenHashMap;
import it.unimi.dsi.fastutil.ints.Int2ObjectMap;
import it.unimi.dsi.fastutil.ints.Int2ObjectOpenHashMap;
import it.unimi.dsi.fastutil.ints.IntList;
import it.unimi.dsi.fastutil.objects.Object2IntMap;
import it.unimi.dsi.fastutil.objects.ObjectSet;

import org.jgrapht.graph.DefaultDirectedGraph;
import org.jgrapht.graph.DefaultEdge;
import org.json.simple.JSONArray; 
import org.json.simple.JSONObject;
import org.json.simple.parser.*; 


public class GenerateQueryForRegions {

	public static List<Integer> getQueriesCorrespondingToDisjointRegions(String viewname, Set<String> allColumnsFromAllCliques, List<String> bucketsToColumnNameMapping,
			Map<String, IntList> bucketFloorsByColumns, Partition partition, BufferedWriter writer2) {
		// TODO Auto-generated method stub
		
		List<Integer> estimateList = new ArrayList<Integer>();
		
		Map<String, String> reverseColumnsMap = PostgresVConfig.reverseColumnAnonyMap;
		Map<String, String> reverseTablesMap = PostgresVConfig.reverseTableAnonyMap;
		

		Map<String, Int2DoubleMap> reverseNumberAnonyMap = PostgresVConfig.reverseNumberAnonyMap;
		//Map<String, Object2IntMap<Date>> reverseDateMap = new HashMap<>();
		Map<String, Int2ObjectMap<Date>> reverseDateAnonyMap = PostgresVConfig.reverseDateAnonyMap;
		//Map<String, Object2IntMap<String>> reverseStringMap = new HashMap<>();
		Map<String, Int2ObjectMap<String>> reverseStringAnonyMap = PostgresVConfig.reverseStringAnonyMap;
		 
		//@SuppressWarnings("unchecked")
		//Map<String, String> temp1 = (Map<String, String>)readObjectFromFile(PostgresCConfig.getProp(Key.ANONYMIZED_TABLE_MAP_LOCATION) + Constants.PATH_SEPARATOR + Constants.TABLE_MAP_FILENAME);//"/home/dsladmin/TablesMap.dat");
	    
		//@SuppressWarnings("unchecked")
		//Map<String, String> temp2 = (Map<String, String>)readObjectFromFile(PostgresCConfig.getProp(Key.ANONYMIZED_COLUMN_MAP_LOCATION) + Constants.PATH_SEPARATOR + Constants.COLUMN_MAP_FILENAME);//"/home/dsladmin/ColumnsMap.dat");

		//System.out.println("Buluk buluk 1 ");
		
		
		
		Object obj=null;
		//obj = readObjectFromFile(PostgresCConfig.getProp(Key.ANONYMIZEDSCHEMA_TARGETFILE));//PostgresCConfig.getProp(Key.ANONYMIZED_COLUMN_MAP_LOCATION) + Constants.PATH_SEPARATOR + Constants.COLUMN_MAP_FILENAME);//"/home/dsladmin/ColumnsMap.dat");
		
		
		try {
			obj = new JSONParser().parse(new FileReader(PostgresCConfig.getProp(PostgresCConfig.Key.ANONYMIZEDSCHEMA_TARGETFILE)));//"/home/dsladmin/sqlqueries/temp/anonymizedschema.info"));///home/dsladmin/TODI/ws_kk/codd-data-gen/resources/cdgvendor/input/postgres/anonymizedschema.info"));
		
			
		} catch (IOException | ParseException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		} 
		
        
        // typecasting obj to JSONObject 
        JSONObject jo = (JSONObject) obj; 
          

		//System.out.println("Buluk buluk 2 ");
              
    	//System.out.println("size of tablemap " + temp1.size());
    	//System.out.println("size of columnmap " + temp2.size());

             
	     //for (Entry<String, String> entry1 : temp1.entrySet()) {
	     //	reverseTablesMap.put(entry1.getValue(), entry1.getKey());
	    	//System.out.println(entry1.getValue() + " : " +   entry1.getKey());
	     //}
		   
		
	     //for (Entry<String, String> entry2 : temp2.entrySet()) {
		  //  	reverseColumnsMap.put(entry2.getValue(), entry2.getKey());
		//    	//System.out.println(entry2.getValue() + " : " +   entry2.getKey());
	     //}
	     
	     
	     Collections.sort(bucketsToColumnNameMapping, new CustomCollator());
	     
	     
	     //System.out.println("bucketsToColumnNameMapping"+ bucketsToColumnNameMapping);
	     /*
	     reverseNumberMap =  Anonymizer.value121.shownValuesByNumberColumns;  //Visibility of class was made "package" for this, and the actual Value121 value121 "private" is made publi static 
	     reverseDateMap = Anonymizer.value121.shownValuesByDateColumns;
	     reverseStringMap = Anonymizer.value121.shownValuesByStringColumns;
	     

			//System.out.println("Buluk buluk 3 ");
	     

	     for (Entry<String, Double2IntMap> entry : reverseNumberMap.entrySet()) {
	            String columnname = entry.getKey();
	            Double2IntMap doubleList = entry.getValue();
	            
	            Int2DoubleMap a = new Int2DoubleOpenHashMap();
	            
             for (Entry<Double, Integer> entry2 : doubleList.entrySet())
             {
             	Double val1 = entry2.getKey();
 	            Integer val2 = entry2.getValue();
                 a.put(val2,val1);
             }
             reverseNumberAnonyMap.put(columnname, a);
             
	     }     
	     
	     for (Entry<String, Object2IntMap<Date>> entry : reverseDateMap.entrySet()) {
	            String columnname = entry.getKey();
	            Object2IntMap<Date> dateList = entry.getValue();
	            
	            Int2ObjectMap<Date> a = new Int2ObjectOpenHashMap<Date>();
	            
             for (Entry<Date, Integer> entry2 : dateList.entrySet())
             {
             	Date val1 = entry2.getKey();
 	            Integer val2 = entry2.getValue();
                 a.put(val2,val1);
             }
             reverseDateAnonyMap.put(columnname, a);
             
	     }     

	     for (Entry<String, Object2IntMap<String>> entry : reverseStringMap.entrySet()) {
	            String columnname = entry.getKey();
	            Object2IntMap<String> stringList = entry.getValue();
	            
	            Int2ObjectMap<String> a = new Int2ObjectOpenHashMap<String>();
	            
          for (Entry<String, Integer> entry2 : stringList.entrySet())
          {
        	  String val1 = entry2.getKey();
	            Integer val2 = entry2.getValue();
              a.put(val2,val1);
          }
          reverseStringAnonyMap.put(columnname, a);
          
	     }     

	     */
	    String originalViewName = reverseTablesMap.get(viewname);
	    boolean viewAlreadyThere = false;	  
	     
	//    System.out.println("reverseTablesMap"+ reverseTablesMap);
	//    System.out.println("reverseColumnsMap" + reverseColumnsMap);
	//   System.out.println("reverseNumberMap" + reverseNumberMap);
	//   System.out.println("reverseDateMap" + reverseDateMap);
	//   System.out.println("reverseStringMap" + reverseStringMap);

		
	 /*   BufferedWriter  writer = null;
	    try {
			writer = new BufferedWriter(new FileWriter("/home/dsladmin/FinalQueries.txt", true));
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
	        */
	    
  	    
  	  BufferedWriter writer3 = null;
	    
	
	    

		//System.out.println("Buluk buluk 4 "+ originalViewName );
	    
	    
  	  
  	  //NOTE ADDED WHILE METADATA PAPER : This stores tablewise columns used in all the cliques put together in this View
	    Map<String, List<String>> allTableAndColumnNameList = new HashMap<>();
	    
	    
		 for(String tableNameAndColumnName : allColumnsFromAllCliques){
					    	
		    String[] nameSplit = tableNameAndColumnName.split("_");	
		    
		    
		    if(viewname.equals(nameSplit[0]))
				viewAlreadyThere=true;
			
			
		    List<String> columnList = allTableAndColumnNameList.get(nameSplit[0]);
		    if (columnList == null)
		    {
		    	columnList = new ArrayList<String>();  
		    	columnList.add(nameSplit[1] + "_" + nameSplit[2]);		    	
		    	allTableAndColumnNameList.put(nameSplit[0], columnList);
		    }
		    else{
		    	columnList.add(nameSplit[1] + "_" + nameSplit[2]);
		    }
		 
		 }
		 
	    
		 
		 //System.out.println("Buluk buluk 4.01 ");
		    
		    
			
	   //  for (Entry<String, List<String>> entry : allTableAndColumnNameList.entrySet()) {
	    	 

	            
	    //	   String anonymousTableName = entry.getKey();
	    //        List<String> columnList = entry.getValue();
	    //        
	  	         //   for(String anonymousColumnName : columnList) {
	      
	  	            	// System.out.println("Check check : " + anonymousTableName + "_" + anonymousColumnName);
	          //  }
	            
	  //   }
	
		 
		    
		/*	
			String originalTableName = reverseTablesMap.get(nameSplit[0]);
			String originalColumnName = reverseColumnsMap.get(tableNameAndColumnName);
			
			
			
			 //System.out.println("originalTableName : " + originalTableName);
			 //System.out.println("originalColumnName : " + originalColumnName);
			
		//	//System.out.println("jo_ : " + jo);
			
			JSONObject ae = (JSONObject) jo.get(nameSplit[0]); ////System.out.println("ae_ : " + ae);
			JSONObject b = (JSONObject) ae.get("columns");////System.out.println("b_ : " + b);
			JSONObject c = (JSONObject) b.get(tableNameAndColumnName);////System.out.println("c_ : " + c);
			String dataType = (String) c.get("columnType"); ////System.out.println("d_ : " + dataType);
			
           //System.out.println("dataType : " + dataType);

           Int2DoubleMap originalNumberMapping=null;
           Int2ObjectMap<Date> originalDateMapping=null;
           Int2ObjectMap<String> originalStringMapping=null;
           
       //    if(dataType.equals("date"))
	            originalDateMapping = reverseDateAnonyMap.get(tableNameAndColumnName);


        //   if(dataType.equals("integer") || dataType.contentEquals("numeric"))					            	
				  originalNumberMapping = reverseNumberAnonyMap.get(tableNameAndColumnName);
           
         //  if(dataType.equals("character") || dataType.contentEquals("character varying"))					            	
				  originalStringMapping = reverseStringAnonyMap.get(tableNameAndColumnName);


	
			
			//Hack
		//	Double leastValue = originalNumberMapping.get(2);
		//	Integer zero = 0;
		//	originalNumberMapping.put(zero,leastValue);
           
           
           //character varying
			
			
		    //System.out.println("originalTableName" + originalTableName);   
		    //System.out.println("originalColumnName" + originalColumnName);
		    //System.out.println("originalNumberMapping" + originalNumberMapping);
		    //System.out.println("originalDateMapping" + originalDateMapping);
		    //System.out.println("originalStringMapping" + originalStringMapping);
		    

			
			//IntList array = bucketFloorsByColumns.get(tableNameAndColumnName);
			//array.get(arg0)
			
			
		    ////System.out.println("array" + array);
			
			
			
			
			Integer weNeedToCheckAtThisIndex = bucketsToColumnNameMapping.indexOf(tableNameAndColumnName);
			
			
			 //System.out.println("weNeedToCheckAtThisIndex" + weNeedToCheckAtThisIndex);

			
			List<Integer> mappingIndex = bucketFloorsByColumns.get(tableNameAndColumnName);

			 //System.out.println("mappingIndex" + mappingIndex);

			
			Integer startIndex, endIndex, greaterThanEqualToPredicateValue, lesserThanPredicateValue;
			
		 
			String	lessThanSymbol = "<"; String greaterThanSymbol = ">"; 	String equalitySymbol = "=";
			

		 }
	    
	    
	    
	    */
		 
		 boolean flagToBePrinted = false; 

		 int queryCount = 0;






/*

for (Region region : partition.getAll()) {
	 
//	 System.out.println("For this region : " + region);
	 
	 //if(queryCount==70 || queryCount==139 || queryCount==2086 || queryCount==3179)
	//if(queryCount==2124 || queryCount==2242 || queryCount==3052 || queryCount==3611)
	
		 
	 
	 Set<String> QueryTableList = new HashSet<String>();
	 Set<String> QueryMainPredicateList = new HashSet<String>();
	 Set<String> QueryJoinPredicateList = new HashSet<String>();
	 
	 boolean firstTime = true;
	 
		    	
	 
   	for (BucketStructure bs : region.getAll()) {
   		
   	 int bucketCount = 0;
		
			
		     for (Entry<String, List<String>> entry : allTableAndColumnNameList.entrySet()) {
		    	   		 
				 Set<String> QueryOneLevelPredicateList = new HashSet<String>();

		            
		    	   String anonymousTableName = entry.getKey();
		    	 	String originalTableName = reverseTablesMap.get(entry.getKey());
		            List<String> columnList = entry.getValue();
		            
		            
		    		QueryTableList.add(originalTableName);
		    		


		            
		            for(String anonymousColumnName : columnList) {
		      
		            	 bucketCount++;
		 		    		Set<String> QueryPredicateList = new HashSet<String>();

		            	
		            	String originalColumnName = reverseColumnsMap.get(anonymousTableName + "_" + anonymousColumnName);
		            	
		           	 
			     	
			            Integer weNeedToCheckAtThisIndex = bucketsToColumnNameMapping.indexOf(anonymousTableName + "_" + anonymousColumnName);
						
						List<Integer> mappingIndex = bucketFloorsByColumns.get(anonymousTableName + "_" + anonymousColumnName);

						 
			     	
					    	
							 Bucket rightNow = bs.at(weNeedToCheckAtThisIndex);
							 
							
							 
							 
							 
					            System.out.println("Bucket "+ bucketCount +" : " + rightNow);
					         
		            }}}}





*/







int regionCount=0;


//for (Region region : partition.getAll()) {
//	 regionCount++;
//		 System.out.println("Region "+ regionCount+ " : " + region);
//}






		
		 for (Region region : partition.getAll()) {
			 
			 //System.out.println("For this region : " + region);
			 
			 //if(queryCount==70 || queryCount==139 || queryCount==2086 || queryCount==3179)
			//if(queryCount==2124 || queryCount==2242 || queryCount==3052 || queryCount==3611)
			if(queryCount==0)// || queryCount==1 || queryCount==2 || queryCount==3)
			 flagToBePrinted = false;
			 else
			 flagToBePrinted = false;
				 
			//flSe
			
			//System.out.println("Check");
			
			 //This if for joinPath
			 Set<String> allColumnsUsed = new HashSet<String>();
			 
			 
			 Set<String> QueryTableList = new HashSet<String>();
			 Set<String> QueryMainPredicateList = new HashSet<String>();
			 Set<String> QueryJoinPredicateList = new HashSet<String>();
			 
			 boolean firstTime = true;
			 
				    	
		    	for (BucketStructure bs : region.getAll()) {
		    		
					 Set<String> QueryTwoLevelPredicateList = new HashSet<String>();

		    		
					
				     for (Entry<String, List<String>> entry : allTableAndColumnNameList.entrySet()) {
				    	 
						 Set<String> QueryOneLevelPredicateList = new HashSet<String>();

				            
				    	   String anonymousTableName = entry.getKey();
				    	 	String originalTableName = reverseTablesMap.get(entry.getKey());
				            List<String> columnList = entry.getValue();
				            
				            
				    		QueryTableList.add(originalTableName);
				    		

				    		//System.out.println("all Col List : " + columnList);
				    		

				            
				            for(String anonymousColumnNameWithHashCode : columnList) {
				      
					    		Set<String> QueryPredicateList = new HashSet<String>();


							    String[] nameSplit = anonymousColumnNameWithHashCode.split("_");	
							    
							    
							    String anonymousColumnName = nameSplit[0];
				            	String originalColumnName = reverseColumnsMap.get(anonymousTableName + "_" + anonymousColumnName);
				            	
				            	
					            if(flagToBePrinted)
					            {
					            	System.out.println("originalColumnName : " + originalColumnName);
					            }
					            
					            //System.out.println("Buluk buluk 4.02 ");
					    	    
					    	    
				        	
					            Integer weNeedToCheckAtThisIndex = -1;
					    	    
								//List<Integer> mappingIndex = bucketFloorsByColumns.get(anonymousTableName + "_" + anonymousColumnName);
								
								List<Integer> mappingIndex=null;//bucketFloorsByColumns.get(anonymousTableAndColumnName);//anonymousTableName + "_" + anonymousColumnName);

								
					            for(Map.Entry<String, IntList> entry11 : bucketFloorsByColumns.entrySet()) {
					            	//String colNameWithHashCode = entry11.getKey();
					            	//String splitTheName[] = colNameWithHashCode.split("_");
					            	//if((splitTheName[0] + "_" + splitTheName[1]).equals(anonymousTableName + "_" + anonymousColumnName)){
					            	
					            	if((anonymousTableName + "_" +anonymousColumnNameWithHashCode).equals(entry11.getKey())){
					            		mappingIndex = entry11.getValue();
					            	    weNeedToCheckAtThisIndex = bucketsToColumnNameMapping.indexOf(entry11.getKey());
					            	}
					            	
					            	
					            }
					            
					            //System.out.println("Buluk buluk 4.03 ");
					    	    
								
					            //System.out.println("Buluk buluk 4.04");
					    	    
					           
									Integer startIndex, endIndex, greaterThanEqualToPredicateValue, lesserThanPredicateValue;
								 
									String	lessThanSymbol = "<"; String greaterThanSymbol = ">"; 	String equalitySymbol = "=";
	
	
			    	
									//System.out.println("Buluk buluk 4.05 ");
									   
							    	
									 Bucket rightNow = bs.at(weNeedToCheckAtThisIndex);
									 
										//System.out.println("Buluk buluk 4.051 ");
										   
									 
									 List<Integer> valueList = rightNow.getAll();
									 
									// if(valueList.size()==1 && valueList.get(0)==0)
									//	 System.out.println("VaadaMaapla");
									 
										//System.out.println("Buluk buluk 4.06 ");
										   
									 
									
									 //System.out.println("Buluk buluk 4.07");
									    
									    
									 
										JSONObject ae = (JSONObject) jo.get(anonymousTableName); ////System.out.println("ae_ : " + ae);
										JSONObject b = (JSONObject) ae.get("columns");////System.out.println("b_ : " + b);
										JSONObject c = (JSONObject) b.get(anonymousTableName + "_" + anonymousColumnName); ////System.out.println("c_ : " + c);
										String dataType = (String) c.get("columnType"); ////System.out.println("d_ : " + dataType);
										
										//if(dataType.equals("integer")) {
										//	flagToBePrinted = true;
										//}
										
										 if(flagToBePrinted)
								            {
								             System.out.println("weNeedToCheckAtThisIndex" + weNeedToCheckAtThisIndex);
											 System.out.println("weNeedToCheckAtThisIndex Checking for : " + anonymousTableName + "_" + anonymousColumnName);
								            
											 System.out.println("BFC for this col : " + mappingIndex);
								            } 
										 
							           if(flagToBePrinted)
										System.out.println("dataType : " + dataType);
										
										//System.out.println("Buluk buluk 4.08 ");
									    
							           if(flagToBePrinted)
								         {
								            System.out.println("Bucket Right Now : " + rightNow);
										    System.out.println("ValueList : " + valueList);
								         }
										 

							           //Int2DoubleMap originalNumberMapping=null;
							           Int2DoubleMap originalNumberMapping=null;
							           Int2ObjectMap<Date> originalDateMapping=null;
							           Int2ObjectMap<String> originalStringMapping=null;
							           
							       //    if(dataType.equals("date"))
							           	originalDateMapping = reverseDateAnonyMap.get(anonymousTableName + "_" + anonymousColumnName);


							        //   if(dataType.equals("integer") || dataType.contentEquals("numeric"))					            	
							           	originalNumberMapping = reverseNumberAnonyMap.get(anonymousTableName + "_" + anonymousColumnName);
							           
							         //  if(dataType.equals("character") || dataType.contentEquals("character varying"))					            	
							           	originalStringMapping = reverseStringAnonyMap.get(anonymousTableName + "_" + anonymousColumnName);


								
									//	 System.out.println("checkPast");

							            if(flagToBePrinted)
								         { 
							            	System.out.println("originalStringMapping : " + originalStringMapping);
							            	System.out.println("originalIntMapping : " + originalNumberMapping);
							            	System.out.println("originalDateMapping : " + originalDateMapping);
									         
								         }
								         
					
					 
											 for (int i=0; i<valueList.size(); i++)
											 {
												 
											    	Set<String> QuerySubPredicateList = new HashSet<String>();
						
													 String subQuery = "";
													 
												 startIndex = valueList.get(i);
											  
												 int stretchCount = 1;
												 
												 while((stretchCount+i) != valueList.size())
												 	{ if(valueList.get(stretchCount+i) == stretchCount+startIndex)
												 	    stretchCount = stretchCount + 1 ;
												 	    else
												 	    	{break;}
												 	}
												
												 endIndex = startIndex + stretchCount; //added this minus 1 later
												 
												 if(endIndex >= mappingIndex.size())
													 endIndex = -1;
												 
												 if(startIndex==0 && endIndex==1)
													 startIndex=-1;
										/*		 else if(stretchCount==valueList.size() && startIndex==0)
												 {
													 startIndex=1;
													 endIndex=-1; //valueList.get(valueList.size()-2); 
													 
													 if(flagToBePrinted)
											            {
											            		System.out.println("Its about damn time!");
											            }
												 }
												 //recent addition post the ITEM FILE BUG
											*/	 
												 
												 i = i + (stretchCount-1);
												 
												 if(flagToBePrinted)
										            {
										            												
												 System.out.println("stretchCount" + stretchCount);
												 System.out.println(); System.out.println("startIndex" + startIndex);
												 System.out.println("endIndex" + endIndex); System.out.println();
												 System.out.println("mappingIndex size " + mappingIndex.size());
												 
										            }
												 
												 //System.out.println(" -1- ");
												 
												 if(startIndex==-1)
													 if( endIndex==-1) 
													 	{
														 System.out.println("Should not be happening");

														 continue;}

												 
												 allColumnsUsed.add(bucketsToColumnNameMapping.get(weNeedToCheckAtThisIndex));
									           	 
												 
												 if(startIndex!=-1) {
													 
													 //if(startIndex==0 && mappingIndex.size()>1)
													 //startIndex=1;
													 
													 //else if (mappingIndex.size()==1 && mappingIndex.get(0)==0)
													//	 continue;
													 
												 		greaterThanEqualToPredicateValue = mappingIndex.get(startIndex); 
												 		
												 		//if(startIndex>0)
												 		//	throw new RuntimeException("hey");
											
												 		//System.out.println(" -1.5- ");
														 
												 		
												 		
												 		
												 		//NEW CODE FOR NEW WAY OF INT ANONYMIZATION
												 		
												 		if(dataType.equals("integer")) {
												 			
												 			Double temp = (double) greaterThanEqualToPredicateValue;							            	
											            	if(!(startIndex==0 && endIndex==-1)){//System.out.println(" -5.5- ");
												            	QuerySubPredicateList.add(originalTableName.toUpperCase() + "." + originalColumnName.toUpperCase() + greaterThanSymbol + equalitySymbol + String.valueOf(temp));
											            	
											            	
												            	if(flagToBePrinted)
												            		if(dataType.contentEquals("integer"))//dataType.equals("integer") || dataType.contentEquals("numeric"))
															   	{
													            	System.out.println(); System.out.println("greaterThanEqualToPredicateValue" + (greaterThanEqualToPredicateValue));
															   	}
											            	}
												 			
												 		}
												 		
												 		
												 		
												 		
												 		
												 		
												 		
														 if(greaterThanEqualToPredicateValue%2 == 1) //greaterThanSymbolCase
														 { 
															
															greaterThanEqualToPredicateValue = greaterThanEqualToPredicateValue - 1;
															
															//System.out.println(" -2- ");
							
												            if(dataType.equals("date"))
												            {
												               	Date temp = originalDateMapping.get(greaterThanEqualToPredicateValue);						            	
												            	if(temp!=null){							            //System.out.println(" -5.5- ");
						
												            		QuerySubPredicateList.add(originalTableName.toUpperCase() + "." + originalColumnName.toUpperCase() + greaterThanSymbol  + "'" + String.valueOf(temp) + "'" );
												            	}
												            }	
												            if(dataType.equals("numeric"))// || dataType.contentEquals("numeric"))
												            {
												               	Double temp = originalNumberMapping.get(greaterThanEqualToPredicateValue);							            	
												            	if(temp!=null){//System.out.println(" -5.5- ");
													            	QuerySubPredicateList.add(originalTableName.toUpperCase() + "." + originalColumnName.toUpperCase() + greaterThanSymbol + String.valueOf(temp));
												            	}
												            }
												            if(dataType.equals("character") || dataType.contentEquals("character varying"))
												            {
												               	String temp = originalStringMapping.get(greaterThanEqualToPredicateValue);							            	
												            	if(temp!=null){//System.out.println(" -5.5- ");
												            		
												            		if(temp.contains("'::bpchar")) {
												            			int place = temp.indexOf("'::bpchar");
												            			//System.err.println("bpchar fix : " + temp);
												            			temp = temp.substring(1, place);

												            			//System.err.println("bpchar fix : " + temp);
												            			
												            		}
												            		
													            	QuerySubPredicateList.add(originalTableName.toUpperCase() + "." + originalColumnName.toUpperCase() + greaterThanSymbol  + "'"+ temp + "'");
												            	}
												            }
												            //System.out.println(" -3- ");
														 
													 }
													 else //greaterThanOrEqualToSymbolCase
													 { 
														 
														 //System.out.println(" -4- ");
														 
														if(dataType.equals("date"))
														{
											               	Date temp = originalDateMapping.get(greaterThanEqualToPredicateValue);							            	
											            	if(temp!=null){	//System.out.println(" -5.5- ");
												            	QuerySubPredicateList.add(originalTableName.toUpperCase() + "." + originalColumnName.toUpperCase() + greaterThanSymbol + equalitySymbol  + "'" + String.valueOf(temp) + "'" );
					
											            	}
											            	
											            		
														}
											            if(dataType.equals("numeric"))// || dataType.contentEquals("numeric"))
											            {
											               	Double temp = originalNumberMapping.get(greaterThanEqualToPredicateValue);
											               	if(temp!=null){	//System.out.println(" -5.5- ");
											            		QuerySubPredicateList.add(originalTableName.toUpperCase() + "." + originalColumnName.toUpperCase() + greaterThanSymbol + equalitySymbol +  String.valueOf(temp));
											               	}
											            }
											            if(dataType.equals("character") || dataType.contentEquals("character varying"))
											            {
											            	String temp = originalStringMapping.get(greaterThanEqualToPredicateValue);
											            	if(temp!=null){//System.out.println(" -5.5- ");
											            		
											            		if(temp.contains("'::bpchar")) {
											            			int place = temp.indexOf("'::bpchar");
											            			//System.err.println("bpchar fix : " + temp);
											            			temp = temp.substring(1, place);

											            			//System.err.println("bpchar fix : " + temp);
											            			
											            		}
						
												            	QuerySubPredicateList.add(originalTableName.toUpperCase() + "." + originalColumnName.toUpperCase() + greaterThanSymbol + equalitySymbol  + "'" + temp + "'");
											            	}
											            	
											            }
											            //System.out.println(" -5- ");
												 
												 }
														 if(flagToBePrinted)
												            {
												            
												 
											            if(dataType.equals("date"))
													   	{
											            	System.out.println(); System.out.println("originalDateMapping.get(greaterThanEqualToPredicateValue)"  + "'" + originalDateMapping.get(greaterThanEqualToPredicateValue) + "'" );
													   	}
						
											            
											            
											            if(dataType.contentEquals("numeric"))//dataType.equals("integer") || dataType.contentEquals("numeric"))
													   	{
											            	System.out.println(); System.out.println("originalNumberMapping.get(greaterThanEqualToPredicateValue)" + originalNumberMapping.get(greaterThanEqualToPredicateValue));
													   	}
						
											            if(dataType.equals("character") || dataType.contentEquals("character varying"))
										            	{
											            	System.out.println(); System.out.println("originalStringMapping.get(greaterThanEqualToPredicateValue)"  + "'"+ originalStringMapping.get(greaterThanEqualToPredicateValue) + "'" );
										            	}
											     
												            }
														 
											            //System.out.println(" -6- ");
					
												 }
												 
							
												 if(endIndex!=-1) {
														 lesserThanPredicateValue = mappingIndex.get(endIndex);
														 
														//NEW CODE FOR NEW WAY OF INT ANONYMIZATION
													 		
													 		 
														 if(dataType.contentEquals("integer"))//dataType.equals("integer") || dataType.contentEquals("numeric"))					            	
												            {
												               	Double temp = (double) lesserThanPredicateValue;							            	
												            	if(temp!=null){
												            		QuerySubPredicateList.add(originalTableName.toUpperCase() + "." + originalColumnName.toUpperCase() + lessThanSymbol + String.valueOf(temp));
												            	}
												            	
												            	if(flagToBePrinted)
												            		if(dataType.equals("integer"))	
																 {
																	 System.out.println("lesserThanPredicateValue" + lesserThanPredicateValue); System.out.println();
																 }
												            }
														 
														 
													 if(lesserThanPredicateValue%2 == 1) //lesserThanOrEqualToSymbolCase
													 { 
														 lesserThanPredicateValue = lesserThanPredicateValue - 1;
														 
														if(dataType.equals("date"))
														{
											               	Date temp = originalDateMapping.get(lesserThanPredicateValue);							            	
											            	if(temp!=null){
											            		QuerySubPredicateList.add(originalTableName.toUpperCase() + "." + originalColumnName.toUpperCase() + lessThanSymbol + equalitySymbol + "'"  + String.valueOf(temp) + "'" );
											            	}
														}
														if(dataType.equals("numeric"))// || dataType.contentEquals("numeric"))					            	
											            {
											               	Double temp = originalNumberMapping.get(lesserThanPredicateValue);							            	
											            	if(temp!=null){
											            		QuerySubPredicateList.add(originalTableName.toUpperCase() + "." + originalColumnName.toUpperCase() + lessThanSymbol + equalitySymbol + String.valueOf(temp));
											            	}
											            }
											            if(dataType.equals("character") || dataType.contentEquals("character varying"))
												         {
											            	String temp = originalStringMapping.get(lesserThanPredicateValue);
											            	
											            	if(temp!=null){
											            		if(temp.contains("'::bpchar")) {
											            			int place = temp.indexOf("'::bpchar");
											            			//System.err.println("bpchar fix : " + temp);
											            			temp = temp.substring(1, place);

											            			//System.err.println("bpchar fix : " + temp);
											            			
											            		}
						
											            	QuerySubPredicateList.add(originalTableName.toUpperCase() + "." + originalColumnName.toUpperCase() + lessThanSymbol + equalitySymbol  + "'" + temp + "'");
											            	}
												         }
												 }
												 else
												 {
													 //lesserThanSymbolCase
													 
													 //System.out.println("Aandava" + dataType);
													 
													 if(dataType.equals("date"))
													 {
											               	Date temp = originalDateMapping.get(lesserThanPredicateValue);							            	
											            	if(temp!=null){	 
											            	QuerySubPredicateList.add(originalTableName.toUpperCase() + "." + originalColumnName.toUpperCase() + lessThanSymbol  + "'" + String.valueOf(temp) + "'" );
											            	}
											         }
													 if(dataType.equals("numeric"))// || dataType.contentEquals("numeric"))					            	
													 {
											               	Double temp = originalNumberMapping.get(lesserThanPredicateValue);							            	
											            	if(temp!=null){
											            	QuerySubPredicateList.add(originalTableName.toUpperCase() + "." + originalColumnName.toUpperCase() + lessThanSymbol +  String.valueOf(temp));
											            	}
											         }
													 if(dataType.equals("character") || dataType.contentEquals("character varying"))
										            { //System.out.println("Aandava2");
													 
										            	String temp = originalStringMapping.get(lesserThanPredicateValue);
										            	if(temp!=null){
										            		if(temp.contains("'::bpchar")) {
										            			int place = temp.indexOf("'::bpchar");
										            			//System.err.println("bpchar fix : " + temp);
										            			temp = temp.substring(1, place);

										            			//System.err.println("bpchar fix : " + temp);
										            			
										            		}
					
										            	QuerySubPredicateList.add(originalTableName.toUpperCase() + "." + originalColumnName.toUpperCase() + lessThanSymbol + "'" + temp + "'");
										            	}
										            }
												 }
													 
													 if(flagToBePrinted)
											            {
											            
														 if(dataType.equals("date"))
														 {
														 System.out.println("originalDateMapping.get(lesserThanPredicateValue)"  + "'" + originalDateMapping.get(lesserThanPredicateValue) + "'" ); System.out.println();
														 }
						

														 
									
														 
														 if(dataType.contentEquals("numeric"))//dataType.equals("integer") || dataType.contentEquals("numeric"))	
														 {
															 System.out.println("originalNumberMapping.get(lesserThanPredicateValue)" + originalNumberMapping.get(lesserThanPredicateValue)); System.out.println();
														 }
								
											            if(dataType.equals("character") || dataType.contentEquals("character varying"))
														 {
											            System.out.println("originalStringMapping.get(lesserThanPredicateValue)" + "'" + originalStringMapping.get(lesserThanPredicateValue) + "'"); System.out.println();
														 }
											            
											            }
					
					
												 }
											 
											 
												 for(String a : QuerySubPredicateList) {
												    	
												    	subQuery = subQuery + a + " AND ";
					
												    	//System.out.println("Inside QuerySubPredicateList : " + a);
												    	//System.out.println("Inside QuerySubPredicateList ( so far ) : " + subQuery);
												    	if(flagToBePrinted) 
														{
														System.out.println("Inside QuerySubPredicateList : " + a);
														}
												    }
												 
												 if(QuerySubPredicateList.size()>0) {
												 subQuery = "(" + subQuery.substring(0,subQuery.length()-5) + ")";
												 QueryPredicateList.add(subQuery);
												 }					   
										 }
					
											 String query = "";

										 
										 	for(String a : QueryPredicateList) {
										    	
										    	query =  query + a + " OR ";
										    	
										    	//System.out.println("Inside QueryPredicateList : " + a);
										    	//System.out.println("Inside QueryPredicateList ( so far ) : " + query);
										    	
										    	if(flagToBePrinted) 
												{
												System.out.println("Inside QueryPredicateList : " + a);
												}
										    }
										    
										    if(QueryPredicateList.size()>0) {
										    	query = query.substring(0,query.length()-4);
											    QueryOneLevelPredicateList.add(query);
					
										    }
										    
									 }
							    	
				            String oneLevelQuery = "";
				    	 
						        	for(String a : QueryOneLevelPredicateList) {
								    	
						        		oneLevelQuery =  oneLevelQuery + "(" + a + ")" + " AND ";
								    	
								    	
						        		
									if(flagToBePrinted) 
										{
										System.out.println("Inside QueryOneLevelPredicateList : " + a);
										}
								    	
						        		
						        		//System.out.println("Inside QueryOneLevelPredicateList ( so far ) : " + oneLevelQuery);
								    	
								    	
								    }
								    
								    if(QueryOneLevelPredicateList.size()>0) {
								    	oneLevelQuery = oneLevelQuery.substring(0,oneLevelQuery.length()-4);
									    QueryTwoLevelPredicateList.add(oneLevelQuery);
			
								    }
						            
				     
				     
				     
				     			}
				     
				     
				     String twoLevelQuery = "";
			    	 
			        	for(String a : QueryTwoLevelPredicateList) {
					    	
			        		twoLevelQuery =  twoLevelQuery +  a + " AND ";
					    	
					    	//System.out.println("Inside QueryTwoLevelPredicateList : " + a);
					    	//System.out.println("Inside QueryTwoLevelPredicateList ( so far ) : " + twoLevelQuery);
					    	
					    	
					    }
					    
					    if(QueryTwoLevelPredicateList.size()>0) {
					    	twoLevelQuery = twoLevelQuery.substring(0,twoLevelQuery.length()-4);
					    	
					    	if(flagToBePrinted) {
					    	System.out.println("Two level query : " + twoLevelQuery);
					    	}
					    	
						    QueryMainPredicateList.add(twoLevelQuery);

					    }
			            
				     
				     
				     
				     
		    	}
		    	

				//System.out.println("Buluk buluk 4.1 ");
		    	
		    	
		    	  if(!viewAlreadyThere)
				    {
				    	QueryTableList.add(originalViewName);

				    }
				    
			 
			 String finalQuery = "SELECT * FROM ";
			 
			    List<String> QueryTableListArray = new ArrayList<String>();
			    

				///////System.out.println("Buluk buluk 4.2  " + JoinMapping.topoTable + " "+ PostgresVConfig.VIEWNAMES_TOPO);
			    
			    
			    List<String> topoListOfOriginalViewNames= new ArrayList<String>( Arrays.asList("store_returns", "web_sales", "store_sales", "catalog_returns", "inventory", "catalog_sales", "web_returns", "web_site", "store", "catalog_page", "call_center", "ship_mode", "warehouse", "promotion", "web_page", "time_dim", "customer", "item", "customer_address", "household_demographics", "customer_demographics", "date_dim", "income_band", "reason"));
			    for(String t : topoListOfOriginalViewNames) {
			    	if(QueryTableList.contains(t)) {
			    		QueryTableListArray.add(t);
			    		

			    		//System.out.println("Buluk buluk 4.3 ");
			    	}
			    }
			    
			    
			    
			    
			    //System.out.println("QueryTableListArray : " + QueryTableListArray+ " "  + QueryTableList + " "+topoListOfOriginalViewNames);
				
					      
			    //ACTUAL QUERYGEN = ADDING TABLES
			   /* for(String a : QueryTableListArray) {
			    	
			    	finalQuery = finalQuery + a.toUpperCase() + ",";
			    	
			    }
			    

			    finalQuery = finalQuery.substring(0,finalQuery.length()-1);
					finalQuery = finalQuery + " WHERE "; 
				
			   */
			    
			    
			    

				//System.out.println("Buluk buluk 4.4 ");
			    
			    //System.out.println("arasuCliqueSet :" +arasuCliqueSet );
			    //System.out.println("viewName :" + viewname);
			    
			    
			  
			   
			    
				//System.out.println("Buluk buluk 4.5 ");
			    
				    //JOIN GRAPH SECTION
			    
			    
			    

				//System.out.println("Buluk buluk 5 ");	    
			    
			    
			   //System.out.println("JoinMapping.ourGraph" + JoinMapping.ourGraph);
			    

        

		//System.out.println("Buluk buluk 6 ");
        
        
        Map<String,ColumnPathInfo>  colPathInfo = PostgresVConfig.COLUMN_ID_MAP;
        

        Map<String,String> allPaths = new HashMap<String, String>();
        
        Set<String> allTables  = new HashSet<String>();
        
        //System.out.println(" reverseColumnsMap " + reverseColumnsMap);
		 
        allTables.add(originalViewName.toUpperCase());
        
        for(String col : allColumnsUsed) {

       	 	ColumnPathInfo colPath = colPathInfo.get(col);
        	
       	 //System.out.println("  col " +  col +" " + colPath);
         
        	
        	 List<String> pkPath = colPath.getPKColumnNames();
        	 List<String> fkPath = colPath.getFKColumnNames();
        	 
        	 
        	 for(int k=0;k<pkPath.size();k++) {
        		 
        		 if(!pkPath.get(k).contains("t")) continue;
			    
        		 //System.out.println(" pkPath.get(k) + fkPath.get(k) " + pkPath.get(k)+ " "+ fkPath.get(k) + " " + pkPath.size());
        		 
        		 //System.out.println(" actualPkColName + actualFkColName " + reverseColumnsMap.get(pkPath.get(k)) + " "+ reverseColumnsMap.get(fkPath.get(k)));
        		 
        		 String actualPkTableName = reverseTablesMap.get(pkPath.get(k).substring(0,pkPath.get(k).indexOf("_"))).toUpperCase();
        		 String actualFkTableName = reverseTablesMap.get(fkPath.get(k).substring(0,fkPath.get(k).indexOf("_"))).toUpperCase();
        		 
        		 allTables.add(actualPkTableName);
        		 allTables.add(actualFkTableName);
            	 
        		 String actualPkColName = reverseColumnsMap.get(pkPath.get(k)).toUpperCase();
        		 String actualFkColName = reverseColumnsMap.get(fkPath.get(k)).toUpperCase();
        		 
        		 //System.out.println(" actualPkColName + actualFkColName " + actualPkColName+ " "+ actualFkColName);
        		 
        		 if(allPaths.get(actualPkTableName + "." + actualPkColName)!=null) {
        			 
        			 //System.out.println("PK already Present " + actualPkColName+ " "+ actualFkColName);
        			 continue;
        			 //throw new RuntimeException("PK already Present " + actualPkColName+ " "+ actualFkColName);
        		 }
        		 else 
        			 allPaths.put(actualPkTableName + "." + actualPkColName, actualFkTableName + "." + actualFkColName);
        		 
        		 
        	 
        	 }
        	
        	 //System.out.println(" allTables " + allTables);
      		
         	//System.out.println(" allPaths " + allPaths);
     		
        	
        }
        
        
        
        
        //LATEST QUERYGEN 
        for(String a : allTables) {
	    	
	    	finalQuery = finalQuery + a.toUpperCase() + ",";
	    	
	    }
	    
	    finalQuery = finalQuery.substring(0,finalQuery.length()-1);
	    
	    finalQuery = finalQuery + " WHERE "; 
		
        
        for(Entry<String, String> e : allPaths.entrySet()) {
        	
        	finalQuery += e.getKey() + " = " + e.getValue() + " AND ";
        }
        /*   
        
        //System.out.println("Buluk buluk 6.3 ");
        
        Set<String> joinListSet  = new HashSet<String>();
        
        Set<String> tempTables = new HashSet<String>(QueryTableListArray);
			    
   boolean joinPathNotFound = false;
   
 
   
	          for(Entry<ArrayList<String>, ArrayList<String>> hey : JoinMapping.tableList.entrySet()) 
	         
			{
				Set<String> dei = new HashSet<String>(hey.getKey()); 
	
				if(dei.size()==tempTables.size())
					dei.removeAll(tempTables);
				
				if(dei.isEmpty())
				{
					//tableList.put(tablesOfThisQuery,predicatesOfThisQuery);
					
					//System.out.println("FOUND" + predicatesOfThisQuery);
					
				//	System.out.println("FOUND" + hey.getKey());
	
				//	System.out.println("FOUND" + hey.getValue());
					
					if(hey.getKey().size()<=hey.getValue().size()) {
						
						//System.out.println("Manual Injection " + QueryTableListArray);
						
						Set<String> findTheTable = new HashSet<String>(hey.getValue());
						
						Set<String> newTableSet = new HashSet<String>();
						
						for(String p : findTheTable) {
							
							int getComma = p.indexOf(".");
							
							String table1 = p.substring(0,getComma);				
							
							//System.out.println("table1 " + table1);
							
							p = p.substring(getComma+1);		
							
							getComma = p.indexOf("= ");
							
							p = p.substring(getComma+1);		
							
							getComma = p.indexOf(".");
							
							String table2 = p.substring(0,getComma);				
							
							//System.out.println("table2 " +table2);
							
							newTableSet.add(table1.trim().toLowerCase());
							newTableSet.add(table2.trim().toLowerCase());
							
						}
						
						Set<String> dei2 = new HashSet<String>(hey.getKey()); 
						
						//System.out.println("AND HERE IT IS : " + dei2 + " " +  newTableSet);
						
						newTableSet.removeAll(dei2);
						
						
						
						
						
					}
					
	
					joinListSet = new HashSet<String>(hey.getValue());
					joinPathNotFound = false;
					break;
					
				}else {
					if(QueryTableListArray.size()>1) {
						
						//System.out.println("EDHO PRACHANA " + QueryTableListArray);
						
						joinPathNotFound = true;
						
						
						//String joinPathFileString = "";
						
						//joinPathFileString = joinPathFileString + "\n________________________\n\nTables : " + QueryTableListArray + "\n\n";
					
						//FileUtils.writeStringToFile(PostgresCConfig.getProp(Key.QUERYGENMODULE_JOINPATHFILE), joinPathFileString);

						
						try {
							//writer3 = new BufferedWriter(new FileWriter("/home/dsladmin/EquationsAndQueries/joinPath" + Integer.toString(DoubleReductionBasedViewSolver.fileCount) + ".txt", true));
							writer3 = new BufferedWriter(new FileWriter(PostgresCConfig.getProp(Key.QUERYGENMODULE_JOINPATHFILE) + Integer.toString(DoubleReductionBasedViewSolver.fileCount) + ".txt", true));
							
							writer3.write("\n________________________\n\nTables : " + QueryTableListArray + "\n\n");
		
							
							
							//System.out.println("I AM FILE NUMBER " + DoubleReductionBasedViewSolver.fileCount + " " + viewname);
					    } catch (IOException e) {
							// TODO Auto-generated catch block
							e.printStackTrace();
						}
					}
				    
				}
			}
			  
			   
			    
	           
	          //System.out.println("Buluk buluk 6.75 ");
		      
        
        
			    
			    
			    Set<String> duplicateJoinList  = new HashSet<String>();
		
			    
			    for(String join : joinListSet)
			    	{
			    	
			    	if(duplicateJoinList.contains(join))
			    		continue;
			    	
			    	String[] a = join.split("=");
			    	
			    //	for(String aa : a)
			    //		System.out.println("PodaPodaPunnaku " + aa);
			    	
			    	if (joinListSet.contains(a[1] + "=" +a[0])){
			    		
				//    	System.out.println("PodaPodaPunnaku2 " + join);

				    	duplicateJoinList.add(a[1] + "=" +a[0]);	    		
			    	}
			    	
			    	}
			    
			    joinListSet.removeAll(duplicateJoinList);
			    
			    
			    
			    //if(joinListSet.size() != allPaths.size() ){
			    //	System.err.println("1 THEREEE IS A MISMATCHHHH : " + joinListSet.size() + " " + allPaths.size());
			    //}
			    
			    //SANITY CHECKING JOIN PATH
			    Set<String> sanityJoinList  = new HashSet<String>();
				
			    for(String join : joinListSet) {
			    	
			    	String[] a = join.split(" = ");
			    	
			    	if(allPaths.containsKey(a[0])) {
			    		
			    		 //System.out.println("A");
			    		 
			    		if(allPaths.get(a[0]).equals(a[1])) {
			    			allPaths.remove(a[0]);
			    			
			    			sanityJoinList.add(join);
			    			 //System.out.println("B");
			    		}
			    		
			    	}else if(allPaths.containsKey(a[1])) {
			    		
			    		 //System.out.println("C");
			    		 
			    		if(allPaths.get(a[1]).equals(a[0])) {
			    			allPaths.remove(a[1]);
			    			
			    			sanityJoinList.add(join);
			    			 //System.out.println("D");
			    		}
			    		
			    	}
			    	
			    }
			    
			    joinListSet.removeAll(sanityJoinList);
			    			    
			    //if(joinListSet.size() != allPaths.size() ){
			    //	System.err.println("2 THEREEE IS A MISMATCHHHH ");
			    //}
			    
			   // System.out.println("Final join path by JoinMapping2 : " + joinListSet + " "+ joinListSet.size());
			    //System.out.println("Final join path by Col path2 : " + allPaths + " " + allPaths.size());
			    
			    //if(allTables.size() != QueryTableListArray.size() ){
			    //	System.err.println("3 THEREEE IS A MISMATCHHHH ");
			    //	System.err.println("allTables " + allTables);
			    //	System.err.println("QueryTableListArray " + QueryTableListArray);
			    //}
			    
			    allTables.removeAll(QueryTableListArray); 
			    
			   // if(allTables.size() != 0 ){
			   // 	System.err.println("4 THEREEE IS A MISMATCHHHH ");
			    //}
			  
			    
			    
			    
			    
			    
			    //ACTUAL QUERYGEN - ADDING JOINS
			    //for(String join : joinListSet)
			    //finalQuery += join + " AND ";
			    
			  	*/    
			    
			    finalQuery = finalQuery + "("  ;
			    
			    for(String a : QueryMainPredicateList) {
			    	
			    	
			    				    
			    	
			    	finalQuery = finalQuery + "(" + a + ") OR ";
			    	firstTime = false;	    	
			    }
			    
			    finalQuery = finalQuery.substring(0,finalQuery.length()-5);
			    
			    
			    finalQuery = finalQuery + "));";
			    
				    
				//System.out.println("Buluk buluk 7 ");
		        
		        
		        
				
				//if(finalQuery.contains("WH));")){
				//	estimateList.add(0);
				//}else {
				
			    
			     
			    
		        if(flagToBePrinted) {
		        	System.out.println("Final query : " + finalQuery);
		        }
			    
		        
		        
		        
			     
				//BELOW CODE IS FOR EXPLAIN ONLY
		        
				//   if(!joinPathNotFound) { 
		            String ea = QueryToExplainAnalyzePostgres.fetchOnlyExplainOutput(finalQuery);
			        //System.out.println(ea);
			         
					//rajkumar wrote this
					int st = ea.indexOf("rows");
					//System.out.println(st);
					//System.out.println(ea.substring(st));
					String fa = ea.substring(st);
					int ft = fa.indexOf(" width");
	
					//System.out.println("Gotcha  : " + Integer.valueOf(ea.substring(st+5,st+ft)));
					
					estimateList.add(Integer.valueOf(ea.substring(st+5,st+ft)));
				   //}
					
					
					
					
				//BELOW CODE IS FOR EXPLAIN ANALYZE
					/*
			    //   if(!joinPathNotFound) { 
				    String ea2 = QueryToExplainAnalyzePostgres.fetchOnlyExplainAnalyzeOutput(finalQuery);
			        //System.out.println(ea);
				         
						//rajkumar wrote this
					int st2 = ea2.indexOf(" width");
					
					ea2 = ea2.substring(st2 + 4);
					
					st2 = ea2.indexOf("rows");
					//System.out.println(st);
					//System.out.println(ea.substring(st));
					String fa2 = ea2.substring(st2);
					int ft2 = fa2.indexOf(" loops");
	
					//System.out.println("Gotcha 2 : " + Integer.valueOf(ea2.substring(st2+5,st2+ft2)));
					
					estimateList.add(Integer.valueOf(ea2.substring(st2+5,st2+ft2)));
				   //}
				
				//}
				
					*/
					
				
			    
			    
			    
				//System.out.println("Buluk buluk 8 ");
		        
		        
		        
				
			
				
				queryCount=queryCount+1;
				//System.out.println("Count : " + queryCount );// + finalQuery);
				
				
		   
				
				try {
					writer2.write(finalQuery + "\n");

					 

					if(flagToBePrinted) 
						{System.out.println("Query : " + finalQuery + "\n\n");
						}
				} catch (IOException e) {
					// TODO Auto-generated catch block
					e.printStackTrace();
				}
				    
		 }
		
			
			//System.out.println("Buluk buluk last " + estimateList);
		 
		 return estimateList;
	    
	}
	
	
	
	/*

	      
	    void DFSUtil(String name, List<String> tableList, DefaultDirectedGraph<String, DefaultEdge> checkGraph, Map<String, Boolean> visited) { 
	        // Mark the current node as visited and print it 
	    	visited.put(name, true);
	    	// System.out.print(v+" "); 
	        // Recur for all the vertices 
	        // adjacent to this vertex 
	        for (String t : tableList) { 
	            if(!t.equals(name) && (checkGraph.containsEdge(name,t) || checkGraph.containsEdge(t,name)) && !visited.get(t)) 
	            	{
	            	//System.out.println("Nijamellam maranthu pochu penne unnale : name : " + name + " \t t : " + t);
	            	DFSUtil(t,tableList,checkGraph,visited);
	            	}
	        } 
	  
	    } 
	    boolean connectedComponents(List<String> tableList, DefaultDirectedGraph<String, DefaultEdge> checkGraph) { 
	        // Mark all the vertices as not visited
	    	Map<String, Boolean> visited = new HashMap<>();
	    	
	    	for (String t : tableList) { 
		        visited.put(t, false);
	    	}
	        //for(int v = 0; v < V; ++v) { 
	        //    if(!visited[v]) { 
	                // print all reachable vertices 
	                // from v 
	                DFSUtil(tableList.get(0),tableList,checkGraph,visited);
	                
	         for (String t : tableList) { 
	        	 if(!visited.get(t))
	    			 return false;
	    	 }
	    	 
	    	 return true;
 
	                
	       //         System.out.println(); 
	       //     } 
	       // } 
	    } 
	     
	
	
	
	
    
    public static Object readObjectFromFile(String file) {
    	Object obj = null;
    	try(FileInputStream fs = new FileInputStream(file)) {
			try(ObjectInputStream os = new ObjectInputStream(fs)) {
				obj = os.readObject();
			}
		} catch (Exception e) {
			e.printStackTrace();
		}
    	return obj;
    }

     
	*/









	

}