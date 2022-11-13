package in.ac.iisc.cds.dsl.cdgvendor.solver;

import java.io.FileWriter;
import java.util.ArrayList;
import java.util.Calendar;
import java.util.Date;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

import org.json.simple.JSONObject;

import in.ac.iisc.cds.dsl.cdgvendor.constants.PostgresVConfig;
import in.ac.iisc.cds.dsl.cdgvendor.reducer.Bucket;
import in.ac.iisc.cds.dsl.cdgvendor.reducer.BucketStructure;
import in.ac.iisc.cds.dsl.cdgvendor.reducer.Region;
import in.ac.iisc.cds.dsl.cdgvendor.utils.Pair;
import it.unimi.dsi.fastutil.ints.Int2DoubleMap;
import it.unimi.dsi.fastutil.ints.Int2DoubleOpenHashMap;
import it.unimi.dsi.fastutil.ints.Int2ObjectMap;
import it.unimi.dsi.fastutil.ints.Int2ObjectOpenHashMap;
import it.unimi.dsi.fastutil.ints.IntList;

public class VolumeCompute {
	
	Region originalRegion;
	List<String> sortedBucketsToColumnNameMapping; 
	List<String> sortedUseableKeys; 
	List<ArrayList<Integer>> fkeysList;
	List<List<Long>> fkRangeArrayList;
	List<Integer> bucketStructureCardinalityList;
	List<String> tableNonKeys;
	List<Long> pkRanges; 
	Map<String, String> minMap;
	Map<String, Map<String, IntList>> allBucketFloors;
	String relName;
	String regionName;
	long totalRowCount;
	int fkOffset; 
	int regionIdentifier;
	int dateOffset; 
	Set<String> usableTableNonKeys; 
	Map<String, Int2DoubleMap> reverseNumberAnonyMap;
	Map<String, Int2ObjectMap<String>> reverseStringAnonyMap;
	Map<String, Int2ObjectMap<Date>> reverseDateAnonyMap;
	Calendar calender; 
	FileWriter fw;
	


	public VolumeCompute(Region originalRegion, List<String> sortedBucketsToColumnNameMapping,
			List<String> sortedUseableKeys, List<ArrayList<Integer>> fkeysList, List<List<Long>> fkRangeArrayList,
			List<Integer> bucketStructureCardinalityList, List<String> tableNonKeys, List<Long> pkRanges,
			Map<String, String> minMap, Map<String, Map<String, IntList>> allBucketFloors, String relName,
			String regionName, long totalRowCount, int fkOffset, int regionIdentifier, int dateOffset,
			Set<String> usableTableNonKeys, Map<String, Int2DoubleMap> reverseNumberAnonyMap,
			Map<String, Int2ObjectMap<String>> reverseStringAnonyMap,
			Map<String, Int2ObjectMap<Date>> reverseDateAnonyMap, Calendar calender, FileWriter fw) {
		super();
		this.originalRegion = originalRegion;
		this.sortedBucketsToColumnNameMapping = sortedBucketsToColumnNameMapping;
		this.sortedUseableKeys = sortedUseableKeys;
		this.fkeysList = fkeysList;
		this.fkRangeArrayList = fkRangeArrayList;
		this.bucketStructureCardinalityList = bucketStructureCardinalityList;
		this.tableNonKeys = tableNonKeys;
		this.pkRanges = pkRanges;
		this.minMap = minMap;
		this.allBucketFloors = allBucketFloors;
		this.relName = relName;
		this.regionName = regionName;
		this.totalRowCount = totalRowCount;
		this.fkOffset = fkOffset;
		this.regionIdentifier = regionIdentifier;
		this.dateOffset = dateOffset;
		this.usableTableNonKeys = usableTableNonKeys;
		this.reverseNumberAnonyMap = reverseNumberAnonyMap;
		this.reverseStringAnonyMap = reverseStringAnonyMap;
		this.reverseDateAnonyMap = reverseDateAnonyMap;
		this.calender = calender;
		this.fw = fw;
	}


	/*
	  
	newVVP.setRegionValuesToComputeVolume(newVVP.getVariable().calculateVolumeForRegion(relName, sortedBucketsToColumnNameMapping, usableTableNonKeys, reverseNumberAnonyMap, reverseStringAnonyMap, reverseDateAnonyMap, minMaxOfAllCols, allBucketFloors, anonymizedschema));
	
	newVVP.getRegionValuesToComputeVolume().accumulate();
		
	newVVP.getRegionValuesToComputeVolume().createNewRegionWithValuesDistributedAccordingToProbability(newRegion, relName,  sortedBucketsToColumnNameMapping, 
			sortedUseableKeys, allBucketFloors, regionName, newVVP.getRowcount(), fkeysList,  fkRangeArrayList, bucketStructureCardinalityList,	
			minMap, tableNonKeys, fkOffset, pkRanges, regionIdentifier,
	calender, dateOffset, usableTableNonKeys, reverseNumberAnonyMap,
	reverseStringAnonyMap,
	reverseDateAnonyMap, anonymizedschema, fw);
	
	*/



	public Region calculateVolumeForRegion() {
    	
		//originalRegion.volumeOfParticipatingBucketStructures = new ArrayList<Double>();
		Region volumeRegion = new Region();    	
    	
    	for (BucketStructure bs : originalRegion.bsList) {
    		BucketStructure volumeOfBucket = calculateVolumeForBucketStructure(bs);   
    		volumeRegion.bsList.add(volumeOfBucket);
    	}
    	
    	return volumeRegion;
    }
	
	


	public BucketStructure calculateVolumeForBucketStructure(BucketStructure originalBS) {
						
		//originalBS.volumeOfParticipatingBuckets = new ArrayList<Double>();
		
		// TODO Auto-generated method stub
		BucketStructure volumeOfBucketStructure = new BucketStructure();
		
		boolean flagToBePrinted = false;
		
		//Object obj=null;
		//try {
		//	obj = new JSONParser().parse(new FileReader("/home/dsladmin/multi-query-workspace/codd-data-gen/resources/cdgvendor/input/postgres/anonymizedschema.info"));//"/home/dsladmin/sqlqueries/temp/anonymizedschema.info"));///home/dsladmin/TODI/ws_kk/codd-data-gen/resources/cdgvendor/input/postgres/anonymizedschema.info"));
		//} catch (IOException | ParseException e) {
			// TODO Auto-generated catch block
		//	e.printStackTrace();
		//} 
        
        // typecasting obj to JSONObject 
        //JSONObject jo = (JSONObject) obj; 
        
		
		//Map<String, Map<String, IntList>> allBucketFloors= (Map<String, Map<String, IntList>>) FileUtils.readObjectFromFile("/home/dsladmin/EquationsAndQueries/BucketFloorsByColumns.dat");

		//Map<String, Map<String, IntList>> allBucketFloors= (Map<String, Map<String, IntList>>) FileUtils.readObjectFromFile("/home/dsladmin/multi-query-workspace/codd-data-gen/resources/cdgvendor/input/postgres/BucketFloorsByColumns.dat");
		
		// FileUtils.writeObjectToFile(bucketFloorsByColumns, "/home/dsladmin/sqlqueries/temp/BucketFloorsByColumns.dat");
	       
        // typecasting obj to JSONObject 
		//org.json.simple.JSONObject jo = anonymizedschema;//(JSONObject) obj; 
    
        //System.err.println("ANONYMIZED SCHEMA : " + jo);
		
		int index = 0;
		int chumma = 0;
		
		//System.out.println("sortedBucketsToColumnNameMapping : " + sortedBucketsToColumnNameMapping);
		
		//System.out.println("usableTableNonKeys  " + usableTableNonKeys);
       
		//System.out.println("Bucketlist inside calc vol:" + bucketList);
		
		
		for(int i=0; i<originalBS.bucketList.size(); i++) {
			Bucket b1 = originalBS.bucketList.get(i);
		//for(Bucket b1 : bucketList) {//String anonymousTableAndColumnName : sortedBucketsToColumnNameMapping) {
		    
			
        	String anonymousTableAndColumnName = sortedBucketsToColumnNameMapping.get(index);
        	index++;
	    	
            //Integer weNeedToCheckAtThisIndex = sortedBucketsToColumnNameMapping.indexOf(anonymousTableName + "_" + anonymousColumnName);
			
				//String	lessThanSymbol = "<"; String greaterThanSymbol = ">"; 	String equalitySymbol = "=";
        	//System.out.println("Chumma " + chumma++ + " " +anonymousTableAndColumnName + bucketList);

        	if(!usableTableNonKeys.contains(anonymousTableAndColumnName))
        		continue;


		    	
				 //Bucket rightNow = bs.at(weNeedToCheckAtThisIndex);
				 
				
				 
				// List<Integer> valueList = rightNow.getAll();
				 
				 //if(b1.getValList().size()==1 && b1.getValList().get(0)==0) {
					 
					//System.out.print("---");
				//	continue;
				 //}
					 //System.out.println("VaadaMaapla");
				 
        	if(flagToBePrinted)
            {   //System.out.println("originalStringMapping : " + reverseStringAnonyMap);
            	//System.out.println("originalIntMapping : " + reverseNumberAnonyMap);
            	//System.out.println("originalDateMapping : " + reverseDateAnonyMap);
		    } 
    		
				 
				 
				 
				 String[] nameSplit = anonymousTableAndColumnName.split("_");	
				 
				 //System.out.println("nameSplit : " + nameSplit[0]);
					
				    
				 if(flagToBePrinted)
		         {
		            //System.out.println("Bucket Right Now : " + rightNow);
				    //System.out.println("ValueList : " + valueList);
		         }
				    
				 
					//JSONObject ae = (JSONObject) jo.get(nameSplit[0]); ////System.out.println("ae_ : " + ae);
					//JSONObject b = (JSONObject) ae.get("columns");////System.out.println("b_ : " + b);
					//JSONObject c = (JSONObject) b.get(nameSplit[0] + "_" +nameSplit[1]);//anonymousTableAndColumnName); //System.out.println("c_ : " + c);
					//String dataType = (String) c.get("columnType"); ////System.out.println("d_ : " + dataType);
					
		           //System.out.println("dataType : " + dataType);
					//String[] nameSplit = tableNonKey.split("_");	

				 
					//org.json.simple.JSONObject ae = (org.json.simple.JSONObject) jo.get(nameSplit[0]); ////System.out.println("ae_ : " + ae);
					// org.json.simple.JSONObject bc = (org.json.simple.JSONObject) ae.get("columns");////System.out.println("b_ : " + b);
						
					//org.json.simple.JSONObject cd = (org.json.simple.JSONObject) bc.get(nameSplit[0] + "_" +nameSplit[1]);//anonymousTableAndColumnName); //System.out.println("c_ : " + c);
					//String dataType = (String) cd.get("columnType"); ////System.out.println("d_ : " + dataType);
					
					String dataType = PostgresVConfig.dataTypesForAllAnonymizedCols.get(nameSplit[0] + "_" +nameSplit[1]);
					
					Map<String, IntList> bucketFloorsByColumns = allBucketFloors.get(relName);
					
					if(flagToBePrinted)
		            {
		             //System.out.println("Doing for : " + relName);
					 //System.out.println("weNeedToCheckAtThisIndex Checking for : " + anonymousTableAndColumnName );//+ sortedBucketsToColumnNameMapping);//anonymousTableName + "_" + anonymousColumnName);
					 System.out.println("bucketFloorsByColumns" + bucketFloorsByColumns);
		            } 
		    		
		            //if(bucketFloorsByColumns==null)continue;

					List<Integer> mappingIndex=null;//bucketFloorsByColumns.get(anonymousTableAndColumnName);//anonymousTableName + "_" + anonymousColumnName);

					
					List<Integer> bfcForThisColumn=null;//bucketFloorsByColumns.get(anonymousTableAndColumnName);//anonymousTableName + "_" + anonymousColumnName);

					
		            for(Map.Entry<String, IntList> entry : bucketFloorsByColumns.entrySet()) {
		            	String colNameWithHashCode = entry.getKey();
		            	String splitTheName[] = colNameWithHashCode.split("_");
		            	
		            	if((splitTheName[0] + "_" + splitTheName[1]).equals(anonymousTableAndColumnName)){
		            		bfcForThisColumn = entry.getValue();
		            	}
		            }
		            
		            if(bfcForThisColumn == null) {
		            	continue; 
		            }
		            
		            //System.out.println("bfcForThisColumn : " + bfcForThisColumn );//+ " " + anonymousTableAndColumnName + " " + dataType);// + bucketFloorsByColumns);
					
					
					if(flagToBePrinted) {
					
						System.out.println("bfcForThisColumn : " + bfcForThisColumn );//+ " " + anonymousTableAndColumnName + " " + dataType);// + bucketFloorsByColumns);
						System.out.println("actual Bucket : " + b1 );//+ " " + anonymousTableAndColumnName + " " + dataType);// + bucketFloorsByColumns);

						System.out.println("Current column whose bucket we are seeing : " +  anonymousTableAndColumnName + " " + dataType);// + bucketFloorsByColumns);
					}
					//if(!nameSplit[0].equals("t16")) continue;
					 
		            
		            //if(mappingIndex==null)continue;
					//if(mappingIndex.size()==1 && mappingIndex.get(0)==0)continue;
					
		           Int2DoubleMap originalNumberMapping=null;
		           Int2ObjectMap<Date> originalDateMapping=null;
		           Int2ObjectMap<String> originalStringMapping=null;
		           
		       //    if(dataType.equals("date"))
		           	originalDateMapping = reverseDateAnonyMap.get(anonymousTableAndColumnName);//anonymousTableName + "_" + anonymousColumnName);

		        //   if(dataType.equals("integer") || dataType.contentEquals("numeric"))					            	
		           	originalNumberMapping = reverseNumberAnonyMap.get(anonymousTableAndColumnName);//anonymousTableName + "_" + anonymousColumnName);
		           
		         //  if(dataType.equals("character") || dataType.contentEquals("character varying"))					            	
		           	originalStringMapping = reverseStringAnonyMap.get(anonymousTableAndColumnName);//anonymousTableName + "_" + anonymousColumnName);

		           	//Pair<String, String> minMaxVal = null;//minMaxOfAllCols.get(anonymousTableAndColumnName);
			
				//	 System.out.println("checkPast");

		            if(flagToBePrinted)
			         { 
		            	//System.out.println("originalStringMapping : " + originalStringMapping + reverseStringAnonyMap);
		            	System.out.println("originalIntMapping : " + originalNumberMapping + " "+ anonymousTableAndColumnName+ " "+reverseNumberAnonyMap);
		            	//System.out.println("originalDateMapping : " + originalDateMapping + reverseDateAnonyMap);
				         
			         }
		            
		            
		            
		        	Bucket b2 = calculateVolumeForBucket(b1, bfcForThisColumn, anonymousTableAndColumnName, dataType, originalNumberMapping, originalStringMapping, originalDateMapping);//reverseNumberAnonyMap, reverseStringAnonyMap, reverseDateAnonyMap);
					volumeOfBucketStructure.bucketList.add(b2);
			
        }
        
        
		
		//for(Bucket b1 : bucketList) {
		//	Bucket b2 = b1.calculateVolumeForBucket(sortedBucketsToColumnNameMapping, reverseNumberAnonyMap, reverseStringAnonyMap, reverseDateAnonyMap);
		//	volumeOfBucketStructure.bucketList.add(b2);
		//}
		
		return volumeOfBucketStructure;
	}
	

	


	private Bucket calculateVolumeForBucket(Bucket currentBucket, List<Integer> bfcForThisColumn,
			String anonymousColumnName, String dataType,  Int2DoubleMap originalNumberMapping,
			Int2ObjectMap<String> originalStringMapping, Int2ObjectMap<Date> originalDateMapping) {

		//System.out.println("Dei dataType " + dataType);
			
			//deanonymizedStringListForVolume = new ArrayList<>();
			//individualVolumeUnits = new ArrayList<>();
				
					// TODO Auto-generated method stub
			Bucket volumeBucket = new Bucket();
			
			volumeBucket.deanonymizedStringListForVolume = new ArrayList<>();
			volumeBucket.individualVolumeUnits = new ArrayList<>();
				
			
			if(dataType.equals("character") || dataType.contentEquals("character varying") || dataType.contentEquals("date"))
			{
				int total = currentBucket.valList.size();
				
				if(total%2==1) total++;
				
				total = total/2;
				
				//System.out.println("valList " + valList + " " +dataType);
				
				for(int i=0;i<total;i++) {
					volumeBucket.deanonymizedStringListForVolume.add(">=1");// + String.valueOf(1));
					volumeBucket.deanonymizedStringListForVolume.add("<=1");// + String.valueOf(1));
			
				}
				
				int containsZero = 0;
				
				//if(valList.contains(0)) containsZero = 1;
				
				//volumeBucket.deanonymizedStringListForVolume.add(String.valueOf(valList.size()-containsZero));// + String.valueOf(1));
				//volumeBucket.deanonymizedStringListForVolume.add("<=1");// + String.valueOf(1));
				//System.out.println("Acc value inside Bucket (Default String) " + String.valueOf(total-containsZero));
			
				return volumeBucket;
				
			}				
				boolean flagToBePrinted = false;
				boolean flagToBePrinted2 = false;
				
				//if(anonymousColumnName.equals("t08_c004")) {
				//	flagToBePrinted = true;
				//	flagToBePrinted2 = true;
				//}
					

				 if(flagToBePrinted) {
					 System.out.println("Col name -> " + anonymousColumnName);
					 System.out.println("Actual Bucket -> " + currentBucket.valList);
					 System.out.println("bfcForThisColumn -> " + bfcForThisColumn);
					 System.out.println("originalNumberMapping -> " + originalNumberMapping );
				 }
				 
        //System.out.println("La");
		        	//Integer startIndex, endIndex, greaterThanEqualToPredicateValue, lesserThanPredicateValue;
					
		        	//List<Integer> mappingIndex = bucketFloorsByColumns.get(anonymousTableName + "_" + anonymousColumnName);

					
						 for (int i=0; i<currentBucket.valList.size(); i++)
						 {
							 int currentAnonyVal = currentBucket.valList.get(i);

							 int nextAnonyVal = Integer.MAX_VALUE;
							 
							 
							 int indexOfCurrentAnonyVal = bfcForThisColumn.indexOf(currentAnonyVal);
							 
							 if(indexOfCurrentAnonyVal+1<bfcForThisColumn.size()) {
								 nextAnonyVal = bfcForThisColumn.get(indexOfCurrentAnonyVal+1);
							 }
							 
							 //System.out.println(" No " + i);   		
							//startIndex = valList.get(i);
							 //endIndex = 0;
						  
							/*
							   int stretchCount = 1;
							 
							 while((stretchCount+i) != valList.size())
							 	{ if(valList.get(stretchCount+i) == stretchCount+startIndex)
							 	    stretchCount = stretchCount + 1 ;
							 	    else
							 	    	{break;}
							 	}
							
							 endIndex = startIndex + stretchCount; //added this minus 1 later
							 
							 if(endIndex >= mappingIndex.size())
								 endIndex = -1;
							 
							 if(startIndex==0 && endIndex==1)
								 startIndex=-1;
							 
							 
							 i = i + (stretchCount-1);
							 
							 if(flagToBePrinted)
					            {
								 System.out.println("bucket right now : " + valList);										
							 System.out.println("stretchCount" + stretchCount);
							 System.out.println(); System.out.println("startIndex" + startIndex);
							 System.out.println("endIndex" + endIndex); 
							 System.out.println("mappingIndex size " + mappingIndex.size());System.out.println();
							 
					            }
							 
							 //System.out.println(" -1- ");
							 
							 if(startIndex==-1)
								 if( endIndex==-1) 
								 	{
									 System.out.println("Should not be happening");

									 continue;}
							 
							 
							 */
							 
					//if(currentAnonyVal>1) {	 
							
							 //System.err.println("Inside bucket -> " + currentAnonyVal);
							 
							 
							 if(flagToBePrinted) {
								 System.out.println("Current anonym value , next anonym value -> " + currentAnonyVal + " " + nextAnonyVal);
							 }
							 
							 
							 
							 if(dataType.equals("integer")) {
								 

								 Double temp = (double) currentAnonyVal;	

								
					               	if(temp!=null){	
					               		
					               		//>=PG MIN from DB
					               		if(currentAnonyVal == Integer.MIN_VALUE) {
					               			
					               			String minVal = PostgresVConfig.minValsForAllAnonymizedCols.get(anonymousColumnName);//QueryToExplainAnalyzePostgres.getMinValForThisAttributeFromDB(anonymousColumnName).strip();
					               			
					               			
					            			volumeBucket.deanonymizedStringListForVolume.add(">!" + String.valueOf(minVal));//minMaxValueOfThisCol.getFirst()));	
					            			
					            			if(flagToBePrinted2) {
						            			System.out.println("THIS IS PG_MIN VALUE FOR THIS ATTRIBUTE " + minVal);//minMaxValueOfThisCol.getFirst()));// + (currentAnonyVal+2) + " " + originalNumberMapping);
						            		}
						            		if(flagToBePrinted) {
						            			System.out.println("Acc value inside Bucket (Integer) \">!\" + " + minVal);//minMaxValueOfThisCol.getFirst()));
						            		}
						               	}
					               		else {  //Put >[N-1]
						            		volumeBucket.deanonymizedStringListForVolume.add(">=" + String.valueOf(temp));
						            		
	
						            		if(flagToBePrinted2) {
						            			//System.out.println("Anonymized value + Integer Map " + currentAnonyVal + " " + originalNumberMapping);
						            		}
						            		if(flagToBePrinted) {
						            			System.out.println("Acc value inside Bucket (Integer) \">=\" + " + temp);
						            		}
					               		}

					            		//if N+1 is present in BFC, do <=[N]
					            		//if(mappingIndex.contains(currentAnonyVal + 1)) {
					               		
					               		//if next value in BFC exists,
					            		if(nextAnonyVal!=Integer.MAX_VALUE) {
					            			
					            			//Consider NextAnonyVal as N now
					            			//Put <[N] if N is even
					            			//if(nextAnonyVal%2==0) { 
					            				
					            				volumeBucket.deanonymizedStringListForVolume.add("<<" + String.valueOf(nextAnonyVal));//originalNumberMapping.get(nextAnonyVal)));
					            			
					            				if(flagToBePrinted2) {
							            			//System.out.println("Anonymized value + Integer Map " + (nextAnonyVal) + " " + originalNumberMapping);
							            		}
							            		if(flagToBePrinted) {
							            			System.out.println("Acc value inside Bucket (Integer) \"<<\" + " + String.valueOf(nextAnonyVal));//originalNumberMapping.get(nextAnonyVal));
							            		}
					            			//}
					            			//Put <=[N-1] if N is odd
					            			/*else {
					            			
					            				volumeBucket.deanonymizedStringListForVolume.add("<=" + String.valueOf(originalNumberMapping.get(nextAnonyVal-1)));
					            				
					            				if(flagToBePrinted2) {
							            			System.out.println("Anonymized value + Integer Map " + (nextAnonyVal-1) + " " + originalNumberMapping);
							            		}
							            		if(flagToBePrinted) {
							            			System.out.println("Acc value inside Bucket (Integer) \"<=\" + " + originalNumberMapping.get(nextAnonyVal-1));
							            		}
					            			}
					            			*/
						            		
					            		}
					            		//Next anonyval doesnt exist, so just put <=PG_MAX
					            		else {
					            			
					            			//if N+1 is not present in BFC, and [N+2] holds, do <[N+2]
						            		//if(originalNumberMapping.containsKey(currentAnonyVal+2)) {
							            		
						            		//	volumeBucket.deanonymizedStringListForVolume.add("<<" + String.valueOf(originalNumberMapping.get(currentAnonyVal+2)));
							            		
							            	//	if(flagToBePrinted2) {
							            	//		System.out.println("Anonymized value + Integer Map " + (currentAnonyVal+2) + " " + originalNumberMapping);
							            	//	}
							            	//	if(flagToBePrinted) {
							            	//		System.out.println("Acc value inside Bucket (Integer) \"<<\" + " + originalNumberMapping.get(currentAnonyVal+2));
							            	//	}
						            		//}//if N+1 is not present in BFC, and [N+2] doesnt hold, <=PG_MAX
						            		//else {
						            			
					            				String maxVal = PostgresVConfig.maxValsForAllAnonymizedCols.get(anonymousColumnName);//QueryToExplainAnalyzePostgres.getMaxValForThisAttributeFromDB(anonymousColumnName).strip();
					               			
						            			volumeBucket.deanonymizedStringListForVolume.add("!<" + String.valueOf(maxVal));//minMaxValueOfThisCol.getSecond()));							
							            		
							            		if(flagToBePrinted2) {
							            			System.out.println("THIS IS PG_MAX VALUE FOR THIS ATTRIBUTE " + maxVal);//minMaxValueOfThisCol.getSecond());// + (currentAnonyVal+2) + " " + originalNumberMapping);
							            		}
							            		if(flagToBePrinted) {
							            			System.out.println("Acc value inside Bucket (Integer) \"!<\" + " + maxVal);//minMaxValueOfThisCol.getSecond());
							            		}
						            		//}					            								            								            			
					            		}
					            		
					               	}

							 }								 
							 
							 
							 
							 
							 
							 
							 
							 
							 
							 
							 
							 
							 
							 
							 
							 
							 
							 
							 
								
						 if(currentAnonyVal%2==1) {
							 //System.out.println("Current anonym value , next anonym value -> " + currentAnonyVal + " " + nextAnonyVal);
								
								
							 //Odd Number case
							 //if(!dataType.equals("integer"))
							 currentAnonyVal--; //Converted to even number
							 

							 if(dataType.contentEquals("numeric"))
					            {
					               	Double temp = originalNumberMapping.get(currentAnonyVal);	
					               	
					               
					               	
					               	if(temp!=null){	
					               		
					               		//>=PG MIN from DB
					               		if(currentAnonyVal == 0) {
					               			
					               			String minVal = PostgresVConfig.minValsForAllAnonymizedCols.get(anonymousColumnName);//QueryToExplainAnalyzePostgres.getMinValForThisAttributeFromDB(anonymousColumnName).strip();
					               			
					            			volumeBucket.deanonymizedStringListForVolume.add(">!" + String.valueOf(minVal));//minMaxValueOfThisCol.getFirst()));	
					            			
					            			if(flagToBePrinted2) {
						            			System.out.println("THIS IS PG_MIN VALUE FOR THIS ATTRIBUTE " + minVal);//minMaxValueOfThisCol.getFirst()));// + (currentAnonyVal+2) + " " + originalNumberMapping);
						            		}
						            		if(flagToBePrinted) {
						            			System.out.println("Acc value inside Bucket (Integer) \">!\" + " + minVal);//minMaxValueOfThisCol.getFirst()));
						            		}
						               	}
					               		else {  //Put >[N-1]
						            		volumeBucket.deanonymizedStringListForVolume.add(">>" + String.valueOf(temp));
						            		
	
						            		if(flagToBePrinted2) {
						            			System.out.println("Anonymized value + Integer Map " + currentAnonyVal + " " + originalNumberMapping);
						            		}
						            		if(flagToBePrinted) {
						            			System.out.println("Acc value inside Bucket (Integer) \">>\" + " + temp);
						            		}
					               		}

					            		//if N+1 is present in BFC, do <=[N]
					            		//if(mappingIndex.contains(currentAnonyVal + 1)) {
					               		
					               		//if next value in BFC exists,
					            		if(nextAnonyVal!=Integer.MAX_VALUE) {
					            			
					            			//Consider NextAnonyVal as N now
					            			//Put <[N] if N is even
					            			if(nextAnonyVal%2==0) { 
					            				
					            				volumeBucket.deanonymizedStringListForVolume.add("<<" + String.valueOf(originalNumberMapping.get(nextAnonyVal)));
					            			
					            				if(flagToBePrinted2) {
							            			System.out.println("Anonymized value + Integer Map " + (nextAnonyVal) + " " + originalNumberMapping);
							            		}
							            		if(flagToBePrinted) {
							            			System.out.println("Acc value inside Bucket (Integer) \"<<\" + " + originalNumberMapping.get(nextAnonyVal));
							            		}
					            			}
					            			//Put <=[N-1] if N is odd
					            			else {
					            			
					            				volumeBucket.deanonymizedStringListForVolume.add("<=" + String.valueOf(originalNumberMapping.get(nextAnonyVal-1)));
					            				
					            				if(flagToBePrinted2) {
							            			System.out.println("Anonymized value + Integer Map " + (nextAnonyVal-1) + " " + originalNumberMapping);
							            		}
							            		if(flagToBePrinted) {
							            			System.out.println("Acc value inside Bucket (Integer) \"<=\" + " + originalNumberMapping.get(nextAnonyVal-1));
							            		}
					            			}
					            			
						            		
					            		}
					            		//Next anonyval doesnt exist, so just put <=PG_MAX
					            		else {
					            			
					            			//if N+1 is not present in BFC, and [N+2] holds, do <[N+2]
						            		//if(originalNumberMapping.containsKey(currentAnonyVal+2)) {
							            		
						            		//	volumeBucket.deanonymizedStringListForVolume.add("<<" + String.valueOf(originalNumberMapping.get(currentAnonyVal+2)));
							            		
							            	//	if(flagToBePrinted2) {
							            	//		System.out.println("Anonymized value + Integer Map " + (currentAnonyVal+2) + " " + originalNumberMapping);
							            	//	}
							            	//	if(flagToBePrinted) {
							            	//		System.out.println("Acc value inside Bucket (Integer) \"<<\" + " + originalNumberMapping.get(currentAnonyVal+2));
							            	//	}
						            		//}//if N+1 is not present in BFC, and [N+2] doesnt hold, <=PG_MAX
						            		//else {
						            			
					            				String maxVal = PostgresVConfig.maxValsForAllAnonymizedCols.get(anonymousColumnName);//QueryToExplainAnalyzePostgres.getMaxValForThisAttributeFromDB(anonymousColumnName).strip();
					               			
						            			volumeBucket.deanonymizedStringListForVolume.add("!<" + String.valueOf(maxVal));//minMaxValueOfThisCol.getSecond()));							
							            		
							            		if(flagToBePrinted2) {
							            			System.out.println("THIS IS PG_MAX VALUE FOR THIS ATTRIBUTE " + maxVal);//minMaxValueOfThisCol.getSecond());// + (currentAnonyVal+2) + " " + originalNumberMapping);
							            		}
							            		if(flagToBePrinted) {
							            			System.out.println("Acc value inside Bucket (Integer) \"!<\" + " + maxVal);//minMaxValueOfThisCol.getSecond());
							            		}
						            		//}
					            								            								            			
					            		}
					            		
					            		
					            		
					            		
					            		
					               	}

					            }
							 else if(dataType.equals("character") || dataType.contentEquals("character varying"))
					            {
					               	String temp = originalStringMapping.get(currentAnonyVal);	
					               	
					               	if(temp!=null){	
					            		
					               		//Put >[N-1]
					            		volumeBucket.deanonymizedStringListForVolume.add(">>" + String.valueOf(temp));

					            		if(flagToBePrinted2) {
					            			System.out.println("Anonymized value + String Map " + currentAnonyVal + " " + originalStringMapping);
					            		}
					            		if(flagToBePrinted) {
					            			System.out.println("Acc value inside Bucket (String) \">>\" + " + temp);
					            		}
					            		
					            		
					            		//if [N+1] holds, do <[N+1]
					            		if(originalStringMapping.containsKey(currentAnonyVal+2)) {
						            		
					            			volumeBucket.deanonymizedStringListForVolume.add("<<" + String.valueOf(originalStringMapping.get(currentAnonyVal+2)));
						            		
						            		if(flagToBePrinted2) {
						            			System.out.println("Anonymized value + String Map " + (currentAnonyVal+2) + " " + originalStringMapping);
						            		}
						            		if(flagToBePrinted) {
						            			System.out.println("Acc value inside Bucket (String) \"<<\" + " + originalStringMapping.get(currentAnonyVal+2));
						            		}
					            		}//if [N+1] doesnt hold, pass, do <=PG_MAX
					            		else {
					            			
					            			String maxVal = PostgresVConfig.maxValsForAllAnonymizedCols.get(anonymousColumnName);//QueryToExplainAnalyzePostgres.getMaxValForThisAttributeFromDB(anonymousColumnName).strip();
					               			
					            			volumeBucket.deanonymizedStringListForVolume.add("<=" + String.valueOf(maxVal));//minMaxValueOfThisCol.getSecond()));							
						            		
						            		if(flagToBePrinted2) {
						            			System.out.println("THIS IS PG_MAX VALUE FOR THIS ATTRIBUTE " + maxVal);//minMaxValueOfThisCol.getSecond());// + (currentAnonyVal+2) + " " + originalNumberMapping);
						            		}
						            		if(flagToBePrinted) {
						            			System.out.println("Acc value inside Bucket (String) \"<=\" + " + maxVal);//minMaxValueOfThisCol.getSecond());
						            		}
					            		}
					               		
					               		
					               		
					               	}

					            }
							 else if(dataType.equals("date"))
					            {
					               	Date temp = originalDateMapping.get(currentAnonyVal);	
					               	

					               	if(temp!=null){	
					               		//Put >[N-1]
					            		volumeBucket.deanonymizedStringListForVolume.add(">>" + String.valueOf(temp));

					            		if(flagToBePrinted2) {
					            			System.out.println("Anonymized value + Date Map " + currentAnonyVal + " " + originalDateMapping);
					            		}
					            		if(flagToBePrinted) {
					            			System.out.println("Acc value inside Bucket (Date) \">>\" + " + temp);
					            		}
					            		
					            		
					            		//if [N+1] holds, do <[N+1]
					            		if(originalDateMapping.containsKey(currentAnonyVal+2)) {
						            		
					            			volumeBucket.deanonymizedStringListForVolume.add("<<" + String.valueOf(originalDateMapping.get(currentAnonyVal+2)));
						            		
						            		if(flagToBePrinted2) {
						            			System.out.println("Anonymized value + Date Map " + (currentAnonyVal+2) + " " + originalDateMapping);
						            		}
						            		if(flagToBePrinted) {
						            			System.out.println("Acc value inside Bucket (Date) \"<<\" + " + originalDateMapping.get(currentAnonyVal+2));
						            		}
					            		}//if [N+1] doesnt hold, pass, do <=PG_MAX
					            		else {
					            			
					            			String maxVal = PostgresVConfig.maxValsForAllAnonymizedCols.get(anonymousColumnName);//QueryToExplainAnalyzePostgres.getMaxValForThisAttributeFromDB(anonymousColumnName).strip();
					               			
					            			volumeBucket.deanonymizedStringListForVolume.add("!<" + String.valueOf(maxVal));//minMaxValueOfThisCol.getSecond()));							
						            		
						            		if(flagToBePrinted2) {
						            			System.out.println("THIS IS PG_MAX VALUE FOR THIS ATTRIBUTE " + maxVal);//minMaxValueOfThisCol.getSecond());// + (currentAnonyVal+2) + " " + originalNumberMapping);
						            		}
						            		if(flagToBePrinted) {
						            			System.out.println("Acc value inside Bucket (Date) \"!<\" + " + maxVal);//minMaxValueOfThisCol.getSecond());
						            		}
					            		}
					               	}

					            }
							 
							 
						 } else {
							 
							 //EVEN NUMBER CASE
							 
							 if(dataType.contentEquals("numeric"))
					            {
					               	Double temp = originalNumberMapping.get(currentAnonyVal);	

					               	if(temp!=null){	
					               		
					               		//>=PG MIN from DB
					               		if(currentAnonyVal == 0) {
					               			
					               			String minVal = PostgresVConfig.minValsForAllAnonymizedCols.get(anonymousColumnName);//QueryToExplainAnalyzePostgres.getMinValForThisAttributeFromDB(anonymousColumnName).strip();
					               			
					               			
					            			volumeBucket.deanonymizedStringListForVolume.add(">!" + String.valueOf(minVal));//minMaxValueOfThisCol.getFirst()));	
					            			
					            			if(flagToBePrinted2) {
						            			System.out.println("THIS IS PG_MIN VALUE FOR THIS ATTRIBUTE " + minVal);//minMaxValueOfThisCol.getFirst());// + (currentAnonyVal+2) + " " + originalNumberMapping);
						            		}
						            		if(flagToBePrinted) {
						            			System.out.println("Acc value inside Bucket (Integer) \">!\" + " + minVal);//minMaxValueOfThisCol.getFirst());
						            		}
						               	}
					               		else {  //Put >=[N]
						            		volumeBucket.deanonymizedStringListForVolume.add(">=" + String.valueOf(temp));
						            		
	
						            		if(flagToBePrinted2) {
						            			System.out.println("Anonymized value + Integer Map " + currentAnonyVal + " " + originalNumberMapping);
						            		}
						            		if(flagToBePrinted) {
						            			System.out.println("Acc value inside Bucket (Integer) \">=\" + " + temp);
						            		}
					               		}

					            		//if N+1 is present in BFC, do <=[N]
					            		//if(mappingIndex.contains(currentAnonyVal + 1)) {
					               		
					               		//if next value in BFC exists,
					            		if(nextAnonyVal!=Integer.MAX_VALUE) {
					            			
					            			//Consider NextAnonyVal as N now
					            			//Put <[N] if N is even
					            			if(nextAnonyVal%2==0) { 
					            				
					            				volumeBucket.deanonymizedStringListForVolume.add("<<" + String.valueOf(originalNumberMapping.get(nextAnonyVal)));
					            			
					            				if(flagToBePrinted2) {
							            			System.out.println("Anonymized value + Integer Map " + (nextAnonyVal) + " " + originalNumberMapping);
							            		}
							            		if(flagToBePrinted) {
							            			System.out.println("Acc value inside Bucket (Integer) \"<<\" + " + originalNumberMapping.get(nextAnonyVal));
							            		}
					            			}
					            			//Put <=[N-1] if N is odd
					            			else {
					            			
					            				volumeBucket.deanonymizedStringListForVolume.add("<=" + String.valueOf(originalNumberMapping.get(nextAnonyVal-1)));
					            				
					            				if(flagToBePrinted2) {
							            			System.out.println("Anonymized value + Integer Map " + (nextAnonyVal-1) + " " + originalNumberMapping);
							            		}
							            		if(flagToBePrinted) {
							            			System.out.println("Acc value inside Bucket (Integer) \"<=\" + " + originalNumberMapping.get(nextAnonyVal-1));
							            		}
					            			}
					            			
						            		
					            		}
					            		//Next anonyval doesnt exist, so just put <=PG_MAX
					            		else {
					            			
					            			//if N+1 is not present in BFC, and [N+2] holds, do <[N+2]
						            		//if(originalNumberMapping.containsKey(currentAnonyVal+2)) {
							            		
						            		//	volumeBucket.deanonymizedStringListForVolume.add("<<" + String.valueOf(originalNumberMapping.get(currentAnonyVal+2)));
							            		
							            	//	if(flagToBePrinted2) {
							            	//		System.out.println("Anonymized value + Integer Map " + (currentAnonyVal+2) + " " + originalNumberMapping);
							            	//	}
							            	//	if(flagToBePrinted) {
							            	//		System.out.println("Acc value inside Bucket (Integer) \"<<\" + " + originalNumberMapping.get(currentAnonyVal+2));
							            	//	}
						            		//}//if N+1 is not present in BFC, and [N+2] doesnt hold, <=PG_MAX
						            		//else {
					            			String maxVal = PostgresVConfig.maxValsForAllAnonymizedCols.get(anonymousColumnName);//QueryToExplainAnalyzePostgres.getMaxValForThisAttributeFromDB(anonymousColumnName).strip();
					               			
						            			
						            			volumeBucket.deanonymizedStringListForVolume.add("!<" + String.valueOf(maxVal));//minMaxValueOfThisCol.getSecond()));							
							            		
							            		if(flagToBePrinted2) {
							            			System.out.println("THIS IS PG_MAX VALUE FOR THIS ATTRIBUTE " + maxVal);//minMaxValueOfThisCol.getSecond());// + (currentAnonyVal+2) + " " + originalNumberMapping);
							            		}
							            		if(flagToBePrinted) {
							            			System.out.println("Acc value inside Bucket (Integer) \"!<\" + " + maxVal);//minMaxValueOfThisCol.getSecond());
							            		}
						            		//}
					            								            								            			
					            		}
					            		
					            		
					            		
					            		
					            		
					               	}

					            }
							 else if(dataType.equals("character") || dataType.contentEquals("character varying"))
					            {
								 /*
					               	String temp = originalStringMapping.get(currentAnonyVal);	
					               	
					               	if(temp!=null){	
					               		
					               		//Put >[N-1]
					            		volumeBucket.deanonymizedStringListForVolume.add(">=" + String.valueOf(temp));
					            		

					            		if(flagToBePrinted2) {
					            			System.out.println("Anonymized value + String Map " + currentAnonyVal + " " + originalStringMapping);
					            		}
					            		if(flagToBePrinted) {
					            			System.out.println("Acc value inside Bucket (String) \">=\" + " + temp);
					            		}
					            		

					            		//if N+1 is present in BFC, do <=[N]
					            		if(bfcForThisColumn.contains(currentAnonyVal + 1)) {
					            			
					            			volumeBucket.deanonymizedStringListForVolume.add("<=" + String.valueOf(originalStringMapping.get(currentAnonyVal)));
						            		
						            		if(flagToBePrinted2) {
						            			System.out.println("Anonymized value + String Map " + (currentAnonyVal) + " " + originalStringMapping);
						            		}
						            		if(flagToBePrinted) {
						            			System.out.println("Acc value inside Bucket (String) \"<=\" + " + originalStringMapping.get(currentAnonyVal));
						            		}
					            			
					            		}else {
					            			
					            			//if N+1 is not present in BFC, and [N+2] holds, do <[N+2]
						            		if(originalStringMapping.containsKey(currentAnonyVal+2)) {
							            		
						            			volumeBucket.deanonymizedStringListForVolume.add("<<" + String.valueOf(originalStringMapping.get(currentAnonyVal+2)));
							            		
							            		if(flagToBePrinted2) {
							            			System.out.println("Anonymized value + String Map " + (currentAnonyVal+2) + " " + originalStringMapping);
							            		}
							            		if(flagToBePrinted) {
							            			System.out.println("Acc value inside Bucket (String) \"<<\" + " + originalStringMapping.get(currentAnonyVal+2));
							            		}
						            		}//if N+1 is not present in BFC, and [N+2] doesnt hold, <=PG_MAX
						            		else {
						            			
						            			volumeBucket.deanonymizedStringListForVolume.add("!<" + String.valueOf(minMaxValueOfThisCol.getSecond()));							
							            		
							            		if(flagToBePrinted2) {
							            			System.out.println("THIS IS PG_MAX VALUE FOR THIS ATTRIBUTE " + minMaxValueOfThisCol.getSecond());// + (currentAnonyVal+2) + " " + originalNumberMapping);
							            		}
							            		if(flagToBePrinted) {
							            			System.out.println("Acc value inside Bucket (String) \"!<\" + " + minMaxValueOfThisCol.getSecond());
							            		}
						            		}
					            								            								            			
					            		}
					            		
					            		
					            		
					            		
					            		
					               	}
					               	*/


					            }
							 else if(dataType.equals("date"))
					            {
					               	Date temp = originalDateMapping.get(currentAnonyVal);	
					               	

					               	if(temp!=null){	
					               		
					               		
					               	//>=PG MIN from DB
					               		if(currentAnonyVal == 0) {
					               			
					               			String minVal = PostgresVConfig.minValsForAllAnonymizedCols.get(anonymousColumnName);
					               			
					            			volumeBucket.deanonymizedStringListForVolume.add(">=" + minVal);	
					            			
					            			if(flagToBePrinted2) {
						            			System.out.println("THIS IS PG_MIN VALUE FOR THIS ATTRIBUTE " + minVal);// + (currentAnonyVal+2) + " " + originalNumberMapping);
						            		}
						            		if(flagToBePrinted) {
						            			System.out.println("Acc value inside Bucket (Integer) \">!\" + " + minVal);
						            		}
						               	}
					               		else { 
					               		//Put >[N-1]
						            		volumeBucket.deanonymizedStringListForVolume.add(">=" + String.valueOf(temp));
						            		
	
						            		if(flagToBePrinted2) {
						            			System.out.println("Anonymized value + Date Map " + currentAnonyVal + " " + originalDateMapping);
						            		}
						            		if(flagToBePrinted) {
						            			System.out.println("Acc value inside Bucket (Date) \">=\" + " + temp);
						            		}
					            		
					               		}
					            		//if N+1 is present in BFC, do <=[N]
					            		if(bfcForThisColumn.contains(currentAnonyVal + 1)) {
					            			
					            			volumeBucket.deanonymizedStringListForVolume.add("<=" + String.valueOf(originalDateMapping.get(currentAnonyVal)));
						            		
						            		if(flagToBePrinted2) {
						            			System.out.println("Anonymized value + Date Map " + (currentAnonyVal) + " " + originalDateMapping);
						            		}
						            		if(flagToBePrinted) {
						            			System.out.println("Acc value inside Bucket (Date) \"<=\" + " + originalDateMapping.get(currentAnonyVal));
						            		}
					            			
					            		}else {
					            			
					            			//if N+1 is not present in BFC, and [N+2] holds, do <[N+2]
						            		if(originalDateMapping.containsKey(currentAnonyVal+2)) {
							            		
						            			volumeBucket.deanonymizedStringListForVolume.add("<<" + String.valueOf(originalDateMapping.get(currentAnonyVal+2)));
							            		
							            		if(flagToBePrinted2) {
							            			System.out.println("Anonymized value + Date Map " + (currentAnonyVal+2) + " " + originalDateMapping);
							            		}
							            		if(flagToBePrinted) {
							            			System.out.println("Acc value inside Bucket (Date) \"<<\" + " + originalDateMapping.get(currentAnonyVal+2));
							            		}
						            		}//if N+1 is not present in BFC, and [N+2] doesnt hold, <=PG_MAX
						            		else {
						            			
						            			String maxVal = PostgresVConfig.maxValsForAllAnonymizedCols.get(anonymousColumnName);
						               			
						            			
						            			volumeBucket.deanonymizedStringListForVolume.add("<=" + maxVal);							
							            		
							            		if(flagToBePrinted2) {
							            			System.out.println("THIS IS PG_MAX VALUE FOR THIS ATTRIBUTE " + maxVal);// + (currentAnonyVal+2) + " " + originalNumberMapping);
							            		}
							            		if(flagToBePrinted) {
							            			System.out.println("Acc value inside Bucket (Date) \"!<\" + " + maxVal);
							            		}
						            		}
					            								            								            			
					            		}
					            		
					            		
					               	}

					            }
							 
						 }
						 if(flagToBePrinted)
							 	System.out.println("End of insertion : " + volumeBucket.deanonymizedStringListForVolume);
										   
					 }
		
		return volumeBucket;
	}

	
	public void accumulateRegion(Region originalRegion) {
				
		//List<Double> currentbucketStructureIndividualVolume = new ArrayList<Double>();
		boolean printFlag = false;	
		
		originalRegion.bucketStructuresIndividualVolume = new ArrayList<Double>();
		
		for(BucketStructure bs : originalRegion.bsList) {
			double vol = accumulateBucketStructure(bs, printFlag);
			originalRegion.bucketStructuresIndividualVolume.add(vol);
		}
		
		if(printFlag)
			System.out.println("Accumulated bucketStructure volume inside Region :  "+ originalRegion.bucketStructuresIndividualVolume );
	}

	
	public double accumulateBucketStructure(BucketStructure currentBucketStructure, boolean printFlag) {
		
		double vol = 1;
		currentBucketStructure.individualVolumeUnits = new ArrayList<Double>();
		for(Bucket bucket : currentBucketStructure.bucketList) {
			
			if(bucket.deanonymizedStringListForVolume.size()!=0) {
				double bucketVol = accumulateBucket(bucket, printFlag);
				currentBucketStructure.individualVolumeUnits.add(bucketVol);
				vol = vol*bucketVol;
			}//else
			//	individualVolumeUnits.add(-1.0);			
		}
		
		if(printFlag) {
			System.out.print("Accumulated bucket volume inside BS : " + vol + "   [");
			//System.out.print("Accumulated bucket volume inside BS : " + vol + currentBucketStructure.individualVolumeUnits);
		for(double d : currentBucketStructure.individualVolumeUnits)
			//if(d!=-1.0) {
				System.out.print(" | " +d);
			//}
		
		System.out.println("]");
		
		}
		return vol;
		
	}


	public double accumulateBucket(Bucket currentBucket, boolean printFlag) {
		// TODO Auto-generated method stub
		
		double vol = 0;
		
		//for(int i=0; i<deanonymizedStringListForVolume.size(); i++) {
			
			//vol += Double.valueOf(deanonymizedStringListForVolume.get(i));
			
		//}
		
		//return vol;

		
		//if(deanonymizedStringListForVolume.size()==0)
		//	System.err.println("Engeyo idikithu");
		
		if(currentBucket.deanonymizedStringListForVolume.size()%2!=0)
			System.err.println("Pracchana + " + currentBucket.deanonymizedStringListForVolume);
		
		//System.out.println("deanonymizedStringListForVolume "  +   deanonymizedStringListForVolume);
		
		for(int i=0; i<currentBucket.deanonymizedStringListForVolume.size(); i=i+2) {

			String s = currentBucket.deanonymizedStringListForVolume.get(i);
			String t = currentBucket.deanonymizedStringListForVolume.get(i+1);

			String symbol1 = s.substring(0,2);
			String symbol2 = t.substring(0,2);
			double val1 = Double.valueOf(s.substring(2));
			double val2 = Double.valueOf(t.substring(2));
			double start = 0, end = 0;
			
			switch(symbol1) 
	        { 
	        case ">>": start = val1+1;
                break; 
            case ">=":  start = val1 ; 
                break; 
            case ">!":  start = val1 ;
                break; 
	        }
			switch(symbol2)
			{
            case "<<":  end = val2-1;
                break; 
            case "<=": end = val2 ;
                break; 
            case "!<": end = val2 ;
                break; 
	         
			}
			
			if(printFlag)
				System.out.println("Accumulated volume inside Bucket :" + (Math.abs(end - start)+1));
			currentBucket.individualVolumeUnits.add(Math.abs(end-start)+1);
			vol = vol + Math.abs(end - start) + 1;
		}
		
		return vol;
	}
	
	
	

}
