package in.ac.iisc.cds.dsl.cdgvendor.solver;

import java.io.FileWriter;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Calendar;
import java.util.Date;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

import org.apache.commons.lang.mutable.MutableInt;
import org.json.simple.JSONObject;

import in.ac.iisc.cds.dsl.cdgvendor.constants.PostgresVConfig;
import in.ac.iisc.cds.dsl.cdgvendor.reducer.Bucket;
import in.ac.iisc.cds.dsl.cdgvendor.reducer.BucketStructure;
import it.unimi.dsi.fastutil.ints.Int2DoubleMap;
import it.unimi.dsi.fastutil.ints.Int2DoubleOpenHashMap;
import it.unimi.dsi.fastutil.ints.Int2ObjectMap;
import it.unimi.dsi.fastutil.ints.Int2ObjectOpenHashMap;

public class DataGeneratorUtil {
	

	Map<String, String> minMap;
	List<String> tableNonKeys;
	Set<String> usableTableNonKeys;
	Map<String, Int2DoubleMap> reverseNumberAnonyMap;
	Map<String, Int2ObjectMap<String>> reverseStringAnonyMap;
	Map<String, Int2ObjectMap<Date>> reverseDateAnonyMap;
	int fkOffset;
	int dateOffset;
	Calendar calender;
	FileWriter fw;




	public DataGeneratorUtil(Map<String, String> minMap, List<String> tableNonKeys, Set<String> usableTableNonKeys,
			Map<String, Int2DoubleMap> reverseNumberAnonyMap, Map<String, Int2ObjectMap<String>> reverseStringAnonyMap,
			Map<String, Int2ObjectMap<Date>> reverseDateAnonyMap, int fkOffset, int dateOffset, Calendar calender,
			FileWriter fw) {
		super();
		this.minMap = minMap;
		this.tableNonKeys = tableNonKeys;
		this.usableTableNonKeys = usableTableNonKeys;
		this.reverseNumberAnonyMap = reverseNumberAnonyMap;
		this.reverseStringAnonyMap = reverseStringAnonyMap;
		this.reverseDateAnonyMap = reverseDateAnonyMap;
		this.fkOffset = fkOffset;
		this.dateOffset = dateOffset;
		this.calender = calender;
		this.fw = fw;
	}







	//public static void writeThisTupleOut(BucketStructure originalBucketStructure, Map<String, String> minMap, BucketStructure currentBucketStructure, List<String> tableNonKeys, long startPkIndex, int fkOffset,
	//		Calendar calender, int dateOffset, Set<String> usableTableNonKeys, HashMap<String, Int2DoubleOpenHashMap> reverseNumberMap,
	//		HashMap<String, Int2ObjectOpenHashMap<String>> reverseStringAnonyMap,
	//		HashMap<String, Int2ObjectOpenHashMap<Date>> reverseDateAnonyMap,
	//		FileWriter fw) {
		
		public void writeThisTupleOut(BucketStructure originalBucketStructure, BucketStructure currentBucketStructure, Long startPkIndex) {
			
		// TODO Auto-generated method stub
	      
				//pkCounter++;
				
				double rand = Math.random();
				
				while(rand==0.0 || rand==1.0) 
					rand = Math.random();
				
				
				
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
					
					Bucket y = currentBucketStructure.at(bs_counter);//fkOffset + viewNonKeyIdx.get(c));
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
						Bucket x = currentBucketStructure.at(fkOffset + c);
						
						
						//System.out.println("Usable non key here " + tableNonKey + " " + colType);
						
						//String
						if(colType.equals("integer")) {// || colType.equals("numeric"))) {
							
						
							if(x.getValList().size()>0)	
								rowTuple = rowTuple + "," +  String.valueOf(x.at(0));
							else
								rowTuple = rowTuple + ","; //NULL ASSIGNMENT
								
								

							//System.out.println("integer  + " + rowTuple);		
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
									
							//System.out.println("numeric  + " + rowTuple);
						}
						else if(colType.startsWith("character")) {
									if(reverseStringAnonyMap.containsKey(tableNonKey)) {
								
								
								//COMMENTED, BUT DONT KNOW WHY THIS WAS THERE		
								//x = newRegion.at(bucketStructureCountCorrespondingToActualRegion).at(bucketCountCorrespondingToActualRegion);
								x = originalBucketStructure.at(bucketCountCorrespondingToActualRegion);
								
								
								
								List<Integer> possibleValues = new ArrayList<Integer>();
								
								for(int t : x.getValList()) {
									if(t%2==0)
										possibleValues.add(t);
								}
								
								if(possibleValues.contains(0))
									possibleValues.remove(0);
								
								//System.out.println("Actual region bucket for string : " + possibleValues);
								
								
								//System.out.println("Chosen reverseStringAnonyMap " +  possibleValues + " " + reverseStringAnonyMap.get(tableNonKey));

								if(possibleValues.size()==0)
									rowTuple = rowTuple + ",\"\"";
								else if(possibleValues.size()==1) {
									rowTuple = rowTuple + "," + String.valueOf(reverseStringAnonyMap.get(tableNonKey).get(possibleValues.get(0)));
								
									//System.out.println("tableNonkey : "  + tableNonKey);
									//System.out.println("Chosen reverseStringAnonyMap.get(tableNonKey) (size 1) " +  possibleValues.get(0) + " " + reverseStringAnonyMap.get(tableNonKey).get(possibleValues.get(0)));
									
								}
								else {
									//System.out.println("tableNonkey : "  + tableNonKey);
									//System.out.println("reverseStringAnonyMap.get(tableNonKey)" + x.getValList() + " " +reverseStringAnonyMap.get(tableNonKey));
									
									int noOfEntriesInThisBucket = possibleValues.size();
									
									//double randomNumber = Math.random();
									//int chosenIndex = (int)(randomNumber * noOfEntriesInThisBucket);
									
									int chosenIndex = (int)(rand * noOfEntriesInThisBucket);
									
									rowTuple = rowTuple + "," + String.valueOf(reverseStringAnonyMap.get(tableNonKey).get(possibleValues.get(chosenIndex)));     
									//System.out.println("Chosen reverseStringAnonyMap.get(tableNonKey) (size n) " +chosenIndex + " "+ possibleValues.get(chosenIndex) + " " + reverseStringAnonyMap.get(tableNonKey).get(possibleValues.get(chosenIndex)));
									
								}
								
								/*
								if(x.getValList().size()==1 && x.getValList().get(0)==0)
									rowTuple = rowTuple + ",\"\"";//"," + String.valueOf(reverseStringAnonyMap.get(tableNonKey).get(2));
								else if(x.getValList().size()==1  && x.getValList().get(0)==1)
									rowTuple = rowTuple + "," + String.valueOf(reverseStringAnonyMap.get(tableNonKey).get(2));
								else {
									
									List<Integer> possibleValues = x.getValList();
									
									if(possibleValues.contains(0)) 
										possibleValues.remove(0);
									
									int noOfEntriesInThisBucket = possibleValues.size();
									
									double randomNumber = Math.random();
								
									int chosenIndex = (int)(randomNumber * noOfEntriesInThisBucket);
									
									rowTuple = rowTuple + "," + String.valueOf(reverseStringAnonyMap.get(tableNonKey).get(possibleValues.get(chosenIndex)));     
								}*/
								
								
							}else
								rowTuple = rowTuple + ",\"\"";
								
						}else if(colType.equals("date")) {
							
							if(reverseDateAnonyMap.containsKey(tableNonKey)) {
								
								//COMMENTED, BUT DONT KNOW WHY THIS WAS THERE		
								//x = newRegion.at(bucketStructureCountCorrespondingToActualRegion).at(bucketCountCorrespondingToActualRegion);
								x = originalBucketStructure.at(bucketCountCorrespondingToActualRegion);
								
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
								
								//System.out.println("Chosen reverseDateAnonyMap.get(tableNonKey) (size 1) " +  possibleValues + " " + " " + reverseDateAnonyMap.get(tableNonKey));
								
								
								if(possibleValues.size()==0) {
									rowTuple = rowTuple + "," + String.valueOf(calender.getTime());
								
									//System.out.println("No vals found for date");
									
								}else if(possibleValues.size()==1) {
									
									int valChosen = possibleValues.get(0);
									
									//if(valChosen%2==1 && reverseDateAnonyMap.get(tableNonKey).get(valChosen-1)==null) {
									//	System.err.println("tbl " + tableNonKey + " " + (valChosen-1)+ " " +reverseDateAnonyMap.get(tableNonKey).get(valChosen-1));
									//	throw new RuntimeException("stop");
									//}
									
									if(valChosen%2==1) {
										rowTuple = rowTuple + "," + String.valueOf(reverseDateAnonyMap.get(tableNonKey).get(valChosen-1));     
										
									}else
										rowTuple = rowTuple + "," + String.valueOf(reverseDateAnonyMap.get(tableNonKey).get(valChosen));     
									
									
									
									//rowTuple = rowTuple + "," + String.valueOf(reverseDateAnonyMap.get(tableNonKey).get(possibleValues.get(0)));
									
								}
								else {

									int noOfEntriesInThisBucket = possibleValues.size();
									
									//double randomNumber = Math.random();
									//int chosenIndex = (int)(randomNumber * noOfEntriesInThisBucket);
									
									int chosenIndex = (int)(rand * noOfEntriesInThisBucket);
									
									int valChosen = possibleValues.get(chosenIndex);
									
									//if(valChosen%2==1 && reverseDateAnonyMap.get(tableNonKey).get(valChosen-1)==null) {
									//	System.err.println("tbl " + tableNonKey + " " + (valChosen-1)+ " " +reverseDateAnonyMap.get(tableNonKey).get(valChosen-1));
									//	throw new RuntimeException("stop");
									//}
									
									if(valChosen%2==1) {
										rowTuple = rowTuple + "," + String.valueOf(reverseDateAnonyMap.get(tableNonKey).get(valChosen-1));     
										
									}else
										rowTuple = rowTuple + "," + String.valueOf(reverseDateAnonyMap.get(tableNonKey).get(valChosen));     
									
									
									//rowTuple = rowTuple + "," + String.valueOf(reverseDateAnonyMap.get(tableNonKey).get(possibleValues.get(chosenIndex)));     
									
								}
								
								/*
								
								if(x.getValList().size()==1)
									rowTuple = rowTuple + "," + String.valueOf(reverseDateAnonyMap.get(tableNonKey).get(2));
								else {
									
									List<Integer> possibleValues = x.getValList();
									
									if(possibleValues.contains(0)) 
										possibleValues.remove(0);
									
									int noOfEntriesInThisBucket = possibleValues.size();
									
									double randomNumber = Math.random();
								
									int chosenIndex = (int)(randomNumber * noOfEntriesInThisBucket);
									
									rowTuple = rowTuple + "," + String.valueOf(reverseDateAnonyMap.get(tableNonKey).get(possibleValues.get(chosenIndex)));     
								
								}
								*/
								
								//if(rowTuple.contains("null"))
								//	System.err.println("culprit here");
								
							}else				
								rowTuple = rowTuple + "," + String.valueOf(calender.getTime());
						}else { //INTEGER
							
							//System.out.println("Here : " + colType);
							
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
							
							//System.out.println("rando " + tableNonKey + " " + rand + " " + minMap.get(tableNonKey) + " " + minMap.get(tableNonKey).length() + " " + minMap);
							//System.out.println(rando.substring(0,Math.min(rando.length(), minMap.get(tableNonKey).length())));
							//rowTuple = rowTuple + ",\"\"";// + String.valueOf(x.at(0));
						}else {
							
							//double random2 = Math.random() * 1000;
							//int ran = (int) (random2);
							
							int ran = (int) (rand*1000);
							rowTuple = rowTuple + "," + String.valueOf(ran);
							

							//System.out.println("rand  + " + String.valueOf(rand*1000));
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
