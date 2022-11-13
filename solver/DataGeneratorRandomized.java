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

import in.ac.iisc.cds.dsl.cdgvendor.reducer.Bucket;
import in.ac.iisc.cds.dsl.cdgvendor.reducer.BucketStructure;
import in.ac.iisc.cds.dsl.cdgvendor.reducer.Region;
import it.unimi.dsi.fastutil.ints.Int2DoubleMap;
import it.unimi.dsi.fastutil.ints.Int2DoubleOpenHashMap;
import it.unimi.dsi.fastutil.ints.Int2ObjectMap;
import it.unimi.dsi.fastutil.ints.Int2ObjectOpenHashMap;
import it.unimi.dsi.fastutil.ints.IntList;

public class DataGeneratorRandomized {

	Region originalRegion;
	String relName;
	String regionName;
	long totalRowCount;
	int fkOffset;
	int dateOffset;
	int regionIdentifier;
	Calendar calender;
	Set<String> usableTableNonKeys;
	List<String> sortedBucketsToColumnNameMapping;	
	List<String> sortedUseableKeys;
	List<ArrayList<Integer>> fkeysList;
	List<List<Long>> fkRangeArrayList;
	List<Integer> bucketStructureCardinalityList;
	List<String> tableNonKeys;
	List<Long> pkRanges;
	Map<String, Map<String, IntList>> allBucketFloors;
	Map<String, String> minMap;
	Map<String, Int2DoubleMap> reverseNumberAnonyMap;
	Map<String, Int2ObjectMap<String>> reverseStringAnonyMap;
	Map<String, Int2ObjectMap<Date>> reverseDateAnonyMap;
	FileWriter fw;

	
	public DataGeneratorRandomized(Region originalRegion, String relName, String regionName, long totalRowCount,
			int fkOffset, int dateOffset, int regionIdentifier, Calendar calender, Set<String> usableTableNonKeys,
			List<String> sortedBucketsToColumnNameMapping, List<String> sortedUseableKeys,
			List<ArrayList<Integer>> fkeysList, List<List<Long>> fkRangeArrayList,			
			List<Integer> bucketStructureCardinalityList, List<String> tableNonKeys, List<Long> pkRanges,
			Map<String, Map<String, IntList>> allBucketFloors, Map<String, String> minMap,
			Map<String, Int2DoubleMap> reverseNumberAnonyMap, Map<String, Int2ObjectMap<String>> reverseStringAnonyMap, 
			Map<String, Int2ObjectMap<Date>> reverseDateAnonyMap, FileWriter fw) {
		super();
		this.originalRegion = originalRegion;
		this.relName = relName;
		this.regionName = regionName;
		this.totalRowCount = totalRowCount;
		this.fkOffset = fkOffset;
		this.dateOffset = dateOffset;
		this.regionIdentifier = regionIdentifier;
		this.calender = calender;
		this.usableTableNonKeys = usableTableNonKeys;
		this.sortedBucketsToColumnNameMapping = sortedBucketsToColumnNameMapping;
		this.sortedUseableKeys = sortedUseableKeys;
		this.fkeysList = fkeysList;
		this.fkRangeArrayList = fkRangeArrayList;
		this.bucketStructureCardinalityList = bucketStructureCardinalityList;
		this.tableNonKeys = tableNonKeys;
		this.pkRanges = pkRanges;
		this.allBucketFloors = allBucketFloors;
		this.minMap = minMap;
		this.reverseNumberAnonyMap = reverseNumberAnonyMap;
		this.reverseDateAnonyMap = reverseDateAnonyMap;
		this.reverseStringAnonyMap = reverseStringAnonyMap;
		this.fw = fw;
	}


	

	private void getValsForFkeys(double rand, BucketStructure temp2) {
		// TODO Auto-generated method stub
    	
    	//List<Bucket> fkBuckets = new ArrayList<Bucket>();
    
    	boolean printFlag = false;
    			
    	
    	for(int index = 0; index<fkeysList.size() ; index++) {
    	//for(List<Integer> key : fkeysList) {
    		
    		//if(index==2 && regionName.equals("t04_0")) printFlag = false;
    		//else printFlag = false;
    		//System.out.println("index " + index);
    		
    		List<Integer> key = fkeysList.get(index);
    		List<Long> fkRangeList = fkRangeArrayList.get(index);
    		
			//double rand = Math.random();
			
			//while(rand==0.0 || rand==1.0) 
			//	rand = Math.random();
			
    		double val;
    		int fkStartIndex = -1;
    		
    		if(key.size()==0) { //NEED TO CHECK CORRECTNESS OCCURRED IN T04
    			
    			if(printFlag)
    				System.out.println("Case 1 - Key size zero case " + relName + " " + index + " "+ key + " " + fkRangeList);
    			
    			Bucket newbuck = new Bucket();
    			newbuck.add(0);
    			//fkBuckets.add(newbuck);
    			temp2.add(newbuck);
	    		
    			continue;
    			
    		}else if(key.size()==1) {
    			
    			fkStartIndex = key.get(0);
    			
    		}else {
    			
    			//fkStartIndex = key.get(0);
    			
    			fkStartIndex = key.get((int) (key.size()*rand));  
    			
    			//fkStartIndex = key.get(1);
    			

    		}
    		
    		
    		//if(fkStartIndex == key.size()-1) {

			//	if(printFlag)
	    	//		System.out.println("Case 1 : " + fkStartIndex + " "+ key.size() + " " + (key.size()*rand));
				
			//	fkStartIndex--;
			//}
			
			//fkStartIndex = key.get(0);
    		
    		//double random = Math.random();

    		//if(relName.contentEquals("t10") || relName.contentEquals("t02")){
    		//System.out.println(key + " , index : " + index);
    		//	System.out.println(fkRangeList + " ,fkStartIndex : "+fkStartIndex + " " );//+ range1 + " " + range2);

    		//}
    		
    		if(fkStartIndex!=-1) {
				long range1 = fkRangeList.get(fkStartIndex);
				long range2 = fkRangeList.get(fkStartIndex+1); 
				
				range2--;
				
				if(printFlag)
	    			if(range1==range2)
					System.out.println("Case 2 - Same range case " + range1 + " " +range2 + " " + fkStartIndex);

				//if(range1+1==range2)
				//	System.out.println("Case 3 - 1 diff range case " + range1 + " " +range2 );
				
				long diff = range2 - range1;
				
				if(printFlag)
	    			if(diff<0){
					System.out.println("Case 2.2 - UNEXPECTED  +range1 + range2 + rand + (range1 + diff*rand) + (range1 + diff)*rand");
					System.out.println( range1 + " " + range2 + " " + rand + " " + (range1 + (diff*rand))  + " " + ((range1 + diff)*rand));
				
				}
				
				//val = range1 + diff*rand;				
				//val = range1;				
				//if(val==range2) val--;
				
				val = range1 + (diff*rand);
				
				//val = range1;
				
				//if(val==range2) {
				//	val--; 
				//	System.out.println("Case 4 - I did decrement " + val + " " + range1 + " " + range2 );
					
				//}
				
	    		
				if(printFlag)
	    			if(val<range1 || val>=range2) {
					System.out.println("Case 5 - UNEXPECTED  + val + range1 + range2 + rand + (range1 + diff*rand) + (range1 + diff)*rand");
					System.out.println(val + " " + range1 + " " + range2 + " " + rand + " " + (range1 + (diff*rand))  + " " + ((range1 + diff)*rand));
				}
	    		
	    		Bucket a = new Bucket();
	    		a.add((int)val);
	    		//fkBuckets.add(a);
	    		
	    		temp2.add(a);
	    		
	    		if(printFlag) System.err.println("val\t" + (int)val);
	    		
    		}
    	}
    	
		//return fkBuckets;
	}
	
    
    public void createNewRegionWithValuesDistributedAccordingToProbability(Region volumeRegion) {
    	
    	//System.out.println("Region Of Relation Summary with anonymized values : "  + this.toString());
		
    	//Region newRegion = new Region();
    	
    	boolean printFlag = false;
		boolean printFlag2 = false;
		
		//System.out.println("relName " + relName);
		//System.out.println("fkeysList " + fkeysList);
		//System.out.println("fkRangeArrayList " + fkRangeArrayList);
		
		//FK COMMON GENERATION WAS HERE
/*
		List<Bucket> fkBuckets = getValsForFkeys(relName, fkeysList, fkRangeArrayList);
		
		BucketStructure temp = new BucketStructure();
		
		for(Bucket b : fkBuckets) {
			temp.add(b);
		}
		
		BucketStructure temp2 = temp.getDeepCopy();
		*/
		
		//if(relName.contentEquals("t12")){
			//printFlag2 = true;
		//}
			//System.out.println("temp " + temp);
			//System.out.println(fkRangeList);
		Long startPkIndex = pkRanges.get(regionIdentifier);
	    
		DataGeneratorUtil dataWriter = new DataGeneratorUtil(minMap, tableNonKeys, usableTableNonKeys, reverseNumberAnonyMap, 
				reverseStringAnonyMap, reverseDateAnonyMap, fkOffset, dateOffset, calender,	fw);
		
		
		if(volumeRegion.bucketStructuresIndividualVolume.size()>1) {
			
			//System.out.println("startPkIndex a" + startPkIndex);
			
			
			long heapFreeSize = Runtime.getRuntime().freeMemory();

			if(heapFreeSize < 35000000000L)
				System.gc();

			
	    	double totalVol = 0;
	
	    	if(printFlag2)
				System.out.println("bucketStructuresIndividualVolume =  " + volumeRegion.bucketStructuresIndividualVolume);

			for(Double d : volumeRegion.bucketStructuresIndividualVolume)
				totalVol += d;
			
			long remainingRows = totalRowCount;
			
			//bucketStructureCardinalityCumulativeList.add(totalRowCount);
			
			for(int i=0; i<volumeRegion.bucketStructuresIndividualVolume.size()-1; i++) {
				double currentBSProbability = volumeRegion.bucketStructuresIndividualVolume.get(i)/totalVol;
				
				int rowCountForThisBS = (int) (currentBSProbability * totalRowCount);
				remainingRows = remainingRows - rowCountForThisBS;
				

				bucketStructureCardinalityList.add(rowCountForThisBS);
				
				if(printFlag) {
					System.out.println("bucketStructuresIndividualVolume.get(i) : totalVol : currentBSProbability "+ volumeRegion.bucketStructuresIndividualVolume.get(i) + " " + totalVol + " " +currentBSProbability);//bucketStructureProbabilityCDF : bucketStructureIndiviadualProbabilities : totalVol : bucketStructuresIndividualVolume :  " +bucketStructureProbabilityCDF + "  " + bucketStructureIndiviadualProbabilities + " " + totalVol + " " +bucketStructuresIndividualVolume );

				System.out.println("Val Gen - Inside region : BS number, assignedCard : totalCard " + i +" " + rowCountForThisBS + " " + totalRowCount);
				}
				//ValueCombination valueCombination = new ValueCombination(bsList.get(i).createNewBucketStructureWithValuesDistributedAccordingToProbability(rowCountForThisBS), rowCountForThisBS);//if you wish to get the valuecombination too
	            //mergedValueCombinations.add(valueCombination);
				
				if(printFlag2)
					System.out.println("rowcount =  " +rowCountForThisBS + " " + i + " " + remainingRows);

				for(int k=0; k<rowCountForThisBS; k++) {
					
					
					double rand = Math.random();
					
					while(rand==0.0 || rand==1.0) 
						rand = Math.random();
					
					BucketStructure temp2 = new BucketStructure();
					
					
					//List<Bucket> fkBuckets = getValsForFkeys(relName, regionName, fkeysList, fkRangeArrayList);

					//for(Bucket b : fkBuckets) {
					//	temp2.add(b);
					//}
					
					
					getValsForFkeys(rand, temp2);
					
					//BucketStructure temp2 = temp.getDeepCopy();
					
					if(printFlag2)
						System.out.println("before " +temp2);
					
					
					BucketStructure randomValuesForThisBucketStructure = createNewBucketStructureWithValuesDistributedAccordingToProbability(volumeRegion.bsList.get(i), printFlag, rand);
					
					
					
					for(Bucket bt : randomValuesForThisBucketStructure.getAll()) {
						temp2.add(bt);
					}
					

					if(printFlag2)
						System.out.println("after " +temp2);
					
					//newRegion.bsList.add(temp2);
					
					BucketStructure originalBucketStructure = originalRegion.at(i);
	            	
					dataWriter.writeThisTupleOut(originalBucketStructure, temp2, startPkIndex);
										
	            	//DataGeneratorUtil.writeThisTupleOut(originalBucketStructure, minMap, temp2, tableNonKeys, startPkIndex, fkOffset,
	            	//		calender, dateOffset, usableTableNonKeys, reverseNumberAnonyMap, reverseStringAnonyMap, reverseDateAnonyMap, fw);
	            	
	            	startPkIndex++;
				}
				
			}

			if(printFlag2)
				System.err.println("relname + remainingrows " + relName + " " +remainingRows);
			//ValueCombination valueCombination = new ValueCombination(bsList.get(bucketStructuresIndividualVolume.size()-1).createNewBucketStructureWithValuesDistributedAccordingToProbability(remainingRows), remainingRows);//if you wish to get the valuecombination too
            //mergedValueCombinations.add(valueCombination);
			if(printFlag) {
				System.out.println("bucketStructuresIndividualVolume.get(i) : totalVol : currentBSProbability "+ volumeRegion.bucketStructuresIndividualVolume.get(volumeRegion.bucketStructuresIndividualVolume.size()-1) + " " + totalVol + " last" );//bucketStructureProbabilityCDF : bucketStructureIndiviadualProbabilities : totalVol : bucketStructuresIndividualVolume :  " +bucketStructureProbabilityCDF + "  " + bucketStructureIndiviadualProbabilities + " " + totalVol + " " +bucketStructuresIndividualVolume );

			System.out.println("Val Gen - Inside region : BS number, assignedCard : " + (volumeRegion.bucketStructuresIndividualVolume.size()-1) +" " + remainingRows);
			}
			
			bucketStructureCardinalityList.add((int) remainingRows);

			
			for(int k=0; k<remainingRows; k++) {
				
				
				double rand = Math.random();
				
				while(rand==0.0 || rand==1.0) 
					rand = Math.random();
				
				BucketStructure temp2 = new BucketStructure();
				
				
				
				//List<Bucket> fkBuckets = getValsForFkeys(relName, regionName, fkeysList, fkRangeArrayList);

				//for(Bucket b : fkBuckets) {
				//	temp2.add(b);
				//}
				

				getValsForFkeys(rand, temp2);
				
				
				//BucketStructure temp2 = temp.getDeepCopy();
				
				if(printFlag2)
					System.out.println("before " +temp2);
				
				BucketStructure randomValuesForThisBucketStructure = createNewBucketStructureWithValuesDistributedAccordingToProbability(volumeRegion.bsList.get(volumeRegion.bucketStructuresIndividualVolume.size()-1), printFlag, rand);
				
				for(Bucket bt : randomValuesForThisBucketStructure.getAll()) {
					temp2.add(bt);
				}
				
				//for(Bucket bt : bsList.get(bucketStructuresIndividualVolume.size()-1).createNewBucketStructureWithValuesDistributedAccordingToProbability(printFlag).getAll()) {
				//	temp2.add(bt);
				//}
				

				if(printFlag2)
					System.out.println("after " +temp2);
				
				//newRegion.bsList.add(temp2);
				BucketStructure originalBucketStructure = originalRegion.at(originalRegion.bsList.size()-1);
            	            	
				
				dataWriter.writeThisTupleOut(originalBucketStructure, temp2, startPkIndex);
				
				//DataGeneratorUtil.writeThisTupleOut(originalBucketStructure, minMap, temp2, tableNonKeys, startPkIndex, fkOffset,
            	//		calender, dateOffset, usableTableNonKeys, reverseNumberAnonyMap, reverseStringAnonyMap, reverseDateAnonyMap, fw);
				
				startPkIndex++;
				
			}
			
			
			//newRegion.bsList.add(bsList.get(bucketStructuresIndividualVolume.size()-1).createNewBucketStructureWithValuesDistributedAccordingToProbability(printFlag));

			
			
			/*
			for(int i=0; i<bucketStructuresIndividualVolume.size(); i++) {
				double currentBSProbability = bucketStructuresIndividualVolume.get(i)/totalVol;
				bucketStructureIndiviadualProbabilities.add(currentBSProbability);
				
				if(cdfUptoPreviousBS!=-1) {
					cdfUptoPreviousBS = cdfUptoPreviousBS + currentBSProbability;
				}
				else
					cdfUptoPreviousBS = currentBSProbability;
				
				bucketStructureProbabilityCDF.add(cdfUptoPreviousBS);
				
			}
			
			
			double randomNumber = Math.random();
			
			while(randomNumber==0.0 || randomNumber==1.0)
				randomNumber = Math.random();
			
			int indexOfBucketChosen = -1;
			
			int i=0;
			
			//for(i=0; i<bucketStructureProbabilityCDF.size(); i++)
			while(i<bucketStructureProbabilityCDF.size() && randomNumber >= bucketStructureProbabilityCDF.get(i))
				i++;
			
			indexOfBucketChosen = i-1;
			
	
			
			
			System.out.println("randomNumber : indexOfBucketChosen : bucketStructureProbabilityCDF : bucketStructureIndiviadualProbabilities : totalVol : bucketStructuresIndividualVolume :  " + randomNumber + " " + indexOfBucketChosen + " " +bucketStructureProbabilityCDF + "  " + bucketStructureIndiviadualProbabilities + " " + totalVol + " " +bucketStructuresIndividualVolume );
		
			*/
			
		}
		else {
			//System.out.println("startPkIndex b " + startPkIndex);
			
			long heapFreeSize = Runtime.getRuntime().freeMemory();

			if(heapFreeSize < 35000000000L)
				System.gc();


			bucketStructureCardinalityList.add((int) totalRowCount);
			
			for(int k=0; k<totalRowCount; k++) {
				
				double rand = Math.random();
				
				while(rand==0.0 || rand==1.0) 
					rand = Math.random();
				BucketStructure temp2 = new BucketStructure();
				
				
				//List<Bucket> fkBuckets = getValsForFkeys(relName, regionName, fkeysList, fkRangeArrayList);

				//for(Bucket b : fkBuckets) {
				//	temp2.add(b);
				//}
				
				
				//List<Bucket> fkBuckets = 	
				getValsForFkeys(rand, temp2);
				
				//System.out.println("k " + k + " " + fkBuckets);
				
				//BucketStructure temp2 = temp.getDeepCopy();
				
				if(printFlag2)
					System.out.println("before2  " +temp2 );
				
				if(printFlag2)
					System.out.println("BS  " + volumeRegion.bsList.get(0));
				
				BucketStructure randomValuesForThisBucketStructure = createNewBucketStructureWithValuesDistributedAccordingToProbability(volumeRegion.bsList.get(0), printFlag, rand);
				
				//System.out.println("randomValuesForThisBucketStructure =  " +randomValuesForThisBucketStructure.printTupleString());

				for(Bucket bt : randomValuesForThisBucketStructure.getAll()) {
					temp2.add(bt);
					//System.out.println(bt + " " +bt.getDeanonymizedTupleValueList());
				}
				
				//for(Bucket bt : bsList.get(0).createNewBucketStructureWithValuesDistributedAccordingToProbability(printFlag).getAll()) {
				//	temp2.add(bt);
				//}
				
				if(printFlag2)
					System.out.println("after2  " +temp2);
				
				//System.out.println("Final BS : "+ temp2); 
            	//newRegion.bsList.add(temp2);
				BucketStructure originalBucketStructure = originalRegion.at(0);
				
				dataWriter.writeThisTupleOut(originalBucketStructure, temp2, startPkIndex);
				
				//DataGeneratorUtil.writeThisTupleOut(originalBucketStructure, minMap, temp2, tableNonKeys, startPkIndex, fkOffset,
            	//		calender, dateOffset, usableTableNonKeys, reverseNumberAnonyMap, reverseStringAnonyMap, reverseDateAnonyMap, fw);
				
				startPkIndex++;
				
			}
			
			
		}
			//newRegion.bsList.add(bsList.get(0).createNewBucketStructureWithValuesDistributedAccordingToProbability(printFlag));
		//System.out.println("Chosen : random number, index, probCDF, probability : " + randomNumber + " " + indexOfBucketChosen + " " + bucketStructureProbabilityCDF.get(indexOfBucketChosen) + " " + bucketStructuresIndividualVolume.get(indexOfBucketChosen)); 
	
		//Region randomlyGeneratedRegion = new Region();
		
		/*
		for(int i=0; i<bucketStructuresIndividualVolume.size(); i++) {
			
			BucketStructure currentBS = bsList.get(i);
			double probabilityForThisBS = individualVolumeUnits.get(i);
			int rowForThisBS = totalCount * probabilityForThisBS; //DOUBLE TO INT ISSUES??
			
			BucketStructure randomlyGeneratedBS = currentBS.generateBucketStructure(rowForThisBS);
		
			randomlyGeneratedRegion.bsList.add(randomlyGeneratedBS);
		}
		
		return randomlyGeneratedRegion;
		*/
		
		//return newRegion;
    }
    
    
	public BucketStructure createNewBucketStructureWithValuesDistributedAccordingToProbability(BucketStructure volumeBucketStructure, boolean printFlag, double rand) {
		// TODO Auto-generated method stub
		BucketStructure newBucketStructure = new BucketStructure();
		
		int index=0;
		
		//Map<String, Map<String, IntList>> allBucketFloors= (Map<String, Map<String, IntList>>) FileUtils.readObjectFromFile("/home/dsladmin/multi-query-workspace/codd-data-gen/resources/cdgvendor/input/postgres/BucketFloorsByColumns.dat");
		
		//System.out.println("Bucketlist inside create:" + bucketList);
		
		
		//List<String> sortedUseableKeys = new ArrayList<>();
		
		//for(String s : sortedUseableKeys2)
		//	sortedUseableKeys.add(s);
		//Collections.sort(sortedUseableKeys);
		
		for(int i=0; i<volumeBucketStructure.bucketList.size(); i++) {
			Bucket b1 = volumeBucketStructure.bucketList.get(i);
			
			//if(i==1) printFlag=true;
			//else printFlag=false;
			

        	String anonymousTableAndColumnName = sortedUseableKeys.get(index);
        	index++;
            //Integer weNeedToCheckAtThisIndex = sortedBucketsToColumnNameMapping.indexOf(anonymousTableName + "_" + anonymousColumnName);
			
				//String	lessThanSymbol = "<"; String greaterThanSymbol = ">"; 	String equalitySymbol = "=";
        	//System.out.println("Chumma " + chumma++ + " " +anonymousTableAndColumnName + bucketList);

        	//System.out.println("print usable "+ anonymousTableAndColumnName + " " + b1.deanonymizedStringListForVolume + " " + usableTableNonKeys);

        	
        	
			
			if(b1.deanonymizedStringListForVolume.size()!=0) {
				
				
				
				Map<String, IntList> bucketFloorsByColumns = allBucketFloors.get(relName);
				
				
				List<Integer> bfcForThisColumn=null;//bucketFloorsByColumns.get(anonymousTableAndColumnName);//anonymousTableName + "_" + anonymousColumnName);

				
	            for(Map.Entry<String, IntList> entry : bucketFloorsByColumns.entrySet()) {
	            	String colNameWithHashCode = entry.getKey();
	            	String splitTheName[] = colNameWithHashCode.split("_");
	            	
	            	if((splitTheName[0] + "_" + splitTheName[1]).equals(anonymousTableAndColumnName)){
	            		bfcForThisColumn = entry.getValue();
	            	}
	            }
	            
	            //System.out.println("Inside vol gen : " + bfcForThisColumn + " "+ anonymousTableAndColumnName+ " "+ bucketFloorsByColumns);
	    		
		
				//Collections.sort(bfcForThisColumn);
				
				double minValueInBfc = Integer.MAX_VALUE;
				
				if(bfcForThisColumn.get(0)==Integer.MIN_VALUE) {
					if(bfcForThisColumn.size()>1)
					minValueInBfc = bfcForThisColumn.get(1);
				}
				else 
					minValueInBfc = bfcForThisColumn.get(0);
				
				if(minValueInBfc == Integer.MAX_VALUE)
					System.out.println("Should not happen in BFC");
					
				if(printFlag)
					System.out.println("Val Gen - Inside Bucket Structure : Bucket now : " + b1.deanonymizedStringListForVolume);
				
				Bucket b2 = createNewBucketWithValuesDistributedAccordingToProbability(b1, minValueInBfc, printFlag, rand);
				
				//System.out.print("b2 " + b2.getValList());
				//System.out.println("   " + b2.getDeanonymizedTupleValueList());
				
				newBucketStructure.bucketList.add(b2);
			}
			else {
				Bucket b2 = new Bucket();
				b2.add(0);
				newBucketStructure.bucketList.add(b2);
			}
			
			
	    	
		}
		
		return newBucketStructure;
	}


	public Bucket createNewBucketWithValuesDistributedAccordingToProbability(Bucket volumeBucket, double minValueInBfc, boolean printFlag, double rand) {
		// TODO Auto-generated method stub
		
		/*Bucket randomlyGeneratedValueContainingBucket = new Bucket();
		
		if(individualVolumeUnits.size()>1) {
			
			int noOfEntriesInThisBucket = valList.size();
			
			double randomNumber = Math.random();
		
			int chosenIndex = (int)(randomNumber * noOfEntriesInThisBucket);
			
			randomlyGeneratedValueContainingBucket.valList.add(valList.get(chosenIndex));

		}
		else {
			
			randomlyGeneratedValueContainingBucket.valList.add(0);
			
		}
		
		return randomlyGeneratedValueContainingBucket; */
		
		//printFlag = true;
		
		Bucket newBucket = new Bucket();
		
		newBucket.deanonymizedTupleValueList = new ArrayList<Double>();
		
		//if(printFlag)
		//	System.out.println("Bucket Vols : " + individualVolumeUnits);
		
		//System.out.println("Currently : " + deanonymizedStringListForVolume);
		
		
		if(volumeBucket.individualVolumeUnits.size()>1) {
		
		List<Double> bucketIndividualProbabilities = new ArrayList<Double>();
		List<Double> bucketIndividualProbabilityCDF = new ArrayList<Double>();
		
			double totalVol = 0;
	
			for(Double d : volumeBucket.individualVolumeUnits)
				totalVol += d;
			
			double cdfUptoPreviousBS = -1;
			
			for(int i=0; i<volumeBucket.individualVolumeUnits.size(); i++) {
				
				double volumeBucketProbability = volumeBucket.individualVolumeUnits.get(i)/totalVol;
				bucketIndividualProbabilities.add(volumeBucketProbability);
				
				if(cdfUptoPreviousBS!=-1) {
					cdfUptoPreviousBS = cdfUptoPreviousBS + volumeBucketProbability;
				}
				else
					cdfUptoPreviousBS = volumeBucketProbability;
				
				bucketIndividualProbabilityCDF.add(cdfUptoPreviousBS);
				
			}
			
			
			//double randomNumber = Math.random();
			
			//while(randomNumber==0.0 || randomNumber==1.0)
			//	randomNumber = Math.random();
			
			int indexOfBucketChosen = -1;
			
			int k=0;
			
			//for(i=0; i<bucketStructureProbabilityCDF.size(); i++)
			while(k<bucketIndividualProbabilityCDF.size() && rand >= bucketIndividualProbabilityCDF.get(k))
				k++;
			
			indexOfBucketChosen = k*2;
			
			boolean isThisAValidCombo = false;
			boolean goLeftTillDeadEnd = false;
			boolean goRightTillDeadEnd = false;
			
			boolean equalityAvailable = false;
			
			int indexOfBucketChosenBackup = indexOfBucketChosen;
			
			double start = 0, end = 0;
			
			
			
			
			Bucket equalBucket = new Bucket();

			
			
			
			for(String st : volumeBucket.deanonymizedStringListForVolume) {
				
				
				if(st.substring(0,2).equals(">=") || st.substring(0,2).equals("<=") ) {
					
					double temp2 = Double.valueOf(st.substring(2));
					
					equalBucket.deanonymizedTupleValueList = new ArrayList<Double>();
					
					equalBucket.valList.add((int)temp2);
					equalBucket.deanonymizedTupleValueList.add(temp2);
					equalityAvailable = true;
					break;
					//return temp;
				}
			}

			
			//newBucket.valList.add(indexOfBucketChosen)
			while(!isThisAValidCombo) {
			
				String s = volumeBucket.deanonymizedStringListForVolume.get(indexOfBucketChosen);
				String t = volumeBucket.deanonymizedStringListForVolume.get(indexOfBucketChosen+1);
	
				String symbol1 = s.substring(0,2);
				String symbol2 = t.substring(0,2);
				double val1 = Double.valueOf(s.substring(2));
				double val2 = Double.valueOf(t.substring(2));
				
				//System.out.println("start, end before  " +val1 + " " + val2 + " " + indexOfBucketChosen + " " + deanonymizedStringListForVolume);

				
				switch(symbol1) 
		        { 
		        case ">>": start = val1+1;
	                break; 
	            case ">=":  start = val1 ; equalityAvailable = true;
	                break; 
	            case ">!":  start = val1 ;
	                break; 
		        }
				switch(symbol2)
				{
	            case "<<":  end = val2-1;
	                break; 
	            case "<=": end = val2 ; equalityAvailable = true;
	                break; 
	            case "!<": end = val2 ;
	                break; 
		         
				}
				
				//System.out.println("start, end  " + start + " " + end + " " +s + " " + t + " " + indexOfBucketChosen + " " + deanonymizedStringListForVolume);
				
				
				if(start<=end) {
					isThisAValidCombo = true;
					break;
				}else if(equalityAvailable) {
					
					return equalBucket;
					
					/*for(String st : deanonymizedStringListForVolume) {
						if(st.substring(0,2).equals(">=") || st.substring(0,2).equals("<=") ) {
							
							Bucket temp = new Bucket();
							double temp2 = Double.valueOf(s.substring(2));
							
							temp.deanonymizedTupleValueList = new ArrayList<Double>();
							
							//temp.valList.add((int)temp2);
							temp.deanonymizedTupleValueList.add(temp2);
							
							return temp;
						}
					}*/
				
				}else if(!goLeftTillDeadEnd) {
					
					//System.out.println("start, end before decrement " + start + " " + end);
					
					if(symbol1.equals(">>") && symbol2.equals("<<")) {
						
						Bucket temp = new Bucket();
						
						start = start - 1;
						end = end + 1;
						
						Double diff = end-start;

						temp.deanonymizedTupleValueList = new ArrayList<Double>();
						temp.deanonymizedTupleValueList.add(start + (diff/2));
						
						//System.out.println("Proceeding with INVALID assignment : " + (start + (diff/2)) + " for " + deanonymizedStringListForVolume);
						//end = end + 1;		
						
						return temp;
						
					}
					
					indexOfBucketChosen -= 2;
					
					
					if(indexOfBucketChosen<0) {
						goLeftTillDeadEnd = true;
						indexOfBucketChosen = indexOfBucketChosenBackup;
					}
					
					//System.out.println("inside goLeftTillDeadEnd after decrement " + indexOfBucketChosen);
					
					
					
				}else if(!goRightTillDeadEnd) {

					//System.out.println("start, end before increment " + start + " " + end);
					
					if(symbol1.equals(">>") && symbol2.equals("<<")) {
						
						Bucket temp = new Bucket();
						
						start = start - 1;
						end = end + 1;
						
						Double diff = end-start;

						temp.deanonymizedTupleValueList = new ArrayList<Double>();
						temp.deanonymizedTupleValueList.add(start + (diff/2));
						
						//System.out.println("Proceeding with INVALID assignment : " + (start + (diff/2)) + " for " + deanonymizedStringListForVolume);
						//end = end + 1;		
						
						return temp;
						
					}
					
					indexOfBucketChosen += 2;
					
					
					
					if(indexOfBucketChosen >= volumeBucket.deanonymizedStringListForVolume.size()) {
						goRightTillDeadEnd = true;
						indexOfBucketChosen = indexOfBucketChosenBackup;
					
						
						/*if(deanonymizedStringListForVolume.get(0).substring(0,2).equals(">!"))
							indexOfBucketChosen = 0;
						else if(deanonymizedStringListForVolume.get(deanonymizedStringListForVolume.size()-1).substring(0,2).equals("!<"))
							indexOfBucketChosen = deanonymizedStringListForVolume.size()-2;*/
					}
					
					//System.out.println("inside goRightTillDeadEnd after increment " + indexOfBucketChosen);
					
					
					
				} else {
					//System.out.println("Illegal case (rand) " + deanonymizedStringListForVolume);
					//end = end + 1;		
					//return new Bucket();
					
					
					if(symbol1.equals(">>") && symbol2.equals("<<")) {
						
						Bucket temp = new Bucket();
						
						start = start - 1;
						end = end + 1;
						
						Double diff = end-start;

						temp.deanonymizedTupleValueList = new ArrayList<Double>();
						temp.deanonymizedTupleValueList.add(start + (diff/2));
						
						//System.out.println("Proceeding with INVALID assignment : " + (start + (diff/2)) );
						//end = end + 1;		
						
						return temp;
						
					}else {
						//System.out.println("Proceeding with null assignment");
						
						
						String PgMin = volumeBucket.deanonymizedStringListForVolume.get(0);
						
						if(!PgMin.contains(">!")) {
							System.out.println("Violation!! There is no PG MIN here");
							return new Bucket();
						}else {
							
							
							double val3 = Double.valueOf(PgMin.substring(2)) ; //ONE LESS THAN PG MIN
							
							
							Bucket pgMinBucket = new Bucket();
							pgMinBucket.deanonymizedTupleValueList = new ArrayList<Double>();
							
							if(val3<minValueInBfc) {
								//System.out.println("Proceeding with LESS THAN PG MIN assignment" + (val3-1) + " " + "Pg min, MinInBfc = " + val3 + ","+minValueInBfc);
								val3 = val3-1;
								pgMinBucket.valList.add((int)val3);
								pgMinBucket.deanonymizedTupleValueList.add(val3);
							}else {
								//System.out.println("Proceeding with LESS THAN PG MIN assignment" + (minValueInBfc-1) + " " + "Pg min, MinInBfc = " + val3 + ","+minValueInBfc);
								minValueInBfc = minValueInBfc-1;
								pgMinBucket.valList.add((int)minValueInBfc);
								pgMinBucket.deanonymizedTupleValueList.add(minValueInBfc);
							
							}
							
							return pgMinBucket;
						}
						
						
					}
					
					/*
					  isThisAValidCombo = true;
					 if(symbol1.equals(">!")) {
						start=start-1;
						System.out.println("Going with " + (start-1) + " " + end);
						
					}else if(symbol2.equals("!<")) {
						end=end+1;
						System.out.println("Going with " + start + " " + (end+1));
						
					}else
						throw new RuntimeException("Strange case " + deanonymizedStringListForVolume +" "+indexOfBucketChosen);
				*/
				}
			
			}
			
			//double rand = Math.random();
			
			//while(rand==0.0 || rand==1.0)
			//	rand = Math.random();
			
			newBucket.valList.add((int) (start + rand*(Math.abs(end-start))));
			newBucket.deanonymizedTupleValueList.add((start + rand*(Math.abs(end-start))));
			
			if(printFlag) {
				System.out.println("randomNumber : indexOfBucketChosen : totalVol : bucketIndividualProbabilities : bucketIndividualProbabilityCDF : individualVolumeUnits :  \n" + rand + " " + indexOfBucketChosen + " " + totalVol + " "  + bucketIndividualProbabilities +  " "+ bucketIndividualProbabilityCDF + "  " + volumeBucket.individualVolumeUnits );
			
			
			System.out.println("ChosenBucketValue (rand): " +  (start + rand*(Math.abs(end-start))));
			}
			
			if(end < start) {
				System.out.println("deanonymizedStringListForVolume " + volumeBucket.deanonymizedStringListForVolume);
				System.out.println("start " + start );
				System.out.println("end " + end );
				
			}
			
			
		}
		else {
			
			
			String s = volumeBucket.deanonymizedStringListForVolume.get(0);
			String t = volumeBucket.deanonymizedStringListForVolume.get(1);

			String symbol1 = s.substring(0,2);
			String symbol2 = t.substring(0,2);
			double val1 = Double.valueOf(s.substring(2));
			double val2 = Double.valueOf(t.substring(2));
			double start = 0, end = 0;
			boolean equalityAvailable = false;
			
			
			switch(symbol1) 
	        { 
	        case ">>": start = val1+1;
                break; 
            case ">=":  start = val1 ; equalityAvailable = true;
			    break; 
            case ">!":  start = val1 ;
                break; 
	        }
			switch(symbol2)
			{
            case "<<":  end = val2-1;
                break; 
            case "<=": end = val2 ; equalityAvailable = true;
                break; 
            case "!<": end = val2 ;
                break; 
	         
			}
			
			//double rand = Math.random();
			
			//while(rand==0.0 || rand==1.0)
			//	rand = Math.random();
			
			if(start>end && !equalityAvailable) {
				
				//System.out.println("Illegal case (def) " + deanonymizedStringListForVolume );
				//return new Bucket();
				
				Bucket temp = new Bucket();
				
				if(symbol1.equals(">>") && symbol2.equals("<<")) {

					start = start - 1;
					end = end + 1;
					
					Double diff = end-start;

					temp.deanonymizedTupleValueList = new ArrayList<Double>();
					temp.deanonymizedTupleValueList.add(start + (diff/2));
					
					//System.out.println("Proceeding with INVALID assignment : " + (start + (diff/2)) );
					//end = end + 1;		
					
					return temp;
					
				}else {
					//System.out.println("Proceeding with null assignment");

					
					String PgMin = volumeBucket.deanonymizedStringListForVolume.get(0);
					
					if(!PgMin.contains(">!")) {
						System.out.println("Violation!! There is no PG MIN here");
						return new Bucket();
					}else {
						double val3 = Double.valueOf(PgMin.substring(2)) ; //ONE LESS THAN PG MIN
						
						
						Bucket pgMinBucket = new Bucket();
						pgMinBucket.deanonymizedTupleValueList = new ArrayList<Double>();
						
						if(val3<minValueInBfc) {
							//System.out.println("Proceeding with LESS THAN PG MIN assignment" + (val3-1) + " " + "Pg min, MinInBfc = " + val3 + ","+minValueInBfc);
							val3 = val3-1;
							pgMinBucket.valList.add((int)val3);
							pgMinBucket.deanonymizedTupleValueList.add(val3);
						}else {
							//System.out.println("Proceeding with LESS THAN PG MIN assignment" + (minValueInBfc-1) + " " + "Pg min, MinInBfc = " + val3 + ","+minValueInBfc);
							minValueInBfc = minValueInBfc-1;
							pgMinBucket.valList.add((int)minValueInBfc);
							pgMinBucket.deanonymizedTupleValueList.add(minValueInBfc);
						
						}
						
						return pgMinBucket;
					}
				}
				
				
			}else if(equalityAvailable) {
				
				for(String st : volumeBucket.deanonymizedStringListForVolume) {
					if(st.substring(0,2).equals(">=") || st.substring(0,2).equals("<=") ) {
						
						Bucket temp = new Bucket();
						double temp2 = Double.valueOf(st.substring(2));
						
						temp.valList.add((int)temp2);

						temp.deanonymizedTupleValueList = new ArrayList<Double>();
						temp.deanonymizedTupleValueList.add(temp2);
						
						if(printFlag) {
							System.out.println("ChosenBucketValue (def): " +  temp2);
							
							}

						
						return temp;
					}
				}
			
			} 
			if(s.contains(">!")) {
				newBucket.valList.add((int) (start + rand*(Math.abs(end-start))));
				
				newBucket.deanonymizedTupleValueList.add( (start + rand*(Math.abs(end-start))));
				
				
			}
			else {
				newBucket.valList.add((int) (end - rand*(Math.abs(end-start))));
				
				newBucket.deanonymizedTupleValueList.add((end - rand*(Math.abs(end-start))));
				
				
			}
			
			//printFlag = true;
			
			if(printFlag) {
			System.out.println("ChosenBucketValue (def): " +  (start + rand*(Math.abs(end-start))));
			
			if(s.contains(">!"))
				System.out.println("ChosenBucketValue (def): " + (start + rand*(Math.abs(end-start))));
			else
				System.out.println("ChosenBucketValue (def): " +  (end - rand*(Math.abs(end-start))));
			
			
			}

			/*if(end < start) {
				System.out.println("deanonymizedStringListForVolume " + deanonymizedStringListForVolume);
				System.out.println("start " + start );
				System.out.println("end " + end );
				
			}*/
		}
		
		
		return newBucket;
	}


	
}
