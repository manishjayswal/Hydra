/**
 * 
 */
package in.ac.iisc.cds.dsl.cdgvendor.solver;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import org.json.JSONArray;
import org.json.JSONObject;

import in.ac.iisc.cds.dsl.cdgvendor.constants.PostgresVConfig;
import in.ac.iisc.cds.dsl.cdgvendor.constants.PostgresVConfig.Key;
import in.ac.iisc.cds.dsl.cdgvendor.model.CCInfo;
import in.ac.iisc.cds.dsl.cdgvendor.model.ValueCombination;
import in.ac.iisc.cds.dsl.cdgvendor.model.VariableValuePair;
import in.ac.iisc.cds.dsl.cdgvendor.model.ViewInfo;
import in.ac.iisc.cds.dsl.cdgvendor.model.ViewSolution;
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
import in.ac.iisc.cds.dsl.cdgvendor.reducer.Region;
import in.ac.iisc.cds.dsl.cdgvendor.utils.FileUtils;
import it.unimi.dsi.fastutil.ints.IntArrayList;
import it.unimi.dsi.fastutil.ints.IntList;

/**
 * 
 * @author tarun
 *
 */
public class NewSkewAlgorithm {

	Map<String, ViewSolution> viewSolutions;
	CCInfo ccInfo;
	Map<String,String> reverseTableAnonyMap = new HashMap<>();
	Map<String,String> reverseColumnAnonyMap = new HashMap<>();
	Map<String,DFvector> ccsDFvectors;
	
	Map<String,Map<FormalCondition,List<String>>> ccToRegionMapViewwise;  // Region name : r0, r1 
	Map<String,Map<String,List<FormalCondition>>> regionToCCMapViewwise;
	Map<String,Map<String, VariableValuePair>> regionToVVPMapViewWise;
	
	
	// t17 -> [ r1 -> [t17_001 -> [11->3, 12->4, 13->1 ... ] ] ]
	Map<String,Map<String,Map<String,Map<Integer,List<Long>>>>> pkValueCountTracker;
		
	// t17 -> [ fkey -> [ interval -> [2-> [pkVal1, pkval2] ]
	Map<String,Map<String, Map<Integer,Map<Integer,List<Long>>>>> pkValLeftInIntervalMap;
		
	// t17 -> [ fkey -> [CC -> [ d -> [pkVal1, pkVal2]] ]
	Map<String,Map<String,Map<FormalCondition, Map<Integer,List<Long>>>>> advancePKValInCC;
		
		
		
	
	
	
	
	public NewSkewAlgorithm(Map<String, ViewSolution> viewSolutions, CCInfo ccInfo) {
		// TODO Auto-generated constructor stub
		this.viewSolutions = viewSolutions;
		this.ccInfo = ccInfo;
		this.ccsDFvectors = new HashMap<>();
		this.ccToRegionMapViewwise = new HashMap<>();
		this.regionToCCMapViewwise = new HashMap<>();
		this.regionToVVPMapViewWise = new HashMap<>();
		
		fetchDFvectors();
		mapRegionsToCC();
		mapCCsToRegions();
		
		solve();
		
		
		
	}
	
	
	private void solve() {
		
		// Table  and column AnonyMap
		JSONObject tableAnonyMap = new JSONObject(FileUtils.readFileToString(PostgresVConfig.getProp(Key.TABLE_ANONY_MAP)));
				
		for(String table : tableAnonyMap.keySet()) {
			reverseTableAnonyMap.put(tableAnonyMap.getString(table), table);
		}
		JSONObject columnAnonyMap = new JSONObject(FileUtils.readFileToString(PostgresVConfig.getProp(Key.COLUMN_ANONY_MAP)));
			
		for(String table : columnAnonyMap.keySet()) {
			reverseColumnAnonyMap.put(columnAnonyMap.getString(table), table);
		}
		
		JSONObject fkeySkewVectors = PostgresVConfig.fkeySkewVectors; // base relation fkeys distribution
		
		for(String view : PostgresVConfig.fkeyToBorrowedAttr.keySet() ) {
			
			this.pkValLeftInIntervalMap.put(view, new HashMap<>());
			this.pkValueCountTracker.put(view, new HashMap<>());
			this.advancePKValInCC.put(view, new HashMap<>());
			
			if(!fkeySkewVectors.has(view)) {
				continue;
			}
			
			Map<String, IntList> bucketFloorColumn = PostgresVConfig.bucketFloorColumnViewWise.get(view);
			// sort on the basis of regions intersecting with most CCs
			Map<String, List<FormalCondition>> regionToCCMap = regionToCCMapViewwise.get(view);
			List<String> orderedRegions =  new ArrayList<>(); // orderedRegions on the basis of most intersecting CCs with a region
			List<Integer> orderedRegionsCCcount = new ArrayList<>();
			
			for(String region : regionToCCMap.keySet()) {
				this.pkValueCountTracker.get(view).put(region, new HashMap<>());
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
			
			List<String> deepCopyOFOrderedRegion = new ArrayList<>();
			for(String reg : orderedRegions) {
				deepCopyOFOrderedRegion.add(reg);
			}
			
			JSONObject baseFkeysSkewVector = fkeySkewVectors.getJSONObject(view);
			Set<String> anonymfkeys = baseFkeysSkewVector.keySet();
			
			Map<String, Map<String, Set<String>>> fkeyToBorrowedAttr = PostgresVConfig.fkeyToBorrowedAttr;;
			for(String fkey : PostgresVConfig.fkeyToBorrowedAttr.get(view).keySet() ) {
				
				Map<FormalCondition, List<String>> CCToRegionMap = this.ccToRegionMapViewwise.get(view);
				Map<String, VariableValuePair> regionToVVPMap = this.regionToVVPMapViewWise.get(view);
				for(String reg : deepCopyOFOrderedRegion) {
					orderedRegions.add(reg);
				}
				
				solveForFKey(orderedRegions,regionToCCMap, CCToRegionMap, regionToVVPMap, baseFkeysSkewVector.get(fkey),
						reverseColumnAnonyMap, columnAnonyMap, tableAnonyMap, fkey, bucketFloorColumn, view );
			
			}
			
			
		}
		
	}
	
	private void solveForFKey(List<String> orderedRegions, Map<String, List<FormalCondition>> regionToCCMap,
			Map<FormalCondition, List<String>> CCToRegionMap, Map<String, VariableValuePair> regionToVVPMap,
			Object object, Map<String, String> reverseColumnAnonyMap, JSONObject columnAnonyMap,
			JSONObject tableAnonyMap, String fkey, Map<String, IntList> bucketFloorColumn, String view) {
		
	
		// Find intervals associated with Interval 
		// Borrowed attr associated with fkey;
		this.pkValLeftInIntervalMap.get(view).put(fkey, new HashMap<>());
		this.advancePKValInCC.get(view).put(fkey, new HashMap<>());
		
		// Get Interval regions using bfc and borrowed attr

		
		
		Map<String, Set<String>> fkeyToBorrowedAttr = PostgresVConfig.fkeyToBorrowedAttr.get(view);
		
		Set<String> borrowedAttrs = fkeyToBorrowedAttr.get(fkey);
		
		if(borrowedAttrs.isEmpty()) {
			System.out.print("NO need to manage fkey ");
			throw new RuntimeException("Can't possible to reach here");
		}
		
		
		
		
	
	}


	private void fetchDFvectors() {
		
		List<String> dfFiles = FileUtils.readLines(PostgresVConfig.getProp(Key.DF_VECTORS), "index");
        List<String> queryNames = new ArrayList<>();
        for (String eaFilename : dfFiles) {
        	if (eaFilename.startsWith("#"))
        		continue;
        	if(eaFilename.contentEquals("index"))
        		continue;
        	//System.out.println(eaFilename);
            JSONObject obj = new JSONObject(FileUtils.readFileToString(PostgresVConfig.getProp(Key.DF_VECTORS), eaFilename));
            JSONArray d = obj.getJSONArray("d");
    		JSONArray f = obj.getJSONArray("f");
    		DFvector df = new DFvector(d,f);
    		ccsDFvectors.put(eaFilename,df );
            
            queryNames.add(eaFilename);
        }
        System.out.println(ccsDFvectors.keySet());
		
	}
	
	
		private void mapRegionsToCC() {
		
				Map<String, List<FormalCondition>> viewnameToCCMap = ccInfo.getViewnameToCCMap();
				Map<String, ViewInfo> viewInfos = PostgresVConfig.ANONYMIZED_VIEWINFOs;
				
				
			
				for(String key : viewnameToCCMap.keySet() ) {
					
					if(!regionToCCMapViewwise.containsKey(key)) {
						regionToCCMapViewwise.put(key,new HashMap<>());
					}
					
					this.regionToVVPMapViewWise.put(key, new HashMap<>());
					
			
					
					List<String> sortedViewNonKeys = new ArrayList<>(viewInfos.get(key).getViewNonkeys());
					Collections.sort(sortedViewNonKeys);
					Map<String,List<FormalCondition>> regionToCCMap = regionToCCMapViewwise.get(key);
					List<FormalCondition> formalConditions = viewnameToCCMap.get(key);
					ViewSolution viewSolution = viewSolutions.get(key);
					
					List<VariableValuePair> variableValuePairs = viewSolution.getVariableValuePairs();
					for(int v_i=0; v_i < variableValuePairs.size(); v_i++) {
						VariableValuePair vvp = variableValuePairs.get(v_i);
						Region r = vvp.variable;
						
						for(FormalCondition formalCondition : formalConditions) {
							
							Set<String> appearingCols = new HashSet<>();
		                    getAppearingCols(appearingCols, formalCondition);
		                    if(checkCCSatifyRegion(r,appearingCols,formalCondition,sortedViewNonKeys)) {
		                    	if(!regionToCCMap.containsKey("r" + v_i)) {
		                    		regionToCCMap.put("r" + v_i, new ArrayList<>());
		                    	}
		                    	regionToCCMap.get("r" + v_i).add(formalCondition);
		                    	
		                    	
		                    }
		                    
						}
						
						this.regionToVVPMapViewWise.get(key).put("r" + v_i, vvp);
						
						
						
					}
					
					
			
					
				}
		
		
		}
		
		private void mapCCsToRegions() {
			
			for(String view : regionToCCMapViewwise.keySet()) {
				if(!ccToRegionMapViewwise.containsKey(view)) {
					ccToRegionMapViewwise.put(view, new HashMap<>());
				}
				Map<FormalCondition, List<String>> ccToRegionMap = ccToRegionMapViewwise.get(view);
				Map<String, List<FormalCondition>> regionToCCMap = regionToCCMapViewwise.get(view);
				for(String region : regionToCCMap.keySet()) {
					List<FormalCondition> formalConditions = regionToCCMap.get(region);
					for(FormalCondition formalCondition : formalConditions) {
						if(!ccToRegionMap.containsKey(formalCondition)) {
							ccToRegionMap.put(formalCondition,new ArrayList<>());
						}
					    ccToRegionMap.get(formalCondition).add(region);
					}
					
				}
			}
			
		}
		
		
		/**
	     * Returns by side effects into attributesFound.
	     * Should be called with an empty attributesFound at caller's end
	     * @param attributesFound
	     * @param condition
	     */
	    public static void getAppearingCols(Set<String> attributesFound, FormalCondition condition) {

	        if (condition instanceof FormalConditionComposite) {
	            FormalConditionComposite composite = (FormalConditionComposite) condition;
	            for (FormalCondition innerCondition : composite.getConditionList()) {
	                getAppearingCols(attributesFound, innerCondition);
	            }

	        } else if (condition instanceof FormalConditionSimpleInt) {
	            FormalConditionSimpleInt simple = (FormalConditionSimpleInt) condition;
	            attributesFound.add(simple.getColumnname());            

	        } else if (condition instanceof FormalConditionBaseAggregate) {
	        } else
	            throw new RuntimeException("Unrecognized type of FormalCondition " + condition.getClass());
	        
	        if (condition instanceof FormalConditionAggregate) {	// Adding those attributes which are part of group key
	        	attributesFound.addAll(((FormalConditionAggregate) condition).getGroupKey());
	        }
	    }
	    
	    
	    private boolean checkCCSatifyRegion(Region r, Set<String> appearingCols, FormalCondition condition,List<String> sortedViewNonKeys) {
			// TODO Auto-generated method stub
			
	        IntList columnValues = getFloorInstantiation(r);
	        ValueCombination valueCombination = new ValueCombination(columnValues, 0);//if you wish to get the valuecombination too
			List<String> sortedColumns = sortedViewNonKeys;
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
	    
	    private IntList getFloorInstantiation(Region variable) {
	        //choose BS with min bucket floors
	        BucketStructure leadingBS = variable.getLeadingBS();
	        IntList columnValues = new IntArrayList(leadingBS.getAll().size());
	        for (Bucket b : leadingBS.getAll()) {
	            columnValues.add(b.min());
	        }
	        return columnValues;
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
	    
	    


}
