package in.ac.iisc.cds.dsl.cdgvendor.solver;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import org.json.JSONObject;

import in.ac.iisc.cds.dsl.cdgvendor.constants.PostgresVConfig;
import in.ac.iisc.cds.dsl.cdgvendor.constants.PostgresVConfig.HydraTypes;
import in.ac.iisc.cds.dsl.cdgvendor.model.ColumnPathInfo;
import in.ac.iisc.cds.dsl.cdgvendor.model.ViewInfo;
import in.ac.iisc.cds.dsl.cdgvendor.model.formal.FormalCondition;
import in.ac.iisc.cds.dsl.cdgvendor.model.formal.FormalConditionBaseAggregate;
import in.ac.iisc.cds.dsl.cdgvendor.model.formal.FormalConditionComposite;
import in.ac.iisc.cds.dsl.cdgvendor.model.formal.FormalConditionSimpleInt;
import in.ac.iisc.cds.dsl.cdgvendor.utils.DebugHelper;
import it.unimi.dsi.fastutil.ints.IntArrayList;
import it.unimi.dsi.fastutil.ints.IntList;
import it.unimi.dsi.fastutil.ints.IntOpenHashSet;
import it.unimi.dsi.fastutil.ints.IntSet;

public class DomainDecomposer {

    public static Map<String, List<Integer>> getTrivialBucketFloors(ViewInfo viewInfo) {

        Map<String, Set<Integer>> bucketFloorsByColumns = new HashMap<>();
        Map<String, String> columnDataTypeMap = PostgresVConfig.columnDataTypeMap;
        for (String columnname : viewInfo.getViewNonkeys()) {

        	
            Set<Integer> integerSet = new HashSet<>();
            if(columnDataTypeMap.get(columnname).contentEquals("integer")&&PostgresVConfig.hydraVersions.contains(HydraTypes.robustHydra)) {
            	integerSet.add(Integer.MIN_VALUE); //IMPORTANT: Adding ZERO as the floor for every column for int type
        	}
            else {
            	integerSet.add(0); //IMPORTANT: Adding ZERO as the floor for every column of non-int type
            }
            	
            
            bucketFloorsByColumns.put(columnname, integerSet);
        }

        Map<String, List<Integer>> result = new HashMap<>();
        for (Entry<String, Set<Integer>> entry : bucketFloorsByColumns.entrySet()) {
            String columnname = entry.getKey();
            List<Integer> list = new ArrayList<>(entry.getValue());
            Collections.sort(list);
            result.put(columnname, list);
        }

        return result;
    }

    public static Map<String, IntList> getBucketFloors(List<FormalCondition> conditions, ViewInfo viewInfo) {

        Map<String, IntSet> bucketFloorSetByColumns = new HashMap<>();
        System.out.println("viewInfo.getViewNonkeys()" + viewInfo.getViewNonkeys());
        Map<String, String> columnDataTypeMap = PostgresVConfig.columnDataTypeMap;
        for (String columnname : viewInfo.getViewNonkeys()) {

            IntSet integerSet = new IntOpenHashSet();
            if(columnDataTypeMap.get(columnname).contentEquals("integer")&&PostgresVConfig.hydraVersions.contains(HydraTypes.robustHydra)) {
            	integerSet.add(Integer.MIN_VALUE); //IMPORTANT: Adding Minimum Int as the floor for every column for int type
        	}
            else {
            	integerSet.add(0); //IMPORTANT: Adding ZERO as the floor for every column of non-int type
            }
            bucketFloorSetByColumns.put(columnname, integerSet);
        }
        DebugHelper.printDebug("Empty bucketFloorsByColumns " + bucketFloorSetByColumns);

        collectBucketFloors(conditions, bucketFloorSetByColumns);
        DebugHelper.printDebug("Filled bucketFloorsByColumns " + bucketFloorSetByColumns);

        Map<String, IntList> bucketFloorListByColumns = new HashMap<>();
        for (Entry<String, IntSet> entry : bucketFloorSetByColumns.entrySet()) {
            String columnname = entry.getKey();
            IntList list = new IntArrayList(entry.getValue());
            Collections.sort(list);
            bucketFloorListByColumns.put(columnname, list);
        }

        return bucketFloorListByColumns;
    }

    /************************************************************
     * Private supporting methods
     ************************************************************/

    /**
     * Looks at each of the condition and fills in the bucketCeilsByColumn map
     * @param conditions
     * @param bucketFloorsByColumns
     * 
     * and in addition to above adds 
     */
    private static void collectBucketFloors(List<FormalCondition> conditions, Map<String, IntSet> bucketFloorsByColumns) {

    	
    	
        for (FormalCondition condition : conditions) {

        	
        	
            //TODO: Should get only simple conditions here
            if (condition instanceof FormalConditionComposite) {
                collectBucketFloors(((FormalConditionComposite) condition).getConditionList(), bucketFloorsByColumns);

            } else if (condition instanceof FormalConditionSimpleInt) {
                FormalConditionSimpleInt formalConditionSimpleInt = (FormalConditionSimpleInt) condition;
                String columnName = formalConditionSimpleInt.getColumnname();      
                Map<String, ColumnPathInfo> COLUMN_ID_MAP = PostgresVConfig.COLUMN_ID_MAP;
                String viewname = condition.getViewname();
                
                // Borrowed attr for duplication code only.
                if(PostgresVConfig.hydraVersions.contains(PostgresVConfig.HydraTypes.duplicationHydra)) {
                	addBorrowedAttrToFkey(columnName, viewname,formalConditionSimpleInt);
                }
                
                
                
                

                
                IntSet integerSet = bucketFloorsByColumns.get(columnName);
                //IMPORTANT: integerSet already has ZERO as the floor for every column
                
                int a = formalConditionSimpleInt.getValue();
                switch (formalConditionSimpleInt.getSymbol()) {
                    case LT:
                        integerSet.add(a);
                        break;
                    case LE:
                        integerSet.add(a + 1);
                        break;
                    case GT:
                        integerSet.add(a + 1);
                        break;
                    case GE:
                        integerSet.add(a);
                        break;
                    case EQ:
                        integerSet.add(a);
                        integerSet.add(a + 1);
                        break;
                    default:
                        throw new RuntimeException("Unrecognized Symbol " + formalConditionSimpleInt.getSymbol());
                }
            } else if (condition instanceof FormalConditionBaseAggregate) {
            } else
                throw new RuntimeException("Unrecognized type of FormalCondition " + condition.getClass());
        }
    }

	private static void addBorrowedAttrToFkey(String columnName, String viewname,
			FormalConditionSimpleInt formalConditionSimpleInt) {
        //ColumnPathInfo columnPathObj = COLUMN_ID_MAP.get(columnName);
        List<String> fkColumns = formalConditionSimpleInt.getFkColumnNames();
        List<String> pkColumns = formalConditionSimpleInt.getPkColumnNames();
       // List<String> fkColumns = columnPathObj.getFKColumnNames();
        if(fkColumns.isEmpty()) {
        	System.out.print("");

        }
        else if (fkColumns.get(0).contentEquals("")) {
        	System.out.print("");
        }
        else {
        	
        	
        	// add entry for a view
        	if(!PostgresVConfig.fkeyToBorrowedAttr.containsKey(viewname)) {
        		PostgresVConfig.fkeyToBorrowedAttr.put(viewname, new HashMap<>());
        	}
        	
        	Map<String, Set<String>> fkeyToBorrowedAttrMap = PostgresVConfig.fkeyToBorrowedAttr.get(viewname);
        
        	List<String> colPath = formalConditionSimpleInt.getColPath();
        	
        	String fkey = null;
        	String pkView = colPath.get(0);
        	if(colPath.size() > 2) {
        		System.out.print("");
        	}
        	
        	/*
        	 *  
        	 */
        	
        	if(fkColumns.size() > 0) {
        		fkey = fkColumns.get(fkColumns.size()-1);
        		String pkey = pkColumns.get(fkColumns.size()-1);
        		String pkTable = pkey.split("_")[0];
        		Integer pathHashCode =colPath.hashCode();
        		
        		// adding current column
        		if(columnName.contains(pkTable)) {
        			if(!fkeyToBorrowedAttrMap.containsKey(fkey)) {
                		fkeyToBorrowedAttrMap.put(fkey, new HashSet<>());
                	}
                	
                	fkeyToBorrowedAttrMap.get(fkey).add(columnName);
        		}
        		
        		
        		// adding transitive columns
        		for(int j=0; j < fkColumns.size()-1; j++) {
        			if(fkColumns.get(j).contains(pkTable)) {
        				if(!fkeyToBorrowedAttrMap.containsKey(fkey)) {
                    		fkeyToBorrowedAttrMap.put(fkey, new HashSet<>());
                    	}
        				Set<String> columnsInPkView = PostgresVConfig.fkeyToBorrowedAttr.get(pkTable).get(fkColumns.get(j));
        				for(String col: columnsInPkView) {
        					
        					ColumnPathInfo columnPathInfo = PostgresVConfig.COLUMN_ID_MAP.get(col);
        					List<String> pkColPath = new ArrayList<>(columnPathInfo.getColPath());
        					pkColPath.add(viewname);
        					String pkCol = columnPathInfo.getColname();
        					
        					fkeyToBorrowedAttrMap.get(fkey).add(pkCol + "_" + pkColPath.hashCode());
        				}
        				
        			}
        		}
        		
        
        		
        		
        	}
        	else {
        		System.out.print("");
        	}
        	
     
        	if(fkey == null) {
        		
        		if(!columnName.contains(viewname)) {
        			System.out.print("");
        			throw new RuntimeException("Not possible: may be some problem with column path generation");
        		}
        	
        	}
        	
        	
        }
		
	}
}
