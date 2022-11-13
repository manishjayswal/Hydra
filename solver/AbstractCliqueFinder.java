package in.ac.iisc.cds.dsl.cdgvendor.solver;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.io.FileWriter;
import java.io.IOException;

import in.ac.iisc.cds.dsl.cdgvendor.constants.PostgresVConfig;
import in.ac.iisc.cds.dsl.cdgvendor.model.ValueCombination;
import in.ac.iisc.cds.dsl.cdgvendor.model.ViewInfo;
import in.ac.iisc.cds.dsl.cdgvendor.model.ViewSolution;
import in.ac.iisc.cds.dsl.cdgvendor.model.formal.FormalCondition;
import in.ac.iisc.cds.dsl.cdgvendor.model.formal.FormalConditionAggregate;
import in.ac.iisc.cds.dsl.cdgvendor.model.formal.FormalConditionBaseAggregate;
import in.ac.iisc.cds.dsl.cdgvendor.model.formal.FormalConditionComposite;
import in.ac.iisc.cds.dsl.cdgvendor.model.formal.FormalConditionSimpleInt;
import in.ac.iisc.cds.dsl.cdgvendor.reducer.Bucket;
import in.ac.iisc.cds.dsl.cdgvendor.reducer.BucketStructure;
import in.ac.iisc.cds.dsl.cdgvendor.reducer.Region;
import in.ac.iisc.cds.dsl.cdgvendor.solver.Z3Solver.ConsistencyMakerType;
import in.ac.iisc.cds.dsl.cdgvendor.utils.StopWatch;
import it.unimi.dsi.fastutil.ints.IntArrayList;
import it.unimi.dsi.fastutil.ints.IntIterator;
import it.unimi.dsi.fastutil.ints.IntList;
import it.unimi.dsi.fastutil.ints.IntOpenHashSet;

abstract class AbstractCliqueFinder {

    protected final String             viewname;
    protected final List<String>       sortedViewColumns;
    public final Map<String, IntList> bucketFloorsByColumns;
    protected final List<boolean[]>    allTrueBS;
    protected final List<Set<String>>  arasuCliques;
    protected final int                cliqueCount;
    protected final List<IntList>      arasuCliquesAsColIndxs;
    protected final IntList            sortedAllCliquesColIndxs;
    protected final long               relationCardinality;
    private final boolean[]            isFakeAttr;

    protected AbstractCliqueFinder(String viewname, ViewInfo viewInfo, List<boolean[]> allTrueBS, List<Set<String>> arasuCliques,
            Map<String, IntList> bucketFloorsByColumns) {

        this.viewname = viewname;
        sortedViewColumns = new ArrayList<>(viewInfo.getViewNonkeys());
        Collections.sort(sortedViewColumns);
        this.bucketFloorsByColumns = bucketFloorsByColumns;

        this.allTrueBS = allTrueBS;

        this.arasuCliques = arasuCliques;
        //System.err.println(arasuCliques);
        cliqueCount = this.arasuCliques.size();
        arasuCliquesAsColIndxs = new ArrayList<>(cliqueCount);
        IntList tempSortedAllCliquesColIndxs = new IntArrayList();
        for (Set<String> arasuClique : arasuCliques) {
            IntList cliqueColIndx = getSortedIndxs(arasuClique);
            //System.err.println(arasuClique);
            //System.err.println(cliqueColIndx);
            arasuCliquesAsColIndxs.add(cliqueColIndx);
            tempSortedAllCliquesColIndxs.addAll(cliqueColIndx);
        }
        sortedAllCliquesColIndxs = new IntArrayList(new IntOpenHashSet(tempSortedAllCliquesColIndxs));
        Collections.sort(sortedAllCliquesColIndxs);

        relationCardinality = viewInfo.getRowcount();

        //Used for expanding ValueCombinations
        isFakeAttr = new boolean[sortedViewColumns.size()];
        Arrays.fill(isFakeAttr, true);
        for (IntIterator iter = sortedAllCliquesColIndxs.iterator(); iter.hasNext();) {
            isFakeAttr[iter.nextInt()] = false;
        }
    }

    protected IntList getSortedIndxs(Set<String> cols) {
        IntList colIndxs = new IntArrayList(cols.size());
        for (String col : cols) {
            colIndxs.add(sortedViewColumns.indexOf(col));
            
            //Writing anonymized col name to col index -- Anupam
            //start
            FileWriter fw;
    		try {
    			fw = new FileWriter("subview-col-to-index.txt", true);
    			//System.err.println(viewname +"djfh");
    			fw.write(viewname + " "+ col +" " + sortedViewColumns.indexOf(col)+ "\n");
    	        fw.close();
    		} catch (IOException e) {
    			// TODO Auto-generated catch block
    			e.printStackTrace();
    		} 
            //System.err.println(col +" " + sortedViewColumns.indexOf(col)); //-- Anupam
    		//stop
        }
        if (colIndxs.contains(-1))
            throw new RuntimeException("Expected cols " + cols + " to be from list of view cols " + sortedViewColumns);
        Collections.sort(colIndxs);
        return colIndxs;
    }

//    public abstract ViewSolution solveView(List<FormalCondition> conditions, List<Region> conditionRegions, FormalCondition consistencyConstraints[], ConsistencyMakerType consistencyMakerType, Map<String, List<Region>> aggregateColumnsToSingleSplitPointRegions);
//    public abstract ViewSolution solveView(List<FormalCondition> conditions, List<Region> conditionRegions, FormalCondition consistencyConstraints[], ConsistencyMakerType consistencyMakerType);
    
    
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
    public static void getAppearingColsTemp(Set<String> attributesFound, FormalCondition condition) {
    	//Ignores projection columns. 
    	        if (condition instanceof FormalConditionComposite) {
    	            FormalConditionComposite composite = (FormalConditionComposite) condition;
    	            for (FormalCondition innerCondition : composite.getConditionList()) {
    	                getAppearingColsTemp(attributesFound, innerCondition);
    	            }

    	        } else if (condition instanceof FormalConditionSimpleInt) {
    	            FormalConditionSimpleInt simple = (FormalConditionSimpleInt) condition;
    	            attributesFound.add(simple.getColumnname());            

    	        } else if (condition instanceof FormalConditionBaseAggregate) {
    	        } else
    	            throw new RuntimeException("Unrecognized type of FormalCondition " + condition.getClass());
    }
    public static void getAppearingCols(Set<String> attributesFound, List<FormalCondition> condition) {

    	for (FormalCondition formalCondition : condition) {
			getAppearingCols(attributesFound, formalCondition);
		}
    }

    public static void removeAggregateCols(Set<String> attributesFound, FormalCondition condition) {
    	attributesFound.removeAll(((FormalConditionAggregate) condition).getGroupKey());
    }
    
    private StopWatch solveSW;
    private StopWatch postSolveSW;

    protected final void beginLPFormulation() {
        solveSW = new StopWatch("LP-Solving-" + viewname);
    }

    protected final void finishSolving() {
        solveSW.displayTimeAndDispose();
        postSolveSW = new StopWatch("Post-Solving-" + viewname);
    }

    protected final void finishPostSolving() {
        postSolveSW.displayTimeAndDispose();
    }

    protected final ValueCombination getReverseMappedValueCombination(ValueCombination valueCombination) {
        IntList reverseMappedValues = new IntArrayList(sortedAllCliquesColIndxs.size());
        for (int i = 0; i < sortedAllCliquesColIndxs.size(); i++) {
            int colIndx = sortedAllCliquesColIndxs.getInt(i);
            String columnname = sortedViewColumns.get(colIndx);
            int oldValue = valueCombination.getColValues().getInt(i);
            int reverseMappedValue = bucketFloorsByColumns.get(columnname).getInt(oldValue);
            reverseMappedValues.add(reverseMappedValue);
        }
        ValueCombination reverseMappedValueCombination = new ValueCombination(reverseMappedValues, valueCombination.getRowcount());
        return reverseMappedValueCombination;
    }

    public final ValueCombination getExpandedValueCombination(ValueCombination oldValueCombination) {
        IntList oldColValues = oldValueCombination.getColValues();
        IntList expandedColValues = new IntArrayList();
        for (int i = 0, k = -1; i < isFakeAttr.length; i++) {
            if (isFakeAttr[i]) {
                expandedColValues.add(0);
            } else {
                expandedColValues.add(oldColValues.getInt(++k));
            }
        }
        ValueCombination expandedValueCombination = new ValueCombination(expandedColValues, oldValueCombination.getRowcount());
        return expandedValueCombination;
    }
    public final Region getExpandedRegion(Region region) {
        Region expandedRegion=new Region();
        for (int j=0;j<region.size();j++){
        BucketStructure bs=region.at(j);
        BucketStructure expandedBS=new BucketStructure();
        for (int i = 0, k = -1; i < isFakeAttr.length; i++) {
               if (isFakeAttr[i]) {
                Bucket b=new Bucket();
                b.add(0);
                expandedBS.add(b);
                }
               else
                expandedBS.add(bs.at(++k));
                }
        expandedRegion.add(expandedBS);
                   
               }
        return expandedRegion;
            }
    
    
        public final Region getReverseMappedRegion(Region region) {
        Region reverseRegion=new Region();
           
            for (int j=0;j< region.size();j++) {
           
            BucketStructure bsOld=region.at(j);
            BucketStructure bsNew=new BucketStructure();
        for (int i = 0; i < sortedAllCliquesColIndxs.size(); i++) {
               Bucket bOld=bsOld.at(i);
               Bucket bNew=new Bucket();
        int colIndx = sortedAllCliquesColIndxs.getInt(i);
               String columnname = sortedViewColumns.get(colIndx);
               for (int k=0;k<bOld.size();k++){
               
                int oldValue = bOld.at(k);
               int reverseMappedValue = bucketFloorsByColumns.get(columnname).getInt(oldValue);
               bNew.add(reverseMappedValue);
               //reverseMappedValues.add(reverseMappedValue);
               }
               bsNew.add(bNew);
           }
        reverseRegion.add(bsNew);
            }
           
            return reverseRegion;
        }
        
        
        public void getReverseMapFromBFC(List<Integer> variable, List<String> pkColumns) {
        	
        	for(int i=0; i<variable.size();i++) {
        		variable.set(i,bucketFloorsByColumns.get(pkColumns.get(i)).getInt(variable.get(i)));
        	}
        	
        }

}
