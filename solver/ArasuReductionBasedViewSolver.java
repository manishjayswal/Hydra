package in.ac.iisc.cds.dsl.cdgvendor.solver;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import com.microsoft.z3.ArithExpr;
import com.microsoft.z3.Context;
import com.microsoft.z3.IntExpr;
import com.microsoft.z3.Model;
import com.microsoft.z3.Solver;
import com.microsoft.z3.Status;

import in.ac.iisc.cds.dsl.cdgvendor.constants.PostgresVConfig;
import in.ac.iisc.cds.dsl.cdgvendor.model.CliqueSolutionInMemory;
import in.ac.iisc.cds.dsl.cdgvendor.model.ValueCombination;
import in.ac.iisc.cds.dsl.cdgvendor.model.ViewInfo;
import in.ac.iisc.cds.dsl.cdgvendor.model.ViewSolution;
import in.ac.iisc.cds.dsl.cdgvendor.model.ViewSolutionDiskBased;
import in.ac.iisc.cds.dsl.cdgvendor.model.ViewSolutionInMemory;
import in.ac.iisc.cds.dsl.cdgvendor.model.formal.FormalCondition;
import in.ac.iisc.cds.dsl.cdgvendor.reducer.Bucket;
import in.ac.iisc.cds.dsl.cdgvendor.reducer.BucketStructure;
import in.ac.iisc.cds.dsl.cdgvendor.reducer.Region;
import in.ac.iisc.cds.dsl.cdgvendor.solver.Z3Solver.ConsistencyMakerType;
import in.ac.iisc.cds.dsl.cdgvendor.solver.Z3Solver.SpillType;
import in.ac.iisc.cds.dsl.cdgvendor.utils.DebugHelper;
import it.unimi.dsi.fastutil.ints.Int2IntMap;
import it.unimi.dsi.fastutil.ints.Int2IntOpenHashMap;
import it.unimi.dsi.fastutil.ints.IntArrayList;
import it.unimi.dsi.fastutil.ints.IntIterator;
import it.unimi.dsi.fastutil.ints.IntList;
import it.unimi.dsi.fastutil.ints.IntListIterator;
import it.unimi.dsi.fastutil.ints.IntOpenHashSet;
import it.unimi.dsi.fastutil.ints.IntSet;
import it.unimi.dsi.fastutil.longs.LongArrayList;
import it.unimi.dsi.fastutil.longs.LongList;

public class ArasuReductionBasedViewSolver extends AbstractCliqueFinder {

    private final SpillType spillType;

    public ArasuReductionBasedViewSolver(String viewname, ViewInfo viewInfo, List<boolean[]> allTrueBS, List<Set<String>> arasuCliques,
            Map<String, IntList> bucketFloorsByColumns, SpillType spillType) {

        super(viewname, viewInfo, allTrueBS, arasuCliques, bucketFloorsByColumns);
        this.spillType = spillType;
    }

   
    public ViewSolution solveView(List<FormalCondition> conditions, List<Region> conditionRegions, FormalCondition consistencyConstraints[], ConsistencyMakerType consistencyMakerType) {

        beginLPFormulation();
        List<CliqueSolutionInMemory> cliqueIdxtoSolutionList = formulateAndSolve(conditions, conditionRegions);
        //printSolution(cliqueIdxtoSolutionMap);
        finishSolving();
        ViewSolution viewSolution = sampleViewSolution(cliqueIdxtoSolutionList);
        finishPostSolving();

        return viewSolution;
    }

    private List<CliqueSolutionInMemory> formulateAndSolve(List<FormalCondition> conditions, List<Region> conditionRegions) {

        //STEP 1: For each Clique find set of applicable conditions
        List<List<Region>> cliqueIdxtoConditionRegionsList = new ArrayList<>(cliqueCount);
        List<LongList> cliqueIdxtoConditionBValuesList = new ArrayList<>(cliqueCount);
        List<List<boolean[]>> cliqueIdxtoAllTrueBSList = new ArrayList<>(cliqueCount);

        for (int i = 0; i < cliqueCount; i++) {

            Set<String> clique = arasuCliques.get(i);
            List<Region> cRegions = new ArrayList<>();
            LongList bvalues = new LongArrayList();
            for (int j = 0; j < conditions.size(); j++) {
                Set<String> appearingCols = new HashSet<>();
                getAppearingCols(appearingCols, conditions.get(j));

                if (clique.containsAll(appearingCols)) {
                    cRegions.add(conditionRegions.get(j));
                    bvalues.add(conditions.get(j).getOutputCardinality());
                }
            }

            //Adding extra cRegion all 1's condition
            Region allOnesCRegion = new Region();
            BucketStructure subConditionBS = new BucketStructure();
            for (int j = 0; j < allTrueBS.size(); j++) {
                Bucket bucket = new Bucket();
                for (int k = 0; k < allTrueBS.get(j).length; k++) {
                    if (allTrueBS.get(j)[k]) {
                        bucket.add(k);
                    }
                }
                subConditionBS.add(bucket);
            }
            allOnesCRegion.add(subConditionBS);
            cRegions.add(allOnesCRegion);
            bvalues.add(relationCardinality);

            cliqueIdxtoConditionRegionsList.add(cRegions);
            cliqueIdxtoConditionBValuesList.add(bvalues);

            List<boolean[]> cliqueAllTrueBS = getTruncatedAllTrueBS(arasuCliquesAsColIndxs.get(i));
            cliqueIdxtoAllTrueBSList.add(cliqueAllTrueBS);
        }

        List<CliqueIntersectionInfoArasu> cliqueIntersectionInfos = new ArrayList<>();
        for (int i = 0; i < cliqueCount; i++) {
            for (int j = i + 1; j < cliqueCount; j++) {
                IntList intersectingColIndxs = getIntersectingColIndxs(arasuCliquesAsColIndxs.get(i), arasuCliquesAsColIndxs.get(j));
                if (!intersectingColIndxs.isEmpty()) {
                    CliqueIntersectionInfoArasu cliqueIntersectionInfo = new CliqueIntersectionInfoArasu();
                    cliqueIntersectionInfo.i = i;
                    cliqueIntersectionInfo.j = j;
                    cliqueIntersectionInfo.intersectingColIndxs = intersectingColIndxs;
                    cliqueIntersectionInfos.add(cliqueIntersectionInfo);
                }
            }
        }

        Map<String, String> contextmap = new HashMap<>();
        contextmap.put("model", "true");
        contextmap.put("unsat_core", "true");
        Context ctx = new Context(contextmap);

        Solver solver = ctx.mkSolver();

        List<int[]> cliqueIdxtoMultipliers = new ArrayList<>(cliqueCount);
        for (int i = 0; i < cliqueCount; i++) {
            IntList cliqueColIndxs = arasuCliquesAsColIndxs.get(i);
            List<Region> cRegions = getTruncatedRegions(cliqueIdxtoConditionRegionsList.get(i), cliqueColIndxs);
            LongList bvalues = cliqueIdxtoConditionBValuesList.get(i);
            List<boolean[]> cliqueAllTrueBS = cliqueIdxtoAllTrueBSList.get(i);

            //Finding cumulative multipliers
            int bucketCount = cliqueAllTrueBS.size();
            int[] multipliers = new int[bucketCount - 1]; //multipliers[i] = product of length of buckets i+1....last bucket
            if (bucketCount >= 2) {
                multipliers[bucketCount - 2] = cliqueAllTrueBS.get(bucketCount - 1).length;
                for (int j = bucketCount - 3; j >= 0; j--) { //LSB to MSB
                    multipliers[j] = cliqueAllTrueBS.get(j + 1).length * multipliers[j + 1];
                }
            }
            cliqueIdxtoMultipliers.add(multipliers);

            List<IntList> cRegionVarIndxsList = new ArrayList<>(cRegions.size());
            IntList allVarIndxsInClique = new IntArrayList();
            for (int j = 0; j < cRegions.size(); j++) {
                IntList cRegionVarIndxs = getIndxsForCondition(cRegions.get(j), cliqueColIndxs, multipliers, bucketCount);
                allVarIndxsInClique.addAll(cRegionVarIndxs);

                //Adding normal constraint
                long outputCardinality = bvalues.getLong(j);
                List<IntExpr> addList = new ArrayList<>(cRegionVarIndxs.size());
                for (Integer indx : cRegionVarIndxs) {
                    String varname = "var" + i + "_" + indx;
                    addList.add(ctx.mkIntConst(varname));
                }
                solver.add(ctx.mkEq(ctx.mkAdd(addList.toArray(new ArithExpr[addList.size()])), ctx.mkInt(outputCardinality)));

                cRegionVarIndxsList.add(cRegionVarIndxs);
            }

            //exportToFile(i, cRegionVarIndxsList, bvalues);

            allVarIndxsInClique = new IntArrayList(new IntOpenHashSet(allVarIndxsInClique));

            //Adding non-negativity constraints
            for (IntIterator iter = allVarIndxsInClique.iterator(); iter.hasNext();) {
                int indx = iter.nextInt();
                String varname = "var" + i + "_" + indx;
                solver.add(ctx.mkGe(ctx.mkIntConst(varname), ctx.mkInt(0)));
            }
        }

        for (CliqueIntersectionInfoArasu cliqueIntersectionInfo : cliqueIntersectionInfos) {
            IntList cliqueI = arasuCliquesAsColIndxs.get(cliqueIntersectionInfo.i);
            IntList cliqueJ = arasuCliquesAsColIndxs.get(cliqueIntersectionInfo.j);
            IntList intersectingColIndxs = cliqueIntersectionInfo.intersectingColIndxs;

            List<boolean[]> cliqueAllTrueBSI = cliqueIdxtoAllTrueBSList.get(cliqueIntersectionInfo.i);
            List<boolean[]> cliqueAllTrueBSJ = cliqueIdxtoAllTrueBSList.get(cliqueIntersectionInfo.j);

            IntList cliqueNonIntersectingI = new IntArrayList(cliqueI);
            cliqueNonIntersectingI.removeAll(intersectingColIndxs);
            IntList cliqueNonIntersectingJ = new IntArrayList(cliqueJ);
            cliqueNonIntersectingJ.removeAll(intersectingColIndxs);

            int[] cliqueMultipliersI = cliqueIdxtoMultipliers.get(cliqueIntersectionInfo.i);
            int[] cliqueMultipliersJ = cliqueIdxtoMultipliers.get(cliqueIntersectionInfo.j);

            /*
             * We need to add as many consistency constraints as are the combinations in intersectingColIndxs
             * Each consistency condition is of the form
             *     sum of vars from cliqueI conforming with combination chosen in intersectingCols
             *      = sum of vars from cliqueJ conforming with combination chosen in intersectingCols
             *
             * For that we create two IntList intersectionAddonsForI and IntList intersectionAddonsForJ.
             * Size of these list is the number of combinations in intersectingColIndxs
             *
             * First element of intersectionAddonsForI is the number which when added to a varIndx computed in cliqueI
             * using non-intersecting cols make it conformant with first combination of intersectingCols
             *
             * We precompute varIndxs coming for non-intersecting cols in cliqueI and cliqueJ
             * */

            IntList varIndxsFromNonIntersectingI = getIndxForGivenCols(cliqueAllTrueBSI, cliqueI, cliqueNonIntersectingI, cliqueMultipliersI);
            IntList varIndxsFromNonIntersectingJ = getIndxForGivenCols(cliqueAllTrueBSJ, cliqueJ, cliqueNonIntersectingJ, cliqueMultipliersJ);

            IntList intersectionAddonsI = getIndxForGivenCols(cliqueAllTrueBSI, cliqueI, intersectingColIndxs, cliqueMultipliersI);
            IntList intersectionAddonsJ = getIndxForGivenCols(cliqueAllTrueBSJ, cliqueJ, intersectingColIndxs, cliqueMultipliersJ);

            for (int a = 0; a < intersectionAddonsI.size(); a++) {

                int intersectionAddonI = intersectionAddonsI.getInt(a);
                int intersectionAddonJ = intersectionAddonsJ.getInt(a);

                List<IntExpr> consistencyLHS = new ArrayList<>();
                for (IntIterator iter = varIndxsFromNonIntersectingI.iterator(); iter.hasNext();) {
                    int indx = iter.nextInt();
                    indx += intersectionAddonI;
                    String varname = "var" + cliqueIntersectionInfo.i + "_" + indx;
                    consistencyLHS.add(ctx.mkIntConst(varname));
                }

                List<IntExpr> consistencyRHS = new ArrayList<>();
                for (IntIterator iter = varIndxsFromNonIntersectingJ.iterator(); iter.hasNext();) {
                    int indx = iter.nextInt();
                    indx += intersectionAddonJ;
                    String varname = "var" + cliqueIntersectionInfo.j + "_" + indx;
                    consistencyRHS.add(ctx.mkIntConst(varname));
                }

                //Adding consistency constraints
                solver.add(ctx.mkEq(ctx.mkAdd(consistencyLHS.toArray(new ArithExpr[consistencyLHS.size()])),
                        ctx.mkAdd(consistencyRHS.toArray(new ArithExpr[consistencyRHS.size()]))));
            }
        }

        Status solverStatus = solver.check();
        DebugHelper.printInfo("Solver Status: " + solverStatus);

        if (!Status.SATISFIABLE.equals(solverStatus)) {
        	ctx.close();
            throw new RuntimeException("solverStatus is not SATISFIABLE");
        }

        Model model = solver.getModel();

        List<CliqueSolutionInMemory> cliqueIdxtoSolutionList = new ArrayList<>(cliqueCount);
        for (int i = 0; i < cliqueCount; i++) {

            IntList colIndxs = arasuCliquesAsColIndxs.get(i);
            int[] cliqueMultipliers = cliqueIdxtoMultipliers.get(i);

            CliqueSolutionInMemory cliqueSolution = new CliqueSolutionInMemory(colIndxs);
            for (int j = getCliqueVarcount(colIndxs) - 1; j >= 0; j--) {

                String varname = "var" + i + "_" + j;
                long rowcount = Long.parseLong(model.evaluate(ctx.mkIntConst(varname), true).toString());
                if (rowcount != 0) {
                    IntList columnValues = getFloorInstantiation(colIndxs, cliqueMultipliers, j);
                    ValueCombination valueCombination = new ValueCombination(columnValues, rowcount);
                    cliqueSolution.addValueCombination(valueCombination);
                }
            }
            cliqueIdxtoSolutionList.add(cliqueSolution);
        }

        ctx.close();
        return cliqueIdxtoSolutionList;
    }

    //    private void exportToFile(int cliqueNo, List<IntList> cRegionVarIndxsList, LongList bvalues) {
    //
    //        try {
    //            FileWriter fw = new FileWriter(new File("/home/dsladmin/CODD/RaghavSood/intermediateCliqueMatrices", viewname + "_" + cliqueNo));
    //            String header = bvalues.size() + "\n";
    //            fw.write(header);
    //
    //            for (int i = 0; i < cRegionVarIndxsList.size(); i++) {
    //                String rowStr = StringUtils.join(cRegionVarIndxsList.get(i), Separator.SPACE);
    //                fw.write(bvalues.getLong(i) + " " + rowStr + "\n");
    //            }
    //
    //            fw.close();
    //        } catch (IOException ex) {
    //            throw new RuntimeException("File writing error", ex);
    //        }
    //    }
    //
    //    private void printSolution(List<CliqueSolutionInMemory> cliqueIdxtoSolutionList) {
    //
    //        System.out.println("Clique idx to Solution List");
    //        for (int i = 0; i < cliqueCount; i++) {
    //            System.out.println(i + " " + cliqueIdxtoSolutionList.get(i));
    //        }
    //    }

    /**
     * Check Example 7 of the paper.
     * @param cliqueIdxtoSolutionList
     * @cite Arasu, Arvind, Raghav Kaushik, and Jian Li. "Data generation using declarative constraints." Proceedings of the 2011 ACM SIGMOD International Conference on Management of data. ACM, 2011.
     * @return
     */
    private ViewSolution sampleViewSolution(List<CliqueSolutionInMemory> cliqueIdxtoSolutionList) {

        IntSet seenColIndxs = new IntOpenHashSet();
        List<IntList> priorColIndxsPerClique = new ArrayList<>(cliqueCount);
        for (int i = 0; i < cliqueCount; i++) {
            IntList allColIndxs = cliqueIdxtoSolutionList.get(i).getColIndexes();
            IntList nonpriorColIndx = new IntArrayList(allColIndxs);
            nonpriorColIndx.removeAll(seenColIndxs);
            IntList priorColIndxs = new IntArrayList(allColIndxs);
            priorColIndxs.removeAll(nonpriorColIndx);
            priorColIndxsPerClique.add(priorColIndxs);
            seenColIndxs.addAll(allColIndxs);
        }

        List<GenerativeDistribution> genDistrnPerClique = new ArrayList<>(cliqueCount);
        for (int i = 0; i < cliqueCount; i++) {
            GenerativeDistribution cliqueGenDistrn;
            if (priorColIndxsPerClique.get(i).isEmpty()) {
                cliqueGenDistrn = new GenerativeDistribution(arasuCliquesAsColIndxs.get(i));
            } else {
                cliqueGenDistrn = new GenerativeDistributionWithPrior(arasuCliquesAsColIndxs.get(i), priorColIndxsPerClique.get(i));
            }

            CliqueSolutionInMemory cliqueSolution = cliqueIdxtoSolutionList.get(i);
            for (ValueCombination valueCombination : cliqueSolution) {
                cliqueGenDistrn.addValueCombination(valueCombination.getColValues(), valueCombination.getRowcount());
            }
            genDistrnPerClique.add(cliqueGenDistrn);
        }

        prepareForSampling(genDistrnPerClique);

        //Needed for getting size of a valueCombination
        ValueCombination firstSampledValueCombination = sampleValueCombination(priorColIndxsPerClique, genDistrnPerClique);
        firstSampledValueCombination = getReverseMappedValueCombination(firstSampledValueCombination);
        firstSampledValueCombination = getExpandedValueCombination(firstSampledValueCombination);

        if (relationCardinality > Integer.MAX_VALUE)
            throw new RuntimeException("Expected cases with int relationCardinality here but found " + relationCardinality);

        ViewSolution sampledViewSolution = getEmptyViewSolutionBasedOnSpillType((int) relationCardinality, firstSampledValueCombination.getSizeInBytes());
        if (relationCardinality > 0) {
            sampledViewSolution.addValueCombination(firstSampledValueCombination);
        }
        for (int i = 1; i < relationCardinality; i++) {
            ValueCombination sampledValueCombination = sampleValueCombination(priorColIndxsPerClique, genDistrnPerClique);
            sampledValueCombination = getReverseMappedValueCombination(sampledValueCombination);
            sampledValueCombination = getExpandedValueCombination(sampledValueCombination);
            sampledViewSolution.addValueCombination(sampledValueCombination);
        }
        return sampledViewSolution;
    }

    //    private List<ValueCombination> getEmptyViewSolutionBasedOnSpillType(int expectedCapacity, int entrySizeInBytes) {
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

    private ViewSolution getEmptyViewSolutionBasedOnSpillType(int expectedCapacity, int entrySizeInBytes) {
        switch (spillType) {
            case INMEMORY:
                return new ViewSolutionInMemory(expectedCapacity);
            case FILEBACKED_FKeyedBased:
                if (PostgresVConfig.ANONYMIZED_VIEWINFOs.get(viewname).getIsNeverFKeyed())
                    return new ViewSolutionDiskBased(viewname, entrySizeInBytes);
                return new ViewSolutionInMemory(expectedCapacity);
            default:
                throw new RuntimeException("Unsupported SpillType " + spillType.name());
        }
    }

    private void prepareForSampling(List<GenerativeDistribution> genDistrnPerClique) {
        for (int i = 0; i < cliqueCount; i++) {
            GenerativeDistribution cliqueGenDistrn = genDistrnPerClique.get(i);
            cliqueGenDistrn.prepareForSampling();
        }
    }

    private ValueCombination sampleValueCombination(List<IntList> priorColIndxsPerClique, List<GenerativeDistribution> genDistrnPerClique) {

        Int2IntMap colIndxToValue = new Int2IntOpenHashMap(sortedAllCliquesColIndxs.size());
        for (int i = 0; i < cliqueCount; i++) {
            GenerativeDistribution cliqueGenDistrn = genDistrnPerClique.get(i);

            IntList priorColIndxs = priorColIndxsPerClique.get(i);
            IntList priorColValues = new IntArrayList(priorColIndxs.size());

            for (IntIterator iter = priorColIndxs.iterator(); iter.hasNext();) {
                int colIndx = iter.nextInt();
                int value = colIndxToValue.get(colIndx);
                priorColValues.add(value);
            }

            IntList sampleCliqueValues = cliqueGenDistrn.sampleWithPrior(priorColValues);
            for (int j = 0; j < cliqueGenDistrn.getColIndxs().size(); j++) {
                colIndxToValue.put(cliqueGenDistrn.getColIndxs().get(j), sampleCliqueValues.get(j));
            }
        }

        IntList colValues = new IntArrayList(sortedAllCliquesColIndxs.size());
        for (IntIterator iter = sortedAllCliquesColIndxs.iterator(); iter.hasNext();) {
            int colIndx = iter.nextInt();
            colValues.add(colIndxToValue.get(colIndx));
        }
        ValueCombination valueCombination = new ValueCombination(colValues, 1);
        return valueCombination;
    }

    private IntList getFloorInstantiation(IntList colIndxs, int[] cliqueMultipliers, int varIndx) {

        int bucketCount = colIndxs.size();
        IntList columnValues = new IntArrayList(bucketCount);
        for (int i = 0; i < bucketCount - 1; i++) { //MSB to LSB
            int pos = varIndx / cliqueMultipliers[i];
            columnValues.add(pos);
            varIndx -= pos * cliqueMultipliers[i];
        }
        columnValues.add(varIndx);
        return columnValues;
    }

    private IntList getIntersectingColIndxs(IntList colIndxsCliqueI, IntList colIndxsCliqueJ) {
        IntList temp = new IntArrayList(colIndxsCliqueI);
        temp.removeAll(colIndxsCliqueJ);
        IntList intersectingColIndxs = new IntArrayList(colIndxsCliqueI);
        intersectingColIndxs.removeAll(temp);
        return intersectingColIndxs;
    }

    private List<boolean[]> getTruncatedAllTrueBS(IntList intersectingColIndxs) {
        List<boolean[]> truncatedAllTrueBS = new ArrayList<>();
        for (int i = 0; i < allTrueBS.size(); i++) {
            if (intersectingColIndxs.contains(i)) {
                truncatedAllTrueBS.add(allTrueBS.get(i));
            }
        }
        return truncatedAllTrueBS;
    }

    private List<Region> getTruncatedRegions(List<Region> regions, IntList intersectingColIndxs) {
        List<Region> truncatedRegions = new ArrayList<>(regions.size());
        for (Region region : regions) {
            Region truncatedRegion = getTruncatedRegion(region, intersectingColIndxs);
            truncatedRegions.add(truncatedRegion);
        }
        return truncatedRegions;
    }

    private Region getTruncatedRegion(Region region, IntList intersectingColIndxs) {
        Region truncatedRegion = new Region();
        for (BucketStructure bs : region.getAll()) {
            BucketStructure truncatedBS = new BucketStructure();
            List<Bucket> buckets = bs.getAll();
            for (int i = 0; i < buckets.size(); i++) {
                if (intersectingColIndxs.contains(i)) {
                    truncatedBS.add(buckets.get(i));
                }
            }
            truncatedRegion.add(truncatedBS);
        }
        return truncatedRegion;
    }

    /**
     * This method looks at the condition and sets the appropriate buckets of a bucketStructures as true.
     * It then creates Z3 int variable by following naming convention:
     * Consider the bucketStructure to be semantically [[0, 4, 8], [0], [0, 2]]
     *  Bucket Combination symantic_varname Index Z3_varname
     *         0 0 0            0_0_0         0     var0
     *         0 0 2            0_0_1         1     var1
     *         4 0 0            1_0_0         2     var2
     *         4 0 2            1_0_1         3     var3
     *         8 0 0            2_0_0         4     var4
     *         8 0 2            2_0_1         5     var5
     * If now the condition asks for [[false, true, false], [true], [true, true]] = output cardinality 100
     * we get z3 constraint as
     *         1_0_0 + 1_0_1 = 100
     * In this case, the list of indices [2, 3] is returned
     * @param sortedColumns
     * @param bucketStructures
     * @param bucketFloorsByColumns
     * @param condition
     * @return
     */
    private IntList getIndxsForCondition(Region cRegion, IntList cliqueColIndxs, int[] multipliers, int bucketCount) {

        IntList indxsInRegion = new IntArrayList();
        for (BucketStructure bucketStructure : cRegion.getAll()) {

            IntList indxsInBS = new IntArrayList();
            int i, j;
            i = bucketCount - 1;
            for (j = 0; j < bucketStructure.at(i).size(); j++) { //Adding indxs from LSB column
                indxsInBS.add(bucketStructure.at(i).at(j));
            }
            if (indxsInBS.isEmpty())
                throw new RuntimeException("Should not be reaching here");
            for (i--; i >= 0; i--) { //LSB TO MSB
                IntList tempIndxsBS = new IntArrayList();
                for (j = 0; j < bucketStructure.at(i).size(); j++) {
                    for (IntIterator iter = indxsInBS.iterator(); iter.hasNext();) {
                        int ind = iter.nextInt();
                        tempIndxsBS.add(ind + bucketStructure.at(i).at(j) * multipliers[i]);
                    }
                }
                indxsInBS = tempIndxsBS;
            }
            indxsInRegion.addAll(indxsInBS);
        }

        IntList sortedUniquedIndxsRegion = new IntArrayList(new IntOpenHashSet(indxsInRegion));
        Collections.sort(sortedUniquedIndxsRegion);
        return sortedUniquedIndxsRegion;
    }

    private IntList getIndxForGivenCols(List<boolean[]> cliqueAllTrueBS, IntList allColIndxs, IntList chosenColIndxs, int[] multipliers) {

        int bucketCount = cliqueAllTrueBS.size();
        //Setting false all but first element in non-chosen cols
        List<boolean[]> cliqueChosenAllTrueBS = deepCopyBS(cliqueAllTrueBS);
        for (int c = 0; c < bucketCount; c++) {
            if (!chosenColIndxs.contains(allColIndxs.get(c))) {
                boolean[] arr = cliqueChosenAllTrueBS.get(c);
                Arrays.fill(arr, 1, arr.length, false);
            }
        }
        return getIndxsFromGivenBS(cliqueChosenAllTrueBS, multipliers);
    }

    private IntList getIndxsFromGivenBS(List<boolean[]> givenBS, int[] multipliers) {
        IntList indxs = new IntArrayList();
        int i, j;
        int bucketCount = givenBS.size();
        i = bucketCount - 1;
        for (j = 0; j < givenBS.get(i).length; j++) { //Adding indices from LSB column
            if (givenBS.get(i)[j]) {
                indxs.add(j);
            }
        }
        if (indxs.isEmpty())
            throw new RuntimeException("Should not be reaching here");
        for (i--; i >= 0; i--) { //LSB TO MSB
            IntList tempIndxs = new IntArrayList();
            for (j = 0; j < givenBS.get(i).length; j++) {
                if (givenBS.get(i)[j]) {
                    for (IntIterator iter = indxs.iterator(); iter.hasNext();) {
                        int ind = iter.nextInt();
                        tempIndxs.add(ind + j * multipliers[i]);
                    }
                }
            }
            indxs = tempIndxs;
        }

        return indxs;
    }

    private static List<boolean[]> deepCopyBS(List<boolean[]> bucketStructures) {
        List<boolean[]> bucketStructuresCopy = new ArrayList<>(bucketStructures.size());
        for (boolean[] bucketStructure : bucketStructures) {
            boolean[] bucketStructureCopy = Arrays.copyOf(bucketStructure, bucketStructure.length);
            bucketStructuresCopy.add(bucketStructureCopy);
        }
        return bucketStructuresCopy;
    }

    private int getCliqueVarcount(IntList cliquesAsColIndxs) {
        int cliqueVarcount = 1;
        for (IntListIterator iter = cliquesAsColIndxs.iterator(); iter.hasNext();) {
            int colIndx = iter.nextInt();
            cliqueVarcount *= allTrueBS.get(colIndx).length;
        }
        return cliqueVarcount;
    }

}

class CliqueIntersectionInfoArasu {
    int     i;
    int     j;
    IntList intersectingColIndxs;
}
