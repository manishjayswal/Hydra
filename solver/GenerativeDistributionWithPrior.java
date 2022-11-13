package in.ac.iisc.cds.dsl.cdgvendor.solver;

import java.util.HashMap;
import java.util.Map;

import it.unimi.dsi.fastutil.ints.IntArrayList;
import it.unimi.dsi.fastutil.ints.IntList;
import it.unimi.dsi.fastutil.objects.Object2IntMap;
import it.unimi.dsi.fastutil.objects.Object2LongMap;

/**
 * For a of list of colIndxs, it stores probability of various valueCombinations.
 * Probability is stored in terms of number of occurrence of that value combination in the view.
 * @author dsladmin
 *
 */
public class GenerativeDistributionWithPrior extends GenerativeDistribution {

    private final boolean isPrior[];
    private final IntList nonpriorColIndxs;

    public GenerativeDistributionWithPrior(IntList colIndxs, IntList priorColIndxs) {
        super(colIndxs);
        if (priorColIndxs.isEmpty() || priorColIndxs.size() >= colIndxs.size() || !colIndxs.containsAll(priorColIndxs))
            throw new RuntimeException("Expected priorColIndxs: " + priorColIndxs + " to be non-empty proper subset of colIndxs: " + colIndxs);

        isPrior = new boolean[colIndxs.size()];
        for (int i = 0; i < colIndxs.size(); i++) {
            isPrior[i] = priorColIndxs.contains(colIndxs.getInt(i));
        }

        nonpriorColIndxs = new IntArrayList(colIndxs);
        nonpriorColIndxs.removeAll(priorColIndxs);
    }

    private Map<IntList, GenerativeDistribution> priorColValuesToGenDistrn;

    @Override
    public void prepareForSampling() {

        priorColValuesToGenDistrn = new HashMap<>();
        for (Object2LongMap.Entry<IntList> entry : colValuesToRowcount.object2LongEntrySet()) {

            IntList allColValues = entry.getKey();
            long rowcount = entry.getLongValue();

            IntList priorColValues = new IntArrayList();
            IntList nonpriorColValues = new IntArrayList();
            separatePriorNonpriorColValues(allColValues, priorColValues, nonpriorColValues);

            GenerativeDistribution nonpriorGenDistrn = priorColValuesToGenDistrn.get(priorColValues);
            if (nonpriorGenDistrn == null) {
                nonpriorGenDistrn = new GenerativeDistribution(nonpriorColIndxs);
                priorColValuesToGenDistrn.put(priorColValues, nonpriorGenDistrn);
            }
            nonpriorGenDistrn.addValueCombination(nonpriorColValues, rowcount);
        }
        for (GenerativeDistribution nonpriorGenDistrn : priorColValuesToGenDistrn.values()) {
            nonpriorGenDistrn.prepareForSampling();
        }
    }

    /**
     * Each call to this method returns a IntList colValues chosen randomly given IntList priorColValues.
     * @param priorColValues
     * @return IntList colValues corresponding to colIndxs
     */
    @Override
    public IntList sampleWithPrior(IntList priorColValues) {
        GenerativeDistribution nonpriorGenDistrn = priorColValuesToGenDistrn.get(priorColValues);
        IntList nonpriorColValues = nonpriorGenDistrn.sampleWithPrior(null);

        IntList allColValues = new IntArrayList();
        collaboratePriorNonpriorColValues(allColValues, priorColValues, nonpriorColValues);
        return allColValues;
    }

    /**
     * allColValues separated into two initially empty lists
     * @param allColValues
     * @param priorColValues
     * @param nonpriorColValues
     */
    private void separatePriorNonpriorColValues(IntList allColValues, IntList priorColValues, IntList nonpriorColValues) {
        for (int i = 0; i < isPrior.length; i++) {
            if (isPrior[i]) {
                priorColValues.add(allColValues.getInt(i));
            } else {
                nonpriorColValues.add(allColValues.getInt(i));
            }
        }
    }

    /**
     * two separated listed joined into an initially empty list
     * @param allColValues
     * @param priorColValues
     * @param nonpriorColValues
     */
    private void collaboratePriorNonpriorColValues(IntList allColValues, IntList priorColValues, IntList nonpriorColValues) {
        for (int i = 0, p = -1, np = -1; i < isPrior.length; i++) {
            if (isPrior[i]) {
                allColValues.add(priorColValues.getInt(++p));
            } else {
                allColValues.add(nonpriorColValues.getInt(++np));
            }
        }
    }

    @Override
    public String toString() {
        return "priorColValuesToGenDistrn=" + priorColValuesToGenDistrn;
    }
}
