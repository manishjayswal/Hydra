package in.ac.iisc.cds.dsl.cdgvendor.solver;

import java.util.ArrayList;
import java.util.List;

import in.ac.iisc.cds.dsl.cdgvendor.utils.RandomGen;
import it.unimi.dsi.fastutil.ints.IntList;
import it.unimi.dsi.fastutil.longs.LongArrayList;
import it.unimi.dsi.fastutil.longs.LongList;
import it.unimi.dsi.fastutil.objects.Object2LongMap;
import it.unimi.dsi.fastutil.objects.Object2LongOpenHashMap;

/**
 * For a of list of colIndxs, it stores probability of various valueCombinations.
 * Probability is stored in terms of number of occurrence of that value combination in the view.
 * @author dsladmin
 *
 */
public class GenerativeDistribution {

    protected final IntList colIndxs;

    public GenerativeDistribution(IntList colIndxs) {
        this.colIndxs = colIndxs;
        colValuesToRowcount = new Object2LongOpenHashMap<>();
        totalRowcount = -1;
        linearizedCumulativeRowcounts = null;
        linearizedColValues = null;
    }

    public IntList getColIndxs() {
        return colIndxs;
    }

    protected final Object2LongMap<IntList> colValuesToRowcount;

    public final void addValueCombination(IntList colValues, long rowcount) {
        long prevcount = colValuesToRowcount.getLong(colValues); // returns 0 when not found
        colValuesToRowcount.put(colValues, prevcount + rowcount);
    }

    private long          totalRowcount;
    private LongList      linearizedCumulativeRowcounts; //linearizes values of colValuesToRowcount map
    private List<IntList> linearizedColValues;           //linearizes keys of colValuesToRowcount map

    public void prepareForSampling() {
        totalRowcount = 0;
        linearizedCumulativeRowcounts = new LongArrayList();
        linearizedColValues = new ArrayList<>();
        for (Object2LongMap.Entry<IntList> entry : colValuesToRowcount.object2LongEntrySet()) {
            IntList colValues = entry.getKey();
            long rowcount = entry.getLongValue();

            totalRowcount += rowcount;
            linearizedCumulativeRowcounts.add(totalRowcount);
            linearizedColValues.add(colValues);
        }
    }

    /**
     * Each call to this method returns a IntList colValues chosen randomly weighted on the pmf.
     * @param priorColValues Ignored. Should be empty
     * @return IntList colValues corresponding to colIndxs
     */
    public IntList sampleWithPrior(IntList priorColValues) {
        long randomPick = RandomGen.nextLong(totalRowcount);
        int chosenPos = binarySearchGE(linearizedCumulativeRowcounts, randomPick);
        //        for (chosenPos = 0; randomPick > 0; chosenPos++) {
        //            randomPick -= linearizedRowcounts.get(chosenPos);
        //        }
        //        chosenPos--;
        return linearizedColValues.get(chosenPos);
    }

    /**
     * Implements iterative binary search to return index of first value GE given key value
     * Assuming key <= list.getInt(list.size()-1)
     * Assuming list.size() >= 1
     * @param list
     * @param key
     * @return
     */
    private static int binarySearchGE(LongList list, long key) {

        int left, right, mid;
        left = 0;
        right = list.size() - 1;
        while (true) {
            mid = (left + right) / 2;
            if (mid > left && list.getLong(mid - 1) >= key) {
                right = mid - 1;
            } else if ((mid == left || list.getLong(mid - 1) < key) && list.getLong(mid) >= key)
                return mid;
            else {
                left = mid + 1;
            }
        }
    }

    @Override
    public String toString() {
        return "colValuesToRowcount=" + colValuesToRowcount + "]";
    }
}
