package beispiele;

import java.util.ArrayList;
import java.util.List;

class CombinationFinder {
    ArrayList<String> list;
    int index;

    public CombinationFinder() {
    }

    /* arr[]  ---> Input Array
    data[] ---> Temporary array to store current combination
    start & end ---> Starting and Ending indexes in arr[]
    index  ---> Current index in data[]
    r ---> Size of a combination to be printed */
    public static List<List<Integer>> combinationUtil(List<Integer> arr, List<Integer> data, int start,
                                                      int end, int index, int r)
    {
        List<List<Integer>> combinations = new ArrayList<>();

        // Current combination is ready to be printed, print it
        if (index == r)
        {
            List<Integer> newCombination = new ArrayList<>();
            for (int j=0; j<r; j++) {
                //System.out.print(data.get(j) + " ");
                newCombination.add(data.get(j));
            }
            combinations.add(newCombination);

            //System.out.println("");
            return combinations;
        }

        // replace index with all possible elements. The condition
        // "end-i+1 >= r-index" makes sure that including one element
        // at index will make a combination with remaining elements
        // at remaining positions
        for (int i=start; i<=end && end-i+1 >= r-index; i++)
        {
            data.add(index, arr.get(i));
            combinations.addAll(combinationUtil(arr, data, i+1, end, index+1, r));
        }
        return combinations;
    }

    // The main function that prints all combinations of size r
    // in arr[] of size n. This function mainly uses combinationUtil()
    public static List<List<Integer>> printCombination(List<Integer> arr, int n, int r)
    {
        // A temporary array list to store all combination one by one
        List<Integer> newCombs = new ArrayList<>();

        // Print all combination using temporary array 'data[]'
        return combinationUtil(arr, newCombs, 0, n-1, 0, r);
    }
}