package in.ac.iisc.cds.dsl.cdgvendor.solver;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import org.jgrapht.UndirectedGraph;
import org.jgrapht.alg.BronKerboschCliqueFinder;
import org.jgrapht.alg.CliqueMinimalSeparatorDecomposition;
import org.jgrapht.alg.ConnectivityInspector;
import org.jgrapht.alg.NeighborIndex;
import org.jgrapht.graph.AbstractBaseGraph;
import org.jgrapht.graph.DefaultEdge;
import org.jgrapht.graph.SimpleGraph;

import in.ac.iisc.cds.dsl.cdgvendor.constants.PostgresVConfig;
import in.ac.iisc.cds.dsl.cdgvendor.model.ViewInfo;
import in.ac.iisc.cds.dsl.cdgvendor.model.formal.FormalCondition;
import in.ac.iisc.cds.dsl.cdgvendor.utils.DebugHelper;

public class CliqueFinder {

    private final List<String>    sortedColumns;
    private final List<boolean[]> allTrueBS;

    public CliqueFinder(ViewInfo viewInfo, List<boolean[]> allTrueBS) {
        sortedColumns = new ArrayList<>(viewInfo.getViewNonkeys());
        Collections.sort(sortedColumns);

        this.allTrueBS = allTrueBS;
    }

    /**
     * Returns cliques other than those with single attribute single split.
     * Cliques are ordered so that first can be merged with second and then third and so on...
     * @param conditions
     * @return
     */
    
    public List<Set<String>> subhoGetOrderedNonTrivialCliques(List<FormalCondition> conditions, String viewname) {

        //STEP 1: Construct an undirected graph with each column as a vertex and edge representing that columns coappear somewhere
        UndirectedGraph<String, DefaultEdge> jgraph = new SimpleGraph<>(DefaultEdge.class);
        for (String column : sortedColumns) {
            jgraph.addVertex(column);
        }
        
//        # Commented by Subho
//        for (FormalCondition condition : conditions) {
//            Set<String> appearingCols = new HashSet<>();
//            AbstractCliqueFinder.getAppearingCols(appearingCols, condition);
//            List<String> colList = new ArrayList<>(appearingCols);
//
//            for (int i = 0; i < colList.size(); i++) {
//                String colI = colList.get(i);
//                for (int j = i + 1; j < colList.size(); j++) {
//                    String colJ = colList.get(j);
//                    jgraph.addEdge(colI, colJ);
//                }
//            }
//        }
//        
        
//        # Added Subho starts
        for (int i = 0; i < sortedColumns.size(); i++) {
            for (int j = i + 1; j < sortedColumns.size(); j++) {
                jgraph.addEdge(sortedColumns.get(i), sortedColumns.get(j));
            }
        }
//        # Added Subho ends

        //Anupam: Added this to remove undesired vertices from the graph. This was done after finding cliques earlier.
        // To remove those vertices that are isolated and also have only one interval in bucketColumn(i.e {0})
        List<String> toBeDeleted = new ArrayList<>();
        for(String vertex:jgraph.vertexSet()){
        	if(jgraph.degreeOf(vertex) == 0 && getSplitCount(vertex) == 1){
        		toBeDeleted.add(vertex);
        		
        	}
        }
        for(String vertex: toBeDeleted){
        	jgraph.removeVertex(vertex);
        }
        toBeDeleted.clear();
        //Anupam: my addition ends here.

        
        //STEP 2: Check if it is chordal. Library method seems fast
        //printMatrix(jgraph);
        CliqueMinimalSeparatorDecomposition<String, DefaultEdge> cmsd = new CliqueMinimalSeparatorDecomposition<>(jgraph);
        if (!cmsd.isChordal()) {
        	DebugHelper.printInfo("Making chordal");
            jgraph = makeChordal(jgraph);
        }

        //STEP 3: Get all maximal cliques
        BronKerboschCliqueFinder<String, DefaultEdge> bkcf = new BronKerboschCliqueFinder<>(jgraph);
        Collection<Set<String>> cliques = bkcf.getAllMaximalCliques();

        //STEP 4: Removing cliques with single column single split
        List<Set<String>> nonTrivialCliques = new ArrayList<>();
        for (Set<String> clique : cliques) {
            if (clique.size() == 1) {
                String columnName = new ArrayList<>(clique).get(0);
                
                if (getSplitCount(columnName) == 1) {
                	DebugHelper.printInfo("singleton clique to be deleted: " +clique);
                    continue;
                }
                /*else{
                	DebugHelper.printInfo("singleton clique to be retained: " +clique);
                }*/
            }
            nonTrivialCliques.add(clique);
        }
        

        if (nonTrivialCliques.size() == 0)
        	throw new RuntimeException("No non trivial cliques found!");

        //Following codepatch is to check the results without sub-view optimization
        /*DebugHelper.printInfo("Nontrivial cliques: " + nonTrivialCliques);
         Set<String> mergedClique = new HashSet<>();
        
        for (Set<String> clique: nonTrivialCliques){
        	for (String col : clique){
        		mergedClique.add(col);
        	}
        }
        
        nonTrivialCliques.clear();
        nonTrivialCliques.add(mergedClique);
        */
        
        //STEP 5: Get cliques in merge order
        DebugHelper.printInfo("Cliques: " + nonTrivialCliques);
        List<Set<String>> orderedCliques = getCliquesInMergeOrder(nonTrivialCliques, jgraph);
        DebugHelper.printInfo("Ordered Cliques: " + orderedCliques);
        return orderedCliques;
    }

    
    public List<Set<String>> getOrderedNonTrivialCliques(List<FormalCondition> conditions, String viewname) {

        //STEP 1: Construct an undirected graph with each column as a vertex and edge representing that columns coappear somewhere
        UndirectedGraph<String, DefaultEdge> jgraph = new SimpleGraph<>(DefaultEdge.class);
        for (String column : sortedColumns) {
            jgraph.addVertex(column);
        }
        
        
        for (FormalCondition condition : conditions) {
            Set<String> appearingCols = new HashSet<>();
            AbstractCliqueFinder.getAppearingCols(appearingCols, condition);
            List<String> colList = new ArrayList<>(appearingCols);

            for (int i = 0; i < colList.size(); i++) {
                String colI = colList.get(i);
                for (int j = i + 1; j < colList.size(); j++) {
                    String colJ = colList.get(j);
                    jgraph.addEdge(colI, colJ);
                }
            }
        }
        
        
        
        
        // ADDED BY - TARUN  Adding extra edges for borrowed attributes to come in same cliques for a fkey.
        // Will be executed in duplication case
        if(PostgresVConfig.fkeyToBorrowedAttr.containsKey(viewname)) {
        	Map<String, Set<String>> fkeyToB = PostgresVConfig.fkeyToBorrowedAttr.get(viewname);
            for(String fkey : fkeyToB.keySet()) {
        		List<String> borrowedColumns = new ArrayList<>(fkeyToB.get(fkey));
        		for(int i=0; i < borrowedColumns.size(); i++) {
        			String colI = borrowedColumns.get(i);
        			for(int j= i+1; j < borrowedColumns.size(); j++) {
        				String colJ = borrowedColumns.get(j);
        				jgraph.addEdge(colI, colJ);
        			}
        		}
        		
            }
        }
        
        
        

        //Anupam: Added this to remove undesired vertices from the graph. This was done after finding cliques earlier.
        // To remove those vertices that are isolated and also have only one interval in bucketColumn(i.e {0})
        List<String> toBeDeleted = new ArrayList<>();
        for(String vertex:jgraph.vertexSet()){
        	if(jgraph.degreeOf(vertex) == 0 && getSplitCount(vertex) == 1){
        		toBeDeleted.add(vertex);
        		
        	}
        }
        for(String vertex: toBeDeleted){
        	jgraph.removeVertex(vertex);
        }
        toBeDeleted.clear();
        //Anupam: my addition ends here.

        //By viewname.equals("t17") to get large LPs
        List<String> unifiedcolList = new ArrayList<>(jgraph.vertexSet());
        for (int i = 0; i < unifiedcolList.size(); i++) {
            String colI = unifiedcolList.get(i);
            for (int j = i + 1; j < unifiedcolList.size(); j++) {
                String colJ = unifiedcolList.get(j);
                if (!jgraph.containsEdge(colI, colJ))
                	jgraph.addEdge(colI, colJ);
            }
        }
        
        //STEP 2: Check if it is chordal. Library method seems fast
        //printMatrix(jgraph);
        CliqueMinimalSeparatorDecomposition<String, DefaultEdge> cmsd = new CliqueMinimalSeparatorDecomposition<>(jgraph);
        if (!cmsd.isChordal()) {
        	DebugHelper.printInfo("Making chordal");
            jgraph = makeChordal(jgraph);
        }

        //STEP 3: Get all maximal cliques
        BronKerboschCliqueFinder<String, DefaultEdge> bkcf = new BronKerboschCliqueFinder<>(jgraph);
        Collection<Set<String>> cliques = bkcf.getAllMaximalCliques();

        //STEP 4: Removing cliques with single column single split
        List<Set<String>> nonTrivialCliques = new ArrayList<>();
        for (Set<String> clique : cliques) {
            if (clique.size() == 1) {
                String columnName = new ArrayList<>(clique).get(0);
                
                if (getSplitCount(columnName) == 1) {
                	DebugHelper.printInfo("singleton clique to be deleted: " +clique);
                    continue;
                }
                /*else{
                	DebugHelper.printInfo("singleton clique to be retained: " +clique);
                }*/
            }
            nonTrivialCliques.add(clique);
        }
        

        if (nonTrivialCliques.size() == 0)
        	throw new RuntimeException("No non trivial cliques found!");

        //Following codepatch is to check the results without sub-view optimization
        /*DebugHelper.printInfo("Nontrivial cliques: " + nonTrivialCliques);
        Set<String> mergedClique = new HashSet<>();
        
        for (Set<String> clique: nonTrivialCliques){
        	for (String col : clique){
        		mergedClique.add(col);
        	}
        }
        
        nonTrivialCliques.clear();
        nonTrivialCliques.add(mergedClique);
        */
        
        //STEP 5: Get cliques in merge order
        DebugHelper.printInfo("Cliques: " + nonTrivialCliques);
        
        // added by Tarun - adding extra column in clique to have all borrowed attr of each fkey in a clique
        // runs for duplication code only
        if(PostgresVConfig.fkeyToBorrowedAttr.containsKey(viewname)) {
    		Map<String, Set<String>> fkeyToB = PostgresVConfig.fkeyToBorrowedAttr.get(viewname);
        	
        	for(String fkey : fkeyToB.keySet()) {
        		Set<String> borrowedColumns = fkeyToB.get(fkey);
        		boolean okFlag = false;
        		List<Integer> columnCountLeft = new ArrayList<>();
        		List<Set<String>> columnsList = new ArrayList<>();
        		for(Set<String> clique : nonTrivialCliques) {
        		
        			Set<String> tempClique = new HashSet<>(borrowedColumns);
        			tempClique.removeAll(clique);
        			if(tempClique.isEmpty()) {
        				okFlag = true;
        				break;
        			}
        			columnCountLeft.add(tempClique.size());
        			columnsList.add(tempClique);
        					
        		}
        		if(!okFlag) {
        			int minIndex = Integer.MAX_VALUE;
        			int cliqueIdx = -1;
        			for(int i=0; i<columnCountLeft.size();i++) {
        				if(minIndex > columnCountLeft.get(i)) {
        					minIndex = columnCountLeft.get(i);
        					cliqueIdx = i;
        				}
        			}
        			
        			System.out.print("");
        			nonTrivialCliques.get(cliqueIdx).addAll(borrowedColumns);
        			
        			
        		}
        	}
    	}
    	
    	
        //System.out.print(nonTrivialCliques);
        List<Set<String>> orderedCliques = getCliquesInMergeOrder(nonTrivialCliques, jgraph);
        DebugHelper.printInfo("Ordered Cliques: " + orderedCliques);
        return orderedCliques;
    }

    public List<Set<String>> unifiedgetOrderedNonTrivialCliques(List<FormalCondition> conditions, String viewname) {

        //STEP 1: Construct an undirected graph with each column as a vertex and edge representing that columns coappear somewhere
        UndirectedGraph<String, DefaultEdge> jgraph = new SimpleGraph<>(DefaultEdge.class);
        for (String column : sortedColumns) {
            jgraph.addVertex(column);
        }
        

        
        for (FormalCondition condition : conditions) {
            Set<String> appearingCols = new HashSet<>();
            AbstractCliqueFinder.getAppearingCols(appearingCols, condition);
            List<String> colList = new ArrayList<>(appearingCols);

            for (int i = 0; i < colList.size(); i++) {
                String colI = colList.get(i);
                for (int j = i + 1; j < colList.size(); j++) {
                    String colJ = colList.get(j);
                    jgraph.addEdge(colI, colJ);
                }
            }
        }
        
        
        
        
        // ADDED BY - TARUN  Adding extra edges for borrowed attributes to come in same cliques for a fkey.
        // Will be executed in duplication case
        if(PostgresVConfig.fkeyToBorrowedAttr.containsKey(viewname)) {
        	Map<String, Set<String>> fkeyToB = PostgresVConfig.fkeyToBorrowedAttr.get(viewname);
            for(String fkey : fkeyToB.keySet()) {
        		List<String> borrowedColumns = new ArrayList<>(fkeyToB.get(fkey));
        		for(int i=0; i < borrowedColumns.size(); i++) {
        			String colI = borrowedColumns.get(i);
        			for(int j= i+1; j < borrowedColumns.size(); j++) {
        				String colJ = borrowedColumns.get(j);
        				jgraph.addEdge(colI, colJ);
        			}
        		}
        		
            }
        }
        
        
        

        //Anupam: Added this to remove undesired vertices from the graph. This was done after finding cliques earlier.
        // To remove those vertices that are isolated and also have only one interval in bucketColumn(i.e {0})
        List<String> toBeDeleted = new ArrayList<>();
        for(String vertex:jgraph.vertexSet()){
        	if(jgraph.degreeOf(vertex) == 0 && getSplitCount(vertex) == 1){
        		toBeDeleted.add(vertex);
        		
        	}
        }
        for(String vertex: toBeDeleted){
        	jgraph.removeVertex(vertex);
        }
        toBeDeleted.clear();
        //Anupam: my addition ends here.

        //PKR
        List<String> unifiedcolList = new ArrayList<>(jgraph.vertexSet());
        for (int i = 0; i < unifiedcolList.size(); i++) {
            String colI = unifiedcolList.get(i);
            for (int j = i + 1; j < unifiedcolList.size(); j++) {
                String colJ = unifiedcolList.get(j);
                if (!jgraph.containsEdge(colI, colJ))
                	jgraph.addEdge(colI, colJ);
            }
        }
        //PKR
        
        //STEP 2: Check if it is chordal. Library method seems fast
        //printMatrix(jgraph);
        CliqueMinimalSeparatorDecomposition<String, DefaultEdge> cmsd = new CliqueMinimalSeparatorDecomposition<>(jgraph);
        if (!cmsd.isChordal()) {
        	DebugHelper.printInfo("Making chordal");
            jgraph = makeChordal(jgraph);
        }

        //STEP 3: Get all maximal cliques
        BronKerboschCliqueFinder<String, DefaultEdge> bkcf = new BronKerboschCliqueFinder<>(jgraph);
        Collection<Set<String>> cliques = bkcf.getAllMaximalCliques();

        //STEP 4: Removing cliques with single column single split
        List<Set<String>> nonTrivialCliques = new ArrayList<>();
        for (Set<String> clique : cliques) {
            if (clique.size() == 1) {
                String columnName = new ArrayList<>(clique).get(0);
                
                if (getSplitCount(columnName) == 1) {
                	DebugHelper.printInfo("singleton clique to be deleted: " +clique);
                    continue;
                }
                /*else{
                	DebugHelper.printInfo("singleton clique to be retained: " +clique);
                }*/
            }
            nonTrivialCliques.add(clique);
        }
        

        if (nonTrivialCliques.size() == 0)
        	throw new RuntimeException("No non trivial cliques found!");

        //Following codepatch is to check the results without sub-view optimization
        /*DebugHelper.printInfo("Nontrivial cliques: " + nonTrivialCliques);
        Set<String> mergedClique = new HashSet<>();
        
        for (Set<String> clique: nonTrivialCliques){
        	for (String col : clique){
        		mergedClique.add(col);
        	}
        }
        
        nonTrivialCliques.clear();
        nonTrivialCliques.add(mergedClique);
        */
        
        //STEP 5: Get cliques in merge order
        DebugHelper.printInfo("Cliques: " + nonTrivialCliques);
        
        // added by Tarun - adding extra column in clique to have all borrowed attr of each fkey in a clique
        // runs for duplication code only
        if(PostgresVConfig.fkeyToBorrowedAttr.containsKey(viewname)) {
    		Map<String, Set<String>> fkeyToB = PostgresVConfig.fkeyToBorrowedAttr.get(viewname);
        	
        	for(String fkey : fkeyToB.keySet()) {
        		Set<String> borrowedColumns = fkeyToB.get(fkey);
        		boolean okFlag = false;
        		List<Integer> columnCountLeft = new ArrayList<>();
        		List<Set<String>> columnsList = new ArrayList<>();
        		for(Set<String> clique : nonTrivialCliques) {
        		
        			Set<String> tempClique = new HashSet<>(borrowedColumns);
        			tempClique.removeAll(clique);
        			if(tempClique.isEmpty()) {
        				okFlag = true;
        				break;
        			}
        			columnCountLeft.add(tempClique.size());
        			columnsList.add(tempClique);
        					
        		}
        		if(!okFlag) {
        			int minIndex = Integer.MAX_VALUE;
        			int cliqueIdx = -1;
        			for(int i=0; i<columnCountLeft.size();i++) {
        				if(minIndex > columnCountLeft.get(i)) {
        					minIndex = columnCountLeft.get(i);
        					cliqueIdx = i;
        				}
        			}
        			
        			System.out.print("");
        			nonTrivialCliques.get(cliqueIdx).addAll(borrowedColumns);
        			
        			
        		}
        	}
    	}
    	
    	
        //System.out.print(nonTrivialCliques);
        List<Set<String>> orderedCliques = getCliquesInMergeOrder(nonTrivialCliques, jgraph);
        DebugHelper.printInfo("Ordered Cliques: " + orderedCliques);
        return orderedCliques;
    }

    
    private UndirectedGraph<String, DefaultEdge> makeChordal(UndirectedGraph<String, DefaultEdge> jgraph) {
    	
    	CliqueMinimalSeparatorDecomposition<String, DefaultEdge> cmsd = new CliqueMinimalSeparatorDecomposition<>(jgraph);
    	jgraph = cmsd.getMinimalTriangulation();
    	cmsd = new CliqueMinimalSeparatorDecomposition<>(jgraph);
    
        
        
        //CliqueMinimalSeparatorDecomposition<String, DefaultEdge> cmsd = new CliqueMinimalSeparatorDecomposition<>(jgraph);
        if (!cmsd.isChordal()){
        	
            throw new RuntimeException("Should not be reaching here - Not Chordal");
        }
        
        return jgraph;
    }

    private void printMatrix(UndirectedGraph<String, DefaultEdge> jgraph) {

        ConnectivityInspector<String, DefaultEdge> ins = new ConnectivityInspector<>(jgraph);
        List<Set<String>> connectedSets = ins.connectedSets();

        List<Set<String>> connectedSets2 = new ArrayList<>();
        for (Set<String> connectedSet : connectedSets) {
            if (connectedSet.size() > 1) {
                connectedSets2.add(connectedSet);
            }
        }

        for (Set<String> connectedSet : connectedSets2) {

            List<String> list = new ArrayList<>(connectedSet);
            Collections.sort(list);

            System.out.println("\n\n" + list);
            int n = list.size();
            int mat[][] = new int[n][n];

            for (int i = 0; i < n; i++) {
                for (int j = 0; j < n; j++) {
                    mat[i][j] = jgraph.containsEdge(list.get(i), list.get(j)) ? 1 : 0;
                }
            }
            for (int i = 0; i < n; i++) {
                for (int j = 0; j < n; j++) {
                    System.out.print(mat[i][j] + " ");
                }
                System.out.println();
            }
        }

    }

    /**
     * @cite Dias, Elisângela Silva, et al. "Efficient enumeration of chordless cycles." arXiv preprint arXiv:1309.1051 (2013). Page 6
     * @param jgraph
     * @return
     */
    private List<List<String>> getChordlessNonTriangleCycles(UndirectedGraph<String, DefaultEdge> jgraph) {

        List<List<String>> T = new ArrayList<>();
        NeighborIndex<String, DefaultEdge> neighborIndex = new NeighborIndex<>(jgraph);
        for (String u : jgraph.vertexSet()) {
            List<String> adjVertices = neighborIndex.neighborListOf(u);
            //Collections.shuffle(adjVertices);
            for (String x : adjVertices) {
                for (String y : adjVertices) {
                	/*if(u.equals("t07_c005") && x.equals("t07_c019") && y.equals("t12_c008")){
                		DebugHelper.printInfo("u: " + u +" x: " + x + " y: " + y);
                		if(jgraph.containsEdge(x,y)){
                			DebugHelper.printInfo("Edge exists");
                		}
                		if (u.compareTo(x) < 0 && x.compareTo(y) < 0 && !jgraph.containsEdge(x, y)) {
                			DebugHelper.printInfo("u: " + u +" x: " + x + " y: " + y);
                		}
                	}*/
                    if (u.compareTo(x) < 0 && x.compareTo(y) < 0 && !jgraph.containsEdge(x, y)) {
                    	/*if(u.equals("t07_c005")){
                    		DebugHelper.printInfo("u: " + u +" x: " + x + " y: " + y);
                    	}*/
                    	/*if(u.equals("t07_c005") && x.equals("t07_c019") && y.equals("t12_c008")){
                    		DebugHelper.printInfo("u: " + u +" x: " + x + " y: " + y);
                    	}*/
                        List<String> triple = new ArrayList<>();
                        triple.add(x);
                        triple.add(u);
                        triple.add(y);
                        T.add(triple);
                    }
                }
            }
        }
        /*for(List<String> p: T){
        	if(p.get(0).equals("t07_c019")){
                DebugHelper.printInfo("triplet: " + p);
        	}
        }*/

        List<List<String>> C = new ArrayList<>();
        while (!T.isEmpty()) {

            List<String> p = T.get(0);
            List<String> temp = new ArrayList<>(p);
            T.remove(0);

            String ulast = p.get(p.size() - 1);
            String u0 = p.get(0);
            String u1 = p.get(1);
            List<String> adjVertices = neighborIndex.neighborListOf(ulast);
            
            for (String v : adjVertices) {
            	/*if(p.get(0).equals("t07_c019") && v.equals("t11_c006")){
                    DebugHelper.printInfo("u0: " + u0 + " u1: " + u1 + " ulast: " + ulast + " v: " + v);
            	}*/
                if (v.compareTo(u1) > 0) {
                    int j;
                    for (j = 1; j < p.size() - 1; j++) {
                    	if(p.get(0).equals("t07_c019")){
                            DebugHelper.printInfo("p: " + p + " v: " + v);
                            DebugHelper.printInfo("j: " +j + " p-size: " + p.size());
                    	}
                        if (jgraph.containsEdge(v, p.get(j))) {
                            break;
                        }
                    }
                    if (j < p.size() - 1) {
                        continue;
                    }
                    
                    
                    p.add(v);
                    
                    if (jgraph.containsEdge(v, u0)) {
                        C.add(p);
                    } else {
                        T.add(p);
                    }
                    
                    p = new ArrayList<>(temp);
                }
            }
        }

        return C;
    }

    private List<Set<String>> getCliquesInMergeOrder(List<Set<String>> unorderedCliques, UndirectedGraph<String, DefaultEdge> jgraph) {

        List<Set<String>> orderedCliques = new ArrayList<>();

        List<String> visitedCols = new ArrayList<>();
        boolean[] visited = new boolean[unorderedCliques.size()];

        orderedCliques.add(unorderedCliques.get(0));
        visitedCols.addAll(unorderedCliques.get(0));
        visited[0] = true;

        while (orderedCliques.size() < unorderedCliques.size()) {
        	boolean adjacentCliqueExists = false;
            int foundCliqueIdx = -1;
            for (int i = 1; i < visited.length; i++) {
                if (visited[i]) {
                    continue;
                }
                //DebugHelper.printInfo("visited columns: " + visitedCols);
                //DebugHelper.printInfo("current clique: " + unorderedCliques.get(i));
                
                Set<String> sharedCols = getColsAlreadyVisited(unorderedCliques.get(i), visitedCols);
                //DebugHelper.printInfo("sharedCols: " + sharedCols);
                
                if (sharedCols.isEmpty()) {
                    continue;
                }

                adjacentCliqueExists = true;

                if (everyPathHasBlockade(unorderedCliques.get(i), new HashSet<>(visitedCols), sharedCols, jgraph)) {
                	//DebugHelper.printInfo("clique found: " + i);
                    foundCliqueIdx = i;
                    break;
                }
            }

            if (adjacentCliqueExists && foundCliqueIdx == -1)
                throw new RuntimeException("We have adjacent unvisted clique(s) but couldn't choose next clique");

            //Picking any unvisitedClique
            if (foundCliqueIdx == -1) {
                for (foundCliqueIdx = 0; foundCliqueIdx < visited.length && visited[foundCliqueIdx]; foundCliqueIdx++) {
                    ;
                }
                if (foundCliqueIdx == visited.length)
                    throw new RuntimeException("Couldn't choose next clique although some are left");
            }

            orderedCliques.add(unorderedCliques.get(foundCliqueIdx));
            visitedCols.addAll(unorderedCliques.get(foundCliqueIdx));
            visited[foundCliqueIdx] = true;

        }

        return orderedCliques;

    }

    /**
     * No side effects method
     * Checks if all paths connecting setA and setB has a police vertex in it
     * @param setA
     * @param setB
     * @param policeSet
     * @param jgraph
     * @return
     */
    private boolean everyPathHasBlockade(Set<String> setA, Set<String> setB, Set<String> policeSet, UndirectedGraph<String, DefaultEdge> jgraph) {

        setA = new HashSet<>(setA);
        setA.removeAll(policeSet);

        setB = new HashSet<>(setB);
        setB.removeAll(policeSet);

        if (setA.isEmpty() || setB.isEmpty())
            return true;

        UndirectedGraph<String, DefaultEdge> jgraphCopy = (UndirectedGraph<String, DefaultEdge>) ((AbstractBaseGraph<String, DefaultEdge>) jgraph).clone();
        jgraphCopy.removeAllVertices(policeSet);
        
        //DebugHelper.printInfo("current clique for path selection: " + setA);
        /*if(jgraphCopy.containsEdge("t07_c005", "t11_c008") && jgraphCopy.containsEdge("t11_c006", "t11_c008")){
        	DebugHelper.printInfo("path exists!");
        }*/
        ConnectivityInspector<String, DefaultEdge> inspector = new ConnectivityInspector<>(jgraphCopy);
        
        //for(String vertexA: setA){
        	for(String vertexB: setB){
        		if (inspector.pathExists(setA.iterator().next(), vertexB)){
        			//DebugHelper.printInfo("see the path exists!");
        			return false;
        		}
        	}
        //}
        
        return true;
        //return !inspector.pathExists(setA.iterator().next(), setB.iterator().next());

    }

    /**
     * Returns those columns of clique which are already visited
     * @param clique
     * @param visitedCols
     * @return
     */
    private Set<String> getColsAlreadyVisited(Set<String> clique, List<String> visitedCols) {

        Set<String> tempSet = new HashSet<>(clique);
        tempSet.removeAll(visitedCols);

        Set<String> resSet = new HashSet<>(clique);
        resSet.removeAll(tempSet);
        return resSet;
    }
    /*
     *  Returns the number of intervals(or split points) for a given column
     *  Example: For Interval: {0,2,3} will return 3 
     */
    private int getSplitCount(String columnName) {

        int colIdx;
        for (colIdx = 0; colIdx < sortedColumns.size() && !sortedColumns.get(colIdx).equals(columnName); colIdx++) {
            ;
        }

        if (colIdx == sortedColumns.size())
            throw new RuntimeException("Not found coumnName: " + columnName + " in sortedColumns: " + sortedColumns);

        return allTrueBS.get(colIdx).length;

    }

    public long getReducedVariableCount(List<Set<String>> cliques) {
        //STEP 4: Count number of variables going clique by clique
        Map<String, Integer> columnsToBucketCount = new HashMap<>();
        for (int i = 0; i < sortedColumns.size(); i++) {
            columnsToBucketCount.put(sortedColumns.get(i), allTrueBS.get(i).length);
        }

        long varcount = 0;
        for (Set<String> clique : cliques) {
            long cliqueVarcount = 1;
            for (String attribute : clique) {
                cliqueVarcount *= columnsToBucketCount.get(attribute);
                //DebugHelper.printDebug(" attribute " + attribute + " vars " + columnsToBucketCount.get(attribute));
            }
            //DebugHelper.printDebug(clique.toString() + " vars " + cliqueVarcount);
            varcount += cliqueVarcount;
        }

        return varcount;
    }

}
