import java.util.Arrays;

public class TarjansAlgorithmArray2 {
    // null pointer checks
        /* public invariant adjVertices != null;
           public invariant (\forall int i; 0 <= i < adjVertices.length; adjVertices[i] != null);*/
        /*@public invariant dfsNumbers != null && lowlinkNumbers != null;
           public invariant stack != null && onStack != null;
           public invariant components != null;
         */

    // variable bounds
        /* public invariant (0 <= currentComp <= adjVertices.length);
           public invariant (-1 <= stackPointer < stack.length);
           public invariant (0 <= currentDFSNumber <= dfsNumbers.length);
          */

    // array lengths
        /* public invariant adjVertices.length == dfsNumbers.length && adjVertices.length == lowlinkNumbers.length;
           public invariant adjVertices.length == stack.length && adjVertices.length == onStack.length;
           public invariant adjVertices.length == components.length;
           public invariant adjVertices.length > 0;
          */

    // adjacency vertices bound
        /* public invariant (\forall int i; 0 <= i < adjVertices.length;
                                (\forall int j; 0 <= j < adjVertices[i].length; 0 <= adjVertices[i][j] < adjVertices.length)
                             );
        */

    // dfsNumbers and lowlinkNumbers bound
        /* public invariant (\forall int i; 0 <= i < dfsNumbers.length; (-1 <= dfsNumbers[i] < currentDFSNumber)
                                                                          && (-1 <= lowlinkNumbers[i] <= dfsNumbers[i])
                             );
         @*/
        // components bound
        // public invariant (\forall int i; 0 <= i < components.length; -1 <= components[i] <= currentComp);


        // stack bounds
        /* public invariant (\forall int i; 0 <= i < stack.length; 0 <= stack[i] < currentDFSNumber);
           public invariant (\forall int i; 0 <= i < onStack.length; onStack[i] == 0 || onStack[i] == 1);
          */

    // implications
        /* public invariant (\forall int i; 0 <= i < currentDFSNumber;
                                (\exists int k; 0 <= k < dfsNumbers.length; dfsNumbers[k] == i
                                    && (\forall int t; 0 <= t < dfsNumbers.length; dfsNumbers[t] != i)
                                )
                             );
           public invariant (\forall int i; 0 <= i < dfsNumbers.length; (dfsNumbers[i] != -1) <==> (lowlinkNumbers[i]!= -1));
           public invariant (\forall int i; 0 <= i < onStack.length; (onStack[i] == 1) ==> (components[i] == -1));
          */

    //TODO SCC reachability

    public int currentComp = 0; // = 0
    public int stackPointer = -1; // -1 indicates empty stack
    public int currentDFSNumber = 0; // = 0

    public int[][] adjVertices; // adjVertices[i] has element j <=> edge from i to j
    public int[] dfsNumbers; // dfsNumbers[i] == -1 <=> no dfs number yet, not visited
    public int[] lowlinkNumbers; // lowlinkNumbers[i] == 1 <=> no dfs number yet, not visited

    public int[] stack;
    public int[] onStack; // onStack[i] == 1 <=> i is on the stack
    public int[] components; // components[i] == k <=> vertex i is in component k
    boolean[][] reachable;


    /*@ pure*/
    public int sumDFS() {
        int sum = 0;
        for (int i : dfsNumbers) {
            if (i != -1) {
                sum++;
            }
        }
        return sum;
    }


    /*@ pure */
    public boolean reachable(int x, int y) {
        if (x == y) {
            return true;
        }
        for(int index : adjVertices[x]) {
            if(index == y)
                return true;
        }

        return false;
    }

    public void populateReachable() {
        reachable = new boolean[adjVertices.length][adjVertices.length];
        for(int i = 0; i < adjVertices.length; ++i) {
            reachable[i][i] = true;
            for(int j = 0; j < adjVertices[i].length; ++j) {
                reachable[i][adjVertices[i][j]] = true;
            }
        }
        for (int k = 0; k < adjVertices.length; k++) {
            for (int i = 0; i < adjVertices.length; i++) {
                for (int j = 0; j < adjVertices.length; j++) {
                    reachable[i][j] = reachable[i][j] || (reachable[i][k] && reachable[k][j]);
                }
            }
        }
    }

    /*@ normal_behaviour
      @ requires graph != null;
      @ requires (\forall int i; 0 <= i < graph.length; graph[i] != null);
      @ requires (\forall int i; 0 <= i < graph.length;
      @             (\forall int j; 0 <= j < graph[i].length;
      @                 0 <= graph[i][j] < graph.length)
      @          );
      @ requires graph.length == dfsNumbers.length && graph.length == lowlinkNumbers.length;
      @ requires graph.length == stack.length && graph.length == onStack.length;
      @ requires graph.length == components.length;
      @ requires graph.length > 0;
      @ requires (\forall int i; 0 <= i < dfsNumbers.length; dfsNumbers[i] == -1);
      @ requires (\forall int i; 0 <= i < lowlinkNumbers.length; lowlinkNumbers[i] == -1);
      @ requires (\forall int i; 0 <= i < onStack.length; onStack[i] == 0);
      @ requires (\forall int i; 0 <= i < components.length; components[i] == -1);
      @ requires stackPointer == -1;
      @ requires currentDFSNumber == 0;
      @ requires currentComp == 0;
      @ ensures (\forall int j; 0 <= j < adjVertices.length;
      @                 (\forall int k; 0 <= k < adjVertices.length;
      @                     (components[j] == components[k]) ==> (reachable[k][j] && reachable[j][k])
      @                 )
      @             );
      @ assignable \everything;
      @*/
    public void startTarjans(int[][] graph) {
        this.adjVertices = graph;
        populateReachable();
        for (int i = 0; i < dfsNumbers.length; i++) {
            if (dfsNumbers[i] == -1) {
                this.dfsSCC(i);
            }
        }
    }

    public void dfsSCC(int vertexLabel) {
        preDFS(vertexLabel);
        for (int neighborVertexInd = 0; neighborVertexInd < adjVertices[vertexLabel].length; neighborVertexInd++) {
            int neighborVertex = adjVertices[vertexLabel][neighborVertexInd];
            if (dfsNumbers[neighborVertex] == -1) {
                dfsSCC(neighborVertex);
                lowlinkNumbers[vertexLabel] = lowlinkNumbers[vertexLabel] < lowlinkNumbers[neighborVertex] ? lowlinkNumbers[vertexLabel] : lowlinkNumbers[neighborVertex];
            } else if (dfsNumbers[neighborVertex] < dfsNumbers[vertexLabel] && onStack[neighborVertex] == 1) {
                lowlinkNumbers[vertexLabel] = lowlinkNumbers[vertexLabel] < dfsNumbers[neighborVertex] ? lowlinkNumbers[vertexLabel] : dfsNumbers[neighborVertex];
            }
        }

        postDFS(vertexLabel);
    }

    public void preDFS(int vertexLabel) {
        dfsNumbers[vertexLabel] = currentDFSNumber;
        lowlinkNumbers[vertexLabel] = currentDFSNumber;
        currentDFSNumber++;

        this.stackPointer++;
        stack[stackPointer] = vertexLabel;
        onStack[vertexLabel] = 1;
    }


    public void postDFS(int vertexLabel) {
        if (dfsNumbers[vertexLabel] == lowlinkNumbers[vertexLabel]) {
            int initialStackPointer = stackPointer; // for loop invariant
            while (stackPointer != -1 && dfsNumbers[stack[stackPointer]] >= dfsNumbers[vertexLabel]) {
                this.components[stack[stackPointer]] = currentComp;
                stackPointer--;
            }
            currentComp++;
        }


    }

    public static void main(String[] args) {
        TarjansAlgorithmArray2 tj = new TarjansAlgorithmArray2();
        int k = 3;
        tj.adjVertices = new int[k][];
        tj.components = new int[k];
        tj.lowlinkNumbers = new int[k];
        for(int i = 0; i < tj.lowlinkNumbers.length; ++i) {
            tj.lowlinkNumbers[i] = -1;
        }
        tj.dfsNumbers = new int[k];
        for(int i = 0; i < tj.dfsNumbers.length; ++i) {
            tj.dfsNumbers[i] = -1;
        }
        tj.stack = new int[k];
        tj.onStack = new int[k];
        tj.components = new int[k];
        tj.adjVertices[0] = new int[]{1};
        tj.adjVertices[1] = new int[]{0};
        tj.adjVertices[2] = new int[]{0};
        tj.populateReachable();
        //tj.startTarjans(tj.adjVertices);
        for(int i : tj.components) {
            System.out.println(i);
        }
        for(boolean[] a : tj.reachable) {
            System.out.println(Arrays.toString(a));
        }
    }
}