public class TreeMax {
    public class Node {
        int id;
        int val;
        Node left;
        Node right;

        public Node(Node left, Node right, int val) {
            this.val = val;
            this.right = right;
            this.left = left;
        }
    }

    //private static Node[] ghostArray;

    private static boolean isMap(Node[] array, Node treeRoot, int lvl, int offset) {
        int test = array.length;
        Node n = array[((1 << lvl) + offset) - 1];
        if(n == null && treeRoot == null) {
            return isNull(array, lvl, offset);
        }
        if(n == null || treeRoot == null) {
            return false;
        }
        boolean base = (n.val == treeRoot.val);
        return base && isMap(array, treeRoot.left, lvl + 1, offset * 2) && isMap(array, treeRoot.right, lvl + 1, offset * 2 + 1);
    }

    private static boolean isNull(Node[] array, int lvl, int offset) {
        int idx = ((1 << lvl) + offset) - 1;
        if (idx >= array.length) {
            return true;
        }
        return array[idx] == null && isNull(array, lvl + 1, offset * 2) && isNull(array, lvl + 1, offset * 2 + 1);
    }

    /*@ private normal_behaviour
      @ requires root != null && depth(root) <= 3;
      @ requires ghostArray != null;
      @ requires ghostArray.length == 1 << depth(root);
      @ requires (\forall int i; 0 <= i < ghostArray.length; (\forall int j; i < j < ghostArray.length;
      @     (ghostArray[i] != null && ghostArray[j] != null) ==> ghostArray[i].id != ghostArray[j].id));
      @ requires isMap(ghostArray, root, 0, 0);
      @ ensures (\forall int i; 0 <= i < (1 << depth(root)) - 1; ghostArray[i] == null || ghostArray[i].val <= \result);
      @ assignable \nothing;
     */
    public static int max(Node root, Node[] ghostArray) {
        int test2 = (1 << depth(root)) - 1;
        int max = root.val;
        if(root.left != null) {
            int val = max(root.left, ghostArray);
            if(val > max) {
                max = val;
            }
        }
        if(root.right != null) {
            int val = max(root.right, ghostArray);
            if(val > max) {
                max = val;
            }
        }
        return max;
    }

    private static int size(Node root1) {
        if(root1 == null) {
            return 1;
        }
        int res = 1;
        res += size(root1.left);
        res += size(root1.right);
        return res;
    }

    private static int depth(Node root2) {
        if(root2 == null) {
            return 1;
        }
        int leftDepth = depth(root2.left);
        int rightDepth = depth(root2.right);
        if(leftDepth > rightDepth) {
            return leftDepth + 1;
        }
        return rightDepth + 1;
    }
}