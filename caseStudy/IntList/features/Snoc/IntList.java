public class IntList {
    /*@ requires \original;
      @ ensures \original;
      @ assignable \nothing; */
    int[] insert(int[] A, int x) {
        int i = 0;
        int[] result = new int[A.length + 1];
        result[0] = x;
		/*@ loop_invariant result.length == A.length + 1 && result[0] == x && 0 <= i && i <= A.length &&
		  @   (\forall int j; 0 <= j < i; (\exists int k; 1 <= k && k <= i; result[k] == A[j]));
		  @ decreases A.length - i;
		  @ assignable result[*], i; */
        while (i < A.length) {
            result[i + 1] = A[i];
            i = i + 1;
        }
        return result;
    }
}