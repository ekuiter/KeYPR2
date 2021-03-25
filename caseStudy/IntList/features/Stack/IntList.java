public class IntList {
    /*@ requires A.length > 0;
      @ ensures \result == A[A.length - 1];
      @ assignable \nothing; */
    public int top(int[] A) {
        return A[A.length - 1];
    }

    /*@ requires A.length > 0;
      @ ensures (\forall int i; 0 <= i < \result.length; (\exists int j; 0 <= j < A.length; A[j] == \result[i]));
      @ assignable \nothing; */
    int[] pop(int[] A) {
        int i = 0;
        int[] result = new int[A.length - 1];
		/*@ loop_invariant result.length == A.length - 1 && 0 <= i && i <= result.length &&
		  @   (\forall int j; 0 <= j < i; (\exists int k; 0 <= k < i; A[k] == result[j]));
		  @ decreases result.length - i;
		  @ assignable result[*], i; */
        while (i < result.length) {
            result[i] = A[i];
            i = i + 1;
        }
        return result;
    }

    /*@ requires true;
      @ ensures \result <==> (A.length == 0);
      @ assignable \nothing; */
    public boolean isEmpty(int[] A) {
        return A.length == 0;
    }
}