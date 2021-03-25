public class IntList {
	/*@ requires A.length > 0;
      @ ensures (\exists int i; 0 <= i < \result.length; \result[i] == x) && (\forall int i; 0 <= i < A.length; (\exists int j; 0 <= j < \result.length; \result[j] == A[i]));
      @ assignable \nothing; */
	int[] insert(int[] A, int x) {
		int i = 0;
		int[] result = new int[A.length + 1];
		result[result.length - 1] = x;
		/*@ loop_invariant result.length == A.length + 1 && result[result.length - 1] == x && 0 <= i && i <= A.length &&
		  @   (\forall int j; 0 <= j < i; (\exists int k; 0 <= k < i; result[k] == A[j]));
		  @ decreases A.length - i;
		  @ assignable result[*], i; */
		while (i < A.length) {
			result[i] = A[i];
			i = i + 1;
		}
		return result;
	}

	/*@ requires A.length > 0;
      @ ensures (\forall int i; 0 <= i < A.length; A[i] != x || A[i] == -1);
      @ assignable A[*]; */
	void remove(int[] A, int x) {
		int i = 0;
		/*@ loop_invariant 0 <= i && i <= A.length && A.length > 0 && (\forall int j; 0 <= j < i; A[j] != x || A[j] == -1);
		  @ decreases A.length - i;
		  @ assignable A[*], i; */
		while (i < A.length) {
			if (A[i] == x)
				A[i] = -1;
			i = i + 1;
		}
	}

	/*@ requires A.length > 0;
	  @ ensures \result <==> (\exists int i; 0 <= i < A.length; A[i] == x);
	  @ assignable \nothing; */
	boolean search(int[] A, int x) {
		int i = A.length - 1;
		/*@ loop_invariant -1 <= i < A.length && !(\exists int j; i + 1 <= j < A.length; A[j] == x);
		  @ decreases i + 1;
		  @ assignable i; */
		while (i >= 0 && A[i] != x) i--;
		return i != -1;
	}
}