public class IntList {
	/*@ requires \original && (\forall int i; 0 <= i < A.length; (\forall int j; i < j < A.length; A[i] <= A[j]));
	  @ ensures (\forall int i; 0 <= i < \result.length - 1; \result[i] <= \result[i + 1]);
	  @ assignable \everything; */
	int[] insert(int[] A, int x) {
		// CALLS int[] original(int[] A, int x)
        // CALLS void sort(int[] A)
        int[] _result = original(A, x);
		sort(_result);
		return _result;
	}

    /*@ requires \original && (\forall int i; 0 <= i < A.length; (\forall int j; i < j < A.length; A[i] <= A[j]));
      @ ensures (\forall int i; 0 <= i < A.length - 1; A[i] <= A[i + 1]);
      @ assignable A[*]; */
    void remove(int[] A, int x) {
        // CALLS void original(int[] A, int x)
        // CALLS void sort(int[] A)
        original(A, x);
        sort(A);
    }

	/*@ requires \original && (\forall int i; 0 <= i < A.length; (\forall int j; i < j < A.length; A[i] <= A[j]));
      @ ensures \original;
	  @ assignable \nothing; */
	boolean search(int[] A, int x) {
		int l = 0, oldL, h = A.length;
		/*@ loop_invariant (\forall int i; 0 <= i < A.length; (\forall int j; i < j < A.length; A[i] <= A[j])) &&
		  @   ((\exists int i; 0 <= i < A.length; A[i] == x) ==> (\exists int i; l <= i < h; A[i] == x)) &&
		  @   0 <= h && h <= A.length && 0 <= l && l <= A.length;
		  @ decreases h - l;
		  @ assignable oldL, l, h; */
		while (h > l + 1) {
			if (x < A[(l+h)/2]) h = (l + h) / 2;
			else if (x > A[(l+h)/2]) l = (l + h) / 2;
			else {
				oldL = l;
				l = (l+h)/2;
				h = (oldL+h)/2+1;
			}
		}
		return h >= l + 1 && A[l] == x;
	}

    /*@ requires A.length > 0;
      @ ensures (\forall int i; 0 <= i < A.length - 1; A[i] <= A[i + 1]) && (\forall int i; 0 <= i < \old(A).length; (\exists int j; 0 <= j < A.length; A[j] == \old(A)[i])) && (\forall int i; 0 <= i < A.length; (\exists int j; 0 <= j < \old(A).length; A[i] == \old(A)[j]));
      @ assignable A[*]; */
    void sort(int[] A) {
        // CALLS int min(int[] A, int start)
        int pos = 0, tmp, i = 0;
		/*@ loop_invariant A.length > 0 && 0 <= pos < A.length && 0 <= i < A.length &&
		  @   (\forall int j; 0 <= j < pos - 1; A[j] <= A[j + 1]) &&
		  @   (pos > 0 ==> (\forall int j; pos <= j < A.length; A[pos - 1] <= A[j]));
		  @ decreases A.length - pos;
		  @ assignable pos, A[*], i, tmp; */
        while (pos < A.length - 1) {
            i = min(A, pos);
            tmp = A[i];
            A[i] = A[pos];
            A[pos] = tmp;
            pos++;
        }
    }

    /*@ requires A.length > 0 && 0 <= start < A.length;
      @ ensures start <= \result && \result < A.length && (\forall int i; start <= i < A.length; A[\result] <= A[i]);
      @ assignable \nothing; */
    int min(int[] A, int start) {
        int cnt = start, _result = start;
		/*@ loop_invariant 0 <= start < A.length && start <= cnt && cnt <= A.length && start <= _result && _result < A.length &&
		  @   start < A.length && (\forall int i; start <= i < cnt; A[_result] <= A[i]);
		  @ decreases A.length - cnt;
		  @ assignable cnt, _result; */
        while (cnt < A.length) {
            if (A[cnt] < A[_result]) _result = cnt;
            cnt++;
        }
        return _result;
    }
}