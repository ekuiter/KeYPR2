public  class IntList {
	/*@ 
	  @ requires (FM.FeatureModel.base) && (FM.FeatureModel.base || !FM.FeatureModel.cons) && (FM.FeatureModel.base || !FM.FeatureModel.snoc) && (FM.FeatureModel.base || !FM.FeatureModel.stack) && (FM.FeatureModel.base || !FM.FeatureModel.sorted);
	  @	requires FM.FeatureModel.base;
	  @ requires A.length > 0;
 ensures (\exists int i; 0 <= i < \result.length; \result[i] == x) && (\forall int i; 0 <= i < A.length; (\exists int j; 0 <= j < \result.length; \result[j] == A[i]));
 assignable \nothing;
	  @*/
	 private int[]  insert__wrappee__Base  (int[] A, int x) {
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

	/*@ 
	  @ requires (FM.FeatureModel.base) && (FM.FeatureModel.base || !FM.FeatureModel.cons) && (FM.FeatureModel.base || !FM.FeatureModel.snoc) && (FM.FeatureModel.base || !FM.FeatureModel.stack) && (FM.FeatureModel.base || !FM.FeatureModel.sorted);
	  @ requires FM.FeatureModel.base || FM.FeatureModel.cons;
	  @ requires FM.FeatureModel.base ==> (A.length > 0);
	  @ ensures FM.FeatureModel.base ==> ((\exists int i; 0 <= i < \result.length; \result[i] == x) && (\forall int i; 0 <= i < A.length; (\exists int j; 0 <= j < \result.length; \result[j] == A[i])));
	  @*/
	 private int[]  insert__wrappee__Cons  (int[] A, int x) {
		if (!FM.FeatureModel.cons)
			return insert__wrappee__Base(A, x);
        return insert__wrappee__Base(A, x);
    }

	/*@ 
	  @ requires (FM.FeatureModel.base) && (FM.FeatureModel.base || !FM.FeatureModel.cons) && (FM.FeatureModel.base || !FM.FeatureModel.snoc) && (FM.FeatureModel.base || !FM.FeatureModel.stack) && (FM.FeatureModel.base || !FM.FeatureModel.sorted);
	  @ requires FM.FeatureModel.base || FM.FeatureModel.cons || FM.FeatureModel.snoc;
	  @ requires FM.FeatureModel.base ==> (A.length > 0);
	  @ ensures FM.FeatureModel.base ==> ((\exists int i; 0 <= i < \result.length; \result[i] == x) && (\forall int i; 0 <= i < A.length; (\exists int j; 0 <= j < \result.length; \result[j] == A[i])));
	  @*/
	 private int[]  insert__wrappee__Snoc  (int[] A, int x) {
		if (!FM.FeatureModel.snoc)
			return insert__wrappee__Cons(A, x);
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

	/*@ 
	  @ requires (FM.FeatureModel.base) && (FM.FeatureModel.base || !FM.FeatureModel.cons) && (FM.FeatureModel.base || !FM.FeatureModel.snoc) && (FM.FeatureModel.base || !FM.FeatureModel.stack) && (FM.FeatureModel.base || !FM.FeatureModel.sorted);
	  @ requires FM.FeatureModel.base || FM.FeatureModel.cons || FM.FeatureModel.snoc || FM.FeatureModel.sorted;
	  @ requires FM.FeatureModel.base ==> (A.length > 0);
	  @ requires FM.FeatureModel.sorted ==> ((\forall int i; 0 <= i < A.length; (\forall int j; i < j < A.length; A[i] <= A[j])));
	  @ ensures !FM.FeatureModel.sorted ==> (FM.FeatureModel.base ==> ((\exists int i; 0 <= i < \result.length; \result[i] == x) && (\forall int i; 0 <= i < A.length; (\exists int j; 0 <= j < \result.length; \result[j] == A[i]))));
	  @ ensures FM.FeatureModel.sorted ==> ((\forall int i; 0 <= i < \result.length - 1; \result[i] <= \result[i + 1]));
	  @*/
	int[] insert(int[] A, int x) {
		if (!FM.FeatureModel.sorted)
			return insert__wrappee__Snoc(A, x);
		
        
        int[] _result = insert__wrappee__Snoc(A, x);
		sort(_result);
		return _result;
	}

	/*@ 
	  @ requires (FM.FeatureModel.base) && (FM.FeatureModel.base || !FM.FeatureModel.cons) && (FM.FeatureModel.base || !FM.FeatureModel.snoc) && (FM.FeatureModel.base || !FM.FeatureModel.stack) && (FM.FeatureModel.base || !FM.FeatureModel.sorted);
	  @	requires FM.FeatureModel.base;
	  @ requires A.length > 0;
 ensures (\forall int i; 0 <= i < A.length; A[i] != x || A[i] == -1);
 assignable A[*];
	  @*/
	 private void  remove__wrappee__Base  (int[] A, int x) {
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

	/*@ 
	  @ requires (FM.FeatureModel.base) && (FM.FeatureModel.base || !FM.FeatureModel.cons) && (FM.FeatureModel.base || !FM.FeatureModel.snoc) && (FM.FeatureModel.base || !FM.FeatureModel.stack) && (FM.FeatureModel.base || !FM.FeatureModel.sorted);
	  @ requires FM.FeatureModel.stack || FM.FeatureModel.sorted;
	  @ requires FM.FeatureModel.stack ==> (A.length > 0);
	  @ requires FM.FeatureModel.sorted ==> ((\forall int i; 0 <= i < A.length; (\forall int j; i < j < A.length; A[i] <= A[j])));
	  @ ensures !FM.FeatureModel.sorted ==> (FM.FeatureModel.stack ==> ((\forall int i; 0 <= i < A.length; A[i] != x || A[i] == -1)));
	  @ ensures FM.FeatureModel.sorted ==> ((\forall int i; 0 <= i < A.length - 1; A[i] <= A[i + 1]));
	  @*/
	void remove(int[] A, int x) {
		if (!FM.FeatureModel.sorted) {
			remove__wrappee__Base(A, x);
			return;
		}


        remove__wrappee__Base(A, x);
        sort(A);
    }

	/*@ 
	  @ requires (FM.FeatureModel.base) && (FM.FeatureModel.base || !FM.FeatureModel.cons) && (FM.FeatureModel.base || !FM.FeatureModel.snoc) && (FM.FeatureModel.base || !FM.FeatureModel.stack) && (FM.FeatureModel.base || !FM.FeatureModel.sorted);
	  @	requires FM.FeatureModel.base;
	  @ requires A.length > 0;
	  @ ensures \result <==> (\exists int i; 0 <= i < A.length; A[i] == x);
	  @ assignable \nothing;
	  @*/
	 private boolean  search__wrappee__Base  (int[] A, int x) {
		int i = A.length - 1;
		/*@ loop_invariant -1 <= i < A.length && !(\exists int j; i + 1 <= j < A.length; A[j] == x);
		  @ decreases i + 1;
		  @ assignable i; */
		while (i >= 0 && A[i] != x) i--;
		return i != -1;
	}

	/*@ 
	  @ requires (FM.FeatureModel.base) && (FM.FeatureModel.base || !FM.FeatureModel.cons) && (FM.FeatureModel.base || !FM.FeatureModel.snoc) && (FM.FeatureModel.base || !FM.FeatureModel.stack) && (FM.FeatureModel.base || !FM.FeatureModel.sorted);
	  @ requires FM.FeatureModel.stack || FM.FeatureModel.sorted;
	  @ requires FM.FeatureModel.stack ==> (A.length > 0);
	  @ requires FM.FeatureModel.sorted ==> ((\forall int i; 0 <= i < A.length; (\forall int j; i < j < A.length; A[i] <= A[j])));
	  @ ensures FM.FeatureModel.stack ==> (\result <==> (\exists int i; 0 <= i < A.length; A[i] == x));
	  @*/
	boolean search(int[] A, int x) {
		if (!FM.FeatureModel.sorted)
			return search__wrappee__Base(A, x);
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

	/*@ 
	  @ requires (FM.FeatureModel.base) && (FM.FeatureModel.base || !FM.FeatureModel.cons) && (FM.FeatureModel.base || !FM.FeatureModel.snoc) && (FM.FeatureModel.base || !FM.FeatureModel.stack) && (FM.FeatureModel.base || !FM.FeatureModel.sorted);
	  @ requires FM.FeatureModel.stack;
	  @ requires A.length > 0;
 ensures \result == A[A.length - 1];
 assignable \nothing;
	  @*/
	public int top(int[] A) {
        return A[A.length - 1];
    }

	/*@ 
	  @ requires (FM.FeatureModel.base) && (FM.FeatureModel.base || !FM.FeatureModel.cons) && (FM.FeatureModel.base || !FM.FeatureModel.snoc) && (FM.FeatureModel.base || !FM.FeatureModel.stack) && (FM.FeatureModel.base || !FM.FeatureModel.sorted);
	  @ requires FM.FeatureModel.stack;
	  @ requires A.length > 0;
 ensures (\forall int i; 0 <= i < \result.length; (\exists int j; 0 <= j < A.length; A[j] == \result[i]));
 assignable \nothing;
	  @*/
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

	/*@ 
	  @ requires (FM.FeatureModel.base) && (FM.FeatureModel.base || !FM.FeatureModel.cons) && (FM.FeatureModel.base || !FM.FeatureModel.snoc) && (FM.FeatureModel.base || !FM.FeatureModel.stack) && (FM.FeatureModel.base || !FM.FeatureModel.sorted);
	  @ requires FM.FeatureModel.stack;
	  @ requires true;
 ensures \result <==> (A.length == 0);
 assignable \nothing;
	  @*/
	public boolean isEmpty(int[] A) {
        return A.length == 0;
    }

	/*@ 
	  @ requires (FM.FeatureModel.base) && (FM.FeatureModel.base || !FM.FeatureModel.cons) && (FM.FeatureModel.base || !FM.FeatureModel.snoc) && (FM.FeatureModel.base || !FM.FeatureModel.stack) && (FM.FeatureModel.base || !FM.FeatureModel.sorted);
	  @ requires FM.FeatureModel.sorted;
	  @ requires A.length > 0;
 ensures (\forall int i; 0 <= i < A.length - 1; A[i] <= A[i + 1]) && (\forall int i; 0 <= i < \old(A).length; (\exists int j; 0 <= j < A.length; A[j] == \old(A)[i])) && (\forall int i; 0 <= i < A.length; (\exists int j; 0 <= j < \old(A).length; A[i] == \old(A)[j]));
 assignable A[*];
	  @*/
	void sort(int[] A) {
        
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

	/*@ 
	  @ requires (FM.FeatureModel.base) && (FM.FeatureModel.base || !FM.FeatureModel.cons) && (FM.FeatureModel.base || !FM.FeatureModel.snoc) && (FM.FeatureModel.base || !FM.FeatureModel.stack) && (FM.FeatureModel.base || !FM.FeatureModel.sorted);
	  @ requires FM.FeatureModel.sorted;
	  @ requires A.length > 0 && 0 <= start < A.length;
 ensures start <= \result && \result < A.length && (\forall int i; start <= i < A.length; A[\result] <= A[i]);
 assignable \nothing;
	  @*/
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
