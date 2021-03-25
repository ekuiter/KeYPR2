public class IntList {
    /*@ requires \original;
      @ ensures \original;
      @ assignable \nothing; */
    int[] insert(int[] A, int x) {
        return original(A, x);
    }
}