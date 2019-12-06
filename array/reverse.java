package array;

public class reverse {
	
	/*@ requires 0 <= n && n <= a.length && n <= b.length;
	  @ ensures (\forall int j; 0 <= j && j < n; b[n-j-1] == a[j]);
	  @ 
	  @*/
	void reverse_array(int[] a, int n, int[] b) {
		/*@ loop_invariant 0 <= i && i <= n &&
		  @ (\forall int j; 0 <= j && j < i; b[n-j-1] == a[j]);
		  @ modifies b[*];
		  @ decreases n - i;
		  @ 
		  @*/
		for(int i = 0; i != n; i++) {
			b[n-i-1] = a[i];
		}
	}
	
	 /*@ public normal_behavior
    @   requires (\forall int x; (\forall int y; 0 <= x && x < y && y < a.length; a[x] <= a[y]));
    @   ensures ((\exists int x; 0 <= x && x < a.length; a[x] == v) ? a[\result] == v : \result == -1);
    @*/
  static /*@pure@*/ int search(int[] a, int v) {
      int l = 0;
      int r = a.length - 1;

      if(a.length == 0) return -1;
      if(a.length == 1) return a[0] == v ? 0 : -1;

      /*@ loop_invariant 0 <= l && l < r && r < a.length
        @                && (\forall int x; 0 <= x && x < l; a[x] < v)
        @                && (\forall int x; r < x && x < a.length; v < a[x]);
        @ assignable \nothing;
        @ decreases r - l;
        @*/
      while(r > l + 1) {
          int mid = l + (r - l) / 2;
          if(a[mid] == v) {
             return mid;
          } else if(a[mid] > v) {
             r = mid;
          } else {
             l = mid;
          }
      }

      if(a[l] == v) return l;
      if(a[r] == v) return r;
      return -1;
  }
}
