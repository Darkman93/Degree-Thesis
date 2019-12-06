package sort;

public class BubbleSort {
	
	/*@ public normal_behavior
	  @ requires b.length > 0 && 0 <= x < b.length && 0 <= y < b.length;
	  @ assignable b[x], b[y];
	  @ ensures b[x] == \old(b[y]) && (b[y] == \old(b[x]));
	  @*/
	void swap(int[] b, int x, int y) {
		int tmp = b[x];
		b[x] = b[y];
		b[y] = tmp;
	}

	/*@ public normal_behavior
	  @ requires a.length > 0;
	  @ ensures (\forall int x; 0 <= x && x < a.length; 
	  @ 			(\forall int y; 0 <= y && y < a.length;
	  @ 				x < y ==> a[x] <= a[y]));
	  @ diverges true;
	  @*/
	void sort(int[] a) {

		/*@ loop_invariant 0 <= n && n <= a.length;
		  @ loop_invariant (\forall int i, k; n <= i && i < a.length && 0 <= k && k < i; a[k] <= a[i]);
		  @ assignable a[*];
		  @ decreases a.length - n;
        @*/
		for (int n = a.length; 0 <= --n;) {

			/*@ loop_invariant  0 <= j && j <= n;
        	  @ loop_invariant (\forall int i, k; n < i && i < a.length && 0 <= k && k < i; a[k] <= a[i]);
        	  @ loop_invariant (\forall int k; 0 <= k && k < j; a[k] <= a[j]);
			  @ assignable a[*];
			  @ decreases n - j;
			  @*/
			for (int j = 0; j < n; j++) {
				if (a[j+1] < a[j]) {
					int tmp = a[j];
					a[j] = a[j+1];
					a[j+1] = tmp;
				}
			}
		}
	}
}
