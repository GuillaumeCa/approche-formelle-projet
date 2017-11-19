/*
external permut_ij : ptr -> ptr -> int -> int -> Prop : Quicksort ;
external permut : ptr -> ptr -> Prop : Quicksort ;
external high_bound : ptr -> int -> int -> int -> Prop : Quicksort ;
external low_bound : ptr -> int -> int -> int -> Prop : Quicksort ;
*/

#define SIZE 100
int T[SIZE];

/*@ requires (0 <= i < SIZE) && (0 <= j < SIZE);
    ensures T[i] == \old(T[j]) && T[j] == \old(T[i]);
    assigns T[i], T[j];
 */
void swap (int i, int j) {
  int v;
  v = T[i];
  T[i] = T[j];
  T[j] = v;
}

/*@
requires (0 <= l < i) && (i < SIZE)
     && (\forall int k; l+1 <= k <= i-1 ==> T[k] <= T[l]);
ensures i-1 <= \result <= i 
     && (\forall int k; l <= k <= \result ==> T[k] <= T[\result])
     && (\forall int res; res == \result ==> 
                          T[l] == \old(T[res]) && T[res] == \old(T[l]))
     && T[\result] <= T[i];
*/
int mv_pv (int l, int i) { 
  int res;
  if (T[i] < T[l]) { 
    swap(l, i);
    res =  i;
    }
  else { 
    swap(l, i - 1); 
    res = i - 1;  
    } 
  return res;
}
      

/*@
requires (0 <= l < r) && r < length(T);
ensures 
  (l <= result && result <= r) && (forall k:int. (k < l || k > r) => T[k] = T@0[k]);
*/
int partition (int l, int r)
{
  int pv, i, j, res;
  pv = T[l];
  i = l+1;
  j = r;

  while (i < j)
    /*@
      loop invariant (l+1 <= i <= r) && j <= r && i <= j+1;
      loop variant i-j;
    */
    {
       while (T[i] <= pv && i < j)
	 /*@
  	  loop invariant l+1 <= i <= r && i <= j+1;
      loop variant i;
	 */
         { i = i + 1; }

       while (T[j] >= pv && i < j) 
	 /*@
      loop invariant j <= r 
      && ~(T[i] <= pv && i < j) && i <= j+1;
      loop variant j;
	 */
	 { j = j - 1; }

       if (i < j) 
         {
      	   swap( i, j);
	   i = i + 1;
	   j = j - 1;
	 }
    } 

  res = mv_pv (l, i);

  return res;
}


/*@
  requires  0 <= l && r < length(T);
  ensures 
      (\forall integer: i,j; l <= i <= j <= r => T[i] <= T[j])  &&
      (\forall integer k; (k < l || k > r) => T[k] = T@0[k]);
*/

void quick_rec (int l, int r) 
{
   int p;
   if (l < r) 
     {
       p = partition(l, r);
       quick_rec(l, p-1);
       quick_rec(p+1, r);
     }
}