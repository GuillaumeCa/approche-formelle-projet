#include <stdio.h>

/*@
  predicate sorted{L}(int *arr, int length) =
    \forall integer i, j; 0 <= i <= j < length ==> arr[i] <= arr[j];
*/

/*@ 
  requires \valid(a) && \valid(b);
  ensures A: *a == \old(*b);
  ensures B: *b == \old(*a);
  assigns *a, *b;
*/
void swap(int *a, int *b) {
    int t = *a;
    *a = *b;
    *b = t;
}
 
/* This function takes last element as pivot, places
   the pivot element at its correct position in sorted
    array, and places all smaller (smaller than pivot)
   to left of pivot and all greater elements to right
   of pivot */
   
/*@ 
  requires \valid(t+(low..high));
  ensures \forall integer n; n <= \result ==> t[n] <= high;
*/
int partition(int *t, int low, int high) {
  int pivot = t[high];    // pivot
  int i = low;  // Index of smaller element
  
  /*@
    loop invariant low <= j < high && low <= i < high - low;
    loop assigns j, i;
    loop variant j - i;
  */
  for (int j = low; j < high; j++) {
    // If current element is smaller than or
    // equal to pivot
    if (t[j] <= pivot) {
      swap(&t[i], &t[j]);
      i++;    // increment index of smaller element
    }
  }
  swap(&t[i], &t[high]);
  return i;
}
 
/* The main function that implements QuickSort
 arr[] --> Array to be sorted,
  low  --> Starting index,
  high  --> Ending index */

/*@ 
  requires \valid(t+(low..high));
  ensures \forall integer i, j; low <= i <= j < high ==> t[i] <= t[j];
*/
void quickSort(int *t, int low, int high) {
  if (low < high) {
    /* pi is partitioning index, arr[p] is now
      at right place */
    int pi = partition(t, low, high);

    // Separately sort elements before
    // partition and after partition
    
    quickSort(t, low, pi - 1);
    
    quickSort(t, pi + 1, high);
  }
}

/*@ 
  requires \valid(t+(0..l-1));
  ensures sorted(t, l);
*/
void sort(int *t, int l) {
  /*@ 
    requires \valid(t+(0..l-1));
    ensures \forall integer i, j; 0 <= i <= j < l-1 ==> t[i] <= t[j];
  */
  quickSort(t, 0, l - 1);
}

void affiche(int *t, int l) { 
  int i;
  printf("[ ");
  for (i=0; i<l-1; i++) {
    printf("%d, ",t[i]); 
  }
  printf("]\n"); 
}


int main() {
  int t[10] = {4,3,8,8,1,0,7,2,9,1}; 
  affiche(t,10);
  sort(t,10);
  affiche(t,10);
  return 0;
}
