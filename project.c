#include <stdio.h>

/*@
  predicate 
    Sorted{L}(int *arr, integer start, integer end) =
      \forall integer i, j; start <= i <= j < end ==> arr[i] <= arr[j];
  
  predicate 
    Sorted{L}(int *arr, integer length) =
      Sorted{L}(arr, 0, length - 1);
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
  assigns t[low..high];
*/
// ensures \forall integer n; n <= \result ==> t[n] <= high;
int partition(int *t, int low, int high) {
  int pivot = t[high];    // pivot
  int i = low;  // Index of smaller element
  
  /*@
    loop invariant low <= j <= high;
    loop invariant low <= i <= high;
    loop invariant i <= j;
    loop assigns j, i, t[low..high];
    loop variant high-j;
  */
  for (int j = low; j < high; j++) {
    // If current element is smaller than or
    // equal to pivot
    if (t[j] <= pivot) {
      /*@
        assigns t[i], t[j];
      */
      swap(&t[i], &t[j]);
      i++;    // increment index of smaller element
    }
  }
  swap(&t[i], &t[high]);
  return i;
}
 
/* 
  The main function that implements QuickSort
  arr[] --> Array to be sorted,
  low   --> Starting index,
  high  --> Ending index 
*/


void affiche(int *t, int l) { 
  int i;
  printf("[ ");
  for (i=0; i<l-1; i++) {
    printf("%d, ",t[i]); 
  }
  printf("%d ]\n", t[i]); 
}

/*@ 
  requires  \valid(t + (low..high));
  ensures   Sorted(t, low, high);
*/
void quickSort(int *t, int low, int high) {
  if (low < high) {
    /* pi is partitioning index, arr[p] is now
      at right place */
    int pi = partition(t, low, high);
    // printf("from %d to %d, pi: %d\n", low, high, pi);
    // affiche(t, 10);
    // Separately sort elements before
    // partition and after partition
    
    quickSort(t, low, pi - 1);
    quickSort(t, pi + 1, high);
  }
}

/*@ 
  requires \valid(t+(0..l-1));
  ensures Sorted(t, l);
*/
void sort(int *t, int l) {
  quickSort(t, 0, l - 1);
}


int main() {
  int t[10] = {4,3,8,8,1,0,7,2,9,1}; 
  affiche(t,10);
  sort(t,10);
  affiche(t,10);
  return 0;
}
