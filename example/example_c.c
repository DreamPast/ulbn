#include "ulbn.h"
#include <stdio.h>

int main(void) {
  const ulbn_alloc_t* alloc = ulbn_default_alloc(); /* get default allocator */
  ulbi_t ro, ao, bo;
  int err;
  
  /* initialize library */
  ulbn_startup(); 
  /* first, we must initialize them */
  ulbi_init(&ro);
  ulbi_init(&ao);
  ulbi_init(&bo);


  ulbi_set_slimb(&ao, 99);              /* set ao = 99, `ulbi_set_slimb` doesn't make errors */
  ulbi_set_slimb(&bo, 99);              /* set bo = 99, `ulbi_set_slimb` doesn't make errors */
  err = ulbi_add(alloc, &ro, &ao, &bo); /* ro = ao + bo */
  if(err) {
    (void)fprintf(stderr, "error: %d\n", err);
    return 1;
  }
  ulbi_print(alloc, stdout, &ro, 10); /* print ro */
  (void)putchar('\n');


  err = ulbi_add_slimb(alloc, &ro, &ao, 99); /* some functions have a simpler version */
  if(err) {
    (void)fprintf(stderr, "error: %d\n", err);
    return 1;
  }
  ulbi_print(alloc, stdout, &ro, 10); /* print ro */
  (void)putchar('\n');


  err = ulbi_pow(alloc, &ro, &ao, &bo); /* we can try larger number */
  if(err) {
    (void)fprintf(stderr, "error: %d\n", err);
    return 1;
  }
  ulbi_print(alloc, stdout, &ro, 10); /* print ro */
  (void)putchar('\n');


  /* finally, don't forget to deinitialize them */
  ulbi_deinit(alloc, &ro);
  ulbi_deinit(alloc, &ao);
  ulbi_deinit(alloc, &bo);

  return 0;
}

#include "ulbn.c" /* we can include source code directly */
