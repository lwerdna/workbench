// from https://github.com/diffblue/cbmc/issues/5099

#include <assert.h>
#include <stdlib.h>

int f(char *a, char *b)
{
  return atoi(a)==123 && atoi(b)==456;
}

#define LENGTH 10

int main (int argc, char **argv) {
  char buffer1[LENGTH];   // Uninitialised things are non-det
  char buffer2[LENGTH];

  buffer1[LENGTH - 1] = '\0'; // Let's work with null terminated strings
  buffer2[LENGTH - 1] = '\0'; // Let's work with null terminated strings

  int res = f(buffer1, buffer2);

  assert(!res);  // Will generate case when res is true

  return 0;
}
