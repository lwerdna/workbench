// can CBMC factor 15? yes
//
// $ cbmc --trace --function f ./factor.c

#include <assert.h>

int f(int a, int b)
{
	int pass = a>1 && b>1 && a*b==15;
	assert(!pass);
}
