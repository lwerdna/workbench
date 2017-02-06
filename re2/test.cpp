#include <stddef.h>
#include <memory>
#include <string>
#include <vector>

#include <stdio.h>
#include <stdlib.h>

#include <re2/re2.h>

int main(int ac, char **av)
{
// Example: successful match
	printf("%d", RE2::FullMatch("hello", "h.*o"));
//
// Example: unsuccessful match (requires full match):
	printf("%d", RE2::FullMatch("hello", "JFW(*EFJ(#FJIF(QWFYYFY&&&&(**e"));

	return 0;
}
