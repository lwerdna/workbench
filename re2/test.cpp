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
	std::string m0, m1, m2;
	printf("%d\n", RE2::FullMatch("hellerooskio", "(h([ler]+)(.*)o)", &m0, &m1, &m2));
	printf("m0: %s\n", m0.c_str());
	printf("m1: %s\n", m1.c_str());
	printf("m2: %s\n", m2.c_str());

	printf("%d\n", RE2::PartialMatch("hellerooskio", "(e*)", &m0));
	printf("m0: %s\n", m0.c_str());
//
// Example: unsuccessful match (requires full match):
	//printf("%d", RE2::FullMatch("hello", "JFW(*EFJ(#FJIF(QWFYYFY&&&&(**e"));

	return 0;
}
