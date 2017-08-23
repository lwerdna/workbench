#include <stdio.h>

/* if /export or __declspec(dllexport) then a .lib is produced */
__declspec(dllexport) int foo(void)
{
    return 31337;
}
