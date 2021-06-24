/* simple typedef */
typedef int MySpecialInt;

/* simple structure */

struct human
{
	char *name;
	int age;
	int height;
	int weight;
};

/*
# "typedef int foo;"           -> YES, "foo" is the name of a type
# "unsigned long;"             -> YES, "unsigned long" is the name of a type
# struct foo {int A; int B;};  -> YES, "struct foo" is the name of a type
*/

/* struct with anonymous enum inside */
struct human2
{
    char *name;
    enum {UNSPEC=0, MALE=1, FEMALE=2} gender;
    struct {int height; int weight;} dimensions;
}

/* anonymous stuff */
//enum {A=1,B=2} foo;"         -> NO, anonymous enum applied to variable foo
//struct {int A; int B;} foo;  -> NO, anonymous struct applied to variable foo

