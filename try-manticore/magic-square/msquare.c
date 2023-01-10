/*
 a b c
 d e f
 g h i
 */
//int magic_square(int a, int b, int c, int d, int e, int f, int g, int h, int i)
int magic_square(char *inputs)
{
	char a = inputs[0];
	char b = inputs[1];
	char c = inputs[2];
	char d = inputs[3];
	char e = inputs[4];
	char f = inputs[5];
	char g = inputs[6];
	char h = inputs[7];
	char i = inputs[8];

	/* valid ranges */
	if(a < 0 || a > 9) return -1;
	if(b < 0 || b > 9) return -1;
	if(c < 0 || c > 9) return -1;
	if(d < 0 || d > 9) return -1;
	if(e < 0 || e > 9) return -1;
	if(f < 0 || f > 9) return -1;
	if(g < 0 || g > 9) return -1;
	if(h < 0 || h > 9) return -1;
	if(i < 0 || i > 9) return -1;

	/* they must be unique */
	if(a == b || a == c || a == d || a == e || a == f || a == g || a == h || a == i) return -1;
	if(b == c || b == d || b == e || b == f || b == g || b == h || b == i) return -1;
	if(c == d || c == e || c == f || c == g || c == h || c == i) return -1;
	if(d == e || d == f || d == g || d == h || d == i) return -1;
	if(e == f || e == g || e == h || e == i) return -1;
	if(f == g || f == h || f == i) return -1;
	if(g == h || g == i) return -1;
	if(h == i) return -1;

	/* rows */
	if(a+b+c != 15) return -1;
	if(d+e+f != 15) return -1;
	if(g+h+i != 15) return -1;

	/* columns */
	if(a+d+g != 15) return -1;
	if(b+e+h != 15) return -1;
	if(c+f+i != 15) return -1;

	/* diagonals */
	if(a+e+i != 15) return -1;
	if(c+e+g != 15) return -1;

	/* success */
	return 0;
}

