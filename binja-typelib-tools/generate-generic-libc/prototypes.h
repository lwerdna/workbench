typedef unsigned int size_t;

// string.h
void *memcpy(void *dest, const void *src, size_t n);
void *memmove(void *dest, const void *src, size_t n);
void *memchr(const void *s, int c, size_t n);
int memcmp(const void *s1, const void *s2, size_t n);
void *memset(void *str, int c, size_t n);
char *strcat(char *dest, const char *src);
char *strncat(char *dest, const char *src, size_t n);
char *strchr(const char *str, int c);
char *strrchr(const char *str, int c);
int strcmp(const char *str1, const char *str2);
int strncmp(const char *str1, const char *str2, size_t n);
int strcoll(const char *str1, const char *str2);
char *strcpy(char *dest, const char *src);
char *strncpy(char *dest, const char *src, size_t n);
char *strerror(int err);
size_t strlen(const char *str);
size_t strspn(const char *str, const char *accept);
size_t strcspn(const char *str, const char *reject);
char *strpbrk(const char *str, const char *accept);
char *strstr(const char *haystack, const char *needle);
char *strtok(char *str, const char * delim);

// stdlib.h
//double atof(const char *str);
//int atoi(const char *str);
//long int atol(const char *str);
//double strtod(const char *str, char **endptr);
//long int strtol(const char *str, char **endptr, int base);
//unsigned long int strtoul(const char *str, char **endptr, int base);
//void *calloc(size_t nitems, size_t size);
//void free(void *ptr;
//void *malloc(size_t size);
//void *realloc(void *ptr, size_t size);
//void abort(void);
//int atexit(void (*func)(void));
//void exit(int status);
//char *getenv(const char *name);
//int system(const char *string);
//void *bsearch(const void *key, const void *base, size_t nitems, size_t size, int (*compar)(const void *, const void *));
//void qsort(void *base, size_t nitems, size_t size, int (*compar)(const void *, const void*));
//int abs(int x);
//div_t div(int numer, int denom);
//long int labs(long int x);
//ldiv_t ldiv(long int numer, long int denom);
//int rand(void);
//void srand(unsigned int seed);
//int mblen(const char *str, size_t n);
//size_t mbstowcs(schar_t *pwcs, const char *str, size_t n);
//int mbtowc(whcar_t *pwc, const char *str, size_t n);
//size_t wcstombs(char *str, const wchar_t *pwcs, size_t n);
//int wctomb(char *str, wchar_t wchar);

