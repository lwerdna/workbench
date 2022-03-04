typedef void (*PFUNC_XTEA)(uint32_t *, uint32_t const *, uint32_t *);

struct test_case
{
	uint32_t key[4];
	uint32_t ptext[2];
	uint32_t ctext[2];
};

void test_suite(PFUNC_XTEA encipher);
