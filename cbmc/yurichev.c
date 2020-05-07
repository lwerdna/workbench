// from https://yurichev.com/news/20200416_CRC64/
//
// $ cbmc --function check --trace ./yurichev.c

#include <assert.h>
#include <stdio.h>
#include <string.h>
#include <stdint.h>
#include <inttypes.h>

uint64_t CRC64(uint64_t crc, uint8_t *buf, size_t len)
{
        int k;

        crc = ~crc;
        while (len--)
        {
                crc ^= *buf++;
                for (k = 0; k < 8; k++)
                        crc = crc & 1UL ? (crc >> 1) ^ 0x42f0e1eba9ea3693UL : crc >> 1;
        }
        return crc;
}

//#define STR "lorem ipsum "
#define STRLEN 12
#define HASH 0x791b385d86c37ffc

void check()
{
	char buf[STRLEN+1];
	buf[STRLEN]=0;
	int string_correct=1;
	for (int i=0; i<STRLEN; i++)
	{
		uint8_t t=buf[i];
		int char_correct=(t==' ' || (t>='a' && t<='z'));
		if (!char_correct)
			string_correct=0;
	};
	if (string_correct)
	{
		assert (CRC64(0, buf, STRLEN)!=HASH);
	};
};

int main()
{
};
