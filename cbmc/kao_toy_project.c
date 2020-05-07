// kao's toy project crackme
//
// $ cbmc --trace --function check ./kao_toy_project.c
//

#include <stdio.h>
#include <stdint.h>
#include <assert.h>

#define ROL(x) (((x)>>31) | ((x)<<1)) & 0xFFFFFFFF
#define SUB(a,b) ((a)-(b)) & 0xff

void check()
{
	// actual values
	//uint32_t ebx = 0xD0124502;
	//uint32_t edx = 0xE7EC6385;

	// floating values for cbmc to find
	uint32_t ebx;
	uint32_t edx;

	uint8_t plain[32] = {
			0xB7, 0x68, 0x83, 0x6E, 0x97, 0x20, 0xD1, 0xF2,
			0xAF, 0x9E, 0x35, 0xCF, 0x1C, 0xCA, 0x97, 0x99,
			0xAB, 0x05, 0xCC, 0x9A, 0xCB, 0x46, 0xBF, 0x74,
			0x49, 0x38, 0x13, 0x57, 0xA4, 0xA3, 0xD5, 0x76
	};

	uint8_t cipher[32];

	for(int i=0; i<32; i++) {
		uint8_t cbyte;
		cbyte = SUB(plain[i], ebx & 0xFF);
		cbyte = cbyte ^ (edx & 0xFF);
		printf("%02X ", cbyte);
		cipher[i] = cbyte;

		edx = ROL(edx);
		ebx = ROL(ebx);
	}

	assert(!(cipher[0]==0x30 && cipher[1]==0x68 && cipher[2]==0x6f && cipher[3]==0x77 && cipher[4]==0x34 && cipher[5]==0x7a && cipher[6]==0x64 && cipher[7]==0x79 && cipher[8]==0x38 && cipher[9]==0x31 && cipher[10]==0x6a && cipher[11]==0x70 && cipher[12]==0x65 && cipher[13]==0x35 && cipher[14]==0x68 && cipher[15]==0x66 && cipher[16]==0x75 && cipher[17]==0x39 && cipher[18]==0x32 && cipher[19]==0x6b && cipher[20]==0x61 && cipher[21]==0x72 && cipher[22]==0x36 && cipher[23]==0x63 && cipher[24]==0x67 && cipher[25]==0x69 && cipher[26]==0x71 && cipher[27]==0x33 && cipher[28]==0x6c && cipher[29]==0x73 && cipher[30]==0x74 && cipher[31]==0x37));

	printf("PASS\n");
}

int main()
{
	check();
	return 0;
}
