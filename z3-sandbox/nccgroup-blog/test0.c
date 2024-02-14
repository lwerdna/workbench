/* DecodePacketNumber() translated to C
 */
#include <stdio.h>
#include <stdint.h>

uint64_t DecodePacketNumber(uint64_t largest_pn, uint64_t truncated_pn, uint64_t pn_nbits)
{
	uint64_t expected_pn = largest_pn + 1;
	uint64_t pn_win = (uint64_t) 1 << pn_nbits;
	uint64_t pn_hwin = pn_win / 2;
	uint64_t pn_mask = pn_win - 1;

	// The incoming packet number should be greater than
	// expected_pn - pn_hwin and less than or equal to
	// expected_pn + pn_hwin
	//
	// This means we can't just strip the trailing bits from
	// expected_pn and add the truncated_pn because that might
	// yield a value outside the window.
	//
	// The following code calculates a candidate value and
	// makes sure it's within the packet number window.
	uint64_t candidate_pn = (expected_pn & (~pn_mask)) | truncated_pn;
	if (candidate_pn <= expected_pn - pn_hwin)
		return candidate_pn + pn_win;

	// Note the extra check for underflow when candidate_pn
	// is near zero.
	if (candidate_pn > expected_pn + pn_hwin && candidate_pn > pn_win)
		return candidate_pn - pn_win;

	return candidate_pn;
}

int main(int ac, char **av)
{
	/* For example, if the highest successfully authenticated packet had a packet number of 0xa82f30ea,
	   then a packet containing a 16-bit value of 0x9b32 will be decoded as 0xa82f9b32 */
	uint64_t result = DecodePacketNumber(0xa82f30ea, 0x9b32, 16);
	printf("result = 0x%016llx\n", result);
	if(result == 0xa82f9b32)
		printf("PASS\n");
	else
		printf("FAIL\n");

	result = DecodePacketNumber(0x3fffffffffffffff, 0x10018001, 32);
	printf("result = 0x%016llx\n", result);
	if(result >= 0x3fffffffffffffff)
		printf("PASS\n");
	else
		printf("FAIL\n");	

	result = DecodePacketNumber(0x3fffffffffffffff, 0x8000, 16);
	printf("result = 0x%016llx\n", result);
	if(result >= 0x3fffffffffffffff)
		printf("PASS\n");
	else
		printf("FAIL\n");

	// here!
	result = DecodePacketNumber(0x3fffffffffff8028, 0x7fff2052, 32);
	printf("result = 0x%016llx\n", result);
	if(result >= 0x3fffffffffffffff)
		printf("PASS\n");
	else
		printf("FAIL\n");

	result = DecodePacketNumber(0x3fffffffffffc028, 0x2052, 16);
	printf("result = 0x%016llx\n", result);
	if(result >= 0x3fffffffffffffff)
		printf("PASS\n");
	else
		printf("FAIL\n");
}
