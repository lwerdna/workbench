/* take as input the normal form representation that omits the x^32 term and print whether its irreducible or not

	eg: 0x04C11DB7 is in normal form because it has x^0 term in LSB
		0xEDB88320 is in reversed form because it has x^0 term in MSB

        both represent the polynomial:
	    x^32 + x^26 + x^23 + x^22 + x^16 + x^12 + x^11 + x^10 + x^8 + x^7 + x^5 + x^4 + x^2 + x + 1

	QUICK START:
	$ gp ./is-irreducible.gp
	? test("04C11DB7")
*/

hex2dec(s) =
{
    local(v=Vec(s),
    	a=10, b=11, c=12, d=13, e=14, f=15,
        A=10, B=11, C=12, D=13, E=14, F=15,
        h
    );

    for(i=1, #v,
        h = (h<<4) + eval(v[i]);
    );
    
    return(h);
}

test(crc32_iso_hdlc_poly_str) =
{
	local(i, start_=start, poly, n_yes=0, n_total=end-start+1);

	poly = x^32 + Pol(binary(hex2dec(crc32_iso_hdlc_poly_str)));

	print(poly);

	if(polisirreducible(poly * Mod(1,2)),
		print("YES irreducible (\"prime\")");
		True;
	,
		print("NO reducible (\"composite\")");
		False;
	);
}

tests() =
{
	print("CRC-32, irreducible");
	print(test("04c11db7") == True);

	print("CRC-32C (Castagnoli), CRC32 x86 instruction, reducible");
	print(test("1EDC6F41") == False);

	print("CRC-32K (Koopman {1,3,28}), reducible");
	print(test("741B8CD7") == False);

	print("CRC-32K2 (Koopman {1,1,30}), reducible");
	print(test("32583499") == False);

	print("CRC-32Q, reducible");
	print(test("814141AB") == False);
}
