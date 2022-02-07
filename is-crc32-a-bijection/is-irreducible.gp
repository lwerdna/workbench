/* take as input the reversed representation that omits the x^32 term and print whether its irreducible or not

	eg: 0xEDB88320 is in reversed form because it has x^0 term in MSB
	    0x04C11DB7 is in normal form because it has x^0 term in LSB

        both represent the polynomial:
	    x^32 + x^26 + x^23 + x^22 + x^16 + x^12 + x^11 + x^10 + x^8 + x^7 + x^5 + x^4 + x^2 + x + 1
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
		print("NOT reducible (\"prime\")")
	,
		print("reducible (\"composite\")")
	);
}

