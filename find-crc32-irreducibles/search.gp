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

/* OBSOLETE! use built-in function polisirreducible()
	https://pari.math.u-bordeaux.fr/dochtml/html/Polynomials_and_power_series.html */
irreducible(p) =
{
	local(factors, rows, cols, first_degree=1);

	factors = factor(p * Mod(1,2));

	rows = matsize(factors)[1];
	cols = matsize(factors)[2];

	if(rows > 0,
		first_factor_degree = factors[1,2];
	);

	rows == 0 || (rows == 1 && first_factor_degree == 1);
}

search(start, end) =
{
	local(i, start_=start, poly, n_yes=0, n_total=end-start+1);

	/* start at odd value (so x^0 coefficient is 1) */
	if(start_ % 2 == 0,
		start_ += 1;
	);

	/* for(i=0, 4294967295, */
	forstep(i=start_, end, 2,
		poly = (Pol(binary(i)) + x^32) * Mod(1,2);

		if(polisirreducible(poly),
			/* print(poly); */
			n_yes += 1;
		);

		if((i-1) % 100000 == 0,
			printf("range [0x%08X, 0x%08X] at 0x%08X (%.02f%%)\n", start, end, i, 100.0*(i-start)/(end-start));
		);
	);

	printf("range [0x%08X, 0x%08X] finished, result: %d/%d == %.02f%%\n", start, end, n_yes, n_total, 100.0*n_yes / n_total);
}

start = hex2dec(getenv("CRC_START"));
end = hex2dec(getenv("CRC_END"));
printf("searching [0x%08X, 0x%08X]\n", start, end);
search(start, end);
quit;
