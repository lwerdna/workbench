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

bits2hex(V)=
{
    local(W, nibl, result, lookup);

    lookup=["0", "1", "2", "3", "4", "5", "6", "7", "8", "9", "A", "B", "C", "D", "E", "F"];

    result = "";

    W = V;
    if(#W % 4,
        W = concat(vector(4 - (#W % 4)),W);
    );

    forstep(i=1,#W,4,
        nibl = 8*W[i] + 4*W[i+1] + 2*W[i+2] + W[i+3];
        result = concat(result, lookup[nibl+1]);
    );

    result;
}

dec2hex(n) =
{
    bits2hex(binary(n));
}

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
	local(i, poly, n_yes=0, n_no=0);

	/* for(i=0, 4294967295, */
	for(i=start, end,
		poly = Pol(binary(i)) + x^32;

		if(irreducible(poly),
			/* print(poly); */
			n_yes += 1;
		,
			n_no += 1;
		);

		/*
		if(i % 1000000 == 0,
			print("i: ", i);
		);
		*/
	);

	print("range [0x", dec2hex(start), ", 0x", dec2hex(end) "] has ", n_yes, " yes, " n_no, " no, ratio: ", 1.0*n_yes / (n_yes + n_no));
}

start = hex2dec(getenv("CRC_START"));
end = hex2dec(getenv("CRC_END"));
print("searching [0x", dec2hex(start), ", 0x", dec2hex(end) "] == [", start, ", ", end "]");
search(start, end);
quit;
