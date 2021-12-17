,               // cell0 = input()
>,              // cell1 = input()
>,              // cell2 = input()
>+              // cell3 = first else flag
>+              // cell4 = second else flag
>+              // cell5 = third else flag

<<<<<           // subtract 2 from cell0
--

[               // if(cell0 != 0)
	// at c0: input0
    >>>-        // clear else flag

    // print "FAIL"
    >>>
    -[------->+<]>---.-----.++++++++.+++.>++++++++++.
	<<<<<
]>>>
[
	// at c3: first else flag
	-

	<<----      	// subtract 4 from cell1

	[				// if(cell1 != 0)
	    >>>-    	// clear second else flag at c4
			    	// print "FAIL"
	    >>
	    -[------->+<]>---.-----.++++++++.+++.>++++++++++.
		<<<<<<<<	// return to c1
	]

	>>>
	[				// at c4: second else flag
		-
		<<------    // subtract 6 from cell2

		[           // at c2: input2
			>>>-    // clear third else flag at c5

			        // print "FAIL"
		    >>
		    -[------->+<]>---.-----.++++++++.+++.>++++++++++.
			<<<<<<<<	// return to c1
		]

		>>>
		[			// at c5: third else flag
			-

	    	// print "PASS"
		    >
		    -[--->+<]>-----.[->++++<]>+.>-[--->+<]>--..>++++++++++.
		    <<<<<<    // return to c5
		]

		<        	// return to c4: second else flag
	]
]

