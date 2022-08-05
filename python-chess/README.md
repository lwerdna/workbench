How fast is it to set up a pgn game reviewer using python-chess?

output:

```
1. e2e4 (stockfish recommended: 1. e2e4)
rnbqkbnr/pppppppp/8/8/4P3/8/PPPP1PPP/RNBQKBNR b KQkq - 0 1
2...e7e5 (stockfish recommended: 2...e7e5)
rnbqkbnr/pppp1ppp/8/4p3/4P3/8/PPPP1PPP/RNBQKBNR w KQkq - 0 2
3. g1f3 (stockfish recommended: 3. g1f3)
rnbqkbnr/pppp1ppp/8/4p3/4P3/5N2/PPPP1PPP/RNBQKB1R b KQkq - 1 2
4...b8c6 (stockfish recommended: 4...b8c6)
r1bqkbnr/pppp1ppp/2n5/4p3/4P3/5N2/PPPP1PPP/RNBQKB1R w KQkq - 2 3
5. b1c3 (stockfish recommended: 5. d2d4)
r1bqkbnr/pppp1ppp/2n5/4p3/4P3/2N2N2/PPPP1PPP/R1BQKB1R b KQkq - 3 3
6...f8c5 (stockfish recommended: 6...g8f6)
r1bqk1nr/pppp1ppp/2n5/2b1p3/4P3/2N2N2/PPPP1PPP/R1BQKB1R w KQkq - 4 4
7. f1c4 (stockfish recommended: 7. f3e5)
r1bqk1nr/pppp1ppp/2n5/2b1p3/2B1P3/2N2N2/PPPP1PPP/R1BQK2R b KQkq - 5 4
8...h7h6 (stockfish recommended: 8...g8f6)
r1bqk1nr/pppp1pp1/2n4p/2b1p3/2B1P3/2N2N2/PPPP1PPP/R1BQK2R w KQkq - 0 5
9. e1g1 (stockfish recommended: 9. c3a4)
r1bqk1nr/pppp1pp1/2n4p/2b1p3/2B1P3/2N2N2/PPPP1PPP/R1BQ1RK1 b kq - 1 5
10...g8f6 (stockfish recommended: 10...d7d6)
r1bqk2r/pppp1pp1/2n2n1p/2b1p3/2B1P3/2N2N2/PPPP1PPP/R1BQ1RK1 w kq - 2 6
11. d2d3 (stockfish recommended: 11. c3a4)
r1bqk2r/pppp1pp1/2n2n1p/2b1p3/2B1P3/2NP1N2/PPP2PPP/R1BQ1RK1 b kq - 0 6
12...d7d5 (stockfish recommended: 12...e8g8)
r1bqk2r/ppp2pp1/2n2n1p/2bpp3/2B1P3/2NP1N2/PPP2PPP/R1BQ1RK1 w kq - 0 7
13. e4d5 (stockfish recommended: 13. e4d5)
r1bqk2r/ppp2pp1/2n2n1p/2bPp3/2B5/2NP1N2/PPP2PPP/R1BQ1RK1 b kq - 0 7
14...c6e7 (stockfish recommended: 14...c6d4)
r1bqk2r/ppp1npp1/5n1p/2bPp3/2B5/2NP1N2/PPP2PPP/R1BQ1RK1 w kq - 1 8
15. f1e1 (stockfish recommended: 15. f3e5)
r1bqk2r/ppp1npp1/5n1p/2bPp3/2B5/2NP1N2/PPP2PPP/R1BQR1K1 b kq - 2 8
16...e8g8 (stockfish recommended: 16...e8g8)
r1bq1rk1/ppp1npp1/5n1p/2bPp3/2B5/2NP1N2/PPP2PPP/R1BQR1K1 w - - 3 9
17. f3e5 (stockfish recommended: 17. f3e5)
r1bq1rk1/ppp1npp1/5n1p/2bPN3/2B5/2NP4/PPP2PPP/R1BQR1K1 b - - 0 9
18...e7d5 (stockfish recommended: 18...f6d5)
r1bq1rk1/ppp2pp1/5n1p/2bnN3/2B5/2NP4/PPP2PPP/R1BQR1K1 w - - 0 10
19. d3d4 (stockfish recommended: 19. d3d4)
r1bq1rk1/ppp2pp1/5n1p/2bnN3/2BP4/2N5/PPP2PPP/R1BQR1K1 b - - 0 10
20...c5b6 (stockfish recommended: 20...c5b6)
r1bq1rk1/ppp2pp1/1b3n1p/3nN3/2BP4/2N5/PPP2PPP/R1BQR1K1 w - - 1 11
21. c3a4 (stockfish recommended: 21. c3d5)
r1bq1rk1/ppp2pp1/1b3n1p/3nN3/N1BP4/8/PPP2PPP/R1BQR1K1 b - - 2 11
22...c8e6 (stockfish recommended: 22...c7c6)
r2q1rk1/ppp2pp1/1b2bn1p/3nN3/N1BP4/8/PPP2PPP/R1BQR1K1 w - - 3 12
23. a4b6 (stockfish recommended: 23. c4b3)
r2q1rk1/ppp2pp1/1N2bn1p/3nN3/2BP4/8/PPP2PPP/R1BQR1K1 b - - 0 12
24...d5b6 (stockfish recommended: 24...a7b6)
r2q1rk1/ppp2pp1/1n2bn1p/4N3/2BP4/8/PPP2PPP/R1BQR1K1 w - - 0 13
25. c4e6 (stockfish recommended: 25. c4e6)
r2q1rk1/ppp2pp1/1n2Bn1p/4N3/3P4/8/PPP2PPP/R1BQR1K1 b - - 0 13
26...f7e6 (stockfish recommended: 26...f7e6)
r2q1rk1/ppp3p1/1n2pn1p/4N3/3P4/8/PPP2PPP/R1BQR1K1 w - - 0 14
27. e5g4 (stockfish recommended: 27. h2h3)
r2q1rk1/ppp3p1/1n2pn1p/8/3P2N1/8/PPP2PPP/R1BQR1K1 b - - 1 14
28...e6e5 (stockfish recommended: 28...d8d6)
r2q1rk1/ppp3p1/1n3n1p/4p3/3P2N1/8/PPP2PPP/R1BQR1K1 w - - 0 15
29. g4f6 (stockfish recommended: 29. g4e5)
r2q1rk1/ppp3p1/1n3N1p/4p3/3P4/8/PPP2PPP/R1BQR1K1 b - - 0 15
30...d8f6 (stockfish recommended: 30...d8f6)
r4rk1/ppp3p1/1n3q1p/4p3/3P4/8/PPP2PPP/R1BQR1K1 w - - 0 16
31. d4e5 (stockfish recommended: 31. c1e3)
r4rk1/ppp3p1/1n3q1p/4P3/8/8/PPP2PPP/R1BQR1K1 b - - 0 16
32...f6e6 (stockfish recommended: 32...f6f2)
r4rk1/ppp3p1/1n2q2p/4P3/8/8/PPP2PPP/R1BQR1K1 w - - 1 17
33. b2b3 (stockfish recommended: 33. d1e2)
r4rk1/ppp3p1/1n2q2p/4P3/8/1P6/P1P2PPP/R1BQR1K1 b - - 0 17
34...a8d8 (stockfish recommended: 34...b6d5)
3r1rk1/ppp3p1/1n2q2p/4P3/8/1P6/P1P2PPP/R1BQR1K1 w - - 1 18
35. d1h5 (stockfish recommended: 35. d1e2)
3r1rk1/ppp3p1/1n2q2p/4P2Q/8/1P6/P1P2PPP/R1B1R1K1 b - - 2 18
36...f8f5 (stockfish recommended: 36...f8f5)
3r2k1/ppp3p1/1n2q2p/4Pr1Q/8/1P6/P1P2PPP/R1B1R1K1 w - - 3 19
37. h5h4 (stockfish recommended: 37. h5g4)
3r2k1/ppp3p1/1n2q2p/4Pr2/7Q/1P6/P1P2PPP/R1B1R1K1 b - - 4 19
38...d8e8 (stockfish recommended: 38...d8d7)
4r1k1/ppp3p1/1n2q2p/4Pr2/7Q/1P6/P1P2PPP/R1B1R1K1 w - - 5 20
39. f2f4 (stockfish recommended: 39. h4g3)
4r1k1/ppp3p1/1n2q2p/4Pr2/5P1Q/1P6/P1P3PP/R1B1R1K1 b - - 0 20
40...g7g5 (stockfish recommended: 40...b6d5)
4r1k1/ppp5/1n2q2p/4Prp1/5P1Q/1P6/P1P3PP/R1B1R1K1 w - - 0 21
41. h4g3 (stockfish recommended: 41. f4g5)
4r1k1/ppp5/1n2q2p/4Prp1/5P2/1P4Q1/P1P3PP/R1B1R1K1 b - - 1 21
42...b6d5 (stockfish recommended: 42...b6d5)
4r1k1/ppp5/4q2p/3nPrp1/5P2/1P4Q1/P1P3PP/R1B1R1K1 w - - 2 22
43. f4g5 (stockfish recommended: 43. f4g5)
4r1k1/ppp5/4q2p/3nPrP1/8/1P4Q1/P1P3PP/R1B1R1K1 b - - 0 22
44...h6g5 (stockfish recommended: 44...h6h5)
4r1k1/ppp5/4q3/3nPrp1/8/1P4Q1/P1P3PP/R1B1R1K1 w - - 0 23
45. c1b2 (stockfish recommended: 45. c1g5)
4r1k1/ppp5/4q3/3nPrp1/8/1P4Q1/PBP3PP/R3R1K1 b - - 1 23
46...d5f4 (stockfish recommended: 46...e6c6)
4r1k1/ppp5/4q3/4Prp1/5n2/1P4Q1/PBP3PP/R3R1K1 w - - 2 24
47. g3c3 (stockfish recommended: 47. a1d1)
4r1k1/ppp5/4q3/4Prp1/5n2/1PQ5/PBP3PP/R3R1K1 b - - 3 24
48...c7c6 (stockfish recommended: 48...e6d5)
4r1k1/pp6/2p1q3/4Prp1/5n2/1PQ5/PBP3PP/R3R1K1 w - - 0 25
49. a1d1 (stockfish recommended: 49. a1d1)
4r1k1/pp6/2p1q3/4Prp1/5n2/1PQ5/PBP3PP/3RR1K1 b - - 1 25
50...b7b6 (stockfish recommended: 50...e8f8)
4r1k1/p7/1pp1q3/4Prp1/5n2/1PQ5/PBP3PP/3RR1K1 w - - 0 26
51. d1d4 (stockfish recommended: 51. d1d6)
4r1k1/p7/1pp1q3/4Prp1/3R1n2/1PQ5/PBP3PP/4R1K1 b - - 1 26
52...c6c5 (stockfish recommended: 52...f4d5)
4r1k1/p7/1p2q3/2p1Prp1/3R1n2/1PQ5/PBP3PP/4R1K1 w - - 0 27
53. d4f4 (stockfish recommended: 53. d4d2)
4r1k1/p7/1p2q3/2p1Prp1/5R2/1PQ5/PBP3PP/4R1K1 b - - 0 27
54...f5f4 (stockfish recommended: 54...f5f4)
4r1k1/p7/1p2q3/2p1P1p1/5r2/1PQ5/PBP3PP/4R1K1 w - - 0 28
55. g2g3 (stockfish recommended: 55. h2h3)
4r1k1/p7/1p2q3/2p1P1p1/5r2/1PQ3P1/PBP4P/4R1K1 b - - 0 28
56...e6g4 (stockfish recommended: 56...f4f5)
4r1k1/p7/1p6/2p1P1p1/5rq1/1PQ3P1/PBP4P/4R1K1 w - - 1 29
57. e5e6 (stockfish recommended: 57. h2h3)
4r1k1/p7/1p2P3/2p3p1/5rq1/1PQ3P1/PBP4P/4R1K1 b - - 0 29
58...f4f3 (stockfish recommended: 58...f4d4)
4r1k1/p7/1p2P3/2p3p1/6q1/1PQ2rP1/PBP4P/4R1K1 w - - 1 30
59. c3g7 (stockfish recommended: 59. c3g7)
4r1k1/p5Q1/1p2P3/2p3p1/6q1/1P3rP1/PBP4P/4R1K1 b - - 2 30
```

