// this is depth first search strategy plus detection of when 
// a square in unreachable

#include <stdint.h>
#include <stdio.h>
#include <string.h>

#define DEBUG 1

/* given a square, return squares knight can go next */
short int sq_to_moves[64][8] = {
    /* sq0 (0,0) */  { 10,17,-1,-1,-1,-1,-1,-1 },
    /* sq1 (0,1) */  { 11,18,16,-1,-1,-1,-1,-1 },
    /* sq2 (0,2) */  { 12,19,17,8,-1,-1,-1,-1 },
    /* sq3 (0,3) */  { 13,20,18,9,-1,-1,-1,-1 },
    /* sq4 (0,4) */  { 14,21,19,10,-1,-1,-1,-1 },
    /* sq5 (0,5) */  { 15,22,20,11,-1,-1,-1,-1 },
    /* sq6 (0,6) */  { 23,21,12,-1,-1,-1,-1,-1 },
    /* sq7 (0,7) */  { 22,13,-1,-1,-1,-1,-1,-1 },
    /* sq8 (1,0) */  { 2,18,25,-1,-1,-1,-1,-1 },
    /* sq9 (1,1) */  { 3,19,26,24,-1,-1,-1,-1 },
    /* sq10 (1,2) */  { 4,20,27,25,0,16,-1,-1 },
    /* sq11 (1,3) */  { 5,21,28,26,1,17,-1,-1 },
    /* sq12 (1,4) */  { 6,22,29,27,2,18,-1,-1 },
    /* sq13 (1,5) */  { 7,23,30,28,3,19,-1,-1 },
    /* sq14 (1,6) */  { 31,29,4,20,-1,-1,-1,-1 },
    /* sq15 (1,7) */  { 30,5,21,-1,-1,-1,-1,-1 },
    /* sq16 (2,0) */  { 10,26,33,1,-1,-1,-1,-1 },
    /* sq17 (2,1) */  { 11,27,34,32,0,2,-1,-1 },
    /* sq18 (2,2) */  { 12,28,35,33,8,24,1,3 },
    /* sq19 (2,3) */  { 13,29,36,34,9,25,2,4 },
    /* sq20 (2,4) */  { 14,30,37,35,10,26,3,5 },
    /* sq21 (2,5) */  { 15,31,38,36,11,27,4,6 },
    /* sq22 (2,6) */  { 39,37,12,28,5,7,-1,-1 },
    /* sq23 (2,7) */  { 38,13,29,6,-1,-1,-1,-1 },
    /* sq24 (3,0) */  { 18,34,41,9,-1,-1,-1,-1 },
    /* sq25 (3,1) */  { 19,35,42,40,8,10,-1,-1 },
    /* sq26 (3,2) */  { 20,36,43,41,16,32,9,11 },
    /* sq27 (3,3) */  { 21,37,44,42,17,33,10,12 },
    /* sq28 (3,4) */  { 22,38,45,43,18,34,11,13 },
    /* sq29 (3,5) */  { 23,39,46,44,19,35,12,14 },
    /* sq30 (3,6) */  { 47,45,20,36,13,15,-1,-1 },
    /* sq31 (3,7) */  { 46,21,37,14,-1,-1,-1,-1 },
    /* sq32 (4,0) */  { 26,42,49,17,-1,-1,-1,-1 },
    /* sq33 (4,1) */  { 27,43,50,48,16,18,-1,-1 },
    /* sq34 (4,2) */  { 28,44,51,49,24,40,17,19 },
    /* sq35 (4,3) */  { 29,45,52,50,25,41,18,20 },
    /* sq36 (4,4) */  { 30,46,53,51,26,42,19,21 },
    /* sq37 (4,5) */  { 31,47,54,52,27,43,20,22 },
    /* sq38 (4,6) */  { 55,53,28,44,21,23,-1,-1 },
    /* sq39 (4,7) */  { 54,29,45,22,-1,-1,-1,-1 },
    /* sq40 (5,0) */  { 34,50,57,25,-1,-1,-1,-1 },
    /* sq41 (5,1) */  { 35,51,58,56,24,26,-1,-1 },
    /* sq42 (5,2) */  { 36,52,59,57,32,48,25,27 },
    /* sq43 (5,3) */  { 37,53,60,58,33,49,26,28 },
    /* sq44 (5,4) */  { 38,54,61,59,34,50,27,29 },
    /* sq45 (5,5) */  { 39,55,62,60,35,51,28,30 },
    /* sq46 (5,6) */  { 63,61,36,52,29,31,-1,-1 },
    /* sq47 (5,7) */  { 62,37,53,30,-1,-1,-1,-1 },
    /* sq48 (6,0) */  { 42,58,33,-1,-1,-1,-1,-1 },
    /* sq49 (6,1) */  { 43,59,32,34,-1,-1,-1,-1 },
    /* sq50 (6,2) */  { 44,60,40,56,33,35,-1,-1 },
    /* sq51 (6,3) */  { 45,61,41,57,34,36,-1,-1 },
    /* sq52 (6,4) */  { 46,62,42,58,35,37,-1,-1 },
    /* sq53 (6,5) */  { 47,63,43,59,36,38,-1,-1 },
    /* sq54 (6,6) */  { 44,60,37,39,-1,-1,-1,-1 },
    /* sq55 (6,7) */  { 45,61,38,-1,-1,-1,-1,-1 },
    /* sq56 (7,0) */  { 50,41,-1,-1,-1,-1,-1,-1 },
    /* sq57 (7,1) */  { 51,40,42,-1,-1,-1,-1,-1 },
    /* sq58 (7,2) */  { 52,48,41,43,-1,-1,-1,-1 },
    /* sq59 (7,3) */  { 53,49,42,44,-1,-1,-1,-1 },
    /* sq60 (7,4) */  { 54,50,43,45,-1,-1,-1,-1 },
    /* sq61 (7,5) */  { 55,51,44,46,-1,-1,-1,-1 },
    /* sq62 (7,6) */  { 52,45,47,-1,-1,-1,-1,-1 },
    /* sq63 (7,7) */  { 53,46,-1,-1,-1,-1,-1,-1 }
};

uint8_t sq_to_moves_n[64] = {
    2,3,4,4,4,4,3,2,3,4,6,6,6,6,4,3,4,6,8,8,8,8,6,4,4,6,8,8,8,8,6,4,
    4,6,8,8,8,8,6,4,4,6,8,8,8,8,6,4,3,4,6,6,6,6,4,3,2,3,4,4,4,4,3,2 
};

int pv[64];
int record = 0;

int
search(int depth, int sq_src, int sq, uint64_t visited, uint8_t *parents_)
{
    uint8_t parents[64];
    int temp;
    int i;
    
    visited |= (((uint64_t)1)<<sq);
    pv[depth] = sq;

    #if DEBUG==1
    if(depth > record)
    {
        int j, k;
        record = depth;
        for(j=0; j<depth; ++j) printf(" ");
        printf("depth:%02d visited=%016llx ", depth, visited);
        for(j=0; j<=depth; ++j) {
            printf("%d ", pv[j]);
        }
        printf("\n");
    }
    #endif

    /* base case: all squares visited? tour complete! */
    if(visited == 0xFFFFFFFFFFFFFFFF) {
        printf("HERE\n");
        return 0;
    }

    /* if we leave an orphan, don't descend */
    memcpy(parents, parents_, sizeof(parents));

    if(sq_src != -1) {
        for(i=0; i<sq_to_moves_n[sq_src]; ++i) {
            short int child = sq_to_moves[sq_src][i];
            if(visited & (1<<child)) {
                continue;
            }
            
            parents[child] -= 1;

            if(parents[child] <= 0) {
                //printf("ORPHAN! %d is unreachable now! aborting!\n", child);
                return -1;
            }
        }

//        {
//            int j;
//            for(j=0; j<32; ++j) {
//                printf("%d ", parents[j]);
//            }
//            printf("\n");
//        }
    }

    /* try all moves */
    for(i=0; i<sq_to_moves_n[sq]; i++) {
        short int candidate = sq_to_moves[sq][i];

        if((candidate / 8) >= 8) {
            continue;
        }

        if((candidate % 8) >= 8) {
            continue;
        }

        /* already visited this square? */
        if(visited & (((uint64_t)1)<<candidate)) continue;


        if(0 == search(depth+1, sq, candidate, visited, parents)) {
            return 0;
        }
    }

    return -1;
}

/* from square sq, generate next moves */
int 
main(int ac, char **av)
{
    int result;
    uint8_t parents[64];

    /* due to reflexivity of the N moves (or any non-pawn move in chess), the number
        of squares that can reach square x is the same as the number of legal moves
        sourced from x */
    memcpy(parents, sq_to_moves_n, sizeof(parents));

    

    /* start search */
    result = search(    0, /* depth */ 
                        -1, /* source square */
                        0, /* destination square */
                        1, /* visited bitmap */
                        parents /* array of parent counts */
                    );

    printf("the result was: %d\n", result);
}
