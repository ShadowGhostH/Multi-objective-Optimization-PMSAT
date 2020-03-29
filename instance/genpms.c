/******************************************************************/
/*                         gensatandre.c                          */
/******************************************************************/
/*       Generation d'une donnee r-SAT aleatoire "in.dat"         */
/*           参数形式: ./gencnf+ n m k s1 s2					  */
/*      different k-sat instances of n variables, m clauses		  */
/*                with seeds from s1 to s2						  */
/******************************************************************/

#include <stdlib.h>
#include <stdio.h>
#include <math.h>
//#include "./randdd.h"

const unsigned int maxn = 10;

long int NbVar;			/* valeur du nombre de variables */
long int NbClause;			/* valeur du nombre de clauses */
long int HClause;
long int SClause;
long int KSat;			/* valeur de la longueur des clauses */
long int costCnt;
long int **SAT;			/* matrice PxR des variables par clause */
long int **Cost;
long int *Var;
FILE *f;

#define RANDOMAX 32767

#include <stdio.h>
#include <sys/time.h>
#include <time.h>
#include <unistd.h>
#include <math.h>

/* A pseudo-random number generator with state space of 2^1,237,193.   */
/* The generator uses 3 powerful generators to produce high-quality    */
/* output useful for simulation or encryption.                         */
/* The exact period depends on the seed used, but it will not be       */
/* less than 2^132,000, so in any case, it is inexhaustibly long.      */
/* Use triseed() with a string as an argument to seed the generator.   */
/* For best results, use a seed of at least 128 characters.            */
/*                                                                     */
/* It is possible to obtain 16 independent streams by using the        */
/* stream function.  However, if you do this, do not use triseed,      */
/* triuni, trirand, trigauss, or triexp, as these use all 16 streams   */
/* and result in the streams not being independent.                    */
/*                                                                     */
/* Because of the large state space, the generator uses about 300k     */
/* of memory.                                                          */
/*                                                                     */
/* triseed(str)   -- seed the generator                                */
/* randomize      -- use the system time and process id to randomize   */
/* streammwc      -- get the next value from one stream.  This makes   */
/*                   it possible to use multiple independent streams.  */
/* trirand        -- the main generator                                */
/* triuni         -- return a double in the range 0..1                 */
/* trirange(n)    -- return a value in the range 0..n-1                */
/* trigauss       -- return values from gaussian normal distribution   */
/* triexp         -- return values from exponential distribution       */
/*                                                                     */
/* This compiles using gcc, and uses the 64-bit long long type.        */

unsigned int streammwc(unsigned int);
void triseed(char *);
void randomize(void);
unsigned int gen1(void);
unsigned int gen2(void);
unsigned int trirand(void);
unsigned int trirange(unsigned int);
double triuni(void);
double trigauss(void);
double triexp(void);

/* Period parameters */
#define N 624
#define M 397
#define MATRIX_A 0x9908b0df   /* constant vector a */
#define UPPER_MASK 0x80000000 /* most significant w-r bits */
#define LOWER_MASK 0x7fffffff /* least significant r bits */

/* Tempering parameters */
#define TEMPERING_MASK_B 0x9d2c5680
#define TEMPERING_MASK_C 0xefc60000
#define TEMPERING_SHIFT_U(y)  (y >> 11)
#define TEMPERING_SHIFT_S(y)  (y << 7)
#define TEMPERING_SHIFT_T(y)  (y << 15)
#define TEMPERING_SHIFT_L(y)  (y >> 18)

static unsigned long mt[N]; /* the array for the state vector  */
static int mti=N+1; /* mti==N+1 means mt[N] is not initialized */

typedef unsigned long long int LL;

#define MASK 4294967295LLU
#define SHIFT 32

/* Default seed values for mwc generators */
static LL x[16]  = {
    18333948987180406405LLU, 3396064103838234601LLU, 9167940573016892060LLU, 
    11602519206222001949LLU, 3498837575370267021LLU, 2045814514671253272LLU,
    17352010865547394356LLU, 7301320009631839272LLU, 4426788213621169175LLU, 
    10325262821174723278LLU, 5843148046786257854LLU, 4224000924873309249LLU,
    11769342045971006032LLU, 8276768149177856750LLU, 9430850181828593547LLU,
    1445644914235662669LLU
};

/* Multiplier values for mwc generator */
/* 16 of these 64 values will be used  */
static LL mlt[64] = {
    4288664358LLU, 4288451889LLU, 4264593054LLU, 4273089819LLU,
    3561001134LLU, 3745276353LLU, 3983479725LLU, 4186539609LLU,
    3984122373LLU, 4106671749LLU, 3644234538LLU, 4210747845LLU,
    4220049069LLU, 4232922903LLU, 3757295538LLU, 3754278753LLU,
    4217746035LLU, 4174384455LLU, 4292687685LLU, 4279284819LLU,
    4208081703LLU, 3791889813LLU, 4241452545LLU, 4166970654LLU, 
    4261981773LLU, 3737152665LLU, 4122080814LLU, 3863889573LLU,
    3686350458LLU, 4166364618LLU, 3485621124LLU, 4114532784LLU,
    4063392483LLU, 4069860663LLU, 3424429314LLU, 3491786943LLU,
    3585022605LLU, 2493488259LLU, 3833424903LLU, 4040426193LLU,
    4112079828LLU, 3910145688LLU, 3297652905LLU, 3799316118LLU,
    4221389424LLU, 3069814695LLU, 2383480239LLU, 4197583104LLU,
    4278774738LLU, 4282407633LLU, 4294929423LLU, 3932151789LLU,
    3940719999LLU, 3683402145LLU, 3784417215LLU, 3725860719LLU,
    4293911373LLU, 4290500823LLU, 4285734759LLU, 4229899653LLU,
    3858215238LLU, 3309564819LLU, 3577946604LLU, 3591699453LLU
};

static unsigned int stag[8192];

static unsigned int s[65536],SI,SJ,SK,SL;

/* Seed the generator with a string */
void triseed(char *seed) {
    int i,j,k;
    LL tmp,n;

    /* Initialize values of x */
    for(i = 0; seed[i]; i++) {
        j = i & 15;
        x[j] = (x[j] << 8) + seed[i] + (x[j] >> 57);
        x[j] = mlt[j] * (x[j] & MASK) + (x[j] >> SHIFT);
        n ^= x[j]++;
        k = x[j] & 63; j = i & 63; 
        tmp = mlt[j]; mlt[j] = mlt[k]; mlt[k] = tmp;
    }

    /* Fill stagger table */
    for(i = 0; i < 8192; i++) {
        n = 4119103479LLU * (n & MASK) + (n >> SHIFT);
        j = n & 15;
        x[j] = mlt[j] * (x[j] & MASK) + (x[j] >> SHIFT);
        stag[i] = (unsigned int)(x[j] & MASK);
    }

    for(i = 0; i < N; i++) mt[i] = streammwc(i&15);
    mti = 0;

    for(i = 0; i < 65536; i++) s[i] = i;
    for(i = 0; i < 65535; i++) {
        j = i + (streammwc(i&15) % (65536-i));
        k = s[i];
        s[i] = s[j];
        s[j] = k;
    }
    SI = streammwc(0) & 65535;
    SJ = streammwc(2) & 65535;
    SK = streammwc(4) & 65535;
    SL = streammwc(8) & 65535;
}

/* Use the system time and process id to initialize generator */
void randomize() {
    struct timeval tp;
    struct timezone tzp;
    struct tm *tms;
    time_t  t;
    unsigned int p,r;
    char seed[1000];

    t = time(0);
    p = getpid();
    tms = localtime(&t);
    gettimeofday(&tp,&tzp);

    sprintf(seed,"%lx %X %x %X %x %X %x %X %x %X -------------------------"
           "-------------------------------------------------------------"
           "-------------------------------------------------------------"
           "-------------------------------------------------------------"
           "-------------------------------------------------------------"
           "-------------------------------------------------------------"
           "-------------------------------------------------------------"
           "-------------------------------------------------------------"
           "-------------------------------------------------------------"
           "-------------------------------------------------------------",
             t,p,tms->tm_hour,tms->tm_yday,tms->tm_sec,tms->tm_mon,
             tms->tm_year,tms->tm_min,tms->tm_wday,tms->tm_mday);
    p += t;
    for(r = 0; seed[r]; r++) {
        p = 63663 * (p & 65535) + (p >> 16);
        if (seed[r] == '-') 
            seed[r] = "0abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ"
                      "123456789!@#$^&*-_=+|~()[]{}<>;:,.?"[(p & 65535) % 88];
    }
    triseed(seed);
}

/* Get the next value in a particular stream */
unsigned int streammwc(unsigned int i) {
    i &= 15;
    return (unsigned int)(x[i]=mlt[i]*(x[i]&MASK)+(x[i]>>SHIFT));
}


/* A C-program for MT19937: Real number version                */
/*   genrand() generates one pseudorandom real number (double) */
/* which is uniformly distributed on [0,1]-interval, for each  */
/* call. sgenrand(seed) set initial values to the working area */
/* of 624 words. Before genrand(), sgenrand(seed) must be      */
/* called once. (seed is any 32-bit integer except for 0).     */
/* Integer generator is obtained by modifying two lines.       */
/*   Coded by Takuji Nishimura, considering the suggestions by */
/* Topher Cooper and Marc Rieffel in July-Aug. 1997.           */

/* This library is free software; you can redistribute it and/or   */
/* modify it under the terms of the GNU Library General Public     */
/* License as published by the Free Software Foundation; either    */
/* version 2 of the License, or (at your option) any later         */
/* version.                                                        */
/* This library is distributed in the hope that it will be useful, */
/* but WITHOUT ANY WARRANTY; without even the implied warranty of  */
/* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.            */
/* See the GNU Library General Public License for more details.    */
/* You should have received a copy of the GNU Library General      */
/* Public License along with this library; if not, write to the    */
/* Free Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA   */
/* 02111-1307  USA                                                 */
/* Copyright (C) 1997 Makoto Matsumoto and Takuji Nishimura.       */
/* When you use this, send an email to: matumoto@math.keio.ac.jp   */
/* with an appropriate reference to your work.                     */

/* Mersianne Twister generator */
unsigned int gen1() {
    unsigned int y;
    static unsigned int mag01[2]={0x0, MATRIX_A};
    /* mag01[x] = x * MATRIX_A  for x=0,1 */

    if (mti >= N) { /* generate N words at one time */
        int kk;
        for (kk=0;kk<N-M;kk++) {
            y = (mt[kk]&UPPER_MASK)|(mt[kk+1]&LOWER_MASK);
            mt[kk] = mt[kk+M] ^ (y >> 1) ^ mag01[y & 0x1];
        }
        for (;kk<N-1;kk++) {
            y = (mt[kk]&UPPER_MASK)|(mt[kk+1]&LOWER_MASK);
            mt[kk] = mt[kk+(M-N)] ^ (y >> 1) ^ mag01[y & 0x1];
        }
        y = (mt[N-1]&UPPER_MASK)|(mt[0]&LOWER_MASK);
        mt[N-1] = mt[M-1] ^ (y >> 1) ^ mag01[y & 0x1];

        mti = 0;
    }

    y = mt[mti++];
    y ^= TEMPERING_SHIFT_U(y);
    y ^= TEMPERING_SHIFT_S(y) & TEMPERING_MASK_B;
    y ^= TEMPERING_SHIFT_T(y) & TEMPERING_MASK_C;
    y ^= TEMPERING_SHIFT_L(y);

    return y; 
}

/* Mutating S-box generator */
unsigned int gen2() {
    unsigned int tmp;
    SI = (SI+1) & 65535;
    SJ ^= s[SI];
    SK ^= s[SJ];
    SL ^= s[SK];
    tmp = s[SI];
    s[SI] = s[SK];
    s[SK] = s[SJ];
    s[SJ] = s[SL];
    s[SL] = tmp;
    return s[s[SI] ^ s[SK]] ^ (s[s[SJ] ^ s[SL]] << 16);
}

/* The generator */
unsigned int trirand() {
    unsigned int rval,n;

    /* Randomize if needed */
    if (mti == N+1) randomize();

    /* Pick a value from the stagger table to return */
    /* Replace that value with a new value from one  */
    /* of the mwc generators                         */
    n = gen1();
    rval = stag[n & 8191];
    stag[n & 8191] ^= streammwc((n>>14)&15);

    /* Return the result */
    return rval + gen2();
}

/* Return a value in the range 0..1 */
double triuni() {
    return (double)trirand() * 2.3283064370807974e-10;
}

/* Return a pseudo-random number in the range 0..lim-1 */
unsigned int trirange(unsigned int lim) {
    unsigned int div=4294967295U/lim;
    unsigned int rval;

    do {
        rval = trirand() / div;
    } while(rval >= lim);
    return rval;
}

/* Return random normal values with mean=0 and standard deviation=1 */
double trigauss() {
    static double V1,V2,S,LS;
    static int phase = 1;
    double X;

    if (phase ^= 1) X = V2 * LS;
    else {
        do {
            V1 = (double)trirand()*4.6566128741615948e-10 - 1.0;
            V2 = (double)trirand()*4.6566128741615948e-10 - 1.0;
            S = V1 * V1 + V2 * V2;
        } while(S >= 1.0 || S == 0.0);
        LS = sqrt(-2.0 * log(S) / S);
        X = V1 * LS;
    }
    return X;
}

/* Return values from exponential distribution with mean=1 */
double triexp() {
    return -log(triuni());
}

/* Seed the generator, demonstrate the different functions,
    and create a diehard test file */

/*
int main() {
    FILE *out;
    int i,j;
    unsigned int a[1000];

    randomize();
    printf("4 values from each stream\n");
    for(i = 0; i < 16; i++) 
        printf("%u %u %u %u\n",
            streammwc(i), streammwc(i), streammwc(i), streammwc(i));
    printf("gen1\n");
    for(i = 0; i < 10; i++) printf("%u\n",gen1());
    printf("gen2\n");
    for(i = 0; i < 10; i++) printf("%u\n",gen2());
    printf("10 32-bit values\n");
    for(i = 0; i < 10; i++) printf("%u\n",trirand());
    printf("10 uni values\n");
    for(i = 0; i < 10; i++) printf("%lf\n",triuni());
    printf("10 values in the range 0..99\n");
    for(i = 0; i < 10; i++) printf("%u\n",trirange(100));
    printf("10 normal values\n");
    for(i = 0; i < 10; i++) printf("%lf\n",trigauss());
    printf("10 exponential values\n");
    for(i = 0; i < 10; i++) printf("%lf\n",triexp());
    printf("Creating a diehard test file....\n");
    out = fopen("tri.out","w");
    for(i = 0; i < 3000; i++) {
        for(j = 0; j < 1000; j++) a[j] = trirand();
        fwrite(a,4,1000,out);
    }
    fclose(out);
    return 0;
}
*/

/**************************************************************/
int main (argc, argv)
     int argc;
     char *argv[];
/**************************************************************/
{
    long int i, j, k, l, t, g1, g2, g;
    double TMP;
    char inst[50], graine[100];


    if (argc != 8) {
        printf ("\n Syntaxe :: %s <nb Var> <nb Hard Clauses> <nb Soft Clauses> <Longueur> <Cost Number> <petit graine> <grand Graine>", argv[0]);
        printf ("\n            Graine -> un entier. \n\n");
        exit (1);
    }
    NbVar   = atol(argv[1]);
    HClause = atol(argv[2]);
    SClause = atol(argv[3]);
    KSat    = atol(argv[4]);
    costCnt = atol(argv[5]);
    g1      = atol(argv[6]);
    g2      = atol(argv[7]);
    NbClause = HClause + SClause;

    for(g=g1; g<=g2; g++) {
	    sprintf(inst,"v%ldhc%ldsc%ldL%ldc%ldg%02ld",NbVar, HClause, SClause, KSat, costCnt, g);
	    srand(g);
	    sprintf(graine, "%d", rand());
	    printf("*** %s", graine);

        /* fonctionne avec le pid et la date courante ::->  randomize(); */
        triseed (graine);
        TMP = (double) NbClause / (double) NbVar;
        printf (" \n\n ### Generation du systeme de clauses soit : \n ###  %ld Clauses %ld-SAT a %ld litteraux \n ### [Clauses/NBVar]->%.3f\n\n", NbClause, KSat, NbVar, TMP);

        /* initialize */
        SAT = (long int **) malloc (NbClause * sizeof (long int));
        for (i = 0; i < NbClause; i++)   // NbClause * KSat
            SAT[i] = (long int *) malloc (KSat * sizeof (long int));
            
        Cost = (long int **) malloc (costCnt * sizeof (long int));
        for(i = 0; i < costCnt; i++)    // costCnt * SClause
            Cost[i] = (long int *) malloc (SClause * sizeof (long int));
            
        Var = (long int *) malloc (NbVar * sizeof (long int));
            
        for (i = 0; i < costCnt; i++) {
            for (j = 0; j < SClause; j++) {
                Cost[i][j] = trirange(maxn);
            }
        }
        for (i = 0; i < NbClause; i++) {
            for (j = 0; j < NbVar; j++) 
                Var[j] = 0;
            for (j = 0; j < KSat; j++) {
                do t = trirange (NbVar);
                while (Var[t]);
                Var[t] = 1;
                t++;
                l = trirange (100);
                if (l > 50) t = -t;
                SAT[i][j] = t;
            }
        }
            
        f = fopen (inst, "w+");
        if (f == NULL){
            printf ("Erreur : ouverture du fichier \"%s\"\n", inst);
        }
        fprintf (f, "p cnf %ld %ld %ld %ld\n", NbVar, HClause, SClause, costCnt);
        for(i = 0; i < costCnt; i++) {
            for(j = 0; j < SClause; j++){
                fprintf(f, "%ld%c", Cost[i][j], (j==SClause-1?'\n':' '));
            }
        }
        for (i = 0; i < NbClause; i++) {
            for (j = 0; j < KSat; j++)
                fprintf (f, " %ld", SAT[i][j]);
            fprintf (f, " 0\n");
        }
        fclose (f);
    }
}
