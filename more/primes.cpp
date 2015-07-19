/*
5 Prime counting functions implementations based on Linnik's Identity, including the 
star here, an implementation that runs in O(n^2/3 ln n) time and O(n^1/3 ln n) space 
(search for the function countprimes5, below).

Nathan McKenzie, 8-9-2011
nathan _AT_ icecreambreakfast.com

See http://www.icecreambreakfast.com/primecount/primecounting.html for descriptions
of the theory behind all of this stuff.

See http://www.icecreambreakfast.com/primecount/primecounting.html#1_1 for a basic
description  of Linnik's identity,and 
http://www.icecreambreakfast.com/primecount/primecounting.html#ch2  for a bit more 
elaboration how this identity can be used to compute the prime counting function.

As a general note, 4 of the 5 of these algorithms could be sped up considerably by
making use of a suitably sized wheel - the fourth algorithm (countprimes4) already 
makes use of such a wheel.

*/


/* !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!

NOTE!  For easy exploration, change the following line
*/

#define primeCountingFunction countprimes5

/* to any of the following values : countprimes1, countprimes2, countprimes3, 
countprimes4, countprimes5 to try out the different prime counting algorithms.

!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!
*/





#include "stdio.h"
#include "stdlib.h"
#include "math.h"
#include "conio.h"
#include "time.h"


typedef long long BigInt;
const int g_wheelLargestPrime = 19;
int scaleNum = 10;

/* ________________________________________________________________________________________

This is the main timing loop, running the prime counting function for increasingly
large input.

Change the #define "primeCountingFunction" to the various "countprime" functions to 
run and performance time them.
________________________________________________________________________________________
*/

BigInt countprimes1( BigInt n );
BigInt countprimes2( BigInt n );
BigInt countprimes3( BigInt n );
BigInt countprimes4( BigInt n );
BigInt countprimes5( BigInt n );
void MakeWheel( int );

int main(int argc, char* argv[]){
    if( primeCountingFunction == countprimes4 ) MakeWheel( g_wheelLargestPrime );

    int oldClock = (int)clock();
    int lastDif = 0;

    printf("                                                                    ");
    printf( "Time\n");
    printf("                                                                    ");
    printf( "Increase\n");
    printf("                                                                    ");
    printf( "for x%d\n", scaleNum);
    printf("         ");
    printf( "__ Input Number __   __ Output Number __ _ MSec _ _ Sec _  Input\n");
    printf( "                                                                    \n");
    for( BigInt i = scaleNum; i <= 1000000000000000000; i *= scaleNum ){
        printf( "%17I64d(10^%4.1f): ", i, log( (double)i )/log(10.0) );
        BigInt total = (BigInt)(primeCountingFunction( i )+.00001);
        int newClock = (int)clock();
        printf( " %20I64d %8d : %4d: x%f\n",
            total, newClock - oldClock, ( newClock - oldClock ) / CLK_TCK,
            ( lastDif ) ? (double)( newClock - oldClock ) / (double)lastDif : 0.0 );
        lastDif = newClock - oldClock;
        oldClock = newClock;
    }

    getch();

    return 0;
}












static BigInt mu[] = { 0, 1, -1, -1, 0, -1, 1, -1, 0, 0, 1, -1, 0, -1, 1, 1, 0, -1, 0, 
    -1, 0, 1, 1, -1, 0, 0, 1, 0, 0, -1, -1, -1, 0, 1, 1, 1, 0, -1, 1, 1, 0, -1, -1, -1,
    0, 0, 1, -1, 0, 0, 0, 1, 0, -1, 0, 1, 0, 1, 1, -1, 0, -1, 1, 0, 0, 1, -1, -1, 0, 1,
    -1, -1, 0, -1, 1, 0, 0, 1, -1, -1, 0, 0 };

/* ________________________________________________________________________________________

ALGORITHM 1 : countprimes1

This is the first implementation of the prime counting function.  It is not at all
fast, but it is at least rather simple.  It runs in something like O(n^1.7) time and 
O(episolon) space - which makes it worse, in fact, that trial division.

See http://www.icecreambreakfast.com/primecount/primecounting.html#3_1 for the source 
identity of countdivisors.
See http://www.icecreambreakfast.com/primecount/primecounting.html#2_4 for the body of 
countprimes1
________________________________________________________________________________________
*/

double countdivisors(BigInt n, BigInt k){
    if (k == 0) return 1; 
    if (k == 1) return n - 1; 
    BigInt t = 0; 
    for (BigInt i = 2; i <= n; i++) t += countdivisors( n / i, k - 1 ); 
    return t;
}

BigInt countprimes1( BigInt n){ 
    double t = 0.0; 
    for (BigInt j = 1; j < log((double)n) / log(2.0); j++)
        for (BigInt k = 1; k < log( pow( n, 1.0 / j ) ) / log(2.0); k++)
            t += pow( -1.0, (double)k+1 ) * countdivisors(pow( n, 1.0 / j ), k)
            / k / j * mu[j];
    return (t+.1);
}

/* ________________________________________________________________________________________

ALGORITHM 2 : countprimes2

This is a recursive implementation of countprimes1.  It's ultimate quite similar,
including its lousy performance.

See http://www.icecreambreakfast.com/primecount/primecounting.html#3_2 for the
source identity of recurseprimes.
See http://www.icecreambreakfast.com/primecount/primecounting.html#2_3 for the body
of countprimes2
________________________________________________________________________________________
*/

double recurseprimes( BigInt n, BigInt k ){
    double t= 0;
    for( BigInt j = 2; j <= n; j++ )t += 1.0 / k - recurseprimes( n/j, k+1 );
    return t;
}

BigInt countprimes2( BigInt n ){
    double t = 0;
    for (BigInt j = 1; j < log((double)n) / log(2.0); j++)
        t += recurseprimes(pow( n, 1.0 / j ), 1) / j * mu[j]; 
    return t+.1;
}

/* ________________________________________________________________________________________

ALGORITHM 3 : countprimes3

This is another, substantially faster, implementation of the prime counting function
via Linnik's Identity.  It relies on internal symmetries of the number of divisors
summatory function to be sped up.  For an algorithm that uses O(epsilon) memory, it 
runs pretty quickly, appearing to clock in just a bit below the O(n) mark.

This algorithm can be sped up massively, in constant time terms, by using a suitably
large wheel.

See http://www.icecreambreakfast.com/primecount/primecounting.html#3_3 for the
source identity of countdivisorsfast
See http://www.icecreambreakfast.com/primecount/primecounting.html#2_4 for the 
body of countprimes3
________________________________________________________________________________________
*/

int inversepow( int n, int k) { 
    return pow(n, 1.0 / k) + .00000001;
}

double factorial(BigInt val){ 
    double total = 1.0; 
    for (int i = 1; i <= val; i++) total *= i; 
    return total;
}

double binomial_(BigInt val, BigInt div) { 
    return factorial(val) / (factorial(div) * factorial(val - div));
}

double countdivisorsfast( BigInt n, BigInt k, BigInt a ){ 
    if( k == 0 )return 1; 
    if( k == 1 )return n - a + 1; 
    double t = 0;
    for( BigInt m = a; m <= inversepow(n,k); m++ )
        for( BigInt j = 0; j < k; j++ ) 
            t += countdivisorsfast( n / pow( (double)m, (double)k - j ), j, m+1 )
            * binomial_( k, j ); 
    return t;
}

BigInt countprimes3(BigInt n){ 
    double t = 0.0; 
    for (BigInt j = 1; j < log((double)n) / log(2.0); j++)
        for (BigInt k = 1; k < log( pow( n, 1.0 / j ) ) / log(2.0); k++)
            t += pow( -1.0, (double)k + 1 ) * countdivisorsfast(inversepow( n, j ), k, 2 )
            / k / j * mu[j];
    return t + .1;
}









/* ________________________________________________________________________________________

ALGORITHM 4 : countprimes4

Although it might be difficult to tell, the following code implements the same
algorithm, essentially, as ALGORITHM 3.  So, its core identities are found in 
http://www.icecreambreakfast.com/primecount/primecounting.html#3_3
and http://www.icecreambreakfast.com/primecount/primecounting.html#2_4

The main difference here is that a lot of integration has happened for performance 
reasons (so, for example, partially computed binomials are kept around as computation
happens), and, especially, a large wheel has been implemented, which speeds up 
computation drastically.

This is a pretty fast prime counting algorithm considering it uses O(episilon) memory.  
I've tried, from a number of different angles, to come up with ways of trading off 
memory usage to increase its runtime performance, but I haven't found any such approaches.

I'm not entirely sure what the Big O runtime performance of this algorithm is, 
ultimately... Up to around 10^15, it seems to be running in something like O(n^4/5), 
but it also seems to be taking slightly longer each power of 10.
________________________________________________________________________________________
*/


const double EPSILON = .00000000001;

typedef long long BigInt;

/* A wheel including 19 has 9.6 million entries. */

/* Used for the construction of the wheel - include more primes as needed,
but this is already enough primes to consume over 75 gigs of RAM */

const int g_primes[] ={ 2,   3,   5,   7,  11,  13,  17,  19,  23,  29 };

int         g_wheelCycleEntries;
int         g_wheelCyclePeriod;
int         g_wheelFirstPrime;
int         g_wheelBasePrimes;
int*        g_wheelTranslation          = 0;
int*        g_wheelOffsets              = 0;

BigInt      g_latticepoints;
BigInt      g_minVarValue;
BigInt      g_boundary;

BigInt      g_scale;
BigInt      g_divisor;

BigInt      g_lastMax;

int         g_variablesLeft;
BigInt      g_lastScaleDivisor;
BigInt      g_scaleVal;

int g_mu[] = {
    0,   1,  -1,  -1,   0,  -1,   1,  -1,   0,   0,
    1,  -1,   0,  -1,   1,   1,   0,  -1,   0,  -1,
    0,   1,   1,  -1,   0,   0,   1,   0,   0,  -1,
    -1,  -1,   0,   1,   1,   1,   0,  -1,   1,   1,
    0,  -1,  -1,  -1,   0,   0,   1,  -1,   0,   0,
    0,   1,   0,  -1,   0,   1,   0,   1,   1,  -1,
    0,  -1,   1,   0,   0,   1,  -1,  -1,   0,   1,
    -1,  -1,   0,  -1,   1,   0,   0,   1,  -1,  -1,
    0,   0,   1,  -1,   0,   1,   1,   1,   0,  -1,
    0,   1,   0,   1,   1,   1,   0,  -1,   0,   0,
    0,  -1,  -1,  -1,   0,  -1,   1,  -1,   0,  -1,
    -1,   1,   0,  -1,  -1,   1,   0,   0,   1,   1,
    0,   0,   1,   1,   0,   0,   0,  -1,   0,   1,
    -1,  -1,   0,   1,   1,   0,   0,  -1,  -1,  -1,
    0,   1,   1,   1,   0,   1,   1,   0,   0,  -1,
    0,  -1,   0,   0,  -1,   1,   0,  -1,   1,   1,
    0,   1,   0,  -1,   0,  -1,   1,  -1,   0,   0,
    -1,   0,   0,  -1,  -1,   0,   0,   1,   1,  -1,
    0,  -1,  -1,   1,   0,   1,  -1,   1,   0,   0,
    -1,  -1,   0,  -1,   1,  -1,   0,  -1,   0,  -1,
    0,   1,   1,   1,   0,   1,   1,   0,   0,   1,
    1,  -1,   0,   1,   1,   1,   0,   1,   1,   1,
    0,   1,  -1,  -1,   0,   0,   1,  -1,   0,  -1,
    -1,  -1,   0,  -1,   0,   1,   0,   1,  -1,  -1,
    0,  -1,   0,   0,   0,   0,  -1,   1,   0,   1,
    0,  -1,   0,   1,   1,  -1,   0,
};

/* Note that with 64 bit ints, we can't go above factorial( 20 ) anyway. */
BigInt g_factorial[] = {
    0, 1, 2, 6, 24, 120, 720, 5040, 40320, 362880, 3628800, 39916800, 479001600,
    6227020800, 87178291200, 1307674368000, 20922789888000, 355687428096000,
    6402373705728000, 121645100408832000, 2432902008176640000
};

inline BigInt InversePower( BigInt x, BigInt y ){
    return ( (BigInt)( pow( (double)x + EPSILON, ( 1.0 / (double)y ) ) + EPSILON ) );
}

inline int GetwheelCyclePeriod( int cap ){
    int val = 1;
    int i   = 0;

    while( g_primes[ i ] <= cap ){
        val *= g_primes[ i ];
        i++;
    }
    return val;
}

inline int GetFirstIncludedPrime( int cap ){
    int i = 0;

    while( g_primes[ i ] <= cap ){
        i++;
    }
    return g_primes[ i ];
}

inline int GetBasePrimes( int cap ){
    int i = 0;
    while( g_primes[ i ] <= cap ){
        i++;
    }
    return i;
}

inline void IncrementWheel( int &offset ){
    offset++;
    if( offset >= g_wheelCycleEntries ){
        offset = 0;
    }
}

void MakeWheel( int cap ){
    g_wheelBasePrimes       = GetBasePrimes( cap );
    g_wheelCyclePeriod      = GetwheelCyclePeriod( cap );
    g_wheelCycleEntries     = 0;

    int cur                 = 0;
    int offset              = -1;

    int* wheelBase          = 0;

    wheelBase               = ( int* )malloc( g_wheelCyclePeriod * sizeof( int ) );
    g_wheelTranslation      = ( int* )malloc( ( g_wheelCyclePeriod + 1 ) * sizeof( int ) );
    g_wheelOffsets          = ( int * )malloc( g_wheelCyclePeriod * sizeof( int ) );
    g_wheelFirstPrime       = GetFirstIncludedPrime( cap );

    for( int i = 0; i < g_wheelCyclePeriod; i++ ){
        wheelBase[ i ] = 1;
        for( int j = 2; j <= cap; j++ ){
            if( !( ( i + 1 ) % j ) ){
                wheelBase[ i ] = 0;
                break;
            }
        }
    }

    while( cur < g_wheelCyclePeriod ){
        if( wheelBase[ cur ] && cur != 0 ){
            g_wheelOffsets[ g_wheelCycleEntries ] = offset + 1;
            offset = 0;
            g_wheelCycleEntries++;
        }else{
            offset++;
        }
        cur++;
    }

    g_wheelOffsets[ g_wheelCycleEntries ] = 2;
    g_wheelCycleEntries++;	

    int total = 0;

    g_wheelTranslation[ 0 ] = 0;
    for( BigInt i = 0; i < g_wheelCyclePeriod; i++ ){
        if( i && wheelBase[ i - 1 ] ){
            total++;
        }
        g_wheelTranslation [ i + 1 ] = total;
    }

    free( wheelBase );
}

/* This function calculates how many entries the wheel leaves
in the range from (rangeStart, rangeStop].*/
inline BigInt CountWheelEntries( BigInt rangeStart, BigInt rangeEnd ){
    rangeEnd++;

    int a = rangeStart % g_wheelCyclePeriod;
    int b = rangeEnd % g_wheelCyclePeriod;

    return ( rangeEnd - b - rangeStart + a ) / g_wheelCyclePeriod *
        g_wheelCycleEntries + g_wheelTranslation[ b ] - g_wheelTranslation[ a ] ;
}

void CountHyperbolaLattice_2_Variables( void ){
    BigInt  finalBoundary   = g_boundary / g_minVarValue;
    BigInt  boundaryRoot    = (BigInt)( sqrt( (double)finalBoundary ) + EPSILON );

    /* For if the final two digits happen to be the same. */
    g_latticepoints += g_scale / ( g_divisor * ( g_divisor + 1 ) );

    /* Leading digit is same, final digit is not. */
    g_latticepoints += 
        ( CountWheelEntries( g_minVarValue, finalBoundary / g_minVarValue ) - 1 )
        * ( g_scale / g_divisor );

    /* For if the final two digits happen to be the same,
    but both differ from the previous. */
    g_latticepoints +=
        ( CountWheelEntries( g_minVarValue, boundaryRoot ) - 1 ) * ( g_scale / 2 );

    /* Both digits differ from all other digits - This is the hellish evil
    loop of portentious doom. */

    int curWheelOffset      = g_wheelTranslation[ g_minVarValue % g_wheelCyclePeriod ];

    BigInt	curLeadingVar   = g_minVarValue + g_wheelOffsets[ curWheelOffset ];
    BigInt	subTotal        = 0;

    IncrementWheel( curWheelOffset );

    while( curLeadingVar <= boundaryRoot ){
        subTotal += CountWheelEntries( curLeadingVar, finalBoundary / curLeadingVar ) - 1;
        curLeadingVar += g_wheelOffsets[ curWheelOffset ];
        IncrementWheel( curWheelOffset );
    }

    g_latticepoints	+= subTotal * g_scale;
}

void CountHyperbolaLattice_3_Variables( BigInt hyperbolaBoundary, BigInt minVarValue ){
    BigInt maxVarValue  = InversePower( hyperbolaBoundary, 3 );

    int curWheelOffset  = g_wheelTranslation[ minVarValue % g_wheelCyclePeriod ];

    g_boundary          = hyperbolaBoundary;
    g_minVarValue       = minVarValue;
    g_scale             = g_scaleVal / g_lastScaleDivisor;
    g_divisor           = g_lastScaleDivisor + 1;

    CountHyperbolaLattice_2_Variables();

    g_minVarValue += g_wheelOffsets[ curWheelOffset ];
    IncrementWheel( curWheelOffset );

    g_scale     = g_scaleVal;
    g_divisor   = 2;
    while( g_minVarValue <= maxVarValue ){
        CountHyperbolaLattice_2_Variables();
        g_minVarValue += g_wheelOffsets[ curWheelOffset ];
        IncrementWheel( curWheelOffset );
    }
}

void CountHyperbolaLattice_X_Variables( BigInt hyperbolaBoundary, BigInt minVarValue ){
    BigInt         maxVarValue      = InversePower( hyperbolaBoundary, g_variablesLeft );

    /* Save global variables that will be restored at end of function */

    BigInt		scaleVal                = g_scaleVal;
    BigInt		lastScaleDivisor        = g_lastScaleDivisor;

    int curWheelOffset = g_wheelTranslation[ minVarValue % g_wheelCyclePeriod ];

    g_variablesLeft--;
    g_lastScaleDivisor                  = lastScaleDivisor + 1;
    g_scaleVal                          = scaleVal / lastScaleDivisor;

    if( g_variablesLeft == 3 ){
        CountHyperbolaLattice_3_Variables( hyperbolaBoundary / minVarValue, minVarValue );
    }else{
        CountHyperbolaLattice_X_Variables( hyperbolaBoundary / minVarValue, minVarValue );
    }

    g_lastScaleDivisor                  = 2;
    g_scaleVal                          = scaleVal;
    minVarValue += g_wheelOffsets[ curWheelOffset ];
    IncrementWheel( curWheelOffset );

    while( minVarValue <= maxVarValue ){
        if( g_variablesLeft == 3 ){
            CountHyperbolaLattice_3_Variables( hyperbolaBoundary / minVarValue, minVarValue );
        }else{
            CountHyperbolaLattice_X_Variables( hyperbolaBoundary / minVarValue, minVarValue );
        }
        minVarValue += g_wheelOffsets[ curWheelOffset ];
        IncrementWheel( curWheelOffset );
    }

    /* Restore global variables */

    g_lastScaleDivisor = lastScaleDivisor;
    g_variablesLeft++;
}

BigInt CountHyperbolaLattice( BigInt hyperbolaBoundary, int hyperbolaVariables ){
    g_latticepoints     = 0;
    g_variablesLeft     = hyperbolaVariables;
    g_lastScaleDivisor  = 1;
    g_scaleVal          = g_factorial[ hyperbolaVariables ];

    if( hyperbolaBoundary < 
        (BigInt)pow( (double)g_wheelFirstPrime, (double)hyperbolaVariables ) ){
            return 0;
    }

    switch( hyperbolaVariables ){
    case 1:
        g_latticepoints = CountWheelEntries( g_wheelFirstPrime, hyperbolaBoundary );
        break;
    case 2:
        /* CountHyperbolaLattice_2_Variables expects a number of global variables
        to be initialized when it is called, which generally happens in
        CountHyperbolaLattice_3_Variables.  We have to do it manually here. */
        g_minVarValue   = g_wheelFirstPrime;
        g_boundary      = g_wheelFirstPrime * hyperbolaBoundary;
        g_scale         = 2;
        g_divisor       = 1;

        CountHyperbolaLattice_2_Variables();
        break;
    case 3:
        CountHyperbolaLattice_3_Variables( hyperbolaBoundary, g_wheelFirstPrime );
        break;
    default:
        CountHyperbolaLattice_X_Variables( hyperbolaBoundary, g_wheelFirstPrime );
        break;
    }
    return g_latticepoints;
}

BigInt countprimes4( BigInt n ){
    int maxPower = ( int )( log( ( double )n + EPSILON ) 
        / log ( ( double )g_wheelFirstPrime + EPSILON ) + EPSILON ) + 1;
    double	total           = 0.0;

    int		oldClock        = (int)clock();
    int		totalTime       = 0;

    for( int curPower = 1; curPower < maxPower; curPower++ ){
        if( !g_mu[ curPower ] ){
            continue;
        }

        BigInt  curMax              = InversePower( n, curPower );
        double  subTotal            = 0.0;
        BigInt  hyperbolaEntries    = 1;
        double  sign                = 1;

        while( 1 ){
            double temp     = sign / hyperbolaEntries;
            sign            *= -1;

            double v2       = (double)CountHyperbolaLattice( curMax, hyperbolaEntries );
            temp            *= v2;

            if( temp == 0.0 ){
                break;
            }

            subTotal        += temp;
            hyperbolaEntries++;

            int newClock    = (int)clock();
            totalTime       += newClock - oldClock;
            oldClock        = newClock;

        }
        subTotal    /= curPower * g_mu[ curPower ];
        total       += subTotal;
    }
    total += g_wheelBasePrimes;

    /* the .5 is to prevent truncation errors - but it's clearly sloppy */
    return (BigInt)( total + 0.5 );
}













/* ________________________________________________________________________________________

ALGORITHM 5

This is the fastest, in terms of O() runtime, and by far most complex, implementation
of a prime counting algorithm based on Linnik's identity that I have found.

Its performance is none too shabby - it runs in roughly O( n^2/3 ln n ) time and 
O( n^1/3 ln n ) space, which puts it in spitting distance of some of the faster methods
for counting primes.

See http://www.icecreambreakfast.com/primecount/primecounting.html#ch4 ,
http://www.icecreambreakfast.com/primecount/primecounting.html#ch5 , and
http://www.icecreambreakfast.com/primecount/primecounting.html#ch6
for general descriptions of the algorithm implemented here.

As currently implemented here, the code stops working for relatively low input values 
(say, 10^11 ish) - this is a consequence of precision and overflow issues, not anything
to do with the underlying math.  Obviously those concerns would have to be addressed to
use it for higher numbers.

As repeatedly mentioned above, this algorithm should be sped up considerably if a wheel
is implemeneted, as was done in ALGORITHM 4 / countprimes4.  To date, I haven't written
such an implementation.  A suitable wheel will come with the side bit of making precision 
issues somewhat more tractable.

I haven't gone out of my way to do much in the way of constant time performance
optimization here - it's already unreadable enough without fiddling with the code
thusly, and integrating a wheel ought to come first anyway.  But there are plenty 
of opportunities.

I'm really curious how fast this approach can be sped up.

The fuzzy transitions between double and BigInt are a cause of imprecision and
consternation.
________________________________________________________________________________________
*/

static BigInt* binomials;		/* This is used as a doubly subscripted array, 128x128.  
                                Indexing is done manually.*/
static BigInt nToTheThird;
static BigInt logn;

static BigInt numPrimes;
static BigInt* primes;

static BigInt* factorsMultiplied;
static BigInt* totalFactors;
static BigInt* factors;			/* This is used as a doubly subscripted array, n^1/3 x ln n.
                                Indexing is done manually.*/
static BigInt* numPrimeBases;

static BigInt* DPrime;			/*This is used as a doubly subscripted array, n^1/3 x ln n.
                                Indexing is done manually.*/

static BigInt curBlockBase;

static double t;

static BigInt nToTheHalf;
static BigInt numDPowers;
static double* dPrime;

static BigInt S1Val;
static BigInt S1Mode;
static BigInt* S3Vals;
static BigInt* S3Modes;

static bool ended;
static BigInt maxSieveValue;

static BigInt ceilval;

static BigInt n;

BigInt binomial( double n, int k ){
    double t = 1;
    for( int i = 1; i <= k; i++ ){
        t *= ( n - ( k - i ) ) / i;
    }
    return BigInt( t + .1 );
}

static BigInt invpow(double n, double k) {
    return (BigInt)(pow(n, 1.0 / k) + .00000001);
}

/* See http://www.icecreambreakfast.com/primecount/primecounting.html#ch5 for a description
of calculating d_k'(n) from a complete factorization of a number n. */
static BigInt d1(BigInt* a, BigInt o, BigInt k, BigInt l){
    BigInt t = 1;
    for (BigInt j = 0; j < l; j++) t *= binomials[(a[o*logn+ j] - 1 + k)*128 + a[o*logn+ j]];
    return t;
}

/* See http://www.icecreambreakfast.com/primecount/primecounting.html#ch5 for a description
of calculating d_k'(n) from a complete factorization of a number n.*/
static BigInt d2(BigInt* a, BigInt o, BigInt k, BigInt l, BigInt numfacts ){
    if (numfacts < k) return 0;
    BigInt t = 0;
    for (BigInt j = 1; j <= k; j++) t += ( ( k - j ) % 2 == 1 ? -1:1 ) 
        * binomials[k * 128 + j] * d1(a, o, j, l);
    return (BigInt)t;
}

static void allocPools( BigInt n ){
    nToTheThird = (BigInt)pow(n, 1.0 / 3);

    logn = (BigInt)(log(pow(n, 2.00001 / 3)) / log(2.0)) + 1;
    factorsMultiplied = new BigInt[nToTheThird];
    totalFactors = new BigInt[nToTheThird];
    factors = new BigInt[nToTheThird * logn];
    numPrimeBases = new BigInt[nToTheThird];
    DPrime = new BigInt[(nToTheThird + 1) * logn];
    binomials = new BigInt[128*128+ 128];
    for (BigInt j = 0; j < 128; j++) 
        for (BigInt k = 0; k <= j; k++)
            binomials[j * 128 + k]= binomial(j, k);
    for (BigInt j = 0; j < logn; j++) DPrime[j] = 0;
    curBlockBase = 0;

    t = n - 1;

    nToTheHalf = (BigInt)pow(n, 1.0 / 2);
    numDPowers = (BigInt)(log(pow(n, 2.00001 / 3)) / log(2.0)) + 1;
    dPrime = new double[(nToTheThird + 1) * (numDPowers + 1)];

    S1Val = 1;
    S1Mode = 0;
    S3Vals = new BigInt[nToTheThird + 1];
    S3Modes = new BigInt[nToTheThird + 1];

    ended = false;
    maxSieveValue = (BigInt)(pow(n, 2.00001 / 3));

    for (BigInt j = 2; j < nToTheThird + 1; j++){
        S3Modes[j] = 0;
        S3Vals[j] = 1;
    }
}

static void deallocPools(){
    delete factorsMultiplied;
    delete totalFactors;
    delete factors;
    delete numPrimeBases;
    delete DPrime;
    delete binomials;
    delete dPrime;
    delete S3Vals;
    delete S3Modes;
    delete primes;
}

/* This finds all the primes less than n^1/3, which will be used for sieving and
generating complete factorizations of numbers up to n^2/3*/
static void fillPrimes(){
    BigInt* primesieve = new BigInt[nToTheThird + 1];
    primes = new BigInt[nToTheThird + 1];
    numPrimes = 0;
    for (BigInt j = 0; j <= nToTheThird; j++) primesieve[j] = 1;
    for (BigInt k = 2; k <= nToTheThird; k++){
        BigInt cur = k;
        if (primesieve[k] == 1){
            primes[numPrimes] = k;
            numPrimes++;
            while (cur <= nToTheThird){
                primesieve[cur] = 0;
                cur += k;
            }
        }
    }
    delete primesieve;
}

/*This resets some state used for the sieving and factoring process.*/
static void clearPools(){
    for (BigInt j = 0; j < nToTheThird; j++){
        numPrimeBases[j] = -1;
        factorsMultiplied[j] = 1;
        totalFactors[j] = 0;
    }
}

/* We can use sieving on our current n^1/3 sized block of numbers to
get their complete prime factorization signatures, with which we can then
quickly compute d_k' values.*/
static void factorRange(){
    for (BigInt j = 0; j < numPrimes; j++){
        /*mark everything divided by each prime, adding a new entry.*/
        BigInt curPrime = primes[j];
        if (curPrime * curPrime > curBlockBase + nToTheThird) break;
        BigInt curEntry = ( curBlockBase % curPrime == 0 ) ? 0:curPrime 
            - (curBlockBase % curPrime);
        while (curEntry < nToTheThird){
            if( curEntry+curBlockBase != 0 ){
                factorsMultiplied[curEntry] *= curPrime;
                totalFactors[curEntry]++;
                numPrimeBases[curEntry]++;
                factors[curEntry*logn+ numPrimeBases[curEntry]] = 1;
            }
            curEntry += curPrime;
        }
        /*mark everything divided by each prime power*/
        BigInt cap = (BigInt)( log((double)(nToTheThird+curBlockBase)) 
            / log((double)curPrime) + 1 );
        BigInt curbase = curPrime;
        for (BigInt k = 2; k < cap; k++){
            curPrime *= curbase;
            curEntry = (curBlockBase % curPrime == 0) ? 0 : curPrime 
                - (curBlockBase % curPrime);
            while (curEntry < nToTheThird){
                factorsMultiplied[curEntry] *= curbase;
                totalFactors[curEntry]++;
                if (curEntry + curBlockBase != 0)
                    factors[curEntry*logn+ numPrimeBases[curEntry]] = k;
                curEntry += curPrime;
            }
        }
    }
    /*account for prime factors > n^1/3*/
    for (BigInt j = 0; j < nToTheThird; j++){
        if (factorsMultiplied[j] < j+curBlockBase){
            numPrimeBases[j]++;
            totalFactors[j]++;
            factors[j*logn+ numPrimeBases[j]] = 1;
        }
    }
}

/* By this point, we have already factored, through sieving, all the numbers in the 
current n^1/3 sized block we are looking at.  With a complete factorization, we 
can calculate d_k'(n) for a number.  Then, D_k'(n) = d_k'(n) + D_k'(n-1).*/
static void buildDivisorSums(){
    for (BigInt j = 1; j < nToTheThird+1; j++){
        if (j + curBlockBase == 1 || j + curBlockBase == 2) continue;
        for (BigInt k = 0; k < logn; k++){
            DPrime[j * logn + k] = DPrime[(j - 1) * logn + k] + 
                d2(factors, j - 1, k, numPrimeBases[j - 1] + 1, totalFactors[j - 1]);
        }
    }
    for (BigInt j = 0; j < logn; j++) DPrime[j] = DPrime[nToTheThird*logn+ j];
}

/*  This general algorithm relies on values of D_k' <= n^2/3 and d_k' <= n^1/3.  
This function calculates those values of d_k'.*/
static void find_dVals(){
    curBlockBase = 1;
    clearPools();
    factorRange();
    buildDivisorSums();

    for (BigInt j = 2; j <= nToTheThird; j++){
        for (BigInt m = 1; m < numDPowers; m++){
            double s = 0;
            for (BigInt r = 1; r < numDPowers; r++) 
                s += pow(-1.0, (double)( r + m )) * (1.0 / (r + m + 1)) * 
                (DPrime[j * logn + r] - DPrime[(j - 1) * logn + r]);
            dPrime[j*(numDPowers + 1)+ m] = s;
        }
    }
}

static void resetDPrimeVals(){
    curBlockBase = 0;
    for (BigInt k = 0; k < nToTheThird + 1; k++)
        for (BigInt j = 0; j < logn; j++)
            DPrime[k * logn + j] = 0;
}

/* This function is calculating the first two sums of 
http://www.icecreambreakfast.com/primecount/primecounting.html#4_4  
It is written to rely on values of D_k' from smallest to greatest, 
to use the segmented sieve.*/
static void calcS1(){
    if (S1Mode == 0){
        while (S1Val <= ceilval){
            BigInt cnt = (n / S1Val - n / (S1Val + 1));
            for (BigInt m = 1; m < numDPowers; m++) 
                t += cnt * (m % 2 == 1 ? -1 : 1) * (1.0 / (m + 1)) * 
                DPrime[(S1Val - curBlockBase + 1) * logn + m];
            S1Val++;
            if (S1Val >= n / nToTheHalf){
                S1Mode = 1;
                S1Val = nToTheHalf;
                break;
            }
        }
    }
    if (S1Mode == 1){
        while (n / S1Val <= ceilval){
            for (BigInt m = 1; m < numDPowers; m++) 
                t += (m % 2 == 1 ? -1 : 1) * (1.0 / (m + 1)) * 
                DPrime[(n / S1Val - curBlockBase + 1) * logn + m];
            S1Val--;
            if (S1Val < nToTheThird + 1){
                S1Mode = 2;
                break;
            }
        }
    }
}

/* This loop is calculating the 3rd term that runs from 2 to n^1/3 in 
http://www.icecreambreakfast.com/primecount/primecounting.html#4_4 */
static void calcS2(){
    for (BigInt j = 2; j <= nToTheThird; j++)
        for (BigInt k = 1; k < numDPowers; k++)
            t += (n / j - 1) * pow(-1.0, (double)k) * (1.0 / (k + 1)) * 
            (DPrime[j * logn + k] - DPrime[(j - 1) * logn + k]);
}

/* This loop is calculating the two double sums in 
http://www.icecreambreakfast.com/primecount/primecounting.html#4_4
It is written to rely on values of D_k' from smallest to greatest, 
to use the segmented sieve.*/
static void calcS3(){
    for (BigInt j = 2; j <= nToTheThird; j++){
        if (S3Modes[j] == 0){
            BigInt endsq = (BigInt)(pow(n / j, .5));
            BigInt endVal = (n / j) / endsq;
            while (S3Vals[j] <= ceilval){
                BigInt cnt = (n / (j * S3Vals[j]) - n / (j * (S3Vals[j] + 1)));
                for (BigInt m = 1; m < numDPowers; m++)
                    t += cnt * DPrime[(S3Vals[j] - curBlockBase + 1) * logn + m] * 
                    dPrime[j*(numDPowers + 1)+ m];
                S3Vals[j]++;
                if (S3Vals[j] >= endVal){
                    S3Modes[j] = 1;
                    S3Vals[j] = endsq;
                    break;
                }
            }
        }
        if (S3Modes[j] == 1){
            while (n / (j * S3Vals[j]) <= ceilval){
                for (BigInt m = 1; m < numDPowers; m++) 
                    t += DPrime[(n / (j * S3Vals[j]) - curBlockBase + 1) * logn + m] * 
                    dPrime[j * (numDPowers + 1) + m];
                S3Vals[j]--;
                if (S3Vals[j] < nToTheThird / j + 1){
                    S3Modes[j] = 2;
                    break;
                }
            }
        }
    }
}

/*	This is the most important function here. How it works:
first we allocate our n^1/3 ln n sized pools and other variables.
Then we go ahead and sieve to get our primes up to n^1/3
We also calculate, through one pass of sieving, values of d_k'(n) up to n^1/3
Then we go ahead and calculate the loop S2 (check the description of the algorithm), 
which only requires values of d_k'(n) up to n^1/3, which we already have.
Now we're ready for the main loop.
We do the following roughly n^1/3 times.
First we clear our sieving variables.
Then we factor, entirely, all of the numbers in the current block sized n^1/3 that
we're looking at.
Using our factorization information, we calculate the values for d_k'(n) for the 
entire range we're looking, and then sum those together to have a rolling set 
of D_k'(n) values
Now we have values for D_k'(n) for this block sized n^1/3
First we see if any of the values of S1 that we need to compute are in this block. We 
can do this by (see the paper) walking through the two S1 loops backwards, which 
will use the D_k'(n) values in order from smallest to greatest
We then do the same thing will all of the S3 values
Once we have completed this loop, we will have calculated the prime power function for n.

This loop is essentially calculating
http://www.icecreambreakfast.com/primecount/primecounting.html#4_4
*/

static double calcPrimePowerCount(BigInt nVal){
    n = nVal;
    allocPools(n);
    fillPrimes();
    find_dVals();
    calcS2();
    resetDPrimeVals();

    for (curBlockBase = 0; curBlockBase <= maxSieveValue; curBlockBase += nToTheThird ){
        clearPools();
        factorRange();
        buildDivisorSums();

        ceilval = curBlockBase + nToTheThird - 1;
        if (ceilval > maxSieveValue) {
            ceilval = maxSieveValue;
            ended = true;
        }

        calcS1();
        calcS3();
        if (ended) break;
    }

    deallocPools();

    return t;
}

/*Make sure to read the header comments labeled "ALGORITHM 5", above*/
static BigInt countprimes5(BigInt num) {
    double total = 0.0;
    for (BigInt i = 1; i < log((double)num) / log(2.0); i++) {
        double val = calcPrimePowerCount( invpow(num, i)) / (double)i * mu[i];
        total += val;
    }
    return total+.1;
}