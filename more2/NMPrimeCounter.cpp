/*
Nathan McKenzie
nathan _AT_ icecreambreakfast.com
1-13-2013

This file contains an implemention of a prime counting algorithm and a small test harness for timing its execution.  There are
three main variants to the algorithm.  With default settings, it runs in something like O(n^(4/5)) time and no meaningful runtime memory
usage (aside from a fixed sized 44 Meg Wheel).  The other two variations will be mentioned below.

-------------------------------
    BASIC IDENTITY
-------------------------------

From a theory perspective, the core identity used to count primes here is this:

    (Latex)
    $D_{0,a}(n) = 1$  
    $D_{1,a}(n) = n-a+1$  
    $D_{k,a}(n) = \displaystyle\sum_{j=1}^{k} \binom{k}{j}\sum_{m=a}^{\lfloor n^{\frac{1}{k}}\rfloor}D_{k-j,m+1}(\frac{n}{m^{j}})$  
    $\pi(n) = \displaystyle\sum_{j=1}^{\log_2 n}j^{-1}\mu(j)\sum_{k=1}^{\log_2 n^\frac{1}{j}}{-1}^{k+1} k^{-1}D_{k,2}(n^{\frac{1}{j}})$  
    where  
    $\pi(n)=$#{ $primes <=n$ }  
    $\mu(n)=$Mobius mu function

Set USE_WHEEL to 0 to see this execute.  This approach runs a bit faster than O(n) and uses trivial amounts of memory.  It's much slower.

-------------------------------
    WITH A WHEEL
-------------------------------

To massively speed up execution speed, though, we're going to adjust the above identity by using a wheel (and possibly Legendre's Function Phi)
so that in D, above, we're only going to be iterating over and counting terms that aren't divisible by the first several primes.  When we do that, our identity will become

    (Latex)
    $p = $  the largest prime we are going to sieve with  
    $V = $ the set of whole numbers not divisible by the primes ${2,3,5,...p } $  
    $r(n) = $ the smallest number in $V > n$  
    $\phi(n,k)=$  Legendre's Formula which satisfies:  
        $\phi(n,1)= \lfloor (n+1)/2 \rfloor $ and  
        $\phi(n,k)= \phi(n,k-1) - \phi(n/p_k, k-1)$ where $ p_k$ is the $k^{th}$ prime

    With all that, our new prime counting identity becomes

    $D_{0,a}(n) = 1$  
    $D_{1,a}(n) = \phi(n,\pi(p))-\phi(a,\pi(p))+1$  
    $D_{k,a}(n) = \displaystyle\sum_{j=1}^{k} \binom{k}{j}\sum_{a <= m <= \lfloor n^{\frac{1}{k}}\rfloor, m \in V}D_{k-j,r(m)}(\frac{n}{m^{j}})$  
    $\pi(n) = \pi(p)+\displaystyle\sum_{j=1}^{\log_2 n}j^{-1}\mu(j)\sum_{k=1}^{\log_2 n^\frac{1}{j}}{-1}^{k+1} k^{-1}D_{k,2}(n^{\frac{1}{j}})$  

    where  

    $\pi(n)=$#{ $primes <=n$ }  
    $\mu(n)=$Mobius mu function

It turns out we can use a wheel to handle both $r(n)$ and $\phi(n,k)$, if k isn't too large, or we can build on top of the wheel and calculate the functions more directly.

By default, we will use a wheel but not direct calculation of Phi for execution here.  With these defaults settings, a fixed sized cache of 44 Megs for the wheel
will be allocated at program startup, after which the algorithm will run in something like (empirically) O(n^(4/5)) time and trivial memory usage.  Its constant
time performance is wildly better than the non-wheel version - for instance, for calculating primes <= 10^10, the wheel version is 1200x faster, and that multiplier
difference grows as n does.

If USE_PHI_AND_WHEEL is set to 1, the algorithm will see a significant constant time speed boost (around x5.5 faster than just the wheel version at 10^13) at the 
expense of more complexity and a larger memory footprint - around 500 Megs.

-----------------------------------------
    WORTH EXPLORING
-----------------------------------------

This approach, as written, mostly doesn't do anything smart with memoization.  In particular, almost all execution takes place in the function
below with the signature "long long D( int k, long long a, int numberRangeID, long long n )".  This is our "D_{k,a}" from above. I've yet to find a good way to take 
advantage of caching or storing off values to speed its calculation up, and I've largely exhausted my own ideas on this front.  I keep thinking there
ought to be something fruitful to be done with that function.

This program uses a very naive, simple approach to speeding up calculations of Phi.  It might be an interesting experiment to replace the function "long long Phi( ... )" 
below with some alternative approaches.

Less importantly, the code here is mostly unoptimized, from a bit-twiddling / cache awareness / loop unrolling / hard-coding perspective.  It might be an 
interesting exercise to see how fast it could be made to run by rolling out the usual hardware aware optimizations.

*/

#include "stdlib.h"
#include "math.h"

typedef long long BigInt;

// ___________________________________________________________________________________________________________________________
//
//                                         Configurable Constants
// ___________________________________________________________________________________________________________________________

const int scaleNum =                 10;                     /* For the test harness, the scaling factor from one test to the next */

#define USE_WHEEL                    1                       /* If this is set, a wheel will cause counting to happen only over values not divisible by primes in the wheel.*/
const int wheelLargestPrime =        19;                     /* If a wheel is in use, this value is the largest prime excluded by the wheel.  Note that the wheel will require primorial( wheelLargestPrime ) * 8 bytes of RAM,
                                                                       which very quickly becomes prohibitive.  If wheelLargestPrime is 19, we need 44 Megs of RAM for the wheel, for example, while 23 uses around 900 Megs.*/

#define USE_PHI_AND_WHEEL            0                       /* If set, a wheel will be combined with Legendre's Phi function to cause counting to happen only over values not divisible by selected primes.
                                                                       This allows for numbers divisble by much larger primes to be discarded than the wheel alone.  If set to 1, with default settings, the algorithm 
                                                                       will have a constant time speed improvement of about x7, while using an extra 500 Megs of RAM.*/
const int phiPrimesToSieve =         25;                     /* If USE_PHI_AND_WHEEL is set to 1, no numbers divisble by the first phiPrimesToSieve primes will be considered when calculating D.  Setting this to larger than 167 
                                                                       entries will crash the program currently - make primes[] larger to accomodate higher values.  Note that as implemented, Phi(y,b) uses around 
                                                                       2^(phiPrimesToSieve-wheelBasePrimes) terms in its absolute worst case, so making this value larger can have a significant speed tradeoff.  Smarter implementations of
                                                                       Phi(n) might adjust that tradeoff.*/
const int nonSievedCacheSize =       100000000;              /* If USE_PHI_AND_WHEEL is set to 1, when iterating through a loop of indices that should not be divisble by selected primes, this value determines how many
                                                                       such values should be cached ahead of time and thus quickly looked up.*/
const int phiCacheSize =             5000000;                /* If USE_PHI_AND_WHEEL is set to 1, this deteremines the largest value of Phi that is cached.  The RAM used by this is equal to phiCacheSize*phiPrimesToSieve*4,
                                                                       so be wary of increasing it (or ideally replace it with a much smarter, tighter implementation of Legendre's Phi function.*/

#define D_FULL_RECURSIVE             0                       /* If set, the function D will be calculated without being unrolled.  This could possibly be useful for exploring certain memoization ideas, but without
                                                                       modification it will quickly overflow the stack.*/

const int binomialLayersToCache =    30;                    /* Number of Binomials to cache.  This is probably enough for most values.*/
const double EPSILON =               .00000000001;          /* Added to account for floating point errors when converting from doubles to long longs*/

#define ACTIVE_WHEEL (USE_PHI_AND_WHEEL+USE_WHEEL)

// ___________________________________________________________________________________________________________________________
//
//                                         Cached Variables
// ___________________________________________________________________________________________________________________________

int primes[] = { 0, 2,3,5,7,11,13,17, 19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,
    89,97,101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 
    179, 181, 191, 193, 197, 199, 211, 223, 227, 229, 233, 239, 241, 251, 257, 263, 
    269, 271, 277, 281, 283, 293, 307, 311, 313, 317, 331, 337, 347, 349, 353, 359, 
    367, 373, 379, 383, 389, 397, 401, 409, 419, 421, 431, 433, 439, 443, 449, 457, 
    461, 463, 467, 479, 487, 491, 499, 503, 509, 521, 523, 541, 547, 557, 563, 569, 
    571, 577, 587, 593, 599, 601, 607, 613, 617, 619, 631, 641, 643, 647, 653, 659, 
    661, 673, 677, 683, 691, 701, 709, 719, 727, 733, 739, 743, 751, 757, 761, 769, 
    773, 787, 797, 809, 811, 821, 823, 827, 829, 839, 853, 857, 859, 863, 877, 881, 
    883, 887, 907, 911, 919, 929, 937, 941, 947, 953, 967, 971, 977, 983, 991, 997, 1009  };

// This is the Moebius Mu function.  We need values of this up to log( n ) / log( firstNonSieveEntry ),
// which won't generally be too large.
BigInt mu[] = { 0, 1, -1, -1, 0, -1, 1, -1, 0, 0, 1, -1, 0, -1, 1, 1, 0, -1, 0, 
    -1, 0, 1, 1, -1, 0, 0, 1, 0, 0, -1, -1, -1, 0, 1, 1, 1, 0, -1, 1, 1, 0, -1, -1, -1,
    0, 0, 1, -1, 0, 0, 0, 1, 0, -1, 0, 1, 0, 1, 1, -1, 0, -1, 1, 0, 0, 1, -1 };

int primesToSieve, firstNonSieveEntry;

// ___________________________________________________________________________________________________________________________
//
//                                         Binomial Coefficients
// ___________________________________________________________________________________________________________________________

long long binomial[binomialLayersToCache][binomialLayersToCache];
void MakeBinomial(){
    printf(" * Caching binomials\n");
    for( int k = 0; k < binomialLayersToCache; k++ ){
        for( int j = 0; j <= k; j++ ){ 
            double m = 1;
            for( double i = 1; i <= j; i++ )m *= ( k - ( j - i ) ) / i;
            binomial[ k ][ j ] = long long( m + .5 );
        }
    }
}

// ___________________________________________________________________________________________________________________________
//
//                                         Wheel
// ___________________________________________________________________________________________________________________________

#if ACTIVE_WHEEL
int wheelCycleEntries, wheelCyclePeriod, wheelFirstPrime, wheelBasePrimes;
int *wheelTranslation = 0, *wheelOffsets = 0;

void MakeWheel(){
    printf(" * Building wheel\n");
    wheelBasePrimes = 1;
    while( primes[ wheelBasePrimes ] <= wheelLargestPrime )wheelBasePrimes++;
    wheelCyclePeriod = 1;
    int i = 1;
    while( primes[ i ] <= wheelLargestPrime ){
        wheelCyclePeriod *= primes[ i ];
        i++;
    }
    wheelCycleEntries = 0;

    int cur = 0, offset = -1, *wheelBase = 0;

    wheelBase = ( int* )malloc( wheelCyclePeriod * sizeof( int ) );
    wheelTranslation = ( int* )malloc( ( wheelCyclePeriod + 1 ) * sizeof( int ) );
    wheelOffsets = ( int * )malloc( wheelCyclePeriod * sizeof( int ) );
    i = 1;
    while( primes[ i ] <= wheelLargestPrime )i++;
    wheelFirstPrime = primes[ i ];

    for( int i = 0; i < wheelCyclePeriod; i++ ){
        wheelBase[ i ] = 1;
        for( int j = 2; j <= wheelLargestPrime; j++ ){
            if( !( ( i + 1 ) % j ) ){
                wheelBase[ i ] = 0;
                break;
            }
        }
    }
    while( cur < wheelCyclePeriod ){
        if( wheelBase[ cur ] && cur != 0 ){
            wheelOffsets[ wheelCycleEntries ] = offset + 1;
            offset = 0;
            wheelCycleEntries++;
        }
        else offset++;
        cur++;
    }
    wheelOffsets[ wheelCycleEntries ] = 2;
    wheelCycleEntries++;	
    int total = 0;
    wheelTranslation[ 0 ] = 0;
    for( BigInt i = 0; i < wheelCyclePeriod; i++ ){
        if( i && wheelBase[ i - 1 ] )total++;
        wheelTranslation [ i + 1 ] = total;
    }
    free( wheelBase );
}
inline void IncrementWheel( int &numberRangeID ){
    numberRangeID++;
    if( numberRangeID >= wheelCycleEntries )numberRangeID = 0;
}
inline BigInt WheelEntriesForRange( BigInt rangeEnd ){
    rangeEnd++;
    int b = rangeEnd % wheelCyclePeriod;
    return ( rangeEnd - b ) / wheelCyclePeriod * wheelCycleEntries + wheelTranslation[ b ];
}
#else
inline void MakeWheel(){}
#endif

// ___________________________________________________________________________________________________________________________
//
//                            Counting Non-Sieved Entries in a Range of Numbers
//
//	Given a range of numbers between 1 and n, inclusive, how many entries are there that aren't divisible by any of the
//	primes we're sieving away?  That's what the function GetRange calculates for us.  If we're just using a wheel, we use
//	the wheel to calculate that for us.  But we can also use an implemention of Legendre's Formula Phi to sieve with many
//	more primes.  The implementation of Phi here is pretty naive and simple.  One possibly interesting task would be
//	to replace this implementation of Phi with something substantially more optimized in an effort to allow us to push
//	primesToSieve up to larger values.
// ___________________________________________________________________________________________________________________________

#if USE_PHI_AND_WHEEL
int** phiCache = 0;
void MakeRangeCache(){
    printf(" * Caching Phi\n");
    primesToSieve = phiPrimesToSieve;
    firstNonSieveEntry = primes[primesToSieve+1]; 
    int firstNonSieveEntry = primes[primesToSieve+1]; 
    phiCache = new int*[ primesToSieve + 1 ];
    for( int i = 0; i <= primesToSieve; i++ ){
        phiCache[i] = new int[ phiCacheSize ];
        for( int j = 0; j < phiCacheSize; j++ )phiCache[i][j] = j;
    }
    for( int j = 0; j < phiCacheSize; j++ )phiCache[0][j] = j;
    for( int j = 0; j < phiCacheSize; j++ )phiCache[1][j] = (j+1)/2;
    for( int i = 2; i <= primesToSieve; i++ )for( int j = 0; j < phiCacheSize; j++ )phiCache[i][j] = phiCache[i-1][j] - phiCache[i-1][j/primes[i]];
}
long long Phi( long long y, int b ){
    if( b == 8 )return WheelEntriesForRange( y );
    if( b == 1 )return (y+1)/2;
    if( y < 1 )return 0;
    if( y < phiCacheSize )return phiCache[ b ][ y ];
    return Phi( y, b-1) - Phi( y/primes[b], b-1 );
}
inline long long GetRange( long long y ){
    return Phi( y, primesToSieve );
}

#else 
#if USE_WHEEL

void MakeRangeCache(){ 
    firstNonSieveEntry = wheelFirstPrime; 
    primesToSieve = wheelBasePrimes - 1;
}
long long GetRange( long long y ){
    return WheelEntriesForRange( y );
}

#else

void MakeRangeCache(){ 
    firstNonSieveEntry = 2; 
    primesToSieve = 0;
}
long long GetRange( long long y ){
    return y;
}

#endif
#endif

// ___________________________________________________________________________________________________________________________
//
//                  Forward Iterating Through Non-Sieved Entries in a Range of Numbers
//
//	In our function D, for values of k > 1, we have to execute a loop over an integer.  That integer should only
//	be taking on values that are not divisible by any of the primes we're sieving out.  If we're just using a wheel, we can
//	use the wheel to make sure we're only taking on appropriate values.  If we're using a wheel combined with Legendre's
//	Phi function, we'll need a way to make sure that we're only selecting appropriate values.  The functions below handle
//	that in a non-complicated way.
// ___________________________________________________________________________________________________________________________

#if USE_PHI_AND_WHEEL

int* nonSievedCache = 0;
int lastNonSievedCacheEntry = 0;
inline void NextNonSieved( long long& n, int& numberRangeID ){
    bool redo;
    do{
        n += wheelOffsets[ numberRangeID ];
        IncrementWheel( numberRangeID );
        redo = false;
        for( int i = wheelBasePrimes; i <= primesToSieve; i++ ){
            if( n % primes[i] == 0 ){ 
                redo = true; 
                break; 
            } 
        }
    }while( redo );
}
void MakeIncrementCache(){
    printf(" * Making Increment cache\n");
    nonSievedCache = new int[ Phi( nonSievedCacheSize, primesToSieve )+1 ];
    lastNonSievedCacheEntry = 0;
    int cur = 0;
    long long n; int numberRangeID;
    n = firstNonSieveEntry;
    numberRangeID = wheelTranslation[ n % wheelCyclePeriod ];
    while( n < nonSievedCacheSize ){
        NextNonSieved( n, numberRangeID );
        nonSievedCache[ cur ] = n;
        cur++;
    }
    lastNonSievedCacheEntry = -cur;
}
inline void IncrementNumber( long long &n, int &numberRangeID ){
    if( numberRangeID < 1 ){
        n = nonSievedCache[ -numberRangeID ];
        numberRangeID--;
        if( numberRangeID == lastNonSievedCacheEntry )numberRangeID = wheelTranslation[ n % wheelCyclePeriod ];
        return;}
    NextNonSieved( n, numberRangeID );
}

#else
#if USE_WHEEL

void MakeIncrementCache(){}
inline void IncrementNumber( long long &n, int &numberRangeID ){
    IncrementWheel( numberRangeID );
    n += wheelOffsets[ numberRangeID ];
}

#else

void MakeIncrementCache(){}
inline void IncrementNumber( long long &n, int &numberRangeID ){
    n++;
}

#endif
#endif

// ___________________________________________________________________________________________________________________________
//
//                                Prime Counting Function
//                                                                    
// ___________________________________________________________________________________________________________________________

#if D_FULL_RECURSIVE
long long D( int k, long long a, int numberRangeID, long long n ){
    if( k == 0 )return 1; 
    if( k == 1 )return GetRange( n ) - GetRange( a )+1;
    if( pow( a, (double)k ) > n )return 0;
    long long t = 0, nn = n, pa = a;
    IncrementNumber( a, numberRangeID );
    t += binomial[k][k];
    for( int j = 0; j < k; j++ ){
        t += D( k-j, a, numberRangeID, nn )*binomial[k][j];
        nn /= pa;
    }
    return t;
}
#else

/* Note for attempts at caching and memoizing : specific values of numberRangeID will always be paired with specific values of
"a".  It's just a helper variable for handling the wheel, and can be disregarded entirely for caching.  It is safe just to store off D( int k, long long a, long long n )*/
long long D( int k, long long a, int numberRangeID, long long n ){
    if( k == 0 )return 1; 
    if( k == 1 )return GetRange( n ) - GetRange( a )+1;
    long long t = 0;
    while( a <= pow(n, 1.0 / k) + EPSILON ){
        long long nn = n/a;
        long long pa = a;
        IncrementNumber( a, numberRangeID );
        t += binomial[k][k];
        for( int j = 1; j < k; j++ ){
            t += D( k-j, a, numberRangeID, nn )*binomial[k][j];
            nn /= pa;
        }
    }
    return t;
}

#endif

long long CountPrimes(long long n){ 
    double t = 0.0; 
    for (int j = 1; j < log((double)n) / log((double)firstNonSieveEntry); j++)
        for (int k = 1; k < log( pow( n, 1.0 / j ) ) / log((double)firstNonSieveEntry); k++)
            t += pow( -1.0, (double)k + 1 ) * D(k, firstNonSieveEntry, 0, long long( pow(n, 1.0 / j) + EPSILON ) ) / k / j * mu[j];
    return t + .5 + primesToSieve;
}

// ___________________________________________________________________________________________________________________________
//
//                                    Timing Harness
//
//	This is a timing test harness to evaluate the speed of CountPrimes.
// ___________________________________________________________________________________________________________________________

#include "conio.h"
#include "time.h"
#include "stdio.h"

void printSpaces( char* str ){
    printf("                                                                    %s", str);
}

int main(int argc, char* argv[]){
    MakeBinomial();
    MakeWheel();
    MakeRangeCache();
    MakeIncrementCache(); 

    printf("\n\n");

    int oldClock = (int)clock(), lastDif = 0;
    printSpaces("Time\n");
    printSpaces("Increase\n");
    printSpaces("");
    printf( "for x%d\n", scaleNum);
    printf( "         __ Input Number __   __ Output Number __ _ MSec _ _ Sec _  Input\n\n");
    for( BigInt i = scaleNum; i <= 1000000000000000000; i *= scaleNum ){
        printf( "%17I64d(10^%4.1f): ", i, log( (double)i )/log(10.0) );

        BigInt total = CountPrimes( i );

        int newClock = (int)clock();
        printf( " %20I64d %8d : %4d: x%f\n", total, newClock - oldClock, ( newClock - oldClock ) / CLK_TCK,
            ( lastDif ) ? (double)( newClock - oldClock ) / (double)lastDif : 0.0 );
        lastDif = newClock - oldClock;
        oldClock = newClock;
    }

    getch();
    return 0;
}