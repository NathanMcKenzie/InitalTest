/*
This file implements the prime counting algorithm described by the formulas (in Latex):
	$D_{0,a}(n) = 1$  
	$D_{k,a}(n) = \displaystyle\sum_{j=1}^{k} \binom{k}{j}\sum_{m=a+1}^{\lfloor n^{\frac{1}{k}}\rfloor}D_{k-j,m}(\frac{n}{m^{j}})$  
	$\pi(n) = \displaystyle\sum_{j=1}^{\log_2 n}j^{-1}\mu(j)\sum_{k=1}^{\log_2 n^\frac{1}{j}}{-1}^{k+1} k^{-1}D_{k,1}(n^{\frac{1}{j}})$

Three things are done to speed up its execution time.  
1) It uses a wheel, so, in the equations above, it excludes values of m divisible by any prime < 23.
2) The calculation of the binomials is handled somewhat more subtly to reduce their run time performance.  
  The variables "permutations" and "repeats" handle this.  It amounts to the same calculation as the equation
  above, but in a more integrated fashion.
3) It combines, specializes, and reduces some of these function values for significant speed gains.  In
practice, that means the above identity is transformed into a somewhat more baroque form.

After these changes, it looks like this, in Latex:

$w(a,b) =$ count of numbers between a and b, including b, not divisible by our wheel  
$v(a,b) =$ the set of numbers between a and b, including b, not divisible by our wheel  
$D_{1,a}(n,p,r) = w(a,n)$  
$D_{2,a}(n,p,r) = \frac{p}{(r+1)(r+2)} + (w(a,\frac{n}{a})-1)(\frac{p}{r+1}) + (w(a,\lfloor n^\frac{1}{2} \rfloor)-1)(\frac{p}{2}) +p \cdot \displaystyle\sum_{m\in v(a+1,\lfloor n^\frac{1}{2} \rfloor ) } w(m,\frac{n}{m}) - 1$  
$D_{k,a}(n,p,r) = D_{k-1,a}(\frac{n}{a}, \frac{p}{r+1}, r+1)+\displaystyle\sum_{m\in v(a+1,\lfloor n^{\frac{1}{k}}\rfloor)}D_{k-1,m}(\frac{n}{m},p,1)$  
$\pi(n) = \displaystyle\sum_{j=1}^{\log_2 n}j^{-1}\mu(j)\sum_{k=1}^{\log_2 n^\frac{1}{j}}{-1}^{k+1} k^{-1}D_{k,2}(n^{\frac{1}{j}}, k!, 0)$

Empirically, this algorithm seems to run in around O(n^{4/5}) time and O(log n) space.

Nathan McKenzie
12-20-2012
nathan@icecreambreakfast.com
*/

#include "stdio.h"
#include "stdlib.h"
#include "math.h"
#include "time.h"

typedef long long BigInt;

const int wheelLargestPrime = 19;
const int scaleNum = 10;
const double EPSILON = .00000000001;

const BigInt factorial[] = { 0, 1, 2, 6, 24, 120, 720, 5040, 40320, 362880, 3628800, 39916800, 479001600, 6227020800, 87178291200, 
	1307674368000, 20922789888000, 355687428096000, 6402373705728000, 121645100408832000, 2432902008176640000
};

int wheelCycleEntries, wheelCyclePeriod, wheelFirstPrime, wheelBasePrimes;
int *wheelTranslation = 0, *wheelOffsets = 0;
void MakeWheel(){
	int primes[] ={ 2, 3, 5, 7, 11, 13, 17, 19, 23, 29 };
	wheelBasePrimes = 0;
    while( primes[ wheelBasePrimes ] <= wheelLargestPrime )wheelBasePrimes++;
	wheelCyclePeriod = 1;
    int i = 0;
    while( primes[ i ] <= wheelLargestPrime ){
        wheelCyclePeriod *= primes[ i ];
        i++;
    }
    wheelCycleEntries = 0;

    int cur = 0, offset = -1, *wheelBase = 0;

    wheelBase = ( int* )malloc( wheelCyclePeriod * sizeof( int ) );
    wheelTranslation = ( int* )malloc( ( wheelCyclePeriod + 1 ) * sizeof( int ) );
    wheelOffsets = ( int * )malloc( wheelCyclePeriod * sizeof( int ) );
	i = 0;
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
inline void IncrementWheel( int &offset ){
    offset++;
    if( offset >= wheelCycleEntries )offset = 0;
}
/* This function calculates how many entries the wheel leaves in the range from (rangeStart, rangeStop].*/
inline BigInt CountWheelEntries( BigInt rangeStart, BigInt rangeEnd ){
    rangeEnd++;
    int a = rangeStart % wheelCyclePeriod;
    int b = rangeEnd % wheelCyclePeriod;
    return ( rangeEnd - b - rangeStart + a ) / wheelCyclePeriod * wheelCycleEntries + wheelTranslation[ b ] - wheelTranslation[ a ] ;
}
inline BigInt InversePower( BigInt x, BigInt y ){
    return ( (BigInt)( pow( (double)x + EPSILON, ( 1.0 / (double)y ) ) + EPSILON ) );
}
BigInt total, _m, _n, _permutations,_repeats;
void D_2( void ){
    BigInt n = _n / _m;
    BigInt max_m = (BigInt)( sqrt( (double)n ) + EPSILON );

    /* For if the final two numbers happen to be the same as leading one. */
    total += _permutations / ( (_repeats+1) * ( _repeats + 2 ) );
    /* Leading number is same as previous one, final number is not. */
    total += ( CountWheelEntries( _m, n / _m ) - 1 ) * ( _permutations / (_repeats+1) );
    /* For if the final two numbers happen to be the same, but both differ from the leading one. */
    total += ( CountWheelEntries( _m, max_m ) - 1 ) * ( _permutations / 2 );
    /* Both numbers differ from leading number and each other */
    int curWheelOffset = wheelTranslation[ _m % wheelCyclePeriod ];
    BigInt m = _m + wheelOffsets[ curWheelOffset ];
    BigInt subTotal = 0;
    IncrementWheel( curWheelOffset );
    while( m <= max_m ){
        subTotal += CountWheelEntries( m, n / m ) - 1;
        m += wheelOffsets[ curWheelOffset ];
        IncrementWheel( curWheelOffset );
    }
    total += subTotal * _permutations;
}
/*We're using a few globals in D_2 to avoid pushing and popping to the stack, because D_2 executes so
frequently, so D_3 has to set up those globals.*/
void D_3( BigInt n, BigInt a, BigInt permutations, BigInt repeats ){
    BigInt max_m = InversePower( n, 3 );

	int curWheelOffset = wheelTranslation[ a % wheelCyclePeriod ];
    _n = n;
    _m = a;
    _permutations = permutations / (repeats+1);
    _repeats = repeats + 1;
    D_2();

    _m += wheelOffsets[ curWheelOffset ];
    IncrementWheel( curWheelOffset );
    _permutations = permutations;
    _repeats = 1;
    while( _m <= max_m ){
        D_2();
        _m += wheelOffsets[ curWheelOffset ];
        IncrementWheel( curWheelOffset );
    }
}
void D_k( BigInt n, BigInt m, BigInt permutations, BigInt repeats, int k ){
    BigInt max_m = InversePower( n, k );

    int curWheelOffset = wheelTranslation[ m % wheelCyclePeriod ];
    if( k == 4 )D_3( n / m, m, permutations / (repeats+1), repeats + 1 );
    else D_k( n / m, m, permutations / (repeats+1), repeats + 1, k-1 );

    m += wheelOffsets[ curWheelOffset ];
    IncrementWheel( curWheelOffset );
    while( m <= max_m ){
        if( k == 4 )D_3( n / m, m, permutations, 1 );
        else D_k( n / m, m, permutations, 1, k-1 );
        m += wheelOffsets[ curWheelOffset ];
        IncrementWheel( curWheelOffset );
    }
}
BigInt D( BigInt n, int k ){
    if( n < (BigInt)pow( (double)wheelFirstPrime, (double)k ) )return 0;

    total = 0;
    switch( k ){
    case 1:
        total = CountWheelEntries( wheelFirstPrime, n );
        break;
    case 2:
        /* D_2 expects global variables to be initialized when it is called, which generally happens in D_3.  We do it manually here. */
        _m = wheelFirstPrime;
        _n = wheelFirstPrime * n;
        _permutations = 2;
        _repeats = 0;
        D_2();
        break;
    case 3:
        D_3( n, wheelFirstPrime, factorial[k], 0 );
        break;
    default:
        D_k( n, wheelFirstPrime, factorial[k], 0, k );
        break;
    }
    return total;
}
BigInt countPrimes( BigInt n ){
	int mu[] = { 0, 1, -1, -1, 0, -1, 1, -1, 0, 0, 1, -1, 0, -1, 1, 1, 0, -1, 0, -1, 0, 1, 1, -1, 0, 0, 1, 0, 0, 
		-1, -1, -1, 0, 1, 1, 1, 0, -1, 1, 1, 0, -1, -1, -1, 0, 0, 1, -1, 0, 0, 0, 1, 0, -1, 0, 1, 0, 1, 1, -1, 0, -1, 1, 0, 0, 1, -1 };
    int maxj = ( int )( log( ( double )n + EPSILON ) / log ( ( double )wheelFirstPrime + EPSILON ) + EPSILON ) + 1;
    double total = wheelBasePrimes;
    for( int j = 1; j < maxj; j++ ){
        if( !mu[ j ] )continue;
        BigInt curN = InversePower( n, j );
		BigInt dval = 1;
		for( int k = 1; dval != 0; k++ ){
			dval = D( curN, k );
			total += dval * pow( -1.0, k+1 ) * mu[j] / j  / k;
		}
    }
    return (BigInt)( total + 0.5 );
}


void printSpaces( char* str ){
	printf("                                                                    %s", str);
}
int timeAlgorithm(){
	MakeWheel();
    int oldClock = (int)clock(), lastDif = 0;
    printSpaces("Time\n");
    printSpaces("Increase\n");
    printSpaces("");
    printf( "for x%d\n", scaleNum);
    printf( "         __ Input Number __   __ Output Number __ _ MSec _ _ Sec _  Input\n\n");
    for( BigInt i = scaleNum; i <= 1000000000000000000; i *= scaleNum ){
        printf( "%17I64d(10^%4.1f): ", i, log( (double)i )/log(10.0) );
        
		BigInt total = countPrimes( i );

        int newClock = (int)clock();
        printf( " %20I64d %8d : %4d: x%f\n", total, newClock - oldClock, ( newClock - oldClock ) / CLK_TCK,
            ( lastDif ) ? (double)( newClock - oldClock ) / (double)lastDif : 0.0 );
        lastDif = newClock - oldClock;
        oldClock = newClock;
    }
    return 0;
}
int main(int argc, char* argv[]){
	timeAlgorithm();
	return 0;
}