/*
This file implements the prime counting algorithm described by the formulas (in Latex):
	$D_{0,a}(n) = 1$  
	$D_{1,a}(n) = n-a+1$  
	$D_{k,a}(n) = \displaystyle\sum_{j=1}^{k} \binom{k}{j}\sum_{m=a}^{\lfloor n^{\frac{1}{k}}\rfloor}D_{k-j,m+1}(\frac{n}{m^{j}})$  
	$\pi(n) = \displaystyle\sum_{j=1}^{\log_2 n}j^{-1}\mu(j)\sum_{k=1}^{\log_2 n^\frac{1}{j}}{-1}^{k+1} k^{-1}D_{k,2}(n^{\frac{1}{j}})$

Empirically, this algorithm seems to run a bit faster than O(n) time and O(log n) space.

Nathan McKenzie
12-21-2012
nathan@icecreambreakfast.com
*/

//_________________________________ Algorithm Implementation____________________________

#include "math.h"
long long binomial[30][30];
double d( long long n, int k, long long a ){ 
   if( k == 0 )return 1; 
   if( k == 1 )return n - a + 1;
   double t = 0;
   for( long long m = a; m <= pow(n, 1.0 / k) + .0000001; m++ )
      for( int j = 1; j <= k; j++ )
         t += d( n / pow( (double)m, j ), k-j, m+1 )*binomial[k][j];
   return t;
}
long long pi(long long n){ 
   int mu[] = { 0, 1, -1, -1, 0, -1, 1, -1, 0, 0, 1, -1, 0, -1, 1, 1, 0, -1, 0,  -1, 0,
      1, 1, -1, 0, 0, 1, 0, 0, -1, -1, -1, 0, 1, 1, 1, 0, -1, 1, 1, 0, -1, -1, -1,0, 0, 
      1, -1, 0, 0, 0, 1, 0, -1, 0, 1, 0, 1, 1, -1, 0, -1, 1, 0, 0, 1, -1 };
   // Cache our binomials.
   for( int k = 1; k < 30; k++ )
      for( int j = 1; j <= k; j++ ){ 
         double m = 1;
         for( double i = 1; i <= j; i++ )m *= ( k - ( j - i ) ) / i;
         binomial[ k ][ j ] = long long( m + .0000001 );
	  }
   // Run the actual prime counting algorithm
   double t = 0.0; 
   for (int j = 1; j < log((double)n) / log(2.0); j++)
      for (int k = 1; k < log( pow( n, 1.0 / j ) ) / log(2.0); k++)
         t += pow( -1.0, k + 1 ) * d(pow(n, 1.0 / j) + .0000001, k, 2 ) / k / j * mu[j];
   return t + .001;
}

//_________________________________ Timing Harness ____________________________

#include "stdio.h"
#include "time.h"
int scaleNum = 10;
void printSpaces( char* str ){
	printf("                                                                    %s", str);
}
int timeAlgorithm(){
    int oldClock = (int)clock(), lastDif = 0;
    printSpaces("Time\n");
    printSpaces("Increase\n");
    printSpaces("");
    printf( "for x%d\n", scaleNum);
    printf( "         __ Input Number __   __ Output Number __ _ MSec _ _ Sec _  Input\n\n");
    for( long long i = scaleNum; i <= 1000000000000000000; i *= scaleNum ){
        printf( "%17I64d(10^%4.1f): ", i, log( (double)i )/log(10.0) );

        long long total = pi( i );

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