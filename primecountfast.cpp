#include "stdio.h"
#include "stdlib.h"
#include "math.h"
#include "conio.h"
#include "time.h"
typedef long long BigInt;
 
static BigInt mu[] = { 0, 1, -1, -1, 0, -1, 1, -1, 0, 0, 1, -1, 0, -1, 1, 1, 0, -1, 0, -1, 0, 1, 1, -1, 0, 0, 1, 0, 0, -1, -1, -1,
    0, 1, 1, 1, 0, -1, 1, 1, 0, -1, -1, -1, 0, 0, 1, -1, 0, 0, 0, 1, 0, -1, 0, 1, 0, 1, 1, -1, 0, -1, 1, 0, 0, 1, -1, -1, 0, 1, -1,
    -1, 0, -1, 1, 0, 0, 1, -1, -1, 0, 0 };
 
static BigInt* binomials;       /* This is used as a doubly subscripted array, 128x128.  Indexing is done manually.*/
static BigInt nToTheThird;
static BigInt logn;
 
static BigInt numPrimes;
static BigInt* primes;
 
static BigInt* factorsMultiplied;
static BigInt* totalFactors;
static BigInt* factors;         /* This is used as a doubly subscripted array, n^1/3 x ln n.  Indexing is done manually.*/
static BigInt* numPrimeBases;
 
static BigInt* DPrime;          /* This is used as a doubly subscripted array, n^1/3 x ln n.  Indexing is done manually.*/
 
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
 
/* See http://www.icecreambreakfast.com/primecount/primecounting.html#ch5 for a description of
calculating d_k'(n) from a complete factorization of a number n.*/
static BigInt d1(BigInt* a, BigInt o, BigInt k, BigInt l){
    BigInt t = 1;
    for (BigInt j = 0; j < l; j++) t *= binomials[(a[o*logn+ j] - 1 + k)*128 + a[o*logn+ j]];
    return t;
}
 
/* See http://www.icecreambreakfast.com/primecount/primecounting.html#ch5 for a description of
calculating d_k'(n) from a complete factorization of a number n.*/
static BigInt d2(BigInt* a, BigInt o, BigInt k, BigInt l, BigInt numfacts ){
    if (numfacts < k) return 0;
    BigInt t = 0;
    for (BigInt j = 1; j <= k; j++) t += ( ( k - j ) % 2 == 1 ? -1:1 ) * binomials[k * 128 + j] * d1(a, o, j, l);
    if( t < 0 ){
        int asdf  = 9;
    }
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
    for (BigInt j = 0; j < 128; j++) for (BigInt k = 0; k <= j; k++)binomials[j * 128 + k] = binomial(j, k);
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
 
/* This finds all the primes less than n^1/3, which will be used for sieving and generating complete factorizations of numbers up to n^2/3*/
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
 
/* This resets some state used for the sieving and factoring process.*/
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
        // mark everything divided by each prime, adding a new entry.
        BigInt curPrime = primes[j];
        if (curPrime * curPrime > curBlockBase + nToTheThird) break;
        BigInt curEntry = ( curBlockBase % curPrime == 0 ) ? 0:curPrime - (curBlockBase % curPrime);
        while (curEntry < nToTheThird){
            if( curEntry+curBlockBase != 0 ){
                factorsMultiplied[curEntry] *= curPrime;
                totalFactors[curEntry]++;
                numPrimeBases[curEntry]++;
                factors[curEntry*logn+ numPrimeBases[curEntry]] = 1;
            }
            curEntry += curPrime;
        }
        // mark everything divided by each prime power
        BigInt cap = (BigInt)( log((double)(nToTheThird+curBlockBase)) / log((double)curPrime) + 1 );
        BigInt curbase = curPrime;
        for (BigInt k = 2; k < cap; k++){
            curPrime *= curbase;
            curEntry = (curBlockBase % curPrime == 0) ? 0 : curPrime - (curBlockBase % curPrime);
            while (curEntry < nToTheThird){
                factorsMultiplied[curEntry] *= curbase;
                totalFactors[curEntry]++;
                if (curEntry + curBlockBase != 0)factors[curEntry*logn+ numPrimeBases[curEntry]] = k;
                curEntry += curPrime;
            }
        }
    }
    // account for prime factors > n^1/3
    for (BigInt j = 0; j < nToTheThird; j++){
        if (factorsMultiplied[j] < j+curBlockBase){
            numPrimeBases[j]++;
            totalFactors[j]++;
            factors[j*logn+ numPrimeBases[j]] = 1;
        }
    }
}
 
/* By this point, we have already factored, through sieving, all the numbers in the current n^1/3 sized block we are looking at.
With a complete factorization, we can calculate d_k'(n) for a number.
Then, D_k'(n) = d_k'(n) + D_k'(n-1).*/
static void buildDivisorSums(){
    for (BigInt j = 1; j < nToTheThird+1; j++){
        if (j + curBlockBase == 1 || j + curBlockBase == 2) continue;
        for (BigInt k = 0; k < logn; k++){
            DPrime[j * logn + k] = DPrime[(j - 1) * logn + k] + d2(factors, j - 1, k, numPrimeBases[j - 1] + 1, totalFactors[j - 1]);
        }
    }
    for (BigInt j = 0; j < logn; j++) DPrime[j] = DPrime[nToTheThird*logn+ j];
}
 
/* This general algorithm relies on values of D_k' <= n^2/3 and d_k' <= n^1/3.  This function calculates those values of d_k'.*/
static void find_dVals(){
    curBlockBase = 1;
    clearPools();
    factorRange();
    buildDivisorSums();
 
    for (BigInt j = 2; j <= nToTheThird; j++){
        for (BigInt m = 1; m < numDPowers; m++){
            double s = 0;
            for (BigInt r = 1; r < numDPowers; r++) s += pow(-1.0, (double)( r + m )) * (1.0 / (r + m + 1)) * (DPrime[j * logn + r] - DPrime[(j - 1) * logn + r]);
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
 
/* This function is calculating the first two sums of http://www.icecreambreakfast.com/primecount/primecounting.html#4_4
It is written to rely on values of D_k' from smallest to greatest, to use the segmented sieve.*/
static void calcS1(){
    if (S1Mode == 0){
        while (S1Val <= ceilval){
            BigInt cnt = (n / S1Val - n / (S1Val + 1));
            for (BigInt m = 1; m < numDPowers; m++) t += cnt * (m % 2 == 1 ? -1 : 1) * (1.0 / (m + 1)) * DPrime[(S1Val - curBlockBase + 1) * logn + m];
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
            for (BigInt m = 1; m < numDPowers; m++) t += (m % 2 == 1 ? -1 : 1) * (1.0 / (m + 1)) * DPrime[(n / S1Val - curBlockBase + 1) * logn + m];
            S1Val--;
            if (S1Val < nToTheThird + 1){
                S1Mode = 2;
                break;
            }
        }
    }
}
 
/* This loop is calculating the 3rd term that runs from 2 to n^1/3 in http://www.icecreambreakfast.com/primecount/primecounting.html#4_4*/
static void calcS2(){
    for (BigInt j = 2; j <= nToTheThird; j++)
        for (BigInt k = 1; k < numDPowers; k++)
            t += (n / j - 1) * pow(-1.0, (double)k) * (1.0 / (k + 1)) * (DPrime[j * logn + k] - DPrime[(j - 1) * logn + k]);
}
 
/* This loop is calculating the two double sums in http://www.icecreambreakfast.com/primecount/primecounting.html#4_4
It is written to rely on values of D_k' from smallest to greatest, to use the segmented sieve.*/
static void calcS3(){
    for (BigInt j = 2; j <= nToTheThird; j++){
        if (S3Modes[j] == 0){
            BigInt endsq = (BigInt)(pow(n / j, .5));
            BigInt endVal = (n / j) / endsq;
            while (S3Vals[j] <= ceilval){
                BigInt cnt = (n / (j * S3Vals[j]) - n / (j * (S3Vals[j] + 1)));
                for (BigInt m = 1; m < numDPowers; m++) t += cnt * DPrime[(S3Vals[j] - curBlockBase + 1) * logn + m] * dPrime[j*(numDPowers + 1)+ m];
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
                for (BigInt m = 1; m < numDPowers; m++) t += DPrime[(n / (j * S3Vals[j]) - curBlockBase + 1) * logn + m] * dPrime[j * (numDPowers + 1) + m];
                S3Vals[j]--;
                if (S3Vals[j] < nToTheThird / j + 1){
                    S3Modes[j] = 2;
                    break;
                }
            }
        }
    }
}
 
/*  This is the most important function here. How it works:
*    first we allocate our n^1/3 ln n sized pools and other variables.
*    Then we go ahead and sieve to get our primes up to n^1/3
*    We also calculate, through one pass of sieving, values of d_k'(n) up to n^1/3
*    Then we go ahead and calculate the loop S2 (check the description of the algorithm), which only requires
*    values of d_k'(n) up to n^1/3, which we already have.
*    Now we're ready for the main loop.
*    We do the following roughly n^1/3 times.
*    First we clear our sieving variables.
*    Then we factor, entirely, all of the numbers in the current block sized n^1/3 that we're looking at.
*    Using our factorization information, we calculate the values for d_k'(n) for the entire range we're looking,
*    and then sum those together to have a rolling set of D_k'(n) values
*    Now we have values for D_k'(n) for this block sized n^1/3
*    First we see if any of the values of S1 that we need to compute are in this block. We can do this by
*    (see the paper) walking through the two S1 loops backwards, which will use the D_k'(n)
*    values in order from smallest to greatest
*    We then do the same thing will all of the S3 values
*    Once we have completed this loop, we will have calculated the prime power function for n.
*  
*   This loop is essentially calculating
*   http://www.icecreambreakfast.com/primecount/primecounting.html#4_4
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
 
static BigInt countprimes(BigInt num) {
    double total = 0.0;
    for (BigInt i = 1; i < log((double)num) / log(2.0); i++) {
        double val = calcPrimePowerCount( invpow(num, i)) / (double)i * mu[i];
        total += val;
    }
    return total+.1;
}
 
int scaleNum = 10;
int main(int argc, char* argv[]){
    int oldClock = (int)clock();
    int lastDif = 0;
 
    printf( "                                                                    Time\n");
    printf( "                                                                    Increase\n");
    printf( "                                                                    for x%d\n", scaleNum);
    printf( "         __ Input Number __   __ Output Number __ _ MSec _ _ Sec _  Input\n");
    printf( "                                                                    \n");
    for( BigInt i = scaleNum; i <= 1000000000000000000; i *= scaleNum ){
        printf( "%17I64d(10^%4.1f): ", i, log( (double)i )/log(10.0) );
        BigInt total = (BigInt)(countprimes( i )+.00001);
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
