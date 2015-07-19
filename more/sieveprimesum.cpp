#include "math.h"
#include "conio.h"

typedef long long BigInt;

int main(void)
{
	bool* ps = new bool[100000001];
	BigInt* sums = new BigInt[100000001];
	for (int vv = 0; vv <= 100000000; vv++) { 
		ps[vv] = true; 
		sums[vv] = 0; 
	}

	for (int j = 2; j <= pow(100000000, .5); j++)
	{
		if (ps[j] == true)
		{
			int cur = j * 2;
			while (cur <= 100000000)
			{
				ps[cur] = false;
				cur += j;
			}
		}
	}

	for (int j = 2; j <= 100000000; j++)
	{
		sums[j] = sums[j - 1];
		if (ps[j]) sums[j] += j;
	}

	for( int j = 10; j <= 100000000; j*=10 )printf( "%20d  %17I64d\n", j, sums[j] );

	getch();

	return 0;
}

