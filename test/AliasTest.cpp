#include "gtest/gtest.h"
#include <map>
#include <cstdint>

// Returns n! (the factorial of n).  For negative n, n! is defined to be 1.
int Factorial(int n) {
	int result = 1;
	for (int i = 1; i <= n; i++) {
		result *= i;
	}
	return result;
}

// Returns true if and only if n is a prime number.
bool IsPrime(int n) {
	if (n <= 1)
		return false;
	if (n % 2 == 0)
		return n == 2;
	for (int i = 3;; i += 2) {
		if (i > n / i)
			break;
		if (n % i == 0)
			return false;
	}
	return true;
}

namespace {

TEST(FactorialTest, Negative) {
	// This test is named "Negative", and belongs to the "FactorialTest"
	// test case.
	EXPECT_EQ(1, Factorial(-5));
	EXPECT_EQ(1, Factorial(-1));
	EXPECT_GT(Factorial(-10), 0);
}

TEST(IsPrimeTest, Negative) {
	// This test belongs to the IsPrimeTest test case.

	EXPECT_FALSE(IsPrime(-1));
	EXPECT_FALSE(IsPrime(-2));
	EXPECT_FALSE(IsPrime(INT_MIN));
}

}
