#include <klee/klee.h>

int factorial(int n) {
    if (n <= 1) {
        return 1;
    }
    return n * factorial(n - 1);
}

int fibonacci(int n) {
    if (n <= 1) {
        return n;
    }
    return fibonacci(n - 1) + fibonacci(n - 2);
}

int main() {
    int x;
    klee_make_symbolic(&x, sizeof(x), "x");
    klee_assume(x >= 0 && x <= 10);
    
    if (x < 5) {
        int result = factorial(x);
        return result;
    } else {
        int result = fibonacci(x - 5);
        return result;
    }
}