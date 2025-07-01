#include <klee/klee.h>
#include <stdio.h>

// Recursive function to test call depth limiting
int deep_recursion(int n) {
    if (n <= 0) {
        return 1;
    }
    return n + deep_recursion(n - 1);
}

// Function with multiple basic blocks
int complex_function(int x) {
    int result = 0;
    
    if (x > 10) {
        result = x * 2;
        if (result > 50) {
            result += 100;
        }
    } else if (x > 5) {
        result = x + 10;
        for (int i = 0; i < x; i++) {
            result += i;
        }
    } else {
        result = x * x;
        if (x % 2 == 0) {
            result -= 5;
        }
    }
    
    return result;
}

// Another function to create more basic blocks
void helper_function(int *ptr) {
    if (ptr != NULL) {
        *ptr += 42;
    }
}

int main() {
    int input;
    klee_make_symbolic(&input, sizeof(input), "input");
    klee_assume(input >= 0 && input <= 20);
    
    int result = 0;
    
    // Test various execution paths
    if (input < 8) {
        result = complex_function(input);
        
        if (input < 3) {
            // Test recursion depth
            result += deep_recursion(input);
        }
    } else {
        result = input * 3;
        helper_function(&result);
        
        if (input > 15) {
            result = complex_function(result % 10);
        }
    }
    
    return result;
}