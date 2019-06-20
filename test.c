#include <stdio.h>

int test(int i){
    if(i<=1)
        return 1;
    else i * test(i-1);
}


int main()
{
    int i;
    i = 0;
    while (i <= 10) {
        printf("阶乘(%2d) = %d\n", i, test(i));
        i = i + 1;
    }
    return 0;
}


