#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>


extern uint64_t addsd(uint64_t x, uint64_t y);
extern uint64_t subsd(uint64_t x, uint64_t y);
extern uint64_t mulsd(uint64_t x, uint64_t y);
extern uint64_t cvttsd2si(uint64_t x);
extern uint64_t cvtsd2si(uint64_t x);
extern uint64_t cvtsi2sd(uint64_t x);
extern uint64_t cmpeqsd(uint64_t x, uint64_t y);
extern uint64_t cmpltsd(uint64_t x, uint64_t y);
extern uint64_t cmplesd(uint64_t x, uint64_t y);
extern uint64_t cmpunordsd(uint64_t x, uint64_t y);
extern uint64_t cmpneqsd(uint64_t x, uint64_t y);
extern uint64_t cmpnltsd(uint64_t x, uint64_t y);
extern uint64_t cmpnlesd(uint64_t x, uint64_t y);
extern uint64_t cmpordsd(uint64_t x, uint64_t y);


int main() {
 double a, b, c;
 uint64_t ci, di;

 a = 1.25;
 b = 2.25;

 ci = addsd(*((uint64_t*)&a), *((uint64_t*)&b));
 c = *((double*)&ci);
 printf("%lf + %lf = %lf\n", a, b, c);
 ci = subsd(*((uint64_t*)&a), *((uint64_t*)&b));
 c = *((double*)&ci);
 printf("%lf - %lf = %lf\n", a, b, c);
 ci = mulsd(*((uint64_t*)&a), *((uint64_t*)&b));
 c = *((double*)&ci);
 printf("%lf * %lf = %lf\n", a, b, c);
 ci = cvttsd2si(*((uint64_t*)&c));
 printf("floor(%lf) = %lld\n", c, ci);
 ci = cvtsd2si(*((uint64_t*)&c));
 printf("round(%lf) = %lld\n", c, ci);
 ci = cmpltsd(*((uint64_t*)&a), *((uint64_t*)&b));
 c = *((double*)&ci);
 printf("%lf < %lf = %d\n", a, b, c!=0);
 ci = cmpneqsd(*((uint64_t*)&a), *((uint64_t*)&a));
 c = *((double*)&ci);
 printf("%lf != %lf = %d\n", a, a, c!=0);
 di = 3345;
 ci = cvtsi2sd(di);
 c = *((double*)&ci);
 printf("double(%lld) = %lf\n", di, c);

 return 0;
}
