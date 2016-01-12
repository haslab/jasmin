from __future__ import print_function
import sys
import logging
import random

sys.ps1 = ""

# * Classes for prime field arithmetic
###########################################################################




# * Functions callable from dmasm
###########################################################################

def confirm_started():
  print("done", file=sys.stdout)

def print_newline(params):
  print("", file=sys.stderr)
  return []

def assert_equal(x, y, params):
  assert (x == y)
  return []

def to_digits(radix,digits,n):
  res = [0] * digits
  for i in range(digits):
    res[i] = n % radix
    n = n / radix
  assert (n == 0)
  return res

def from_digits(radix,digits):
  res = 0
  for i,n in enumerate(digits):
    res = res + n*(radix**i)
  return res

def print_u64_arr(x,params):
  #print('>>> print_u64_arr: x=%s'%(str(x)), file=sys.stderr)
  y = from_digits(2**64,x) % p
  print('>>> print_u64_arr: x=%s'%(str(y)), file=sys.stderr)
  #print('>>> print_u64_arr: n=%s'%(str(params['n'])), file=sys.stderr)
  return []

def print_u64(x,params):
  print('%s '%(str(x)), file=sys.stderr, end="")
  return []

# * Functions for 25519 with 4 limbs
###########################################################################

p = 2**255 - 19
two64 = 2**64

def to_big_int(n):
  return (from_digits(two64,n) % p)

def rand(s,params):
  # print('>>> rand_arr: x=%s'%(str(s)), file=sys.stderr)
  random.seed(s)
  n = random.getrandbits(512) % p
  res = to_digits(two64,4,n)
  # print('>>> rand_arr: res=%s'%(str(res)), file=sys.stderr)
  return res

def assert_equal_add(x,y,z,params):
  xi = to_big_int(x)
  yi = to_big_int(y)
  zi = to_big_int(z)
  assert ((xi + yi) % p == (zi % p))
  return []

def assert_equal_sub(x,y,z,params):
  xi = to_big_int(x)
  yi = to_big_int(y)
  zi = to_big_int(z)
  assert ((xi - yi) % p == (zi % p))
  return []

def assert_equal_mul(x,y,z,params):
  xi = to_big_int(x)
  yi = to_big_int(y)
  zi = to_big_int(z)
  assert ((xi * yi) % p == (zi % p))
  return []

# translated from:
# https://github.com/agl/curve25519-donna/blob/master/curve25519-donna-c64.c
def fmonty( x, z            # Q
          , xprime, zprime  # Q'
          , qmqp            # Q - Q'
          ):
  origx = x                             # memcpy(origx, x, 5 * sizeof(limb))
  x = (x + z)                      % p  # fsum(x,z)
  z = (origx - z)                  % p  # fdifference_backwards(z, origx);
  origxprime = xprime                   # memcpy(origxprime, xprime, sizeof(limb) * 5)
  xprime = (xprime + zprime)       % p  # fsum(xprime, zprime)
  zprime = (origxprime - zprime)   % p  # fdifference_backwards(zprime, origxprime)
  xxprime = (xprime * z)           % p  # fmul(xxprime, xprime, z);
  zzprime = (x * zprime)           % p  # fmul(zzprime, x, zprime)
  origxprime = xxprime             % p  # memcpy(origxprime, xxprime, sizeof(limb) * 5)
  xxprime = (xxprime + zzprime)    % p  # fsum(xxprime, zzprime)
  zzprime = (origxprime - zzprime) % p  # fdifference_backwards(zzprime, origxprime)
  x3 = (xxprime * xxprime)         % p  # fsquare_times(x3, xxprime, 1)
  zzzprime = (zzprime * zzprime)   % p  # fsquare_times(zzzprime, zzprime, 1)
  z3 = (zzzprime * qmqp)           % p  # fmul(z3, zzzprime, qmqp)
  xx = (x * x)                     % p  # fsquare_times(xx, x, 1)
  zz = (z * z)                     % p  # fsquare_times(zz, z, 1)
  x2 = (xx * zz)                   % p  # fmul(x2, xx, zz)
  zz = (xx - zz)                   % p  # fdifference_backwards(zz, xx)
  zzz = (zz*121665)                % p  # fscalar_product(zzz, zz, 121665)
  zzz = (zzz + xx)                 % p  # fsum(zzz, xx)
  z2 = (zz * zzz)                  % p  # fmul(z2, zz, zzz)
  
  # return values:
  # x2, z2 = 2Q
  # x3, z3 = Q + Q' 
  return (x2,z2,x3,z3)


# translated from Verify25519 paper (Algorithm 2)
def monty_tracing(x1, x2, z2, x3, z3):
  #print("monty input:\n%s\n"%(str((x1,x2,z2,x3,z3))), file=sys.stderr)
  t1 = (x2 + z2)     % p; l1  = t1
  t2 = (x2 - z2)     % p; l2  = t2
  t7 = (t2 * t2)     % p; l3  = t7
  t6 = (t1 * t1)     % p; l4  = t6
  t5 = (t6 - t7)     % p; l5  = t5
  t3 = (x3 + z3)     % p; l6  = t3
  t4 = (x3 - z3)     % p; l7  = t4
  t9 = (t3 * t2)     % p; l8  = t9
  t8 = (t4 * t1)     % p; l9  = t8
  x3 = (t8 + t9)     % p; l10 = x3

  z3 = (t8 - t9)     % p; l11 = z3
  x3 = (x3 * x3)     % p; l12 = x3
  z3 = (z3 * z3)     % p; l13 = z3
  z3 = (z3 * x1)     % p; l14 = z3
  x2 = (t6 * t7 )    % p; l15 = x2
  z2 = (121666 * t5) % p; l16 = z2
  z2 = (z2 + t7)     % p; l17 = z2
  z2 = (z2 * t5)     % p; l18 = z2

  #print("monty result:\n%s\n"%(str((x2,z2,x3,z3))), file=sys.stderr)
  return (l1,l2,l3,l4,l5,l6,l7,l8,l9,l10,l11,l12,l13,l14,l15,l16,l17,l18)

def monty(x1, x2, z2, x3, z3):
  #print("monty input:\n%s\n"%(str((x1,x2,z2,x3,z3))), file=sys.stderr)
  t1 = (x2 + z2)     % p
  t2 = (x2 - z2)     % p
  t7 = (t2 * t2)     % p
  t6 = (t1 * t1)     % p
  t5 = (t6 - t7)     % p
  t3 = (x3 + z3)     % p
  t4 = (x3 - z3)     % p
  t9 = (t3 * t2)     % p
  t8 = (t4 * t1)     % p
  x3 = (t8 + t9)     % p

  z3 = (t8 - t9)     % p
  x3 = (x3 * x3)     % p
  z3 = (z3 * z3)     % p
  z3 = (z3 * x1)     % p
  x2 = (t6 * t7 )    % p
  z2 = (121666 * t5) % p
  z2 = (z2 + t7)     % p
  z2 = (z2 * t5)     % p

  #print("monty result:\n%s\n"%(str((x2,z2,x3,z3))), file=sys.stderr)
  return (x2,z2,x3,z3)

def mul_py(x,y,params):
  a = from_digits(two64,x)
  b = from_digits(two64,y)
  c = (a*b) % p
  z = to_digits(two64,4,c)
  print_u64_arr(x,params)
  print_u64_arr(y,params)
  print_u64_arr(z,params)
  print('>>> monty a=%s'%(str(a)), file=sys.stderr)
  print('>>> monty b=%s'%(str(b)), file=sys.stderr)
  print('>>> monty c=%s'%(str(c)), file=sys.stderr)
  return z

def assert_equal_test(c,params):
  c = to_big_int(c)
  assert(c == 47172631526548581395056365918773001275216341294900259085443495545076823360125)
  return []
def check_equal(s,a,b):
  a = a % p
  b = b % p
  # print("\n%s:\n%s ==\n%s\n"%(s,str(a),str(b)), file=sys.stderr)
  assert(a == b)

def assert_equal_ladderstep_tracing(x1,x2,z2,x3,z3
  ,l1,l2,l3,l4,l5,l6,l7,l8,l9,l10,l11,l12,l13,l14,l15,l16,l17,l18, params):
  x1 = to_big_int(x1)
  x2 = to_big_int(x2)
  z2 = to_big_int(z2)
  x3 = to_big_int(x3)
  z3 = to_big_int(z3)

  l1  = to_big_int(l1)
  l2  = to_big_int(l2)
  l3  = to_big_int(l3)
  l4  = to_big_int(l4)
  l5  = to_big_int(l5)
  l6  = to_big_int(l6)
  l7  = to_big_int(l7)
  l8  = to_big_int(l8)
  l9  = to_big_int(l9)
  l10 = to_big_int(l10)
  l11 = to_big_int(l11)
  l12 = to_big_int(l12)
  l13 = to_big_int(l13)
  l14 = to_big_int(l14)
  l15 = to_big_int(l15)
  l16 = to_big_int(l16)
  l17 = to_big_int(l17)
  l18 = to_big_int(l18)

  (s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16,s17,s18) = monty_tracing(x1,x2,z2,x3,z3)
  check_equal("1",s1,l1)
  check_equal("2",s2,l2)
  check_equal("3",s3,l3)
  check_equal("4",s4,l4)
  check_equal("5",s5,l5)
  check_equal("6",s6,l6)
  check_equal("7",s7,l7)
  check_equal("8",s8,l8)
  check_equal("9",s9,l9)
  check_equal("10",s10,l10)
  check_equal("11",s11,l11)
  check_equal("12",s12,l12)
  check_equal("13",s13,l13)
  check_equal("14",s14,l14)
  check_equal("15",s15,l15)
  check_equal("16",s16,l16)
  check_equal("17",s17,l17)
  check_equal("18",s18,l18)
  return []

def assert_equal_ladderstep(x1,x2,z2,x3,z3,x2_r,z2_r,x3_r,z3_r,params):
  x1 = to_big_int(x1)
  x2 = to_big_int(x2)
  z2 = to_big_int(z2)
  x3 = to_big_int(x3)
  z3 = to_big_int(z3)

  (x2_p,z2_p,x3_p,z3_p) = monty(x1,x2,z2,x3,z3)

  x2_r = to_big_int(x2_r)
  z2_r = to_big_int(z2_r)
  x3_r = to_big_int(x3_r)
  z3_r = to_big_int(z3_r)
 
  check_equal("x2",x2_r,x2_p)
  check_equal("z2",z2_r,z2_p)
  check_equal("x3",x3_r,x3_p)
  check_equal("z3",z3_r,z3_p)
  return []

# * Tests
###########################################################################

if __name__ == "__main__":
  rand_25519(1)

  # test from_digits
  random.seed(1)
  n = random.getrandbits(512) % p25519
  res = to_digits(two64,4,n)
  assert (from_digits(two64,res) == n)

  
  
