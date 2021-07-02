
import math
import time
import matplotlib.pyplot as plt

import primefac
from quadratic_sieve import quadratic_sieve


# ### factorization algorithms ### #

# utility
def is_primary(num):
    factors  = list(range(2, num))
    for elem in factors:
        if num % elem == 0 :
            return False
    else:
        return True

# Trivial division factorization
def trivial_division(number):
    factors = list()

    for i in range(2, number+1):
        if number % i == 0:
            if is_primary(i):
                factors.append(i)
  
    return factors



# Fermat factorization (is aplicable for odd numbers only)

# utility, find one pair of nubber's factors 
def fermat_one_step(number): 
   
    a = math.ceil(number**0.5)

    while a < number: 
        b2 = a*a - number  
        b = b2 ** 0.5 
        if b == int(b):
            b = int(b)
            return (a-b), (a+b)
        a += 1

# find full list of primary factors of the number
def fermat_factorisation(number):

   factors = list() # if number is even
   if number % 2 == 0:
       return 0
 
   a, b  = fermat_one_step(number) 
   factors.append(a)
   factors.append(b)

   for elem in factors:
       if not is_primary(elem):
           c, d = fermat_one_step(elem)
           factors.remove(elem)
           factors.append(c)
           factors.append(d)

   return sorted(list(factors))

#Pollard's rho algorithm

# return one factor of number
def pollards_rho_step(number):

    a = 2
    b = 2
    d = 1

    def f(a):
        return (a**2 + 1) % number

    while d == 1:
        x = f(a); b = f(f(b))
        d = math.gcd(abs(a-b), number)

    if d != number:
        return d


# find full list og primary factros of number
def pollards_rho(number):

    factors = list()
    a = pollards_rho_step(number)
    factors.append(a)
    factors.append(int(number/a))

    for elem in factors:
       if not is_primary(elem):
           a = pollards_rho_step(elem)
           factors.append(a)
           factors.append(int(elem/a))
           factors.remove(elem)

    return sorted(list(factors))


# General number filed sieve (using method from primefac)
def genneral_number_field_sieve(number):
    factors  = list()
    
    while not is_primary(number):
        x = primefac.mpqs(number)
        factors.append(x)
        number = int(number/x)
    else:
        factors.append(number)

    return factors



# utility for measure the time of algorithms working 
def time_measure(number, method):

    t_start = time.time_ns()
    lst = method(number)
    t_end = time.time_ns()

    #print(method.__name__, " " , lst)
    print("{} : {}".format(method.__name__, lst))
    return t_end - t_start



def main():

    number = 433635

    print("Number is equal to ", number)

    t1 = time_measure(number, trivial_division) / 10**9  # to get time in seconds  
    t2 = time_measure(number, fermat_factorisation) / 10**9
    t3 = time_measure(number, pollards_rho) / 10**9
    t4 = time_measure(number, quadratic_sieve) / 10**9 
    t5 = time_measure(number, genneral_number_field_sieve) / 10**9

    fig, ax = plt.subplots()
    ax.plot(1, t1, marker = 'o', markersize = 7, label = "Trivial division")
    ax.plot(2, t2, marker = 'o', markersize = 7, label = "Fermat factorisation")
    ax.plot(3, t3, marker = 'o', markersize = 7, label = "Pollard's rho")
    ax.plot(4, t4, marker = 'o', markersize = 7, label = "Quadratic sieve")
    ax.plot(5, t5, marker = 'o', markersize = 7, label = "GNFS")

    plt.ylabel('time (s)', fontsize=14)
    plt.xticks([])

    ax.set_yscale('log')
    ax.legend(loc=2, numpoints=1)
    plt.show()
    fig.savefig("algorithm_time.pdf")

    print()

main()