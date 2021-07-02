from math import gcd, ceil, exp, sqrt, log
from random import randint
from itertools import chain

from statistics import mean
import matplotlib.pyplot as plt
from timeit import timeit
from time import time


########################################################
# were imports from other files
def product(lst):
    """ Return product of all numbers in a list
    """
    prod = 1
    for _ in lst:
        prod *= _
    return prod


def kth_iroot(n, k):
    """ Return the integer k-th root of a number by Newton's method
    """
    u = n
    s = n + 1
    while u < s:
        s = u
        t = (k - 1) * s + n // pow(s, k - 1)
        u = t // k
    return s


def isqrt(n):
    """ Return the square root of a number rounded down to the closest integer
    """
    if n < 0:
        raise ValueError("Square root of negative number!")
    x = int(n)
    if n == 0:
        return 0
    a, b = divmod(x.bit_length(), 2)
    n = 2 ** (a + b)
    while True:
        y = (n + x // n) // 2
        if y >= x:
            return x
        x = y


def is_probable_prime(a):
    """ Perform Rabin-Miller primality test to determine whether given number
        is prime. Return True if number is very likely to be a prime, and False
        if it is definitely composite
    """
    if a == 2:
        return True

    if a == 1 or a % 2 == 0:
        return False

    return rabin_miller_primality_test(a, 50)


def rabin_miller_primality_test(a, iterations):
    """ Rabin Miller primality test
    """
    r, s = 0, a - 1

    while s % 2 == 0:
        r += 1
        s //= 2

    for _ in range(iterations):
        n = randint(2, a - 1)
        x = pow(n, s, a)
        if x == 1 or x == a - 1:
            continue
        for _ in range(r - 1):
            x = pow(x, 2, a)
            if x == a - 1:
                break
        else:
            return False
    return True


def quad_residue(a, n):
    # checks if a is quad residue of n
    l = 1
    q = (n - 1) // 2
    x = q ** l
    if x == 0:
        return 1

    a = a % n
    z = 1
    while x != 0:
        if x % 2 == 0:
            a = (a ** 2) % n
            x //= 2
        else:
            x -= 1
            z = (z * a) % n

    return z


# Returns k such that b^k = 1 (mod p)
def order(p, q):
    if gcd(p, q) != 1:
        print(p, ' and ', q, 'are not co-prime')
        return -1
    k = 3
    while True:
        if pow(q, k, p) == 1:
            return k
        k += 1


# function return p - 1 (= x argument) as x * 2^e,
# where x will be odd sending e as reference because
# updation is needed in actual e
def convertx2e(x):
    e = 0
    while x % 2 == 0:
        x /= 2
        e += 1
    return int(x), e


# Main function for finding the modular square root
def STonelli(n, p):  # tonelli-shanks to solve modular square root, x^2 = N (mod p)
    assert quad_residue(n, p) == 1, "not a square (mod p)"
    q = p - 1
    s = 0

    while q % 2 == 0:
        q //= 2
        s += 1
    if s == 1:
        r = pow(n, (p + 1) // 4, p)
        return r, p - r
    for z in range(2, p):
        # print(quad_residue(z, p))
        if p - 1 == quad_residue(z, p):
            break
    c = pow(z, q, p)
    r = pow(n, (q + 1) // 2, p)
    t = pow(n, q, p)
    m = s
    t2 = 0
    while (t - 1) % p != 0:
        t2 = (t * t) % p
        for i in range(1, m):
            if (t2 - 1) % p == 0:
                break
            t2 = (t2 * t2) % p
        b = pow(c, 1 << (m - i - 1), p)
        r = (r * b) % p
        c = (b * b) % p
        t = (t * c) % p
        m = i

    return (r, p - r)


def mprint(M):  # prints a matrix in readable form
    for row in M:
        print(row)


def prime_gen(n):  # sieve of Eratosthenes, generates primes up to a bound n
    if n < 2:
        return []

    nums = []
    isPrime = []

    for i in range(0, n + 1):  # Creates list of numbers from 0 to n
        nums.append(i)
        isPrime.append(True)

    isPrime[0] = False
    isPrime[1] = False

    for j in range(2, int(n / 2)):  # tries all size gaps that make sense
        if isPrime[j] == True:
            for i in range(2 * j, n + 1, j):  # starts from j+j, jumps by gap size j and crosses out that number
                isPrime[i] = False

    primes = []
    for i in range(0, n + 1):  # Adds leftovers
        if isPrime[i] == True:
            primes.append(nums[i])

    return primes


# def quad_residue(a, p): #quad_residue symbol of (a/p)
#     return pow(a, (p - 1) // 2, p)

def quad_residue(a, n):
    # checks if a is quad residue of n
    l = 1
    q = (n - 1) // 2
    x = q ** l
    if x == 0:
        return 1

    a = a % n
    z = 1
    while x != 0:
        if x % 2 == 0:
            a = (a ** 2) % n
            x //= 2
        else:
            x -= 1
            z = (z * a) % n

    return z


def size_bound(N):  # finds optimal factor base size and interval

    F = pow(exp(sqrt(log(N) * log(log(N)))), sqrt(2) / 4)
    I = F ** 3
    # print(F,I)
    return int(F), int(I)


def find_base(N, B):
    # generates a B-smooth factor base

    factor_base = []
    primes = prime_gen(B)
    # print(primes)

    for p in primes:  # such that N is a quadratic residue mod p
        if quad_residue(N, p) == 1:
            factor_base.append(p)
    return factor_base


def find_smooth(factor_base, N, I):
    # tries to find B-smooth numbers in sieve_seq, using sieving

    def sieve_prep(N, sieve_int):
        # generates a sequence from Y(x) = x^2 - N, starting at x = root
        sieve_seq = [x ** 2 - N for x in range(root, root + sieve_int)]
        # sieve_seq_neg = [x**2 - N for x in range(root,root-sieve_int,-1)]
        return sieve_seq

    sieve_seq = sieve_prep(N, I)
    sieve_list = sieve_seq.copy()  # keep a copy of sieve_seq for later
    if factor_base[0] == 2:
        i = 0
        while sieve_list[i] % 2 != 0:
            i += 1
        for j in range(i, len(sieve_list), 2):  # found the 1st even term, now every other term will also be even
            while sieve_list[j] % 2 == 0:  # account for powers of 2
                sieve_list[j] //= 2
    # print("")
    for p in factor_base[1:]:  # not including 2
        residues = STonelli(N, p)  # finds x such that x^2 = n (mod p). There are two start solutions

        for r in residues:
            for i in range((r - root) % p, len(sieve_list), p):  # Now every pth term will also be divisible
                while sieve_list[i] % p == 0:  # account for prime powers
                    sieve_list[i] //= p
    xlist = []  # original x terms
    smooth_nums = []
    indices = []  # index of discovery

    for i in range(len(sieve_list)):
        if len(smooth_nums) >= len(factor_base) + T:  # probability of no solutions is 2^-T
            break
        if sieve_list[i] == 1:  # found B-smooth number
            smooth_nums.append(sieve_seq[i])
            xlist.append(i + root)
            indices.append(i)

    return (smooth_nums, xlist, indices)


def build_matrix(smooth_nums, factor_base):
    # generates exponent vectors mod 2 from previously obtained smooth numbers, then builds matrix

    def factor(n, factor_base):  # trial division from factor base
        factors = []
        if n < 0:
            factors.append(-1)
        for p in factor_base:
            if p == -1:
                pass
            else:
                while n % p == 0:
                    factors.append(p)
                    n //= p
        return factors

    M = []
    factor_base.insert(0, -1)
    for n in smooth_nums:
        exp_vector = [0] * (len(factor_base))
        n_factors = factor(n, factor_base)
        # print(n,n_factors)
        for i in range(len(factor_base)):
            if factor_base[i] in n_factors:
                exp_vector[i] = (exp_vector[i] + n_factors.count(factor_base[i])) % 2

        # print(n_factors, exp_vector)
        if 1 not in exp_vector:  # search for squares
            return True, n
        else:
            pass

        M.append(exp_vector)
        # print("Matrix built:")
    # mprint(M)
    return False, transpose(M)


def transpose(matrix):
    # transpose matrix so columns become rows, makes list comp easier to work with
    new_matrix = []
    for i in range(len(matrix[0])):
        new_row = []
        for row in matrix:
            new_row.append(row[i])
        new_matrix.append(new_row)
    return (new_matrix)


def gauss_elim(M):
    # reduced form of gaussian elimination, finds rref and reads off the nullspace
    # https://www.cs.umd.edu/~gasarch/TOPICS/factoring/fastgauss.pdf

    # M = optimize(M)
    marks = [False] * len(M[0])

    for i in range(len(M)):  # do for all rows
        row = M[i]
        # print(row)

        for num in row:  # search for pivot
            if num == 1:
                # print("found pivot at column " + str(row.index(num)+1))
                j = row.index(num)  # column index
                marks[j] = True

                for k in chain(range(0, i), range(i + 1, len(M))):  # search for other 1s in the same column
                    if M[k][j] == 1:
                        for i in range(len(M[k])):
                            M[k][i] = (M[k][i] + row[i]) % 2
                break

    M = transpose(M)

    sol_rows = []
    for i in range(len(marks)):  # find free columns (which have now become rows)
        if marks[i] == False:
            free_row = [M[i], i]
            sol_rows.append(free_row)

    if not sol_rows:
        return ("No solution found. Need more smooth numbers.")
    # print("Found {} potential solutions".format(len(sol_rows)))
    return sol_rows, marks, M


def solve_row(sol_rows, M, marks, K=0):
    solution_vec, indices = [], []
    free_row = sol_rows[K][0]  # may be multiple K
    for i in range(len(free_row)):
        if free_row[i] == 1:
            indices.append(i)
    for r in range(len(M)):  # rows with 1 in the same column will be dependent
        for i in indices:
            if M[r][i] == 1 and marks[r]:
                solution_vec.append(r)
                break

    solution_vec.append(sol_rows[K][1])
    return (solution_vec)


def solve(solution_vec, smooth_nums, xlist, N):
    solution_nums = [smooth_nums[i] for i in solution_vec]
    x_nums = [xlist[i] for i in solution_vec]

    Asquare = 1
    for n in solution_nums:
        Asquare *= n

    b = 1
    for n in x_nums:
        b *= n

    a = isqrt(Asquare)

    factor = gcd(b - a, N)
    return factor


def QS(n, B, I):
    # single polynomial version of quadratic sieve, given smoothness bound B and sieve interval I

    # global n
    global root
    global T  # tolerance factor
    n, root, K, T = n, int(sqrt(n)), 0, 1

    if n == 0:
        return []

    if n == 1:
        return [1]

    if is_probable_prime(n):
        return [1, n]

    if int(sqrt(n)) == sqrt(n):
        return [isqrt(n), QS(isqrt(n), B, I)]

    # print(root)
    # print("Attempting to factor {}...".format(N))
    # F,I = size_bound(N)

    # print("Generating {}-smooth factor base...".format(B))
    factor_base = find_base(n, B)  # generates a B-smooth factor base
    # print(factor_base)

    global F
    F = len(factor_base)

    # print("Looking for {} {}-smooth relations...".format(F + T, B))
    smooth_nums, xlist, indices = find_smooth(factor_base, n, I)
    # finds B-smooth relations, using sieving and Tonelli-Shanks

    # print("Found {} B-smooth numbers.".format(len(smooth_nums)))

    # print(smooth_nums)

    if len(smooth_nums) < len(factor_base):
        return "Not enough smooth numbers. Increase the sieve interval or size of the factor base."

    # print("Building exponent matrix...")
    is_square, t_matrix = build_matrix(smooth_nums, factor_base)
    # builds exponent matrix mod 2 from relations

    if is_square:
        x = smooth_nums.index(t_matrix)
        factor = gcd(xlist[x] + int(sqrt(t_matrix)), n)
        # print("Found a square!")
        return QS(factor, B, I) + QS(n // factor, B, I)

    # print("Performing Gaussian Elimination...")
    sol_rows, marks, M = gauss_elim(t_matrix)  # solves the matrix for the null space, finds perfect square
    solution_vec = solve_row(sol_rows, M, marks, 0)

    # print("Solving congruence of squares...")
    # print(solution_vec)
    factor = solve(solution_vec, smooth_nums, xlist, n)  # solves the congruence of squares to obtain factors

    for K in range(1, len(sol_rows)):
        if factor == 1 or factor == n:
            # print("Didn't work. Trying different solution vector...")
            solution_vec = solve_row(sol_rows, M, marks, K)
            factor = solve(solution_vec, smooth_nums, xlist, n)
        else:
            # print("Found factors!")
            return QS(factor, B, I) + QS(n // factor, B, I)

    return [n]


#########################################################
# user code below

def trial_division_trivial(n):
    # this one return all divisors, not just prime ones
    return [k for k in range(1, n // 2 + 1) if not n % k]


def trial_division_optimized(n):
    """Factorize number into prime divisors"""
    prime = False

    factors = []
    while not prime:
        # check until sqrt(n)
        for k in range(2, int(n ** 0.5 + 1)):
            if n % k == 0:
                n = n // k  # divide and start again from 2
                factors.append(k)
                break
        else:  # if checked all up to sqrt(n) but not found a divisor
            prime = True
            factors.append(n)

    return factors


def fermat_factorization(n):
    """Fermat's factorization algorithm, as described in Wikipedia
    https://en.wikipedia.org/wiki/Fermat%27s_factorization_method

    We extend it recursively to return all prime divisors, not just two.
    """

    if n % 2 == 0:  # if n is even
        return [2] + fermat_factorization(n // 2)

    # simplest split
    a = ceil(n ** 0.5)
    b2 = a * a - n

    # while b is not a full square
    while int(b2 ** 0.5) != ceil(b2 ** 0.5):
        a += 1
        b2 = a * a - n

    factor = a - int(b2 ** 0.5)

    if factor == 1:
        return [n]
    else:
        return fermat_factorization(factor) + fermat_factorization(n // factor)


def pollards_rho_factorization(n):
    """Pollard's rho factorization algorithm, as described in Wikipedia
    https://en.wikipedia.org/wiki/Pollard%27s_rho_algorithm

    We extend it recursively to return all prime divisors, not just two.

    Important note: this algorithm is only a heuristic,
    i.e., is not guaranteed to output the correct result.
    """

    def g(x):
        return (x * x + 1) % n

    # randomize the seed of heuristic, as is recommended in "Introduction to Algorithms"
    x = randint(1, n - 1)
    y, d = x, 1

    while d == 1:
        x = g(x)
        y = g(g(y))
        d = gcd(abs(x - y), n)

    if d != n and d != 1:
        return pollards_rho_factorization(d) + pollards_rho_factorization(n // d)
    else:
        return [d]


def run_until_timeout(func, timeout):
    array_with_times = []

    start = time()
    while time() < start + timeout:
        array_with_times.append(timeit(func, number=1))

    return array_with_times


def main():
    numbers_to_test = [12, 123, 6767, 31289, 128938, 7693268, 4712800839, 131432131299, 23617823698126]

    times = {
        # "Trial Trivial": [],
        "Trial Optimized": [],
        "Fermat's": [],
        "Pollard's": [],
        "Quadratic Sieve": []
    }

    # collect time data
    # run each algorithm 1000 times for every number above
    for N in numbers_to_test:
        timeout = 1  # in seconds
        # append mean value of all runs, however many of them there are
        # times['Trial Trivial'].append(mean(run_until_timeout(lambda: trial_division_trivial(N), timeout)))

        times["Fermat's"].append(mean(run_until_timeout(lambda: fermat_factorization(N), timeout)))

        times["Trial Optimized"].append(mean(run_until_timeout(lambda: trial_division_optimized(N), timeout)))

        times["Pollard's"].append(mean(run_until_timeout(lambda: pollards_rho_factorization(N), timeout)))

        times["Quadratic Sieve"].append(mean(run_until_timeout(lambda: QS(N, 1000, 10000), timeout)))

    # display results

    for algorithm in times:
        plt.plot(numbers_to_test, times[algorithm], label=algorithm)

    plt.ylabel('Time, [s]');
    plt.xlabel('Input to algorithm')
    plt.loglog();
    plt.legend()
    plt.title('Comparison of different factorization algorithms\nLogLog scale')

    plt.xticks(numbers_to_test, map(str, numbers_to_test), rotation=45)

    plt.tight_layout()  # adjust plot margins

    plt.show()


if __name__ == '__main__':
    main()
