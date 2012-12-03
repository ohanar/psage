#################################################################################
#
# (c) Copyright 2012 R. Andrew Ohana
#
#  This file is part of PSAGE
#
#  PSAGE is free software: you can redistribute it and/or modify
#  it under the terms of the GNU General Public License as published by
#  the Free Software Foundation, either version 3 of the License, or
#  (at your option) any later version.
#
#  PSAGE is distributed in the hope that it will be useful,
#  but WITHOUT ANY WARRANTY; without even the implied warranty of
#  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
#  GNU General Public License for more details.
#
#  You should have received a copy of the GNU General Public License
#  along with this program.  If not, see <http://www.gnu.org/licenses/>.
#
#################################################################################

include 'gmp.pxi'
include 'stdsage.pxi'

from sage.rings.number_field.number_field_ideal import NumberFieldIdeal
from sage.libs.pari.gen cimport PariInstance
from sage.libs.pari.gen import pari

cdef extern from 'pari/pari.h':
    ctypedef long *GEN
    GEN   Fp_sqrt(GEN, GEN)

cdef extern from 'gmp.h':
    ctypedef __mpz_struct *mpz_ptr

#cdef extern from 'convert.h':
#    cdef void t_INT_to_ZZ(mpz_t, GEN)

# libcsage symbol is not being found for some reason
# so just include code here for now
cdef extern from 'pari/pari.h':
    long  signe(GEN)
    long  lgefint(GEN)
    long *int_LSW(GEN)

cdef void t_INT_to_ZZ(mpz_t r, GEN g):
    cdef long limbs = 0
    limbs = lgefint(g) - 2
    mpz_realloc2(r, limbs)
    mpz_import(r, limbs, -1, sizeof(long), 0, 0, int_LSW(g))
    if signe(g) < 0:
        mpz_neg(r, r)

cdef PariInstance pari_instance = pari

cdef void mpz_sqrtm(mpz_t r, mpz_t b, mpz_t p):
    # wrapper for pari method
    sig_on()
    t_INT_to_ZZ(r, Fp_sqrt(
            pari_instance._new_GEN_from_mpz_t(b),
            pari_instance._new_GEN_from_mpz_t(p)))
    pari_instance.clear_stack()

cdef class QuadraticIdeal:
    def __init__(self, *args):
        if not args:
            raise ValueError('cannot determine base ring')
        for i, arg in enumerate(args):
            if arg:
                break
        if isinstance(arg, NumberFieldElement_quadratic):
            self._ring = arg.parent()
        elif isinstance(arg, QuadraticIdeal):
            self._ring = (<QuadraticIdeal>arg)._ring
        elif isinstance(arg, NumberFieldIdeal):
            # currently we allow construction from sage ideal
            self._ring = arg.ring()
        self.D = <Integer>self._ring._D
        self._1mod4 = mpz_tstbit(self.D.value, 0u) \
                and not mpz_tstbit(self.D.value, 1u)
        self._1mod8 = self._1mod4 and not mpz_tstbit(self.D.value, 2u)
        if self._1mod4:
            try:
                self.F = <Integer>self._ring._F
            except AttributeError:
                self._ring._F = (self.D-1)/4
                self.F = <Integer>self._ring._F
        else:
            self.F = self.D

        if arg:
            if isinstance(arg, NumberFieldElement_quadratic):
                self._set_from_elt(arg)
            elif isinstance(arg, QuadraticIdeal):
                mpq_set(self.a, (<QuadraticIdeal>arg).a)
                mpz_set(self.b, (<QuadraticIdeal>arg).b)
                mpz_set(self.c, (<QuadraticIdeal>arg).c)
            elif isinstance(arg, NumberFieldIdeal):
                self._set_from_sage_ideal(arg)
        else:
            mpq_set_ui(self.a, 0u, 1u)
            mpz_set_ui(self.b, 1u)
            mpz_set_ui(self.c, 0u)
            return

        if self.is_one(): return

        args = args[i+1:]

        cdef QuadraticIdeal I = self._new()
        for arg in args:
            if not arg: continue

            if isinstance(arg, NumberFieldElement_quadratic):
                I._set_from_elt(arg)
            elif isinstance(arg, QuadraticIdeal):
                mpq_set(I.a, (<QuadraticIdeal>arg).a)
                mpz_set(I.b, (<QuadraticIdeal>arg).b)
                mpz_set(I.c, (<QuadraticIdeal>arg).c)
            elif isinstance(arg, NumberFieldIdeal):
                I._set_from_sage_ideal(arg)
            else:
                arg = self._ring(arg)
                I._set_from_elt(arg)

            self._c_iadd(I)
            if self.is_one(): return

    def __cinit__(self):
        mpq_init(self.a)
        mpz_init(self.b)
        mpz_init(self.c)

    def __dealloc__(self):
        mpq_clear(self.a)
        mpz_clear(self.b)
        mpz_clear(self.c)

    cdef QuadraticIdeal _new(self):
        '''
        Constructs a new fractional ideal over self._ring. Be careful
        the ideal doesn't yet have initialized values.
        '''
        cdef QuadraticIdeal res = PY_NEW(QuadraticIdeal)
        res._ring = self._ring
        res.D = self.D
        res.F = self.F
        res._1mod4 = self._1mod4
        res._1mod8 = self._1mod8
        return res

    cdef NumberFieldElement_quadratic _new_elt(self):
        '''
        Constructs a new element of self._ring. Be careful, the
        element doesn't yet have initialized values.
        '''
        cdef NumberFieldElement_quadratic res
        res = PY_NEW(NumberFieldElement_quadratic)
        res._parent = self._ring
        res.D = self.D
        return res

    cdef void _set_from_elt(self, NumberFieldElement_quadratic elt):
        mpz_set(mpq_denref(self.a), elt.denom)

        cdef mpz_t t0
        mpz_init(t0)

        if self._1mod4:
            # Compute the HNF of
            # [ a-b 2*b*F ]
            # [ 2*b   a+b ]
            mpz_mul_2exp(self.b, elt.b, 1u) # use as temp
            mpz_add(self.c, elt.a, elt.b) # use as temp
            mpz_gcdext(mpq_numref(self.a), self.b, self.c, self.b, self.c)
            mpz_mul_2exp(self.c, self.c, 1u)
            mpz_sub(t0, elt.a, elt.b)
            mpz_mul(self.c, self.c, elt.b)
            mpz_mul(self.c, self.c, self.F.value)
            mpz_addmul(self.c, self.b, t0)
        else:
            # Compute the HNF of
            # [ a b*D ]
            # [ b   a ]
            mpz_gcdext(mpq_numref(self.a), self.b, self.c, elt.b, elt.a)
            mpz_mul(self.c, self.c, elt.b)
            mpz_mul(self.c, self.c, self.D.value)
            mpz_addmul(self.c, elt.a, self.b)

        mpz_pow_ui(self.b, elt.a, 2u)
        mpz_pow_ui(t0, elt.b, 2u)
        mpz_submul(self.b, t0, self.D.value)
        if mpz_sgn(self.b) < 0:
            mpz_neg(self.b, self.b)
        mpz_divexact(self.b, self.b, mpq_numref(self.a))

        self._c_reduce(mpq_numref(self.a))

        mpz_clear(t0)

    cdef void _set_from_sage_ideal(self, I):
        cdef NumberFieldElement_quadratic a, b
        a,b = I.integral_basis()
        mpz_set(mpq_numref(self.a), b.b)
        mpz_set(mpq_denref(self.a), b.denom)
        mpz_divexact(self.b, b.denom, a.denom)
        mpz_mul(self.b, self.b, a.a)
        mpz_divexact(self.b, self.b, b.b)
        mpz_divexact(self.c, b.a, b.b)

        cdef mpz_t t0
        if self._1mod4:
            mpz_sub_ui(self.c, self.c, 1u)
            if mpz_tstbit(self.b, 0u):
                mpz_init(t0)
                mpz_cdiv_q_2exp(t0, self.b, 1u)
                mpz_mul(self.c, self.c, t0)
                mpz_clear(t0)
            else:
                mpz_mul_2exp(mpq_numref(self.a), mpq_numref(self.a), 1u)
                mpz_tdiv_q_2exp(self.b, self.b, 1u)
                mpz_tdiv_q_2exp(self.c, self.c, 1u)
        mpq_canonicalize(self.a)
        # sometimes some extra reduction might be needed now
        # depending on what sage returns for an integral basis
        mpz_mod(self.c, self.c, self.b)

    def __nonzero__(self):
        return mpq_sgn(self.a)

    def __invert__(self):
        if not self:
            raise ZeroDivisionError('division by zero')

        cdef QuadraticIdeal res = self.__copy__()

        sig_on() # probably not needed

        mpq_inv(res.a, res.a)
        if mpz_cmp_ui(res.b, 1u):
            # not rational
            if res._1mod4:
                # linear coefficient is 1 instead of 0
                mpz_sub(res.c, res.b, res.c)
                mpz_sub_ui(res.c, res.c, 1u)
            elif mpz_sgn(res.c):
                # there is a non-ramified prime divisor
                mpz_sub(res.c, res.b, res.c)
            mpz_mul(mpq_denref(res.a), mpq_denref(res.a), res.b)
            mpq_canonicalize(res.a)

        sig_off()

        return res

    def _add_(left, right):
        cdef QuadraticIdeal res = left.__copy__()
        sig_on()
        res._c_iadd(right)
        sig_off()
        return res

    def _mul_(left, right):
        cdef QuadraticIdeal res = left.__copy__()
        sig_on()
        res._c_imul(right)
        sig_off()
        return res

    def _div_(left, right):
        cdef QuadraticIdeal res = ~right
        sig_on()
        res._c_imul(left)
        sig_off()
        return res

    def __pow__(self, long n, dummy):
        cdef NumberFieldElement_quadratic gen
        cdef QuadraticIdeal res, tmp

        if n == 0:
            # return one ideal
            res = self._new()
            mpq_set_ui(res.a, 1u, 1u)
            mpz_set_ui(res.b, 1u)
            mpz_set_ui(res.c, 0u)
            return res

        if self.is_principal():
            # if self is principal, it is usually faster to
            # exponentiate a principal generator
            gen = self.gen(0)
            gen **= n
            res = self._new()
            res._set_from_elt(gen)
            return res

        if n > 0:
            res = self.__copy__()
        elif n == -1:
            return ~self
        else:
            res = ~self
            self = res.__copy__()
            n = -n
        if n == 1:
            return res

        res._c_isq()
        if n == 2:
            return res
        if n == 3:
            res._c_imul(self)
            return res
        m = n&1
        n >>= 1
        while not n&1:
            res._c_isq()
            n >>= 1
        n >>= 1
        tmp = res.__copy__()
        if m:
            res._c_imul(self)

        while n:
            tmp._c_isq()
            if n&1:
                res._c_imul(tmp)
            n >>= 1
        return res

    cdef void _c_reduce(self, mpz_t gcd):
        if mpz_cmp_ui(gcd, 1u):
            mpz_divexact(self.b, self.b, gcd)
            mpz_divexact(self.c, self.c, gcd)
            if gcd != mpq_numref(self.a):
                mpz_mul(mpq_numref(self.a), mpq_numref(self.a), gcd)
            mpq_canonicalize(self.a)
        mpz_mod(self.c, self.c, self.b)

    cdef void _c_imul(self, QuadraticIdeal right):
        '''
        This function multiplies self by right inplace
        '''
        # quickly handle when one factor is zero
        if not self: return
        if not right:
            mpq_set_ui(self.a, 0u, 1u)
            mpz_set_ui(self.b, 1u)
            mpz_set_ui(self.c, 0u)
            return

        # the factored out portion can be multiplied directly
        mpq_mul(self.a, self.a, right.a)

        # quickly handle when one factor is rational
        if not mpz_cmp_ui(right.b, 1u): return
        if not mpz_cmp_ui(self.b, 1u):
            mpz_set(self.b, right.b)
            mpz_set(self.c, right.c)
            return

        # We are computing the HNF of
        # [ b*y b*z y*c c*z+D ]
        # [   0   b   y   c+z ]
        # which has known determinate of b*y

        # start by consolidating the 2nd and 3rd columns
        cdef mpz_t t0, t1, t2
        mpz_init(t0); mpz_init(t1); mpz_init(t2)

        mpz_gcdext(t0, t1, t2, self.b, right.b)
        mpz_mul(t1, t1, self.b)
        mpz_mul(t2, t2, right.b)
        mpz_mul(t1, t1, right.c)
        mpz_addmul(t1, t2, self.c)

        mpz_mul(self.b, self.b, right.b)
        if not mpz_cmp_ui(t0, 1u): # if gcd = 1, we are done
            mpz_mod(self.c, t1, self.b)

            mpz_clear(t0); mpz_clear(t1); mpz_clear(t2)
            return

        # now we need to consolidate the 4th column
        cdef mpz_t t3
        mpz_init(t3)

        mpz_add(t2, self.c, right.c)
        if self._1mod4:
            # linear coefficient is 1 instead of 0
            mpz_add_ui(t2, t2, 1u)
        mpz_mul(self.c, self.c, right.c)
        mpz_add(self.c, self.c, self.F.value)
        mpz_gcdext(t0, t2, t3, t0, t2)
        mpz_mul(self.c, self.c, t3)
        mpz_addmul(self.c, t2, t1)
        mpz_divexact(self.b, self.b, t0)

        self._c_reduce(t0)

        mpz_clear(t0); mpz_clear(t1); mpz_clear(t2); mpz_clear(t3)

    cdef void _c_isq(self):
        '''
        This function squares self inplace
        '''
        # quickly handle zero
        if not self: return

        # the factored out portion can be squared directly
        mpz_pow_ui(mpq_numref(self.a), mpq_numref(self.a), 2u)
        mpz_pow_ui(mpq_denref(self.a), mpq_denref(self.a), 2u)

        # if rational, then we are done
        if not mpz_cmp_ui(self.b, 1u): return

        # We are computing the HNF of
        # [ b*b b*c c*c+D ]
        # [   0   b   2*c ]
        # which has known determinate of b*b

        # just need to consolidate 2nd and 3rd columns
        cdef mpz_t t0, t1, t2
        mpz_init(t0); mpz_init(t1); mpz_init(t2);

        mpz_mul_2exp(t0, self.c, 1u)
        if self._1mod4:
            # linear coefficient is 1 instead of 0
            mpz_add_ui(t0, t0, 1u)
        mpz_gcdext(t0, t1, t2, self.b, t0)
        mpz_mul(t1, t1, self.c)
        mpz_pow_ui(self.c, self.c, 2u)
        mpz_add(self.c, self.c, self.F.value)
        mpz_mul(self.c, self.c, t2)
        mpz_addmul(self.c, t1, self.b)
        mpz_pow_ui(self.b, self.b, 2u)
        mpz_divexact(self.b, self.b, t0)

        self._c_reduce(t0)
        mpz_clear(t0); mpz_clear(t1); mpz_clear(t2)

    cdef void _c_iadd(self, QuadraticIdeal right):
        # quickly handle when one summand contains the other
        if self <= right: return
        if right <= self:
            mpq_set(self.a, right.a)
            mpz_set(self.b, right.b)
            mpz_set(self.c, right.c)
            return

        # quickly handle when both ideals are rational
        if not (mpz_cmp_ui(self.b, 1u) or  mpz_cmp_ui(right.b, 1u)):
            mpz_gcd(mpq_numref(self.a), mpq_numref(self.a),
                    mpq_numref(right.a))
            mpz_lcm(mpq_denref(self.a), mpq_denref(self.a),
                    mpq_denref(right.a))
            return

        # Compute the HNF of the integer matrix
        # [ d*a.n*b w*x.n*y d*a.n*c w*x.n*z ]
        # [       0       0   d*a.n   w*x.n ]
        # d = lcm(a.d, x.d)/a.d, w = lcm(a.d, x.d)/x.d
        cdef mpz_t t0, t1
        mpz_init(t0); mpz_init(t1)

        if self.is_integral() and right.is_integral():
            # no work in the case that the ideals are integral
            mpz_set(t0, mpq_numref(right.a))
        else:
            # compute d*a.n and w*x.n
            mpz_lcm(t0, mpq_denref(self.a), mpq_denref(right.a))
            mpz_mul(mpq_numref(self.a), mpq_numref(self.a), t0)
            mpz_divexact(mpq_numref(self.a), mpq_numref(self.a),
                    mpq_denref(self.a))
            mpz_set(mpq_denref(self.a), t0)
            mpz_divexact(t0, mpq_denref(self.a), mpq_denref(right.a))
            mpz_mul(t0, t0, mpq_numref(right.a))

        # consolidate first two columns
        mpz_mul(self.b, self.b, mpq_numref(self.a))
        mpz_mul(t1, right.b, t0)
        mpz_gcd(self.b, self.b, t1)

        if not mpz_cmp_ui(self.b, 1u):
            # can terminate early since a.n must divide this number
            mpz_set_ui(mpq_numref(self.a), 1u)
            mpz_set_ui(self.c, 0u)

            mpz_clear(t0); mpz_clear(t1)
            return

        cdef mpz_t t2, t3
        mpz_init(t2); mpz_init(t3)

        mpz_sub(t1, self.c, right.c)
        mpz_mul(t1, t1, mpq_numref(self.a))
        mpz_mul(self.c, self.c, mpq_numref(self.a))

        mpz_gcdext(mpq_numref(self.a), t2, t3, mpq_numref(self.a), t0)

        mpz_mul(self.c, self.c, t2)
        mpz_mul(t3, t3, right.c)
        mpz_addmul(self.c, t3, t0)

        mpz_divexact(t1, t1, mpq_numref(self.a))
        mpz_mul(t1, t1, t0)

        mpz_gcd(self.b, self.b, t1)

        self._c_reduce(mpq_numref(self.a))

        mpz_clear(t0); mpz_clear(t1); mpz_clear(t2); mpz_clear(t3)

    cdef int _cmp_c_impl(left, right_py):
        # for quick sorting
        # richcmp is used for poset order based on reversed containment
        cdef int res
        cdef QuadraticIdeal right = right_py
        # sort by norm, then lexigraphically by b and c
        res = (<Rational>left.norm())._cmp_c_impl(right.norm())
        if res:
            return res
        res = mpz_cmp(left.b, right.b)
        if res:
            return res
        return mpz_cmp(left.c, right.c)

    cdef bint _richcmp_c_impl(left, right_py, int op):
        if op == Py_EQ:
            return not left._richcmp_c_impl(right_py, Py_NE)
        if op == Py_LT:
            return left._richcmp_c_impl(right_py, Py_NE) \
                    and left._richcmp_c_impl(right_py, Py_LE)
        if op == Py_GT:
            return left._richcmp_c_impl(right_py, Py_NE) \
                    and left._richcmp_c_impl(right_py, Py_GE)

        cdef QuadraticIdeal right = right_py
        if op == Py_NE:
            # left != right when any of a,b,c disagree
            return mpq_cmp(left.a, right.a) or mpz_cmp(left.b, right.b) \
                    or mpz_cmp(left.c, right.c)

        # probably can be done in a faster fashion
        cdef NumberFieldElement_quadratic x
        if op == Py_LE:
            # left <= right if and only if right/left is integral
            # right/left is integral if and only if
            # left contains a generating set of right
            for x in right.integral_basis():
                if not left._contains_(x):
                    return False
            return True
        if op == Py_GE:
            # left >= right if and only if left/right is integral
            # left/right is integral if and only if
            # right contains a generating set of left
            for x in left.integral_basis():
                if not right._contains_(x):
                    return False
            return True

    def __hash__(self):
        # TODO: figure out a better hash function
        cdef Rational a = PY_NEW(Rational)
        cdef Integer b = PY_NEW(Integer), c = PY_NEW(Integer)
        mpq_set(a.value, self.a)
        mpz_set(b.value, self.b)
        mpz_set(c.value, self.c)
        return hash((a,b,c))

    cpdef QuadraticIdeal __copy__(self):
        cdef QuadraticIdeal res = self._new()
        mpq_set(res.a, self.a)
        mpz_set(res.b, self.b)
        mpz_set(res.c, self.c)
        return res

    cpdef bint _contains_(self, x_py):
        cdef NumberFieldElement_quadratic x = x_py
        cdef bint ret
        cdef mpz_t t0real
        cdef mpz_ptr t0 = <mpz_ptr>t0real

        if not mpz_sgn(x.b):
            # rational in this case
            if not mpz_sgn(x.a):
                # zero is in every ideal
                return True
            # so x.a/(x.denom*a*b) must be integral
            ret = mpz_divisible_p(x.a, mpq_numref(self.a))
            if ret:
                ret = mpz_divisible_p(mpq_denref(self.a), x.denom)
                if ret:
                    mpz_init(t0)
                    mpz_divexact(t0, x.a, mpq_numref(self.a))
                    mpz_mul(t0, t0, mpq_denref(self.a))
                    mpz_divexact(t0, t0, x.denom)
                    ret = mpz_divisible_p(t0, self.b)
                    mpz_clear(t0)

            return ret

        cdef mpz_t t1, t2

        if self._1mod4:
            # want to solve
            # [ a*b a*c ] * [ y ] = [ (x.a-x.b)/x.denom ]
            # [   0   a ] * [ z ] = [     2*x.b/x.denom ]
            # for integers y, z

            mpz_init(t0)
            mpz_mul_2exp(t0, x.b, 1u) # t0 = 2*x.b
        else:
            # want to solve
            # [ a*b a*c ] * [ y ] = [ x.a/x.denom ]
            # [   0   a ] * [ z ] = [ x.b/x.denom ]
            # for integers y, z

            t0 = <mpz_ptr>x.b

        # z = t0/(a*x.denom)
        # check to see if z is integral, if so compute
        if not mpz_divisible_p(t0, mpq_numref(self.a)):
            if self._1mod4: mpz_clear(t0)
            return False
        mpz_init(t1)
        mpz_divexact(t1, t0, mpq_numref(self.a))
        mpz_mul(t1, t1, mpq_denref(self.a))
        if mpz_divisible_p(t1, x.denom):
            mpz_divexact(t1, t1, x.denom)
        else:
            if self._1mod4: mpz_clear(t0)
            mpz_clear(t1)
            return False

        if self._1mod4:
            mpz_sub(t0, x.a, x.b) # t0 = x.a-x.b
        else:
            t0 = <mpz_ptr>x.a

        # y = (t0/(a*x.denom) - c*z)/b
        # check to see if y is integral
        if not mpz_divisible_p(t0, mpq_numref(self.a)):
            if self._1mod4: mpz_clear(t0)
            mpz_clear(t1)
            return False
        mpz_init(t2)
        mpz_divexact(t2, t0, mpq_numref(self.a))
        mpz_mul(t2, t2, mpq_denref(self.a))
        if mpz_divisible_p(t2, x.denom):
            mpz_divexact(t2, t2, x.denom)
        else:
            if self._1mod4: mpz_clear(t0)
            mpz_clear(t1); mpz_clear(t2)
            return False
        mpz_submul(t2, t1, self.c)
        ret = mpz_divisible_p(t2, self.b)

        if self._1mod4: mpz_clear(t0)
        mpz_clear(t1); mpz_clear(t2)

        return ret

    cpdef Rational norm(self):
        # norm = a^2*b
        cdef Rational res = PY_NEW(Rational)
        mpz_pow_ui(mpq_numref(res.value), mpq_numref(self.a), 2u)
        mpz_pow_ui(mpq_denref(res.value), mpq_denref(self.a), 2u)
        mpz_mul(mpq_numref(res.value), mpq_numref(res.value), self.b)
        mpq_canonicalize(res.value)
        return res

    cpdef bint is_integral(self):
        return not mpz_cmp_ui(mpq_denref(self.a), 1u)

    cpdef bint is_principal(self):
        if not mpz_cmp_ui(self.b, 1u):
            # rationals are principal
            return True

        cdef dict ring_dict = self._ring.__dict__
        if '_NumberField_quadratic__class_number' in ring_dict:
            # the __class_number is a private attribute,
            # so we have to hack to find it
            if ring_dict['_NumberField_quadratic__class_number'] == 1:
                return True

        # the ideal is principal if and only if the binary quadratic
        # form b*x**2+2*c*x*y+(c**2-D)/b*y**2 has minimum 1
        cdef mpz_t m, n, k, s, t0, t1, t2, t3
        cdef Integer sqrt_disc
        cdef bint ret
        cdef short ts0
        mpz_init(m); mpz_init(n); mpz_init(k); mpz_init(s)
        mpz_init(t0)

        mpz_set(m, self.b)
        mpz_mul_2exp(n, self.c, 1u)
        mpz_pow_ui(k, self.c, 2u)
        mpz_sub(k, k, self.F.value)
        if self._1mod4:
            mpz_add_ui(n, n, 1u)
            mpz_add(k, k, self.c)
        mpz_divexact(k, k, self.b)

        if mpz_sgn(self.D.value) < 0:
            # positive definite form case

            # normalize the form if necessary
            if mpz_cmp(m, n) < 0:
                mpz_add(k, k, m)
                mpz_sub(k, k, n)
                mpz_submul_ui(n, m, 2u)

            while True:
                # apply reduction until reduced
                ts0 = mpz_cmp(m, k)
                if ts0 < 0 or (mpz_sgn(n) >= 0 and not ts0):
                    break
                mpz_add(s, k, n)
                mpz_fdiv_q_2exp(s, s, 1u)
                mpz_fdiv_q(s, s, k)
                mpz_pow_ui(t0, s, 2u)
                mpz_addmul(m, k, t0)
                mpz_submul(m, n, s)
                mpz_mul_2exp(t0, s, 1u)
                mpz_submul(n, t0, k)
                mpz_neg(n, n)
                mpz_set(t0, k)
                mpz_set(k, m)
                mpz_set(m, t0)

            ret = not mpz_cmp_ui(m, 1u)
        else:
            # indefinite form case

            # get the floor of the square root of the discriminant
            if '_sqrt_disc' not in ring_dict:
                if self._1mod4:
                    ring_dict['_sqrt_disc'] = self.D.sqrtrem()[0]
                else:
                    ring_dict['_sqrt_disc'] = (4*self.D).sqrtrem()[0]
            sqrt_disc = <Integer>ring_dict['_sqrt_disc']

            # normalize the form if necessary
            if mpz_cmp(m, sqrt_disc.value) >= 0:
                if mpz_cmp(m, n) < 0:
                    mpz_add(k, k, m)
                    mpz_sub(k, k, n)
                    mpz_submul_ui(n, m, 2u)
            else:
                mpz_sub(s, sqrt_disc.value, n)
                mpz_fdiv_q_2exp(s, s, 1u)
                mpz_fdiv_q(s, s, m)
                mpz_pow_ui(t0, s, 2u)
                mpz_addmul(k, m, t0)
                mpz_addmul(k, n, s)
                mpz_mul_2exp(t0, s, 1u)
                mpz_addmul(n, m, t0)

            while True:
                # apply reduction until reduced
                mpz_mul_2exp(t0, m, 1u)
                if mpz_sgn(t0) < 0:
                    mpz_neg(t0, t0)
                mpz_sub(t0, t0, n)
                if mpz_cmp(t0, sqrt_disc.value) <= 0:
                    break

                ts0 = mpz_sgn(k)
                if ts0 < 0:
                    mpz_neg(t0, k)
                else:
                    mpz_set(t0, k)
                if mpz_cmp(t0, sqrt_disc.value) < 0:
                    mpz_add(s, sqrt_disc.value, n)
                else:
                    mpz_add(s, n, t0)
                mpz_fdiv_q_2exp(s, s, 1u)
                mpz_fdiv_q(s, s, t0)
                if ts0 < 0:
                    mpz_neg(s, s)

                mpz_pow_ui(t0, s, 2u)
                mpz_addmul(m, k, t0)
                mpz_submul(m, n, s)
                mpz_mul_2exp(t0, s, 1u)
                mpz_submul(n, t0, k)
                mpz_neg(n, n)
                mpz_set(t0, k)
                mpz_set(k, m)
                mpz_set(m, t0)

            # indefinite, so make first coefficient positive
            if mpz_sgn(m) < 0:
                mpz_neg(m, m)
                mpz_neg(k, k)

            ret = not mpz_cmp_ui(m, 1u)
            if not ret:
                # check to see if the leading coefficient is one
                # for any other form in the cycle
                mpz_init(t1); mpz_init(t2); mpz_init(t3)
                mpz_set(t1, m)
                mpz_set(t2, n)
                mpz_set(t3, k)
                while True:
                    ts0 = mpz_sgn(t3)
                    if ts0 < 0:
                        mpz_neg(t3, t3)
                    mpz_add(s, t2, sqrt_disc.value)
                    mpz_fdiv_q_2exp(s, s, 1u)
                    mpz_fdiv_q(s, s, t3)

                    mpz_pow_ui(t0, s, 2u)
                    if ts0 < 0:
                        mpz_submul(t1, t3, t0)
                    else:
                        mpz_addmul(t1, t3, t0)
                    mpz_addmul(t1, t2, s)
                    mpz_mul_2exp(t0, s, 1u)
                    mpz_submul(t2, t0, t3)
                    mpz_neg(t2, t2)
                    mpz_set(t0, t3)
                    mpz_neg(t3, t1)
                    mpz_set(t1, t0)

                    ret = not mpz_cmp_ui(t1, 1u)
                    if ret or not \
                            (  mpz_cmp(t1, m) \
                            or mpz_cmp(t2, n) \
                            or mpz_cmp(t3, k)):
                        break

                mpz_clear(t1); mpz_clear(t2); mpz_clear(t3)

        mpz_clear(t0)
        mpz_clear(m); mpz_clear(n); mpz_clear(k); mpz_clear(s)
        return ret

    def is_one(self):
        return not (mpz_cmp_ui(self.b, 1u) or mpq_cmp_ui(self.a, 1u, 1u))

    def factor(self, proof=None):
        # we piggy back off of integer factorization
        cdef QuadraticIdeal tmp
        cdef Integer p, z = PY_NEW(Integer)
        cdef dict f_dict = PY_NEW(dict)
        cdef int legendre
        mpz_set(z.value, self.b)
        for p, e in z.factor(proof=proof):
            tmp = self._new()
            mpq_set_ui(tmp.a, 1u, 1u)
            mpz_set(tmp.b, p.value)
            mpz_mod(tmp.c, self.c, tmp.b)
            f_dict[tmp] = e
        mpz_set(z.value, mpq_numref(self.a))
        h_factor = dict(z.factor(proof=proof))
        mpz_set(z.value, mpq_denref(self.a))
        for p, e in z.factor(proof=proof):
            if p in h_factor:
                h_factor[p] -= e
            else:
                h_factor[p] = -e
        for p, e in h_factor.iteritems():
            # use the legendre symbol to determine whether or not p splits
            if not mpz_tstbit(p.value, 0u):
                # 2 breaks the legendre symbol, so deal with it separately
                if self._1mod8:
                    legendre = 1
                elif self._1mod4:
                    legendre = -1
                else:
                    legendre = 0
            else:
                legendre = mpz_legendre(self.D.value, p.value)

            tmp = self._new()
            if legendre == -1:
                # handle inert case
                mpq_set_z(tmp.a, p.value)
                mpz_set_ui(tmp.b, 1u)
                mpz_set_ui(tmp.c, 0u)
                f_dict[tmp] = e
                continue

            # split/ramified case
            mpq_set_ui(tmp.a, 1u, 1u)
            mpz_set(tmp.b, p.value)

            if not mpz_tstbit(p.value, 0u):
                # like usual, arithmetic for 2 is a bit off
                # thankfully it is easy in this case
                mpz_set_ui(tmp.c, mpz_tstbit(self.D.value, 0u))
            else:
                mpz_sqrtm(tmp.c, self.D.value, tmp.b)
                if self._1mod4:
                    # tmp.c = (-1+tmp.c)/2 (mod tmp.b)
                    if mpz_tstbit(tmp.c, 0u):
                        mpz_tdiv_q_2exp(tmp.c, tmp.c, 1u)
                    else:
                        mpz_sub_ui(tmp.c, tmp.c, 1u)
                        mpz_addmul(tmp.c, tmp.c, tmp.b)
                        mpz_tdiv_q_2exp(tmp.c, tmp.c, 1u)
                        mpz_mod(tmp.c, tmp.c, tmp.b)

            if tmp in f_dict:
                f_dict[tmp] += e
            else:
                f_dict[tmp] = e

            if not legendre:
                # ramified, so we don't have a conjugate
                # so just double the exponent
                f_dict[tmp] += e
                continue

            # construct conjugate
            tmp = tmp.__copy__()
            mpz_sub(tmp.c, tmp.b, tmp.c)
            if tmp._1mod4:
                # linear coefficient is 1 instead of 0
                mpz_sub_ui(tmp.c, tmp.c, 1u)

            if tmp in f_dict:
                f_dict[tmp] += e
            else:
                f_dict[tmp] = e

        f_list = f_dict.items()
        f_list.sort()

        from sage.structure.factorization import Factorization
        return Factorization(f_list)

    def is_prime(self, proof=None):
        if not self.is_integral() or self.is_one():
            return False
        if not self:
            # zero is prime
            return True
        # inert primes have b = 1, split/ramified primes have a = 1
        cdef bint inert, split
        split = mpz_cmp_ui(mpq_numref(self.a), 1u) == 0
        inert = mpz_cmp_ui(self.b, 1u) == 0
        if not (split or inert):
            # both not inert and not split, so not prime
            return False
        cdef Integer z
        if inert:
            # we are in the case of I=(a), so first check if
            # we have splitting by using the kronecker symbol
            if not mpz_tstbit(mpq_numref(self.a), 0u):
                # even things break the kronecker, so deal
                # with them separately
                if mpz_cmp_ui(mpq_numref(self.a), 2u):
                    # not (2), so done
                    return False
                # the only case (2) is prime is when D = 5mod8
                return self._1mod4 and not self._1mod8
            elif mpz_kronecker(self.D.value, mpq_numref(self.a)) > -1:
                return False

            # no splitting, so just need to check and
            # see if a is prime over ZZ
            z = PY_NEW(Integer)
            mpz_set(z.value, mpq_numref(self.a))
        else: # split/ramified case
            z = PY_NEW(Integer)
            mpz_set(z.value, self.b)
        # we piggy back off of Integer's is_prime
        return z.is_prime(proof=proof)

    def integral_basis(self):
        return list(self._integral_basis())

    def _integral_basis(self):
        cdef NumberFieldElement_quadratic x, y
        x, y = self._new_elt(), self._new_elt()

        # x = self.a*self.b
        mpz_mul(x.a, mpq_numref(self.a), self.b)
        mpz_set_ui(x.b, 0u)
        mpz_set(x.denom, mpq_denref(self.a))
        x._reduce_c_()

        if self._1mod4:
            # y = self.a*(X+self.c)
            #   = self.a*(sqrt(D)+1+2*self.c)/2
            mpz_mul_2exp(y.a, self.c, 1u)
            mpz_add_ui(y.a, y.a, 1u)
            mpz_mul(y.a, y.a, mpq_numref(self.a))
            mpz_set(y.b, mpq_numref(self.a))
            mpz_mul_2exp(y.denom, mpq_denref(self.a), 1u)
            y._reduce_c_()
        else:
            # y = self.a*(sqrt(D)+self.c)
            mpz_mul(y.a, mpq_numref(self.a), self.c)
            mpz_set(y.b, mpq_numref(self.a))
            mpz_set(y.denom, mpq_denref(self.a))
        return x,y

    def gens(self):
        cdef NumberFieldElement_quadratic ret

        # quickly handle rational case
        if not mpz_cmp_ui(self.b, 1u):
            ret = self._new_elt()
            mpz_set(ret.a, mpq_numref(self.a))
            mpz_set_ui(ret.b, 0u)
            mpz_set(ret.denom, mpq_denref(self.a))
            return ret,

        # there is a principal generator if and only if there is an integer
        # solution to b*x**2+2*c*x*y+(c**2-D)/b*y**2 = 1
        cdef mpz_t m, n, k, s, t0, t1, t2, t3, t4
        cdef mpz_t M0, M1, M2, M3, M4
        cdef Integer sqrt_disc
        cdef short ts0
        cdef bint is_principal
        cdef dict ring_dict
        mpz_init(m); mpz_init(n); mpz_init(k); mpz_init(s)
        mpz_init(M0); mpz_init(M1); mpz_init(M2); mpz_init(M3)
        mpz_init(t0)

        mpz_set(m, self.b)
        mpz_mul_2exp(n, self.c, 1u)
        mpz_pow_ui(k, self.c, 2u)
        mpz_sub(k, k, self.F.value)
        if self._1mod4:
            mpz_add_ui(n, n, 1u)
            mpz_add(k, k, self.c)
        mpz_divexact(k, k, self.b)

        if mpz_sgn(self.D.value) < 0:
            # positive definite form

            mpz_set_ui(M0, 1u)
            mpz_set_ui(M2, 0u)
            mpz_set_ui(M3, 1u)

            if mpz_cmp(m, n) < 0:
                # normalize the form
                mpz_add(k, k, m)
                mpz_sub(k, k, n)
                mpz_submul_ui(n, m, 2u)

                mpz_set_si(M1, -1)
            else:
                mpz_set_ui(M1, 0u)

            while True:
                # apply reduction until reduced
                ts0 = mpz_cmp(m, k)
                if ts0 < 0 or (mpz_sgn(n) >= 0 and not ts0):
                    break
                mpz_add(s, k, n)
                mpz_fdiv_q_2exp(s, s, 1u)
                mpz_fdiv_q(s, s, k)
                mpz_pow_ui(t0, s, 2u)
                mpz_addmul(m, k, t0)
                mpz_submul(m, n, s)
                mpz_mul_2exp(t0, s, 1u)
                mpz_submul(n, t0, k)
                mpz_neg(n, n)
                mpz_set(t0, k)
                mpz_set(k, m)
                mpz_set(m, t0)

                mpz_submul(M0, M1, s)
                mpz_neg(t0, M0)
                mpz_set(M0, M1)
                mpz_set(M1, t0)

                mpz_submul(M2, M3, s)
                mpz_neg(t0, M2)
                mpz_set(M2, M3)
                mpz_set(M3, t0)

            is_principal = not mpz_cmp_ui(m, 1u)
        else:
            # indefinite form case

            # get the floor of the square root of the discriminant
            ring_dict = self._ring.__dict__
            if '_sqrt_disc' not in ring_dict:
                if self._1mod4:
                    ring_dict['_sqrt_disc'] = self.D.sqrtrem()[0]
                else:
                    ring_dict['_sqrt_disc'] = (4*self.D).sqrtrem()[0]
            sqrt_disc = <Integer>ring_dict['_sqrt_disc']

            mpz_set_ui(M0, 1u)
            mpz_set_ui(M2, 0u)
            mpz_set_ui(M3, 1u)

            # normalize the form if necessary
            if mpz_cmp(m, sqrt_disc.value) >= 0:
                if mpz_cmp(m, n) < 0:
                    mpz_add(k, k, m)
                    mpz_sub(k, k, n)
                    mpz_submul_ui(n, m, 2u)

                    mpz_set_si(M1, -1)
                else:
                    mpz_set_ui(M1, 0u)
            else:
                mpz_sub(s, sqrt_disc.value, n)
                mpz_fdiv_q_2exp(s, s, 1u)
                mpz_fdiv_q(s, s, m)
                mpz_pow_ui(t0, s, 2u)
                mpz_addmul(k, m, t0)
                mpz_addmul(k, n, s)
                mpz_mul_2exp(t0, s, 1u)
                mpz_addmul(n, m, t0)

                mpz_set(M1, s)

            while True:
                # apply reduction until reduced
                mpz_mul_2exp(t0, m, 1u)
                if mpz_sgn(t0) < 0:
                    mpz_neg(t0, t0)
                mpz_sub(t0, t0, n)
                if mpz_cmp(t0, sqrt_disc.value) <= 0:
                    break

                ts0 = mpz_sgn(k)
                if ts0 < 0:
                    mpz_neg(t0, k)
                else:
                    mpz_set(t0, k)
                if mpz_cmp(t0, sqrt_disc.value) < 0:
                    mpz_add(s, sqrt_disc.value, n)
                else:
                    mpz_add(s, n, t0)
                mpz_fdiv_q_2exp(s, s, 1u)
                mpz_fdiv_q(s, s, t0)
                if ts0 < 0:
                    mpz_neg(s, s)

                mpz_pow_ui(t0, s, 2u)
                mpz_addmul(m, k, t0)
                mpz_submul(m, n, s)
                mpz_mul_2exp(t0, s, 1u)
                mpz_submul(n, t0, k)
                mpz_neg(n, n)
                mpz_set(t0, k)
                mpz_set(k, m)
                mpz_set(m, t0)

                mpz_submul(M0, M1, s)
                mpz_neg(t0, M0)
                mpz_set(M0, M1)
                mpz_set(M1, t0)

                mpz_submul(M2, M3, s)
                mpz_neg(t0, M2)
                mpz_set(M2, M3)
                mpz_set(M3, t0)

            # indefinite, so make first coefficient positive
            if mpz_sgn(m) < 0:
                mpz_neg(m, m)
                mpz_neg(k, k)
                mpz_neg(M1, M1)
                mpz_neg(M3, M3)

            is_principal = not mpz_cmp_ui(m, 1u)
            if not is_principal:
                # check to see if the leading coefficient is one
                # for any other form in the cycle
                mpz_init(t1); mpz_init(t2); mpz_init(t3)
                mpz_set(t1, m)
                mpz_set(t2, n)
                mpz_set(t3, k)
                while True:
                    ts0 = mpz_sgn(t3)
                    if ts0 < 0:
                        mpz_neg(t3, t3)
                    mpz_add(s, t2, sqrt_disc.value)
                    mpz_fdiv_q_2exp(s, s, 1u)
                    mpz_fdiv_q(s, s, t3)

                    mpz_pow_ui(t0, s, 2u)
                    if ts0 < 0:
                        mpz_submul(t1, t3, t0)
                    else:
                        mpz_addmul(t1, t3, t0)
                    mpz_addmul(t1, t2, s)
                    mpz_mul_2exp(t0, s, 1u)
                    mpz_submul(t2, t0, t3)
                    mpz_neg(t2, t2)
                    mpz_set(t0, t3)
                    mpz_neg(t3, t1)
                    mpz_set(t1, t0)

                    mpz_addmul(M0, M1, s)
                    mpz_set(t0, M0)
                    mpz_set(M0, M1)
                    mpz_set(M1, t0)

                    mpz_addmul(M2, M3, s)
                    mpz_set(t0, M2)
                    mpz_set(M2, M3)
                    mpz_set(M3, t0)

                    is_principal = not mpz_cmp_ui(t1, 1u)
                    if is_principal or not \
                            (  mpz_cmp(t1, m) \
                            or mpz_cmp(t2, n) \
                            or mpz_cmp(t3, k)):
                        break

                mpz_clear(t1); mpz_clear(t2); mpz_clear(t3)

        if is_principal:
            ret = self._new_elt()
            mpz_mul(ret.a, M0, self.b)
            mpz_addmul(ret.a, M2, self.c)
            mpz_mul(ret.a, ret.a, mpq_numref(self.a))
            mpz_mul(ret.b, M2, mpq_numref(self.a))
            if self._1mod4:
                mpz_mul_2exp(ret.a, ret.a, 1u)
                mpz_add(ret.a, ret.a, M2)
                mpz_mul_2exp(ret.denom, mpq_denref(self.a), 1u)
            else:
                mpz_set(ret.denom, mpq_denref(self.a))

            ret._reduce_c_()
            if mpz_sgn(ret.a) < 0:
                # not necessary, I prefer when at least one of the
                # coefficients is positive
                mpz_neg(ret.a, ret.a)
                mpz_neg(ret.b, ret.b)

        mpz_clear(m); mpz_clear(n); mpz_clear(k); mpz_clear(s)
        mpz_clear(M0); mpz_clear(M1); mpz_clear(M2); mpz_clear(M3)
        mpz_clear(t0)

        if is_principal:
            return ret,
        else:
            return self._integral_basis()

    # methods to be inherited
    def ring(self):
        return self._ring

    def __repr__(self):
        return 'Quadratic Fractional Ideal (' + \
                ', '.join([str(g) for g in self.gens()]) + ')'

    def __add__(left, right):
        return left._add_(right)

    def __mul__(left, right):
        return left._mul_(right)

    def __div__(left, right):
        return left._div_(right)

    def __contains__(self, x):
        try:
            x = self._ring(x)
        except TypeError:
            return False
        return self._contains_(x)

    def __cmp__(left, right):
        return left._cmp_c_impl(right)

    def __richcmp__(left, right, op):
        return (<QuadraticIdeal>left)._richcmp_c_impl(right, op)

    def divides(self, other):
        return self <= other

    def gcd(self, other):
        return self + other

    def is_zero(self):
        return not self

    def gen(self, i):
        return self.gens()[i]
