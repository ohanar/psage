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

cdef void mpz_sqrtm(mpz_t r, mpz_t b, mpz_t p):
    # p is assumed to be an odd prime
    # b is assumed to have a square root modulo p

    if mpz_divisible_p(b, p):
        mpz_set_ui(r, 0u)
        return

    if mpz_tstbit(p, 1u):
        # 3mod4 case
        mpz_cdiv_q_2exp(r, p, 2u)
        mpz_powm(r, b, r, p) # r = b**((p+1)/4)
        return

    cdef mpz_t t0, t1
    mpz_init(t0); mpz_init(t1)

    if mpz_tstbit(p, 2u):
        # 5mod8 case
        mpz_mul_2exp(r, b, 1u)
        mpz_tdiv_q_2exp(t0, p, 3u)
        mpz_powm(t0, r, t0, p) # t0 = (2*b)**((p-5)/8)
        mpz_powm_ui(t1, t0, 2u, p)
        mpz_mul(t1, r, t1) # t1 = (2*b)**((p-1)/4)
        mpz_mul(r, t0, b)
        mpz_submul(r, r, t1) # r = b*t0*(1-t1)
        mpz_mod(r, r, p)

        mpz_clear(t0); mpz_clear(t1)
        return

    cdef mpz_t t2, t3
    mpz_init(t2); mpz_init(t3)

    if mpz_tstbit(p, 3u):
        # 9mod16 case
        mpz_mul_2exp(r, b, 1u)
        mpz_tdiv_q_2exp(t3, p, 4u)
        mpz_powm(t0, r, t3, p) # t0 = (2*b)**((p-9)/16)
        mpz_powm_ui(t1, t0, 2u, p)
        mpz_mul(t1, r, t1) # t1 = (2*b)**((p-1)/8)

        mpz_powm_ui(t2, t1, 2u, p)

        if not mpz_cmp_ui(t2, 1u):
            # find a quadratic non-residue
            mpz_set_ui(r, 2u)
            while mpz_legendre(r, p) > -1:
                mpz_add_ui(r, r, 1u)

            # t0 *= r**(p-1)/8
            # t1 *= r**(p-1)/4
            mpz_mul_2exp(t3, t3, 1u)
            mpz_add_ui(t3, t3, 1u)
            mpz_powm(r, r, t3, p)
            mpz_mul(t0, t0, r)
            mpz_powm_ui(r, r, 2u, p)
            mpz_mul(t1, t1, r)

        mpz_mul(r, t0, b)
        mpz_submul(r, r, t1) # r = b*t0*(1-t1)
        mpz_mod(r, r, p)

        mpz_clear(t0); mpz_clear(t1); mpz_clear(t2); mpz_clear(t3)
        return

    # TODO: implement Shanks-Tonelli for 1mod16
    raise NotImplementedError('Shanks-Tonelli not yet implemented')

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
            mpz_mul_2exp(self.b, elt.b, 1u)
            mpz_add(self.c, elt.a, elt.b)
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
        cdef QuadraticIdeal res = self.__copy__()
        res._c_iinvert()
        return res

    def _add_(left, right):
        return left.__copy__()._iadd_(right)

    def _iadd_(self, right):
        self._c_iadd(right)
        return self

    def _mul_(left, right):
        return left.__copy__()._imul_(right)

    def _imul_(self, right):
        self._c_imul(right)
        return self

    def _div_(left, right):
        cdef QuadraticIdeal res = ~right
        res._c_imul(left)
        return res

    def _idiv_(left, right):
        right._c_iinvert()
        left._c_mul(right)
        right._c_iinvert()
        return left

    def __pow__(QuadraticIdeal self, long n, dummy):
        cdef QuadraticIdeal res, tmp
        if n == 0:
            res = self._new()
            mpq_set_ui(res.a, 1u, 1u)
            mpz_set_ui(res.b, 1u)
            mpz_set_ui(res.c, 0u)
            return res
        if n > 0:
            res = self.__copy__()
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
        m = n & 1
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

    cdef void _c_iinvert(self):
        '''
        This function inverts self inplace
        '''
        if not self:
            raise ZeroDivisionError('division by zero')
        mpq_inv(self.a, self.a)
        if mpz_cmp_ui(self.b, 1u):
            # not rational
            if self._1mod4:
                # linear coefficient is 1 instead of 0
                mpz_sub(self.c, self.b, self.c)
                mpz_sub_ui(self.c, self.c, 1u)
            elif mpz_sgn(self.c):
                # there is a non-ramified prime divisor
                mpz_sub(self.c, self.b, self.c)
            mpz_mul(mpq_denref(self.a), mpq_denref(self.a), self.b)
            mpq_canonicalize(self.a)

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
        # quickly handle when if zero
        if not self: return

        # the factored out portion can be squared directly
        mpz_pow_ui(mpq_numref(self.a), mpq_numref(self.a), 2u)
        mpz_pow_ui(mpq_denref(self.a), mpq_denref(self.a), 2u)

        # if rational, then we are done
        if not mpz_cmp_ui(self.b, 1u): return

        # We are computing the HNF of
        # [ b*b b*c c*c+D ]
        # [   0   b   2*c ]

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
        # quickly handle when one factor is zero
        if not right: return
        if not self:
            mpq_set(self.a, right.a)
            mpz_set(self.b, right.b)
            mpz_set(self.c, right.c)
            return

        # quickly handle when both ideals are rational
        if not mpz_cmp_ui(self.b, 1u) and not mpz_cmp_ui(right.b, 1u):
            mpz_gcd(mpq_numref(self.a), mpq_numref(self.a), \
                    mpq_numref(right.a))
            mpz_lcm(mpq_denref(self.a), mpq_denref(self.a), \
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
            mpz_divexact(mpq_numref(self.a), mpq_numref(self.a), \
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
        cdef mpz_t t0

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

            # z = t0/(a*x.denom)
            # check to see if z is integral, if so compute
            if not mpz_divisible_p(t0, mpq_numref(self.a)):
                mpz_clear(t0)
                return False
            mpz_init(t1)
            mpz_divexact(t1, t0, mpq_numref(self.a))
            mpz_mul(t1, t1, mpq_denref(self.a))
            if mpz_divisible_p(t1, x.denom):
                mpz_divexact(t1, t1, x.denom)
            else:
                mpz_clear(t0); mpz_clear(t1)
                return False

            mpz_sub(t0, x.a, x.b) # t0 = x.a-x.b
            # y = (t0/(a*x.denom) - c*z)/b
            # check to see if y is integral
            if not mpz_divisible_p(t0, mpq_numref(self.a)):
                mpz_clear(t0); mpz_clear(t1)
                return False
            mpz_init(t2)
            mpz_divexact(t2, t0, mpq_numref(self.a))
            mpz_mul(t2, t2, mpq_denref(self.a))
            if mpz_divisible_p(t2, x.denom):
                mpz_divexact(t2, t2, x.denom)
            else:
                mpz_clear(t0); mpz_clear(t1); mpz_clear(t2)
                return False
            mpz_submul(t2, t1, self.c)
            ret = mpz_divisible_p(t2, self.b)

            mpz_clear(t0); mpz_clear(t1); mpz_clear(t2)
        else:
            # want to solve
            # [ a*b a*c ] * [ y ] = [ x.a/x.denom ]
            # [   0   a ] * [ z ] = [ x.b/x.denom ]
            # for integers y, z

            # z = x.b/(a*x.denom)
            # y = (x.a/(a*x.denom) - c*z)/b
            # some quick checks
            if not mpz_divisible_p(x.b, mpq_numref(self.a)):
                return False
            if not mpz_divisible_p(x.a, mpq_numref(self.a)):
                return False

            # check to see if z is integral, if so compute
            mpz_init(t0)
            mpz_divexact(t0, x.b, mpq_numref(self.a))
            mpz_mul(t0, t0, mpq_denref(self.a))
            if mpz_divisible_p(t0, x.denom):
                mpz_divexact(t0, t0, x.denom)
            else:
                mpz_clear(t0)
                return False

            # check to see if y is integral
            mpz_init(t1)
            mpz_divexact(t1, x.a, mpq_numref(self.a))
            mpz_mul(t1, t1, mpq_denref(self.a))
            if mpz_divisible_p(t1, x.denom):
                mpz_divexact(t1, t1, x.denom)
            else:
                mpz_clear(t0); mpz_clear(t1)
                return False
            mpz_submul(t1, t0, self.c)
            ret = mpz_divisible_p(t1, self.b)

            mpz_clear(t0); mpz_clear(t1)
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

    def is_one(self):
        return not (mpz_cmp_ui(self.b, 1u) or mpq_cmp_ui(self.a, 1u, 1u))

    def factor(self, proof=None):
        # we piggy back off of integer factorization
        cdef QuadraticIdeal tmp
        cdef Integer p, z = PY_NEW(Integer)
        cdef dict f_dict = {}
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

    gens = integral_basis

#    def gen_tuple(self):
#        try:
#            return self._gen
#        except AttributeError:
#            pass
#        if not self.r:
#            self._gen = self.gcd, 0
#            return self._gen
#        cdef long Nr = self.r*(self.r+1)-1
#        if Nr == self.n:
#            self._gen = std_tuple(self.gcd*self.r, self.gcd)
#            return self._gen
#        # find a generator by solving n*x^2+(2*r+1)*x*y+N(r)/n*y^2 == 1
#        # using the convergents of the continued fractions for -(r+a)/p
#        # where a is (1+/-sqrt(5))/2
#        Nr /= self.n
#        cdef long rg = 2*self.r+1
#        cdef long p1 = 0, q1 = 1
#        cdef long p2 = 1, q2 = 0
#        cdef long p3 = 0, q3 = 1
#        cdef long p4 = 1, q4 = 0
#        cdef long b1=-rg,c1=1,d1=2*self.n
#        cdef long b2=b1,c2=c1,d2=d1
#        cdef long an
#        cdef long N1 = self.n*p2*p2
#        cdef long N2 = N1
#        cdef long t
#        while True:
#            t1 = 5*c1*c1
#            t2 = sqrt_ceil(t1)
#            an = (b1+t2)/d1
#            p2,p1 = p2*an+p1,p2
#            q2,q1 = q2*an+q1,q2
#            N = (self.n*p2+rg*q2)*p2+Nr*q2*q2
#            if N == 1 or N == -1:
#                self._gen = std_tuple(self.gcd*(p2*self.n+q2*self.r), \
#                        self.gcd*q2)
#                return self._gen
#            b1 -= d1*an
#            b1, c1, d1 = b1*d1, c1*d1, b1*b1-t1
#            if d1 < 0:
#                b1, d1 = -b1, -d1
#            t1 = gcd(b1, c1, d1)
#            b1 /= t1; c1 /= t1; d1 /= t1
#
#            t1 = 5*c2*c2
#            t2 = sqrt_ceil(t1)
#            an = (b2-t2)/d2
#            p4,p3 = p4*an+p3,p4
#            q4,q3 = q4*an+q3,q4
#            N = (self.n*p4+rg*q4)*p4+Nr*q4*q4
#            if N == 1 or N == -1:
#                self._gen = std_tuple(self.gcd*(p4*self.n+q4*self.r), \
#                        self.gcd*q4)
#                return self._gen
#            b2 -= d2*an
#            b2, c2, d2 = b2*d2, c2*d2, b2*b2-t1
#            if d1 < 0:
#                b1, d1 = -b1, -d1
#            t1 = gcd(b1, c1, d1)
#            b1 /= t1; c1 /= t1; d1 /= t1

    # methods to be inherited
    def ring(self):
        return self._ring

    def __repr__(self):
        cdef Rational t = PY_NEW(Rational)
        cdef Integer T = PY_NEW(Integer)
        mpq_set(t.value, self.a)
        mpz_set(T.value, self.b)
        s = '('+T.str() + ', x + '
        mpz_set(T.value, self.c)
        return t.str()+s+T.str()+')'

    def __add__(left, right):
        return left._add_(right)

    def __iadd__(left, right):
        return left._iadd_(right)

    def __mul__(left, right):
        return left._mul_(right)

    def __imul__(self, right):
        return self._imul_(right)

    def __div__(left, right):
        return left._div_(right)

    def __idiv__(self, right):
        return self._idiv_(right)

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
