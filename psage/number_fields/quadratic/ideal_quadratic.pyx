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

cdef mpz_t mpz_tmp0, mpz_tmp1, mpz_tmp2, mpz_tmp3
mpz_init(mpz_tmp0); mpz_init(mpz_tmp1); mpz_init(mpz_tmp2); mpz_init(mpz_tmp3)

cdef Integer int_tmp0, int_tmp1
int_tmp0 = PY_NEW(Integer); int_tmp1 = PY_NEW(Integer)

cdef Rational rat_tmp
rat_tmp = PY_NEW(Rational)

cdef void mpz_sqrtm(mpz_t r, mpz_t b, mpz_t p):
    # p is assumed to be an odd prime
    # b is assumed to have a square root modulo p

    if mpz_divisible_p(b, p):
        mpz_set_ui(r, 0u)
        return

    if mpz_tstbit(p, 1u):
        # 3mod4 case
        mpz_add_ui(r, p, 1u)
        mpz_fdiv_q_2exp(r, r, 2u)
        mpz_powm(r, b, r, p)
        return

    if mpz_tstbit(p, 2u):
        # 5mod8 case
        mpz_mul_2exp(r, b, 1u)
        mpz_sub_ui(mpz_tmp0, p, 5u)
        mpz_fdiv_q_2exp(mpz_tmp0, mpz_tmp0, 3u)
        mpz_powm(mpz_tmp0, r, mpz_tmp0, p)
        mpz_powm_ui(mpz_tmp1, mpz_tmp0, 2u, p)
        mpz_mul(mpz_tmp1, r, mpz_tmp1)
        mpz_mul(r, mpz_tmp0, b)
        mpz_submul(r, r, mpz_tmp1)
        mpz_mod(r, r, p)
        return

    if mpz_tstbit(p, 3u):
        # 9mod16 case
        mpz_mul_2exp(r, b, 1u)
        mpz_sub_ui(mpz_tmp3, p, 9u)
        mpz_fdiv_q_2exp(mpz_tmp3, mpz_tmp3, 4u)
        mpz_powm(mpz_tmp0, r, mpz_tmp3, p)
        mpz_powm_ui(mpz_tmp1, mpz_tmp0, 2u, p)
        mpz_mul(mpz_tmp1, r, mpz_tmp1)

        mpz_powm_ui(mpz_tmp2, mpz_tmp1, 2u, p)

        if not mpz_cmp_ui(mpz_tmp2, 1u):
            # find a quadratic non-residue
            mpz_set_ui(r, 2u)
            while mpz_legendre(r, p) != -1:
                mpz_add_ui(r, r, 1u)

            # mpz_tmp0 *= r**(p-1)/8
            # mpz_tmp1 *= r**(p-1)/4
            mpz_mul_2exp(mpz_tmp3, mpz_tmp3, 1u)
            mpz_add_ui(mpz_tmp3, mpz_tmp3, 1u)
            mpz_powm(r, r, mpz_tmp3, p)
            mpz_mul(mpz_tmp0, mpz_tmp0, r)
            mpz_powm_ui(r, r, 2u, p)
            mpz_mul(mpz_tmp1, mpz_tmp1, r)

        mpz_mul(r, mpz_tmp0, b)
        mpz_submul(r, r, mpz_tmp1)
        mpz_mod(r, r, p)
        return

    # TODO: implement Shanks-Tonelli for 1mod16
    raise NotImplementedError('Shanks-Tonelli not yet implemented')

cdef class QuadraticIdeal:
    def __init__(self, I):
    # currently is just constructed from sage ideal (using integral basis)
        self._ring = I.ring()
        self.D = <Integer>self._ring._D
        self._1mod4 = mpz_tstbit(self.D.value, 0u) \
                and not mpz_tstbit(self.D.value, 1u)
        self._1mod8 = self._1mod4 and not mpz_tstbit(self.D.value, 2u)
        if self._1mod8:
            try:
                self.F = <Integer>self._ring._F
            except AttributeError:
                self._ring._F = (self.D-1)/4
                self.F = <Integer>self._ring._F

        cdef NumberFieldElement_quadratic a, b
        a,b = I.integral_basis()
        if self._1mod8:
             # 2 splits, so we have to do things differently here
             raise NotImplementedError
        else:
            if self._1mod4:
                # in this case we multiply b by two
                # which is fine since 2 is inert for 5mod8
                b *= 2
            # in this case, we know that the denominators should be equal
            assert not mpz_cmp(a.denom, b.denom)
            mpz_set(mpq_denref(self.a), a.denom)
            # we also know that b.b should divide both a.a and b.a
            assert mpz_divisible_p(a.a, b.b) and mpz_divisible_p(b.a, b.b)
            mpz_set(mpq_numref(self.a), b.b)
            mpz_divexact(self.b, a.a, b.b)
            mpz_divexact(self.c, b.a, b.b)
            if self._1mod4:
                # sometimes some extra reduction might be needed now
                mpz_mod(self.c, self.c, self.b)

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
        res._1mod4 = self._1mod4
        res._1mod8 = self._1mod8
        if res._1mod8:
            res.F = self.F
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

    def __mul__(left, right):
        return left._mul_(right)

    def __imul__(self, right):
        return self._imul_(right)

    def __div__(left, right):
        return left._div_(right)

    def __idiv__(self, right):
        return self._idiv_(right)

    def __contains__(self, x):
        return self._contains_(self._ring(x))

    def __cmp__(left, right):
        return left._cmp_c_impl(right)

    # keep from here on
    def __invert__(self):
        cdef QuadraticIdeal res = self.__copy__()
        res._c_iinvert()
        return res

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

        #res._c_isq()
        res._c_imul(res)
        if n == 2:
            return res
        if n == 3:
            res._c_imul(self)
            return res
        m = n & 1
        n >>= 1
        while not n&1:
            #res._c_isq()
            res._c_imul(res)
            n >>= 1
        n >>= 1
        tmp = res.__copy__()
        if m:
            res._c_imul(self)

        while n:
            #tmp._c_isq()
            tmp._c_imul(tmp)
            if n&1:
                res._c_imul(tmp)
            n >>= 1
        return res

    cdef void _c_iinvert(self):
        '''
        This function inverts self inplace
        '''
        if not mpq_sgn(self.a):
            raise ZeroDivisionError('division by zero')
        mpq_inv(self.a, self.a)
        if mpz_cmp_ui(self.b, 1u):
            # in this case the generators are not in QQ
            if mpz_sgn(self.c):
                mpz_sub(self.c, self.b, self.c)
                if self._1mod8:
                    # the linear coefficient is -1 instead of 0
                    # in this case
                    mpz_sub_ui(self.c, self.c, 1u)
            mpz_mul(mpq_denref(self.a), mpq_denref(self.a), self.b)
            mpq_canonicalize(self.a)

    # this method could probably be improved
    cdef void _c_imul(self, QuadraticIdeal right):
        '''
        This function multiplies self by right inplace
        '''
        # quickly handle when one factor is zero
        if not mpq_sgn(self.a): return
        if not mpq_sgn(right.a):
            mpq_set_ui(self.a, 0u, 1u)
            mpz_set_ui(self.b, 1u)
            mpz_set_ui(self.c, 0u)
            return

        # the factored out portion can be multiplied directly
        mpq_mul(self.a, self.a, right.a)

        mpz_gcdext(mpz_tmp0, mpz_tmp1, mpz_tmp2, self.b, right.b)
        mpz_mul(mpz_tmp1, mpz_tmp1, self.b)
        mpz_mul(mpz_tmp2, mpz_tmp2, right.b)
        mpz_mul(self.b, self.b, right.b)
        if not mpz_cmp_ui(mpz_tmp0, 1u): # if gcd = 1, simple case
            mpz_mul(self.c, mpz_tmp2, self.c)
            mpz_addmul(self.c, mpz_tmp1, right.c)
            mpz_mod(self.c, self.c, self.b)
            return
        # gcd > 1, need to do another xgcd
        mpz_mul(mpz_tmp2, mpz_tmp2, self.c)
        mpz_addmul(mpz_tmp2, mpz_tmp1, right.c)
        mpz_add(mpz_tmp1, self.c, right.c)
        mpz_mul(self.c, self.c, right.c)
        # TODO: fix for 1mod8 case
        mpz_add(self.c, self.c, self.D.value)
        mpz_gcdext(mpz_tmp0, mpz_tmp1, mpz_tmp3, mpz_tmp0, mpz_tmp1)
        mpz_mul(self.c, mpz_tmp3, self.c)
        mpz_addmul(self.c, mpz_tmp1, mpz_tmp2)
        if mpz_cmp_ui(mpz_tmp0, 1u): # if gcd > 1, have to do a bit extra
            mpz_divexact(self.b, self.b, mpz_tmp0)
            mpz_divexact(self.b, self.b, mpz_tmp0)
            mpz_divexact(self.c, self.c, mpz_tmp0)
            mpz_mul(mpq_numref(self.a), mpq_numref(self.a), mpz_tmp0)
            mpq_canonicalize(self.a)
        mpz_mod(self.c, self.c, self.b)

    # TODO: Currently broken, fix
    cdef void _c_isq(self):
        '''
        This function squares self inplace
        '''
        if not mpq_sgn(self.a): return

        mpz_pow_ui(mpq_numref(self.a), mpq_numref(self.a), 2u)
        mpz_pow_ui(mpq_denref(self.a), mpq_denref(self.a), 2u)

        if not mpq_cmp_ui(self.a, 1u, 1u):
            return

        if not self._1mod8 and not mpz_sgn(self.c):
            mpz_mul(mpq_numref(self.a), mpq_numref(self.a), self.b)
            mpq_canonicalize(self.a)
            mpz_divexact(mpz_tmp0, self.b, self.D.value)
            mpz_gcd(self.b, self.b, mpz_tmp0)
            return

        mpz_mul_2exp(mpz_tmp0, self.c, 1u)
        mpz_gcdext(mpz_tmp0, mpz_tmp1, mpz_tmp2, self.b, mpz_tmp0)
        mpz_mul(mpz_tmp1, mpz_tmp1, self.c)
        mpz_pow_ui(self.c, self.c, 2u)
        mpz_add(self.c, self.c, self.D.value)
        mpz_mul(self.c, self.c, mpz_tmp2)
        mpz_addmul(self.c, self.b, mpz_tmp1)
        mpz_pow_ui(self.b, self.b, 2u)
        if mpz_cmp_ui(mpz_tmp0, 1u):
            mpz_divexact(self.b, self.b, mpz_tmp0)
            mpz_divexact(self.c, self.c, mpz_tmp0)
            mpz_mul(mpq_numref(self.a), mpq_numref(self.a), mpz_tmp0)
            mpq_canonicalize(self.a)
        mpz_mod(self.c, self.c, self.b)

    cdef int _cmp_c_impl(left, right_py):
        # for quick sorting
        # richcmp is used for poset order based on containment
        cdef int res
        cdef QuadraticIdeal right = right_py
        # sort by norm, and then lexigraphically by b and c
        res = cmp(left.norm(), right.norm())
        if res:
            return res
        res = mpz_cmp(left.b, right.b)
        if res:
            return res
        return mpz_cmp(left.c, right.c)

    def __hash__(self):
        mpq_set(rat_tmp.value, self.a)
        mpz_set(int_tmp0.value, self.b)
        mpz_set(int_tmp1.value, self.c)
        return hash((rat_tmp,int_tmp0,int_tmp1))

    cpdef QuadraticIdeal __copy__(self):
        cdef QuadraticIdeal res = self._new()
        mpq_set(res.a, self.a)
        mpz_set(res.b, self.b)
        mpz_set(res.c, self.c)
        return res

    # TODO: make sure logic works for 1mod8 (probably doesn't)
    cpdef bint _contains_(self, x):
        cdef NumberFieldElement_quadratic y = x

        if not mpz_sgn(y.b): # in this case x in QQ
            mpz_mul(mpz_tmp0, y.a, mpq_denref(self.a))
            mpz_mul(mpz_tmp1, y.denom, mpq_numref(self.a))
            mpz_mul(mpz_tmp1, mpz_tmp1, self.b)
            return mpz_divisible_p(mpz_tmp0, mpz_tmp1)

        mpz_mul(mpz_tmp0, y.b, mpq_denref(self.a))
        if self._1mod4:
            mpz_mul_2exp(mpz_tmp0, mpz_tmp0, 1u)
        mpz_mul(mpz_tmp1, y.denom, mpq_numref(self.a))

        if not mpz_divisible_p(mpz_tmp0, mpz_tmp1):
            return False

        if self._1mod4:
            mpz_cdiv_q_2exp(mpz_tmp1, self.b, 1u)
            mpz_mul(mpz_tmp0, mpz_tmp0, mpz_tmp1)
            mpz_sub_ui(mpz_tmp1, self.c, 1u)
            mpz_mul(mpz_tmp0, mpz_tmp0, mpz_tmp1)
            mpz_sub(mpz_tmp1, y.a, y.b)
            mpz_submul(mpz_tmp0, mpz_tmp1, mpq_denref(self.a))
        else:
            mpz_mul(mpz_tmp0, mpz_tmp0, self.c)
            mpz_submul(mpz_tmp0, y.a, mpq_denref(self.a))

        mpz_mul(mpz_tmp1, self.b, mpq_numref(self.a))
        mpz_mul(mpz_tmp1, mpz_tmp1, y.denom)

        return mpz_divisible_p(mpz_tmp0, mpz_tmp1)

    cpdef Rational norm(self):
        # norm = a^2*b
        cdef Rational res = PY_NEW(Rational)
        mpz_pow_ui(mpq_numref(res.value), mpq_numref(self.a), 2u)
        mpz_pow_ui(mpq_denref(res.value), mpq_denref(self.a), 2u)
        mpz_mul(mpq_numref(res.value), mpq_numref(res.value), self.b)
        mpq_canonicalize(res.value)
        return res

    cpdef bint is_integral(self):
        return mpz_cmp_ui(mpq_denref(self.a), 1u) == 0

    def integral_basis(self):
        if self._1mod8 or not self._1mod4:
            return self.gens()

        # in the case of 5mod8 we do not use an integral basis internally
        cdef NumberFieldElement_quadratic x, y
        x, y = self._new_elt(), self._new_elt()

        # x = self.a*self.b
        mpz_mul(x.a, mpq_numref(self.a), self.b)
        mpz_set_ui(x.b, 0u)
        mpz_set(x.denom, mpq_denref(self.a))

        # y = (self.a/2)*(sqrt(D)+
        #                   1+2*(((self.b+1)/2)*(self.c-1)%self.b)
        #                )
        mpz_set(y.b, mpq_numref(self.a))
        if mpz_sgn(self.c):
            mpz_cdiv_q_2exp(y.a, self.b, 1u)
            mpz_submul(y.a, self.c, y.a)
            mpz_neg(y.a, y.a)
            mpz_mod(y.a, y.a, self.b)

            mpz_mul_2exp(y.a, y.a, 1u)
            mpz_add_ui(y.a, y.a, 1u)
        else:
            # in the ramified case, everything simplifies
            mpz_set(y.a, self.b)
        mpz_mul(y.a, mpq_numref(self.a), y.a)
        mpz_set(y.denom, mpq_denref(self.a))
        mpz_mul_2exp(y.denom, y.denom, 1u)
        y._reduce_c_()

        return x,y

#    def divides(self, x):
#        # TODO: add special case for Integer and Rational
#        cdef QuadraticIdeal other
##        other = self._parent(x)
#        other = x
#
#        # a*b in me
#        #
#        if not mpz_divides_p():
#            return False

#        if right.gcd%self.gcd: return False
#        cdef long t = right.gcd/self.gcd
#        if t*right.n%self.n: return False
#        if t*(right.r-self.r)%self.n: return False
#        return True

    def factor(self):
        # we piggy back off of integer factorization
        cdef QuadraticIdeal tmp
        cdef Integer p
        cdef dict f_dict = {}
        cdef bint inert
        mpz_set(int_tmp0.value, self.b)
        for p, e in int_tmp0.factor():
            tmp = self._new()
            mpq_set_ui(tmp.a, 1u, 1u)
            mpz_set(tmp.b, p.value)
            mpz_mod(tmp.c, self.c, tmp.b)
            f_dict[tmp] = e
        mpz_set(int_tmp0.value, mpq_numref(self.a))
        h_factor = dict(int_tmp0.factor())
        mpz_set(int_tmp0.value, mpq_denref(self.a))
        for p, e in int_tmp0.factor():
            if p in h_factor:
                h_factor[p] -= e
            else:
                h_factor[p] = -e
        for p, e in h_factor.iteritems():
            # use the legendre symbol to determine whether or not p splits
            if not mpz_tstbit(p.value, 0u):
                # 2 breaks the legendre symbol, so deal with it separately
                # 2 is only inert if D is 5mod8
                inert = self._1mod4 and not self._1mod8
            else:
                inert = mpz_legendre(self.D.value, p.value) == -1

            tmp = self._new()
            if inert:
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
                if self._1mod8:
                    # tmp.c = (1+tmp.c)/2 (mod tmp.b)
                    mpz_add_ui(tmp.c, tmp.c, 1u)
                    if not mpz_tstbit(tmp.c, 0u):
                        mpz_addmul(tmp.c, tmp.c, tmp.b)
                        mpz_fdiv_q_2exp(tmp.c, tmp.c, 1u)
                        mpz_mod(tmp.c, tmp.c, tmp.b)
                    else:
                        mpz_fdiv_q_2exp(tmp.c, tmp.c, 1u)

            if tmp in f_dict:
                f_dict[tmp] += e
            else:
                f_dict[tmp] = e

            if not mpz_tstbit(p.value, 0u):
                # test 2 for ramification seperately
                if not self._1mod8:
                    f_dict[tmp] += e
                    continue
            elif mpz_divisible_p(self.D.value, p.value):
                # ramified, so we don't have a conjugate
                # so just double the exponent
                f_dict[tmp] += e
                continue

            # construct conjugate
            tmp = tmp.__copy__()
            mpz_sub(tmp.c, tmp.b, tmp.c)
            if tmp._1mod8:
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
        if not self.is_integral():
            return False
        # inert primes have b = 1, split/ramified primes have a = 1
        cdef bint inert, split
        split = mpz_cmp_ui(mpq_numref(self.a), 1u) == 0
        inert = mpz_cmp_ui(self.b, 1u) == 0
        if split and inert:
            # the case when I = K
            return False
        if not (split or inert):
            # both not inert and not split, so not prime
            return False
        if inert:
            # we are in the case of I=(a), so first check if
            # we have splitting by using the kronecker symbol
            if not mpz_tstbit(mpq_numref(self.a), 0u):
                # even things break the kronecker, so deal
                # with them separately
                if mpz_cmp_ui(mpq_numref(self.a), 2u):
                    # not 2, so done
                    return False
                if self._1mod4 and not self._1mod8:
                    # D = 5mod8, the only case (2) is prime
                    return True
                return False
            elif mpz_kronecker(self.D.value, mpq_numref(self.a)) > -1:
                return False

            # no splitting, so make check to see if a is prime over ZZ
            mpz_set(int_tmp0.value, mpq_numref(self.a))
        else: # split/ramified case
            mpz_set(int_tmp0.value, self.b)
        # we piggy back off of Integer's is_prime
        return int_tmp0.is_prime(proof=proof)

    def gens(self):
        cdef NumberFieldElement_quadratic x, y
        x, y = self._new_elt(), self._new_elt()

        # x = self.a*self.b
        mpz_mul(x.a, mpq_numref(self.a), self.b)
        mpz_set_ui(x.b, 0u)
        mpz_set(x.denom, mpq_denref(self.a))
        x._reduce_c_()

        if self._1mod8:
            # y = self.a*(X+self.c)
            #   = self.a*(sqrt(D)+1+2*self.c)/2
            mpz_mul_2exp(y.a, self.c, 1u)
            mpz_add_ui(y.a, y.a, 1u)
            mpz_set(y.b, mpq_numref(self.a))
            mpz_mul_2exp(y.denom, mpq_denref(self.a), 1u)
            y._reduce_c_()
        else:
            # y = self.a*(sqrt(D)+self.c)
            mpz_mul(y.a, mpq_numref(self.a), self.c)
            mpz_set(y.b, mpq_numref(self.a))
            mpz_set(y.denom, mpq_denref(self.a))
        return x,y

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
