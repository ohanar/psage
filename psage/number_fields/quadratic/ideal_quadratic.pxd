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

include 'cdefs.pxi'

from sage.rings.integer cimport Integer
from sage.rings.rational cimport Rational
from sage.rings.number_field.number_field_element_quadratic cimport NumberFieldElement_quadratic

cdef class QuadraticIdeal:
    cdef object _ring

    # if D != 1 (mod 8), then we store
    # I = a(b,sqrt(D)+c), where b,c in ZZ, c^2 = D (mod b)
    # if D = 1 (mod 8), then we store
    # I = a(b,X+c), where b,c in ZZ, c^2 = c+F (mod b)
    # and X^2-X-F = 0, with F = (D-1)/4
    cdef mpq_t a
    cdef mpz_t b, c
    cdef Integer D
    cdef Integer F

    cdef bint _1mod4
    cdef bint _1mod8

    cpdef Rational norm(self)
    cpdef bint is_integral(self)

    cdef QuadraticIdeal _new(self)
    cdef NumberFieldElement_quadratic _new_elt(self)

    cpdef QuadraticIdeal __copy__(self)

    cdef void _c_iinvert(self)
    cdef void _c_imul(self, QuadraticIdeal right)
    cdef void _c_isq(self)

    # to inherit
    cpdef bint _contains_(self, x)
