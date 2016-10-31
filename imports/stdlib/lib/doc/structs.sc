/*
 * Copyright (C) 2015 Cybernetica
 *
 * Research/Commercial License Usage
 * Licensees holding a valid Research License or Commercial License
 * for the Software may use this file according to the written
 * agreement between you and Cybernetica.
 *
 * GNU Lesser General Public License Usage
 * Alternatively, this file may be used under the terms of the GNU Lesser
 * General Public License version 3 as published by the Free Software
 * Foundation and appearing in the file LICENSE.LGPLv3 included in the
 * packaging of this file.  Please review the following information to
 * ensure the GNU Lesser General Public License version 3 requirements
 * will be met: http://www.gnu.org/licenses/lgpl-3.0.html.
 *
 * For further information, please contact us at sharemind@cyber.ee.
 */

/**
@page structs Data structures
@brief Data structures in SecreC

@section structs Data structures

SecreC supports basic data structures currently intended to be used for returning multiple values from functions and for simple aggregation of data. The types of structure fields is not restricted in any way: it's possible to store other structures, arrays and private data within a structure. Structures themselves, however, are limited in multiple ways. Namely, they are restricted to be public data and may not not be stored as elements of arrays.

For example, to two-dimensional integer elements can be implemented as a structure with two integer fields x and y.

Listing 6.34: Example of a data structure definition
\code
    struct elem2d {
        int x;
        int y;
    }

    public elem2d v;
    v.x = 1;
    v.y = 2;
\endcode

The language also supports polymorphic structures. A structure may have various type-level parameters that all need to be specified whenever a structure with that name is used. The previous structure can be declared type-polymorphically in which case, when defining data of that type, the type parameter has to be specified as well.

Listing 6.35: Example of a type-polymorhic data structure
\code
    template <type T>
    struct elem2d {
        T x;
        T y;
    }

    public elem2d<int> v;
    v.x = 1;
    v.y = 2;
\endcode

Structures may also be polymorphic over protection domains.

Listing 6.36: Example of a domain-polymorphic data structure
\code
    template <domain D, type T>
    struct elem2d {
        D T x;
        D T y;
    }

    public elem2d<pd_shared3p, int> v;
    v.x = 1;
    v.y = 2;
\endcode

*/
