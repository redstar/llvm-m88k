//===----------------------------------------------------------------------===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//

// UNSUPPORTED: no-localization

// <random>

// template<class RealType = double>
// class gamma_distribution

// template <class CharT, class Traits, class RealType>
// basic_ostream<CharT, Traits>&
// operator<<(basic_ostream<CharT, Traits>& os,
//            const gamma_distribution<RealType>& x);

// template <class CharT, class Traits, class RealType>
// basic_istream<CharT, Traits>&
// operator>>(basic_istream<CharT, Traits>& is,
//            gamma_distribution<RealType>& x);

#include <random>
#include <sstream>
#include <cassert>

#include "test_macros.h"

int main(int, char**)
{
    {
        typedef std::gamma_distribution<> D;
        D d1(7, 5);
        std::ostringstream os;
        os << d1;
        std::istringstream is(os.str());
        D d2;
        is >> d2;
        assert(d1 == d2);
    }

  return 0;
}
