//===-- Unittests for nextafterf128 ---------------------------------------===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//

#include "NextAfterTest.h"

#include "src/math/nextafterf128.h"

LIST_NEXTAFTER_TESTS(float128, LIBC_NAMESPACE::nextafterf128)
