//===--- BuiltinsM88k.td - M88k Builtin function database ----------------===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//

include "clang/Basic/BuiltinsBase.td"

def FindFirstSet : Builtin {
  let Spellings = ["__builtin_m88k_ff1"];
  let Attributes = [NoThrow, Const];
  let Prototype = "int(unsigned int)";
}

def FindFirstClear : Builtin {
  let Spellings = ["__builtin_m88k_ff0"];
  let Attributes = [NoThrow, Const];
  let Prototype = "int(unsigned int)";
}
