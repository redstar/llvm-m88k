// RUN: %clang_cc1 %s -O0 -emit-llvm -triple x86_64-unknown-unknown -o - | FileCheck %s --check-prefix=X86
// RUN: %clang_cc1 %s -O0 -emit-llvm -triple x86_64-pc-win64 -o - | FileCheck %s --check-prefix=X86
// RUN: %clang_cc1 %s -O0 -emit-llvm -triple i686-unknown-unknown -o - | FileCheck %s --check-prefix=X86
// RUN: %clang_cc1 %s -O0 -emit-llvm -triple powerpc-unknown-unknown -o - | FileCheck %s --check-prefix=PPC
// RUN: %clang_cc1 %s -O0 -emit-llvm -triple armv7-none-linux-gnueabi -o - | FileCheck %s --check-prefix=ARM
// RUN: %clang_cc1 %s -O0 -emit-llvm -triple armv7-none-linux-gnueabihf -o - | FileCheck %s --check-prefix=ARMHF
// RUN: %clang_cc1 %s -O0 -emit-llvm -triple thumbv7k-apple-watchos2.0 -o - -target-abi aapcs16 | FileCheck %s --check-prefix=ARM7K
// RUN: %clang_cc1 %s -O0 -emit-llvm -triple aarch64-unknown-unknown -ffast-math -ffp-contract=fast -complex-range=improved -o - | FileCheck %s --check-prefix=AARCH64-FASTMATH
// RUN: %clang_cc1 %s -O0 -emit-llvm -triple spir -o - | FileCheck %s --check-prefix=SPIR

float _Complex add_float_rr(float a, float b) {
  // X86-LABEL: @add_float_rr(
  // X86: fadd
  // X86-NOT: fadd
  // X86: ret
  return a + b;
}
float _Complex add_float_cr(float _Complex a, float b) {
  // X86-LABEL: @add_float_cr(
  // X86: fadd
  // X86-NOT: fadd
  // X86: ret
  return a + b;
}
float _Complex add_float_rc(float a, float _Complex b) {
  // X86-LABEL: @add_float_rc(
  // X86: fadd
  // X86-NOT: fadd
  // X86: ret
  return a + b;
}
float _Complex add_float_cc(float _Complex a, float _Complex b) {
  // X86-LABEL: @add_float_cc(
  // X86: fadd
  // X86: fadd
  // X86-NOT: fadd
  // X86: ret
  return a + b;
}

float _Complex sub_float_rr(float a, float b) {
  // X86-LABEL: @sub_float_rr(
  // X86: fsub
  // X86-NOT: fsub
  // X86: ret
  return a - b;
}
float _Complex sub_float_cr(float _Complex a, float b) {
  // X86-LABEL: @sub_float_cr(
  // X86: fsub
  // X86-NOT: fsub
  // X86: ret
  return a - b;
}
float _Complex sub_float_rc(float a, float _Complex b) {
  // X86-LABEL: @sub_float_rc(
  // X86: fsub
  // X86: fneg
  // X86-NOT: fsub
  // X86: ret
  return a - b;
}
float _Complex sub_float_cc(float _Complex a, float _Complex b) {
  // X86-LABEL: @sub_float_cc(
  // X86: fsub
  // X86: fsub
  // X86-NOT: fsub
  // X86: ret
  return a - b;
}

float _Complex mul_float_rr(float a, float b) {
  // X86-LABEL: @mul_float_rr(
  // X86: fmul
  // X86-NOT: fmul
  // X86: ret
  return a * b;
}
float _Complex mul_float_cr(float _Complex a, float b) {
  // X86-LABEL: @mul_float_cr(
  // X86: fmul
  // X86: fmul
  // X86-NOT: fmul
  // X86: ret
  return a * b;
}
float _Complex mul_float_rc(float a, float _Complex b) {
  // X86-LABEL: @mul_float_rc(
  // X86: fmul
  // X86: fmul
  // X86-NOT: fmul
  // X86: ret
  return a * b;
}

float _Complex mul_float_cc(float _Complex a, float _Complex b) {
  // X86-LABEL: @mul_float_cc(
  // X86: %[[AC:[^ ]+]] = fmul
  // X86: %[[BD:[^ ]+]] = fmul
  // X86: %[[AD:[^ ]+]] = fmul
  // X86: %[[BC:[^ ]+]] = fmul
  // X86: %[[RR:[^ ]+]] = fsub
  // X86: %[[RI:[^ ]+]] = fadd
  // X86-DAG: %[[AD]]
  // X86-DAG: ,
  // X86-DAG: %[[BC]]
  // X86: fcmp uno float %[[RR]]
  // X86: fcmp uno float %[[RI]]
  // X86: call {{.*}} @__mulsc3(
  // X86: ret
  // SPIR: call spir_func {{.*}} @__mulsc3(
  return a * b;
}

float _Complex div_float_rr(float a, float b) {
  // X86-LABEL: @div_float_rr(
  // X86: fdiv
  // X86-NOT: fdiv
  // X86: ret
  return a / b;
}
float _Complex div_float_cr(float _Complex a, float b) {
  // X86-LABEL: @div_float_cr(
  // X86: fdiv
  // X86: fdiv
  // X86-NOT: fdiv
  // X86: ret
  return a / b;
}
float _Complex div_float_rc(float a, float _Complex b) {
  // X86-LABEL: @div_float_rc(
  // X86-NOT: fdiv
  // X86: call {{.*}} @__divsc3(
  // X86: ret

  // SPIR: call spir_func {{.*}} @__divsc3(

  // a / b = (A+iB) / (C+iD) = (E+iF)
  // if (|C| >= |D|)
  //   DdC = D/C
  //   CpRD = C+DdC*D
  //   E = (A+B*DdC)/CpRD
  //   F = (B-A*DdC)/CpRD
  // else
  //   CdD = C/D
  //   DpRC= D+CdD*C
  //   E = (A*CdD+B)/DpRC
  //   F = (B*CdD-A)/DpRC
  // AARCH64-FASTMATH-LABEL: @div_float_rc(float noundef nofpclass(nan inf) %a, [2 x float] noundef nofpclass(nan inf) alignstack(8) %b.coerce)
  // |C|
  // AARCH64-FASTMATH: call {{.*}}float @llvm.fabs.f32(float {{.*}})
  // |D|
  // AARCH64-FASTMATH-NEXT: call {{.*}}float @llvm.fabs.f32(float {{.*}})
  // AARCH64-FASTMATH-NEXT: fcmp {{.*}}ugt float
  // AARCH64-FASTMATH-NEXT: br i1 {{.*}}, label
  // AARCH64-FASTMATH:      abs_rhsr_greater_or_equal_abs_rhsi:

  // |C| >= |D|
  // DdC=D/C
  // AARCH64-FASTMATH-NEXT: fdiv {{.*}}float

  // CpRD=C+CdC*D
  // AARCH64-FASTMATH-NEXT: fmul {{.*}}float
  // AARCH64-FASTMATH-NEXT: fadd {{.*}}float

  // A+BR/CpRD
  // AARCH64-FASTMATH-NEXT: fmul {{.*}}float
  // AARCH64-FASTMATH-NEXT: fadd {{.*}}float
  // AARCH64-FASTMATH-NEXT: fdiv {{.*}}float

  // B-AR/CpRD
  // AARCH64-FASTMATH-NEXT: fmul {{.*}}float
  // AARCH64-FASTMATH-NEXT: fsub {{.*}}float
  // AARCH64-FASTMATH-NEXT: fdiv {{.*}}float
  // AARCH64-FASTMATH-NEXT: br label
  // AARCH64-FASTMATH:      abs_rhsr_less_than_abs_rhsi:

  // |C| < |D|
  // CdD=C/D
  // AARCH64-FASTMATH-NEXT: fdiv {{.*}}float

  // DpRC=D+CdD*C
  // AARCH64-FASTMATH-NEXT: fmul {{.*}}float
  // AARCH64-FASTMATH-NEXT: fadd {{.*}}float

  // (A*CdD+B)/DpRC
  // AARCH64-FASTMATH-NEXT: fmul {{.*}}float
  // AARCH64-FASTMATH-NEXT: fadd {{.*}}float
  // AARCH64-FASTMATH-NEXT: fdiv {{.*}}float

  // (BCdD-A)/DpRC
  // AARCH64-FASTMATH-NEXT: fmul {{.*}}float
  // AARCH64-FASTMATH-NEXT: fsub {{.*}}float
  // AARCH64-FASTMATH-NEXT: fdiv {{.*}}float

  // AARCH64-FASTMATH-NEXT: br label
  // AARCH64-FASTMATH:      complex_div:
  // AARCH64-FASTMATH-NEXT: phi {{.*}}float
  // AARCH64-FASTMATH-NEXT: phi {{.*}}float
  // AARCH64-FASTMATH: ret
  return a / b;
}
float _Complex div_float_cc(float _Complex a, float _Complex b) {
  // X86-LABEL: @div_float_cc(
  // X86-NOT: fdiv
  // X86: call {{.*}} @__divsc3(
  // X86: ret

  // SPIR: call spir_func {{.*}} @__divsc3(

  // a / b = (A+iB) / (C+iD) = (E+iF)
  // if (|C| >= |D|)
  //   DdC = D/C
  //   CpRD = C+DdC*D
  //   E = (A+B*DdC)/CpRD
  //   F = (B-A*DdC)/CpRD
  // else
  //   CdD = C/D
  //   DpRC= D+CdD*C
  //   E = (A*CdD+B)/DpRC
  //   F = (B*CdD-A)/DpRC
  // AARCH64-FASTMATH-LABEL: @div_float_cc([2 x float] noundef nofpclass(nan inf) alignstack(8) %a.coerce, [2 x float] noundef nofpclass(nan inf) alignstack(8) %b.coerce)
  // |C|
  // AARCH64-FASTMATH: call {{.*}}float @llvm.fabs.f32(float {{.*}})
  // |D|
  // AARCH64-FASTMATH-NEXT: call {{.*}}float @llvm.fabs.f32(float {{.*}})
  // AARCH64-FASTMATH-NEXT: fcmp {{.*}}ugt float
  // AARCH64-FASTMATH-NEXT: br i1 {{.*}}, label
  // AARCH64-FASTMATH:      abs_rhsr_greater_or_equal_abs_rhsi:

  // |C| >= |D|
  // DdC=D/C
  // AARCH64-FASTMATH-NEXT: fdiv {{.*}}float

  // CpRD=C+CdC*D
  // AARCH64-FASTMATH-NEXT: fmul {{.*}}float
  // AARCH64-FASTMATH-NEXT: fadd {{.*}}float

  // A+BR/CpRD
  // AARCH64-FASTMATH-NEXT: fmul {{.*}}float
  // AARCH64-FASTMATH-NEXT: fadd {{.*}}float
  // AARCH64-FASTMATH-NEXT: fdiv {{.*}}float

  // B-AR/CpRD
  // AARCH64-FASTMATH-NEXT: fmul {{.*}}float
  // AARCH64-FASTMATH-NEXT: fsub {{.*}}float
  // AARCH64-FASTMATH-NEXT: fdiv {{.*}}float
  // AARCH64-FASTMATH-NEXT: br label
  // AARCH64-FASTMATH:      abs_rhsr_less_than_abs_rhsi:

  // |C| < |D|
  // CdD=C/D
  // AARCH64-FASTMATH-NEXT: fdiv {{.*}}float

  // DpRC=D+CdD*C
  // AARCH64-FASTMATH-NEXT: fmul {{.*}}float
  // AARCH64-FASTMATH-NEXT: fadd {{.*}}float

  // (A*CdD+B)/DpRC
  // AARCH64-FASTMATH-NEXT: fmul {{.*}}float
  // AARCH64-FASTMATH-NEXT: fadd {{.*}}float
  // AARCH64-FASTMATH-NEXT: fdiv {{.*}}float

  // (BCdD-A)/DpRC
  // AARCH64-FASTMATH-NEXT: fmul {{.*}}float
  // AARCH64-FASTMATH-NEXT: fsub {{.*}}float
  // AARCH64-FASTMATH-NEXT: fdiv {{.*}}float

  // AARCH64-FASTMATH-NEXT: br label
  // AARCH64-FASTMATH:      complex_div:
  // AARCH64-FASTMATH-NEXT: phi {{.*}}float
  // AARCH64-FASTMATH-NEXT: phi {{.*}}float
  return a / b;
}

double _Complex add_double_rr(double a, double b) {
  // X86-LABEL: @add_double_rr(
  // X86: fadd
  // X86-NOT: fadd
  // X86: ret
  return a + b;
}
double _Complex add_double_cr(double _Complex a, double b) {
  // X86-LABEL: @add_double_cr(
  // X86: fadd
  // X86-NOT: fadd
  // X86: ret
  return a + b;
}
double _Complex add_double_rc(double a, double _Complex b) {
  // X86-LABEL: @add_double_rc(
  // X86: fadd
  // X86-NOT: fadd
  // X86: ret
  return a + b;
}
double _Complex add_double_cc(double _Complex a, double _Complex b) {
  // X86-LABEL: @add_double_cc(
  // X86: fadd
  // X86: fadd
  // X86-NOT: fadd
  // X86: ret
  return a + b;
}

double _Complex sub_double_rr(double a, double b) {
  // X86-LABEL: @sub_double_rr(
  // X86: fsub
  // X86-NOT: fsub
  // X86: ret
  return a - b;
}
double _Complex sub_double_cr(double _Complex a, double b) {
  // X86-LABEL: @sub_double_cr(
  // X86: fsub
  // X86-NOT: fsub
  // X86: ret
  return a - b;
}
double _Complex sub_double_rc(double a, double _Complex b) {
  // X86-LABEL: @sub_double_rc(
  // X86: fsub
  // X86: fneg
  // X86-NOT: fsub
  // X86: ret
  return a - b;
}
double _Complex sub_double_cc(double _Complex a, double _Complex b) {
  // X86-LABEL: @sub_double_cc(
  // X86: fsub
  // X86: fsub
  // X86-NOT: fsub
  // X86: ret
  return a - b;
}

double _Complex mul_double_rr(double a, double b) {
  // X86-LABEL: @mul_double_rr(
  // X86: fmul
  // X86-NOT: fmul
  // X86: ret
  return a * b;
}
double _Complex mul_double_cr(double _Complex a, double b) {
  // X86-LABEL: @mul_double_cr(
  // X86: fmul
  // X86: fmul
  // X86-NOT: fmul
  // X86: ret
  return a * b;
}
double _Complex mul_double_rc(double a, double _Complex b) {
  // X86-LABEL: @mul_double_rc(
  // X86: fmul
  // X86: fmul
  // X86-NOT: fmul
  // X86: ret
  return a * b;
}
double _Complex mul_double_cc(double _Complex a, double _Complex b) {
  // X86-LABEL: @mul_double_cc(
  // X86: %[[AC:[^ ]+]] = fmul
  // X86: %[[BD:[^ ]+]] = fmul
  // X86: %[[AD:[^ ]+]] = fmul
  // X86: %[[BC:[^ ]+]] = fmul
  // X86: %[[RR:[^ ]+]] = fsub double %[[AC]], %[[BD]]
  // X86: %[[RI:[^ ]+]] = fadd double
  // X86-DAG: %[[AD]]
  // X86-DAG: ,
  // X86-DAG: %[[BC]]
  // X86: fcmp uno double %[[RR]]
  // X86: fcmp uno double %[[RI]]
  // X86: call {{.*}} @__muldc3(
  // X86: ret

  // SPIR: call spir_func {{.*}} @__muldc3(
  return a * b;
}

double _Complex div_double_rr(double a, double b) {
  // X86-LABEL: @div_double_rr(
  // X86: fdiv
  // X86-NOT: fdiv
  // X86: ret
  return a / b;
}
double _Complex div_double_cr(double _Complex a, double b) {
  // X86-LABEL: @div_double_cr(
  // X86: fdiv
  // X86: fdiv
  // X86-NOT: fdiv
  // X86: ret
  return a / b;
}
double _Complex div_double_rc(double a, double _Complex b) {
  // X86-LABEL: @div_double_rc(
  // X86-NOT: fdiv
  // X86: call {{.*}} @__divdc3(
  // X86: ret

  // SPIR: call spir_func {{.*}} @__divdc3(

  // a / b = (A+iB) / (C+iD) = (E+iF)
  // if (|C| >= |D|)
  //   DdC = D/C
  //   CpRD = C+DdC*D
  //   E = (A+B*DdC)/CpRD
  //   F = (B-A*DdC)/CpRD
  // else
  //   CdD = C/D
  //   DpRC= D+CdD*C
  //   E = (A*CdD+B)/DpRC
  //   F = (B*CdD-A)/DpRC
  // AARCH64-FASTMATH-LABEL: @div_double_rc(double noundef nofpclass(nan inf) %a, [2 x double] noundef nofpclass(nan inf) alignstack(8) %b.coerce)
  // |C|
  // AARCH64-FASTMATH: call {{.*}}double @llvm.fabs.f64(double {{.*}})
  // |D|
  // AARCH64-FASTMATH-NEXT: call {{.*}}double @llvm.fabs.f64(double {{.*}})
  // AARCH64-FASTMATH-NEXT: fcmp {{.*}}ugt double
  // AARCH64-FASTMATH-NEXT: br i1 {{.*}}, label
  // AARCH64-FASTMATH:      abs_rhsr_greater_or_equal_abs_rhsi:

  // |C| >= |D|
  // DdC=D/C
  // AARCH64-FASTMATH-NEXT: fdiv {{.*}}double

  // CpRD=C+CdC*D
  // AARCH64-FASTMATH-NEXT: fmul {{.*}}double
  // AARCH64-FASTMATH-NEXT: fadd {{.*}}double

  // A+BR/CpRD
  // AARCH64-FASTMATH-NEXT: fmul {{.*}}double
  // AARCH64-FASTMATH-NEXT: fadd {{.*}}double
  // AARCH64-FASTMATH-NEXT: fdiv {{.*}}double

  // B-AR/CpRD
  // AARCH64-FASTMATH-NEXT: fmul {{.*}}double
  // AARCH64-FASTMATH-NEXT: fsub {{.*}}double
  // AARCH64-FASTMATH-NEXT: fdiv {{.*}}double
  // AARCH64-FASTMATH-NEXT: br label
  // AARCH64-FASTMATH:      abs_rhsr_less_than_abs_rhsi:

  // |C| < |D|
  // CdD=C/D
  // AARCH64-FASTMATH-NEXT: fdiv {{.*}}double

  // DpRC=D+CdD*C
  // AARCH64-FASTMATH-NEXT: fmul {{.*}}double
  // AARCH64-FASTMATH-NEXT: fadd {{.*}}double

  // (A*CdD+B)/DpRC
  // AARCH64-FASTMATH-NEXT: fmul {{.*}}double
  // AARCH64-FASTMATH-NEXT: fadd {{.*}}double
  // AARCH64-FASTMATH-NEXT: fdiv {{.*}}double

  // (BCdD-A)/DpRC
  // AARCH64-FASTMATH-NEXT: fmul {{.*}}double
  // AARCH64-FASTMATH-NEXT: fsub {{.*}}double
  // AARCH64-FASTMATH-NEXT: fdiv {{.*}}double

  // AARCH64-FASTMATH-NEXT: br label
  // AARCH64-FASTMATH:      complex_div:
  // AARCH64-FASTMATH-NEXT: phi {{.*}}double
  // AARCH64-FASTMATH-NEXT: phi {{.*}}double
  // AARCH64-FASTMATH: ret
  return a / b;
}
double _Complex div_double_cc(double _Complex a, double _Complex b) {
  // X86-LABEL: @div_double_cc(
  // X86-NOT: fdiv
  // X86: call {{.*}} @__divdc3(
  // X86: ret

  // SPIR: call spir_func {{.*}} @__divdc3(

  // a / b = (A+iB) / (C+iD) = (E+iF)
  // if (|C| >= |D|)
  //   DdC = D/C
  //   CpRD = C+DdC*D
  //   E = (A+B*DdC)/CpRD
  //   F = (B-A*DdC)/CpRD
  // else
  //   CdD = C/D
  //   DpRC= D+CdD*C
  //   E = (A*CdD+B)/DpRC
  //   F = (B*CdD-A)/DpRC
  // AARCH64-FASTMATH-LABEL: @div_double_cc([2 x double] noundef nofpclass(nan inf) alignstack(8) %a.coerce, [2 x double] noundef nofpclass(nan inf) alignstack(8) %b.coerce)
  // |C|
  // AARCH64-FASTMATH: call {{.*}}double @llvm.fabs.f64(double {{.*}})
  // |D|
  // AARCH64-FASTMATH-NEXT: call {{.*}}double @llvm.fabs.f64(double {{.*}})
  // AARCH64-FASTMATH-NEXT: fcmp {{.*}}ugt double
  // AARCH64-FASTMATH-NEXT: br i1 {{.*}}, label
  // AARCH64-FASTMATH:      abs_rhsr_greater_or_equal_abs_rhsi:

  // |C| >= |D|
  // DdC=D/C
  // AARCH64-FASTMATH-NEXT: fdiv {{.*}}double

  // CpRD=C+CdC*D
  // AARCH64-FASTMATH-NEXT: fmul {{.*}}double
  // AARCH64-FASTMATH-NEXT: fadd {{.*}}double

  // A+BR/CpRD
  // AARCH64-FASTMATH-NEXT: fmul {{.*}}double
  // AARCH64-FASTMATH-NEXT: fadd {{.*}}double
  // AARCH64-FASTMATH-NEXT: fdiv {{.*}}double

  // B-AR/CpRD
  // AARCH64-FASTMATH-NEXT: fmul {{.*}}double
  // AARCH64-FASTMATH-NEXT: fsub {{.*}}double
  // AARCH64-FASTMATH-NEXT: fdiv {{.*}}double
  // AARCH64-FASTMATH-NEXT: br label
  // AARCH64-FASTMATH:      abs_rhsr_less_than_abs_rhsi:

  // |C| < |D|
  // CdD=C/D
  // AARCH64-FASTMATH-NEXT: fdiv {{.*}}double

  // DpRC=D+CdD*C
  // AARCH64-FASTMATH-NEXT: fmul {{.*}}double
  // AARCH64-FASTMATH-NEXT: fadd {{.*}}double

  // (A*CdD+B)/DpRC
  // AARCH64-FASTMATH-NEXT: fmul {{.*}}double
  // AARCH64-FASTMATH-NEXT: fadd {{.*}}double
  // AARCH64-FASTMATH-NEXT: fdiv {{.*}}double

  // (BCdD-A)/DpRC
  // AARCH64-FASTMATH-NEXT: fmul {{.*}}double
  // AARCH64-FASTMATH-NEXT: fsub {{.*}}double
  // AARCH64-FASTMATH-NEXT: fdiv {{.*}}double

  // AARCH64-FASTMATH-NEXT: br label
  // AARCH64-FASTMATH:      complex_div:
  // AARCH64-FASTMATH-NEXT: phi {{.*}}double
  // AARCH64-FASTMATH-NEXT: phi {{.*}}double
  // AARCH64-FASTMATH: ret
  return a / b;
}

long double _Complex add_long_double_rr(long double a, long double b) {
  // X86-LABEL: @add_long_double_rr(
  // X86: fadd
  // X86-NOT: fadd
  // X86: ret
  return a + b;
}
long double _Complex add_long_double_cr(long double _Complex a, long double b) {
  // X86-LABEL: @add_long_double_cr(
  // X86: fadd
  // X86-NOT: fadd
  // X86: ret
  return a + b;
}
long double _Complex add_long_double_rc(long double a, long double _Complex b) {
  // X86-LABEL: @add_long_double_rc(
  // X86: fadd
  // X86-NOT: fadd
  // X86: ret
  return a + b;
}
long double _Complex add_long_double_cc(long double _Complex a, long double _Complex b) {
  // X86-LABEL: @add_long_double_cc(
  // X86: fadd
  // X86: fadd
  // X86-NOT: fadd
  // X86: ret
  return a + b;
}

long double _Complex sub_long_double_rr(long double a, long double b) {
  // X86-LABEL: @sub_long_double_rr(
  // X86: fsub
  // X86-NOT: fsub
  // X86: ret
  return a - b;
}
long double _Complex sub_long_double_cr(long double _Complex a, long double b) {
  // X86-LABEL: @sub_long_double_cr(
  // X86: fsub
  // X86-NOT: fsub
  // X86: ret
  return a - b;
}
long double _Complex sub_long_double_rc(long double a, long double _Complex b) {
  // X86-LABEL: @sub_long_double_rc(
  // X86: fsub
  // X86: fneg
  // X86-NOT: fsub
  // X86: ret
  return a - b;
}
long double _Complex sub_long_double_cc(long double _Complex a, long double _Complex b) {
  // X86-LABEL: @sub_long_double_cc(
  // X86: fsub
  // X86: fsub
  // X86-NOT: fsub
  // X86: ret
  return a - b;
}

long double _Complex mul_long_double_rr(long double a, long double b) {
  // X86-LABEL: @mul_long_double_rr(
  // X86: fmul
  // X86-NOT: fmul
  // X86: ret
  return a * b;
}
long double _Complex mul_long_double_cr(long double _Complex a, long double b) {
  // X86-LABEL: @mul_long_double_cr(
  // X86: fmul
  // X86: fmul
  // X86-NOT: fmul
  // X86: ret
  return a * b;
}
long double _Complex mul_long_double_rc(long double a, long double _Complex b) {
  // X86-LABEL: @mul_long_double_rc(
  // X86: fmul
  // X86: fmul
  // X86-NOT: fmul
  // X86: ret
  return a * b;
}
long double _Complex mul_long_double_cc(long double _Complex a, long double _Complex b) {
  // X86-LABEL: @mul_long_double_cc(
  // X86: %[[AC:[^ ]+]] = fmul
  // X86: %[[BD:[^ ]+]] = fmul
  // X86: %[[AD:[^ ]+]] = fmul
  // X86: %[[BC:[^ ]+]] = fmul
  // X86: %[[RR:[^ ]+]] = fsub x86_fp80 %[[AC]], %[[BD]]
  // X86: %[[RI:[^ ]+]] = fadd x86_fp80
  // X86-DAG: %[[AD]]
  // X86-DAG: ,
  // X86-DAG: %[[BC]]
  // X86: fcmp uno x86_fp80 %[[RR]]
  // X86: fcmp uno x86_fp80 %[[RI]]
  // X86: call {{.*}} @__mulxc3(
  // X86: ret
  // PPC-LABEL: @mul_long_double_cc(
  // PPC: %[[AC:[^ ]+]] = fmul
  // PPC: %[[BD:[^ ]+]] = fmul
  // PPC: %[[AD:[^ ]+]] = fmul
  // PPC: %[[BC:[^ ]+]] = fmul
  // PPC: %[[RR:[^ ]+]] = fsub ppc_fp128 %[[AC]], %[[BD]]
  // PPC: %[[RI:[^ ]+]] = fadd ppc_fp128
  // PPC-DAG: %[[AD]]
  // PPC-DAG: ,
  // PPC-DAG: %[[BC]]
  // PPC: fcmp uno ppc_fp128 %[[RR]]
  // PPC: fcmp uno ppc_fp128 %[[RI]]
  // PPC: call {{.*}} @__multc3(
  // PPC: ret
  // SPIR: call spir_func {{.*}} @__muldc3(
  return a * b;
}

long double _Complex div_long_double_rr(long double a, long double b) {
  // X86-LABEL: @div_long_double_rr(
  // X86: fdiv
  // X86-NOT: fdiv
  // X86: ret
  return a / b;
}
long double _Complex div_long_double_cr(long double _Complex a, long double b) {
  // X86-LABEL: @div_long_double_cr(
  // X86: fdiv
  // X86: fdiv
  // X86-NOT: fdiv
  // X86: ret
  return a / b;
}
long double _Complex div_long_double_rc(long double a, long double _Complex b) {
  // X86-LABEL: @div_long_double_rc(
  // X86-NOT: fdiv
  // X86: call {{.*}} @__divxc3(
  // X86: ret
  // PPC-LABEL: @div_long_double_rc(
  // PPC-NOT: fdiv
  // PPC: call {{.*}} @__divtc3(
  // PPC: ret
  // SPIR: call spir_func {{.*}} @__divdc3(

  // a / b = (A+iB) / (C+iD) = (E+iF)
  // if (|C| >= |D|)
  //   DdC = D/C
  //   CpRD = C+DdC*D
  //   E = (A+B*DdC)/CpRD
  //   F = (B-A*DdC)/CpRD
  // else
  //   CdD = C/D
  //   DpRC= D+CdD*C
  //   E = (A*CdD+B)/DpRC
  //   F = (B*CdD-A)/DpRC
  // AARCH64-FASTMATH-LABEL: @div_long_double_rc(fp128 noundef nofpclass(nan inf) %a, [2 x fp128] noundef nofpclass(nan inf) alignstack(16) %b.coerce)
  // |C|
  // AARCH64-FASTMATH: call {{.*}}fp128 @llvm.fabs.f128(fp128 {{.*}})
  // |D|
  // AARCH64-FASTMATH-NEXT: call {{.*}}fp128 @llvm.fabs.f128(fp128 {{.*}})
  // AARCH64-FASTMATH-NEXT: fcmp {{.*}}ugt fp128
  // AARCH64-FASTMATH-NEXT: br i1 {{.*}}, label
  // AARCH64-FASTMATH:      abs_rhsr_greater_or_equal_abs_rhsi:

  // |C| >= |D|
  // DdC=D/C
  // AARCH64-FASTMATH-NEXT: fdiv {{.*}}fp128

  // CpRD=C+CdC*D
  // AARCH64-FASTMATH-NEXT: fmul {{.*}}fp128
  // AARCH64-FASTMATH-NEXT: fadd {{.*}}fp128

  // A+BR/CpRD
  // AARCH64-FASTMATH-NEXT: fmul {{.*}}fp128
  // AARCH64-FASTMATH-NEXT: fadd {{.*}}fp128
  // AARCH64-FASTMATH-NEXT: fdiv {{.*}}fp128

  // B-AR/CpRD
  // AARCH64-FASTMATH-NEXT: fmul {{.*}}fp128
  // AARCH64-FASTMATH-NEXT: fsub {{.*}}fp128
  // AARCH64-FASTMATH-NEXT: fdiv {{.*}}fp128
  // AARCH64-FASTMATH-NEXT: br label
  // AARCH64-FASTMATH:      abs_rhsr_less_than_abs_rhsi:

  // |C| < |D|
  // CdD=C/D
  // AARCH64-FASTMATH-NEXT: fdiv {{.*}}fp128

  // DpRC=D+CdD*C
  // AARCH64-FASTMATH-NEXT: fmul {{.*}}fp128
  // AARCH64-FASTMATH-NEXT: fadd {{.*}}fp128

  // (A*CdD+B)/DpRC
  // AARCH64-FASTMATH-NEXT: fmul {{.*}}fp128
  // AARCH64-FASTMATH-NEXT: fadd {{.*}}fp128
  // AARCH64-FASTMATH-NEXT: fdiv {{.*}}fp128

  // (BCdD-A)/DpRC
  // AARCH64-FASTMATH-NEXT: fmul {{.*}}fp128
  // AARCH64-FASTMATH-NEXT: fsub {{.*}}fp128
  // AARCH64-FASTMATH-NEXT: fdiv {{.*}}fp128

  // AARCH64-FASTMATH-NEXT: br label
  // AARCH64-FASTMATH:      complex_div:
  // AARCH64-FASTMATH-NEXT: phi {{.*}}fp128
  // AARCH64-FASTMATH-NEXT: phi {{.*}}fp128
  // AARCH64-FASTMATH: ret
  return a / b;
}
long double _Complex div_long_double_cc(long double _Complex a, long double _Complex b) {
  // X86-LABEL: @div_long_double_cc(
  // X86-NOT: fdiv
  // X86: call {{.*}} @__divxc3(
  // X86: ret
  // PPC-LABEL: @div_long_double_cc(
  // PPC-NOT: fdiv
  // PPC: call {{.*}} @__divtc3(
  // PPC: ret
  // SPIR: call spir_func {{.*}} @__divdc3(

  // a / b = (A+iB) / (C+iD) = (E+iF)
  // if (|C| >= |D|)
  //   DdC = D/C
  //   CpRD = C+DdC*D
  //   E = (A+B*DdC)/CpRD
  //   F = (B-A*DdC)/CpRD
  // else
  //   CdD = C/D
  //   DpRC= D+CdD*C
  //   E = (A*CdD+B)/DpRC
  //   F = (B*CdD-A)/DpRC
  // AARCH64-FASTMATH-LABEL: @div_long_double_cc([2 x fp128] noundef nofpclass(nan inf) alignstack(16) %a.coerce, [2 x fp128] noundef nofpclass(nan inf) alignstack(16) %b.coerce)
  // |C|
  // AARCH64-FASTMATH: call {{.*}}fp128 @llvm.fabs.f128(fp128 {{.*}})
  // |D|
  // AARCH64-FASTMATH-NEXT: call {{.*}}fp128 @llvm.fabs.f128(fp128 {{.*}})
  // AARCH64-FASTMATH-NEXT: fcmp {{.*}}ugt fp128
  // AARCH64-FASTMATH-NEXT: br i1 {{.*}}, label
  // AARCH64-FASTMATH:      abs_rhsr_greater_or_equal_abs_rhsi:

  // |C| >= |D|
  // DdC=D/C
  // AARCH64-FASTMATH-NEXT: fdiv {{.*}}fp128

  // CpRD=C+CdC*D
  // AARCH64-FASTMATH-NEXT: fmul {{.*}}fp128
  // AARCH64-FASTMATH-NEXT: fadd {{.*}}fp128

  // A+BR/CpRD
  // AARCH64-FASTMATH-NEXT: fmul {{.*}}fp128
  // AARCH64-FASTMATH-NEXT: fadd {{.*}}fp128
  // AARCH64-FASTMATH-NEXT: fdiv {{.*}}fp128

  // B-AR/CpRD
  // AARCH64-FASTMATH-NEXT: fmul {{.*}}fp128
  // AARCH64-FASTMATH-NEXT: fsub {{.*}}fp128
  // AARCH64-FASTMATH-NEXT: fdiv {{.*}}fp128
  // AARCH64-FASTMATH-NEXT: br label
  // AARCH64-FASTMATH:      abs_rhsr_less_than_abs_rhsi:

  // |C| < |D|
  // CdD=C/D
  // AARCH64-FASTMATH-NEXT: fdiv {{.*}}fp128

  // DpRC=D+CdD*C
  // AARCH64-FASTMATH-NEXT: fmul {{.*}}fp128
  // AARCH64-FASTMATH-NEXT: fadd {{.*}}fp128

  // (A*CdD+B)/DpRC
  // AARCH64-FASTMATH-NEXT: fmul {{.*}}fp128
  // AARCH64-FASTMATH-NEXT: fadd {{.*}}fp128
  // AARCH64-FASTMATH-NEXT: fdiv {{.*}}fp128

  // (BCdD-A)/DpRC
  // AARCH64-FASTMATH-NEXT: fmul {{.*}}fp128
  // AARCH64-FASTMATH-NEXT: fsub {{.*}}fp128
  // AARCH64-FASTMATH-NEXT: fdiv {{.*}}fp128

  // AARCH64-FASTMATH-NEXT: br label
  // AARCH64-FASTMATH:      complex_div:
  // AARCH64-FASTMATH-NEXT: phi {{.*}}fp128
  // AARCH64-FASTMATH-NEXT: phi {{.*}}fp128
  // AARCH64-FASTMATH: ret
  return a / b;
}

// Comparison operators don't rely on library calls or have interseting math
// properties, but test that mixed types work correctly here.
_Bool eq_float_cr(float _Complex a, float b) {
  // X86-LABEL: @eq_float_cr(
  // X86: fcmp oeq
  // X86: fcmp oeq
  // X86: and i1
  // X86: ret
  return a == b;
}
_Bool eq_float_rc(float a, float _Complex b) {
  // X86-LABEL: @eq_float_rc(
  // X86: fcmp oeq
  // X86: fcmp oeq
  // X86: and i1
  // X86: ret
  return a == b;
}
_Bool eq_float_cc(float _Complex a, float _Complex b) {
  // X86-LABEL: @eq_float_cc(
  // X86: fcmp oeq
  // X86: fcmp oeq
  // X86: and i1
  // X86: ret
  return a == b;
}
_Bool ne_float_cr(float _Complex a, float b) {
  // X86-LABEL: @ne_float_cr(
  // X86: fcmp une
  // X86: fcmp une
  // X86: or i1
  // X86: ret
  return a != b;
}
_Bool ne_float_rc(float a, float _Complex b) {
  // X86-LABEL: @ne_float_rc(
  // X86: fcmp une
  // X86: fcmp une
  // X86: or i1
  // X86: ret
  return a != b;
}
_Bool ne_float_cc(float _Complex a, float _Complex b) {
  // X86-LABEL: @ne_float_cc(
  // X86: fcmp une
  // X86: fcmp une
  // X86: or i1
  // X86: ret
  return a != b;
}

// Check that the libcall will obtain proper calling convention on ARM
_Complex double foo(_Complex double a, _Complex double b) {
  // These functions are not defined as floating point helper functions in
  // Run-time ABI for the ARM architecture document so they must not always
  // use the base AAPCS.

  // ARM-LABEL: @foo(
  // ARM: call void @__muldc3

  // SPIR: call spir_func void @__muldc3

  // ARMHF-LABEL: @foo(
  // ARMHF: call { double, double } @__muldc3

  // ARM7K-LABEL: @foo(
  // ARM7K: call { double, double } @__muldc3
  return a*b;
}

typedef _Complex double ComplexDouble;
typedef double Double;

float _Complex double_cr_sugar(ComplexDouble a, Double b) {
  // X86-LABEL: @double_cr_sugar(
  // X86: fmul
  // X86: fmul
  // X86-NOT: fmul
  // X86: ret
  return a *= b;
}
