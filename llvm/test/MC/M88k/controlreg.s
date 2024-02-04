# RUN: llvm-mc  %s -triple=m88k-unknown-openbsd -show-encoding -mcpu=mc88100 | FileCheck %s

# Check encoding of alternate register names.

  fldcr    %r0, %FPECR
  fldcr    %r0, %FPHS1
  fldcr    %r0, %FPLS1
  fldcr    %r0, %FPHS2
  fldcr    %r0, %FPLS2
  fldcr    %r0, %FPPT
  fldcr    %r0, %FPRH
  fldcr    %r0, %FPRL
  fldcr    %r0, %FPIT
  fldcr    %r0, %FPSR
  fldcr    %r0, %FPCR
# CHECK: fldcr %r0, %fcr0                        | encoding: [0x80,0x00,0x48,0x00]
# CHECK: fldcr %r0, %fcr1                        | encoding: [0x80,0x00,0x48,0x20]
# CHECK: fldcr %r0, %fcr2                        | encoding: [0x80,0x00,0x48,0x40]
# CHECK: fldcr %r0, %fcr3                        | encoding: [0x80,0x00,0x48,0x60]
# CHECK: fldcr %r0, %fcr4                        | encoding: [0x80,0x00,0x48,0x80]
# CHECK: fldcr %r0, %fcr5                        | encoding: [0x80,0x00,0x48,0xa0]
# CHECK: fldcr %r0, %fcr6                        | encoding: [0x80,0x00,0x48,0xc0]
# CHECK: fldcr %r0, %fcr7                        | encoding: [0x80,0x00,0x48,0xe0]
# CHECK: fldcr %r0, %fcr8                        | encoding: [0x80,0x00,0x49,0x00]
# CHECK: fldcr %r0, %fcr62                       | encoding: [0x80,0x00,0x4f,0xc0]
# CHECK: fldcr %r0, %fcr63                       | encoding: [0x80,0x00,0x4f,0xe0]

  ldcr         %r0, %PID
  ldcr         %r0, %PSR
  ldcr         %r0, %EPSR
  ldcr         %r0, %SSBR
  ldcr         %r0, %SXIP
  ldcr         %r0, %SNIP
  ldcr         %r0, %SFIP
  ldcr         %r0, %VBR
  ldcr         %r0, %DMT0
  ldcr         %r0, %DMD0
  ldcr         %r0, %DMA0
  ldcr         %r0, %DMT1
  ldcr         %r0, %DMD1
  ldcr         %r0, %DMA1
  ldcr         %r0, %DMT2
  ldcr         %r0, %DMD2
  ldcr         %r0, %DMA2
  ldcr         %r0, %SR0
  ldcr         %r0, %SR1
  ldcr         %r0, %SR2
  ldcr         %r0, %SR3
# CHECK: ldcr %r0, %cr0                          | encoding: [0x80,0x00,0x40,0x00]
# CHECK: ldcr %r0, %cr1                          | encoding: [0x80,0x00,0x40,0x20]
# CHECK: ldcr %r0, %cr2                          | encoding: [0x80,0x00,0x40,0x40]
# CHECK: ldcr %r0, %cr3                          | encoding: [0x80,0x00,0x40,0x60]
# CHECK: ldcr %r0, %cr4                          | encoding: [0x80,0x00,0x40,0x80]
# CHECK: ldcr %r0, %cr5                          | encoding: [0x80,0x00,0x40,0xa0]
# CHECK: ldcr %r0, %cr6                          | encoding: [0x80,0x00,0x40,0xc0]
# CHECK: ldcr %r0, %cr7                          | encoding: [0x80,0x00,0x40,0xe0]
# CHECK: ldcr %r0, %cr8                          | encoding: [0x80,0x00,0x41,0x00]
# CHECK: ldcr %r0, %cr9                          | encoding: [0x80,0x00,0x41,0x20]
# CHECK: ldcr %r0, %cr10                         | encoding: [0x80,0x00,0x41,0x40]
# CHECK: ldcr %r0, %cr11                         | encoding: [0x80,0x00,0x41,0x60]
# CHECK: ldcr %r0, %cr12                         | encoding: [0x80,0x00,0x41,0x80]
# CHECK: ldcr %r0, %cr13                         | encoding: [0x80,0x00,0x41,0xa0]
# CHECK: ldcr %r0, %cr14                         | encoding: [0x80,0x00,0x41,0xc0]
# CHECK: ldcr %r0, %cr15                         | encoding: [0x80,0x00,0x41,0xe0]
# CHECK: ldcr %r0, %cr16                         | encoding: [0x80,0x00,0x42,0x00]
# CHECK: ldcr %r0, %cr17                         | encoding: [0x80,0x00,0x42,0x20]
# CHECK: ldcr %r0, %cr18                         | encoding: [0x80,0x00,0x42,0x40]
# CHECK: ldcr %r0, %cr19                         | encoding: [0x80,0x00,0x42,0x60]
# CHECK: ldcr %r0, %cr20                         | encoding: [0x80,0x00,0x42,0x80]
