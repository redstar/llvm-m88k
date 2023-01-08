// RUN: llvm-tblgen -I %p/../../../include -gen-global-isel-combiner \
// RUN:     -combiners=MyCombinerHelper -gicombiner-stop-after-build %s \
// RUN:     -o %t.inc | FileCheck %s

// This is the example from the paper of Chase. Please note the values in the
// lookup table are not exactly the same. The encoding of the match sets depends
// on the order of calculation, which is not described. However, it is easy to
// see that the structure is the same, and a bijective function from the values
// in the paper to the values here in the test case can be easily defined.

include "llvm/Target/Target.td"
include "llvm/Target/GlobalISel/Combine.td"

def MyTargetISA : InstrInfo;
def MyTarget : Target { let InstructionSet = MyTargetISA; }

def dummy;

def R0 : Register<"r0"> { let Namespace = "MyTarget"; }
def GPR32 : RegisterClass<"MyTarget", [i32], 32, (add R0)>;
class I<dag OOps, dag IOps, list<dag> Pat>
  : Instruction {
  let Namespace = "MyTarget";
  let OutOperandList = OOps;
  let InOperandList = IOps;
  let Pattern = Pat;
}
def A : I<(outs GPR32:$dst), (ins GPR32:$src1, GPR32:$src2), []>;
def B : I<(outs GPR32:$dst), (ins), []>;
def C : I<(outs GPR32:$dst), (ins), []>;

def Rule0 : GICombineRule<
  (defs root:$d),
  (match (B $t2),
         (B $t3),
         (A $t1, $t3, $s1),
         (A $d, $t1, $t2)),
  (apply [{ APPLY }])>;

def Rule1 : GICombineRule<
  (defs root:$d),
  (match (C $t2),
         (C $t3),
         (A $t1, $s1, $t3),
         (A $d, $t1, $t2)),
  (apply [{ APPLY }])>;

def MyCombinerHelper: GICombinerHelper<"GenMyCombinerHelper", [
  Rule0,
  Rule1
]>;

// CHECK:     PatternForest: # PF
// CHECK-DAG:  - 1: B [ ]
// CHECK-DAG:  - 6: A [ 5, 4 ]
// CHECK-DAG:  - 3: A [ 2, 1 ]
// CHECK-DAG:  - 4: C [ ]
// CHECK-DAG:  - 2: A [ 1, 0 ]
// CHECK-DAG:  - 0: *
// CHECK-DAG:  - 5: A [ 0, 4 ]
// CHECK-NEXT:MatchSets: # R
// CHECK-DAG:  - [[MS0:[0-9]+]]: [ 0 ]
// CHECK-DAG:  - [[MS1:[0-9]+]]: [ 0, 1 ]
// CHECK-DAG:  - [[MS2:[0-9]+]]: [ 0, 2 ]
// CHECK-DAG:  - [[MS3:[0-9]+]]: [ 0, 3 ]
// CHECK-DAG:  - [[MS4:[0-9]+]]: [ 0, 4 ]
// CHECK-DAG:  - [[MS5:[0-9]+]]: [ 0, 5 ]
// CHECK-DAG:  - [[MS6:[0-9]+]]: [ 0, 2, 5 ]
// CHECK-DAG:  - [[MS7:[0-9]+]]: [ 0, 5, 6 ]
// CHECK-NEXT:ChildPatternSets: # P_A
// CHECK-NEXT:  A:
// CHECK-NEXT:    - 0: [ 0, 1, 2, 5 ]
// CHECK-NEXT:    - 1: [ 0, 1, 4 ]
// CHECK-NEXT:  B:
// CHECK-NEXT:  C:
// CHECK-NEXT:RepresenterSets: # S_A
// CHECK-NEXT:  A:
// CHECK-NEXT:    - 0:
// CHECK-DAG:      - [ 0 ]
// CHECK-DAG:      - [ 0, 1 ]
// CHECK-DAG:      - [ 0, 2 ]
// CHECK-DAG:      - [ 0, 5 ]
// CHECK-DAG:      - [ 0, 2, 5 ]
// CHECK-NEXT:    - 1:
// CHECK-DAG:      - [ 0 ]
// CHECK-DAG:      - [ 0, 1 ]
// CHECK-DAG:      - [ 0, 4 ]
// CHECK-NEXT:  B:
// CHECK-NEXT:  C:
// CHECK-NEXT:LeafTables:
// CHECK-DAG:  B: [[MS1]]
// CHECK-DAG:  C: [[MS4]]
// CHECK-NEXT:Tables:
// CHECK-NEXT:  A:
// CHECK-NEXT:    C:
// CHECK-DAG:      - [ 0, [[MS0]], [[X00:[0-9]+]] ]
// CHECK-DAG:      - [ 0, [[MS1]], [[X01:[0-9]+]] ]
// CHECK-DAG:      - [ 0, [[MS2]], [[X02:[0-9]+]] ]
// CHECK-DAG:      - [ 0, [[MS3]], [[X00]] ]
// CHECK-DAG:      - [ 0, [[MS4]], [[X00]] ]
// CHECK-DAG:      - [ 0, [[MS5]], [[X03:[0-9]+]] ]
// CHECK-DAG:      - [ 0, [[MS6]], [[X04:[0-9]+]] ]
// CHECK-DAG:      - [ 0, [[MS7]], [[X03]] ]
// CHECK-DAG:      - [ 1, [[MS0]], [[X10:[0-9]+]] ]
// CHECK-DAG:      - [ 1, [[MS1]], [[X11:[0-9]+]] ]
// CHECK-DAG:      - [ 1, [[MS2]], [[X10]] ]
// CHECK-DAG:      - [ 1, [[MS3]], [[X10]] ]
// CHECK-DAG:      - [ 1, [[MS4]], [[X12:[0-9]+]] ]
// CHECK-DAG:      - [ 1, [[MS5]], [[X10]] ]
// CHECK-DAG:      - [ 1, [[MS6]], [[X10]] ]
// CHECK-DAG:      - [ 1, [[MS7]], [[X10]] ]
// CHECK-NEXT:    T:
// CHECK-DAG:      - [ [[X00]], [[X10]], [[MS0]] ]
// CHECK-DAG:      - [ [[X00]], [[X11]], [[MS0]] ]
// CHECK-DAG:      - [ [[X00]], [[X12]], [[MS5]] ]
// CHECK-DAG:      - [ [[X01]], [[X10]], [[MS2]] ]
// CHECK-DAG:      - [ [[X01]], [[X11]], [[MS2]] ]
// CHECK-DAG:      - [ [[X01]], [[X12]], [[MS6]] ]
// CHECK-DAG:      - [ [[X02]], [[X10]], [[MS0]] ]
// CHECK-DAG:      - [ [[X02]], [[X11]], [[MS3]] ]
// CHECK-DAG:      - [ [[X02]], [[X12]], [[MS5]] ]
// CHECK-DAG:      - [ [[X03]], [[X10]], [[MS0]] ]
// CHECK-DAG:      - [ [[X03]], [[X11]], [[MS0]] ]
// CHECK-DAG:      - [ [[X03]], [[X12]], [[MS7]] ]
// CHECK-DAG:      - [ [[X04]], [[X10]], [[MS0]] ]
// CHECK-DAG:      - [ [[X04]], [[X11]], [[MS3]] ]
// CHECK-DAG:      - [ [[X04]], [[X12]], [[MS7]] ]
