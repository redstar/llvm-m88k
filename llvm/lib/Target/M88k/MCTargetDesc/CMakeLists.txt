add_llvm_component_library(LLVMM88kDesc
  M88kInstPrinter.cpp
  M88kMCCodeEmitter.cpp
  M88kMCAsmInfo.cpp
  M88kMCTargetDesc.cpp

  LINK_COMPONENTS
  MC
  Support
  M88kInfo

  ADD_TO_COMPONENT
  M88k
  )
