set(LLVM_LINK_COMPONENTS
        LLVMAggressiveInstCombine
        LLVMAnalysis
        LLVMAsmParser
        LLVMAsmPrinter
        LLVMBinaryFormat
        LLVMBitReader
        LLVMBitWriter
        LLVMBitstreamReader
        LLVMCodeGen
        LLVMCore
        LLVMCoroutines
        LLVMDemangle
        LLVMFrontendOpenMP
        LLVMIRReader
        LLVMInstCombine
        LLVMInstrumentation
        LLVMLTO
        LLVMLinker
        LLVMMC
        LLVMMCParser
        LLVMMIRParser
        LLVMObject
        LLVMObjectYAML
        LLVMOption
        LLVMPasses
        LLVMProfileData
        LLVMRemarks
        LLVMScalarOpts
        LLVMSupport
        LLVMTarget
        LLVMTransformUtils
        LLVMVectorize
        LLVMipo
)

set(CMAKE_BUILD_TYPE Debug)
add_executable(canary canary.cpp)
if (${CMAKE_SYSTEM_NAME} MATCHES "Linux")
    target_link_libraries(canary PRIVATE
            CanaryNullPointer CanaryDyckAA CanaryTransform CanarySupport
            # CanarySMT
            -Wl,--start-group
            ${LLVM_LINK_COMPONENTS}
            -Wl,--end-group
            z ncurses pthread dl
    )
else()
    target_link_libraries(canary PRIVATE
            CanaryNullPointer CanaryDyckAA CanaryTransform CanarySupport
            # CanarySMT
            ${LLVM_LINK_COMPONENTS}
            z ncurses pthread dl
    )
endif()