set(files
  adxintrin.h
  altivec.h
  ammintrin.h
  arm_acle.h
  armintr.h
  arm64intr.h
  avx2intrin.h
  avx512bf16intrin.h
  avx512bwintrin.h
  avx512bitalgintrin.h
  avx512vlbitalgintrin.h
  avx512cdintrin.h
  avx512vpopcntdqintrin.h
  avx512dqintrin.h
  avx512erintrin.h
  avx512fintrin.h
  avx512ifmaintrin.h
  avx512ifmavlintrin.h
  avx512pfintrin.h
  avx512vbmiintrin.h
  avx512vbmivlintrin.h
  avx512vbmi2intrin.h
  avx512vlvbmi2intrin.h
  avx512vlbf16intrin.h
  avx512vlbwintrin.h
  avx512vlcdintrin.h
  avx512vldqintrin.h
  avx512vlintrin.h
  avx512vp2intersectintrin.h
  avx512vlvp2intersectintrin.h
  avx512vpopcntdqvlintrin.h
  avx512vnniintrin.h
  avx512vlvnniintrin.h
  avxintrin.h
  bmi2intrin.h
  bmiintrin.h
  __clang_cuda_builtin_vars.h
  __clang_cuda_cmath.h
  __clang_cuda_complex_builtins.h
  __clang_cuda_device_functions.h
  __clang_cuda_intrinsics.h
  __clang_cuda_libdevice_declares.h
  __clang_cuda_math_forward_declares.h
  __clang_cuda_runtime_wrapper.h
  __clang_hip_automatic_cuda_open.h
  __clang_hip_automatic_hip.h
  __clang_hip_automatic_cuda.h
  __clang_openmp_runtime_wrapper.h
  cetintrin.h
  cldemoteintrin.h
  clzerointrin.h
  cpuid.h
  clflushoptintrin.h
  clwbintrin.h
  emmintrin.h
  enqcmdintrin.h
  f16cintrin.h
  float.h
  fma4intrin.h
  fmaintrin.h
  fxsrintrin.h
  gfniintrin.h
  htmintrin.h
  htmxlintrin.h
  ia32intrin.h
  immintrin.h
  intrin.h
  inttypes.h
  invpcidintrin.h
  iso646.h
  limits.h
  lwpintrin.h
  lzcntintrin.h
  mm3dnow.h
  mmintrin.h
  mm_malloc.h
  module.modulemap
  movdirintrin.h
  msa.h
  mwaitxintrin.h
  nmmintrin.h
  opencl-c.h
  opencl-c-base.h
  pkuintrin.h
  pmmintrin.h
  pconfigintrin.h
  popcntintrin.h
  prfchwintrin.h
  ptwriteintrin.h
  rdseedintrin.h
  rtmintrin.h
  sgxintrin.h
  s390intrin.h
  shaintrin.h
  smmintrin.h
  stdalign.h
  stdarg.h
  stdatomic.h
  stdbool.h
  stddef.h
  __stddef_max_align_t.h
  stdint.h
  stdnoreturn.h
  tbmintrin.h
  tgmath.h
  tmmintrin.h
  unwind.h
  vadefs.h
  vaesintrin.h
  varargs.h
  vecintrin.h
  vpclmulqdqintrin.h
  waitpkgintrin.h
  wbnoinvdintrin.h
  wmmintrin.h
  __wmmintrin_aes.h
  __wmmintrin_pclmul.h
  x86intrin.h
  xmmintrin.h
  xopintrin.h
  xsavecintrin.h
  xsaveintrin.h
  xsaveoptintrin.h
  xsavesintrin.h
  xtestintrin.h
  )

set(cuda_wrapper_files
  cuda_wrappers/algorithm
  cuda_wrappers/complex
  cuda_wrappers/new
)

# TODO schi add below and hip_files
set(cuda_open_files
  cuda_open/__clang_cuda_open_builtins.h
  cuda_open/__clang_cuda_open_builtin_vars.h
  cuda_open/__clang_cuda_open_cmath.h
  cuda_open/__clang_cuda_open_complex_builtins.h
  cuda_open/__clang_cuda_open_device_functions.h
  cuda_open/__clang_cuda_open_intrinsics.h
  cuda_open/__clang_cuda_open_math_forward_declares.h
  cuda_open/__clang_cuda_open_nv_declares.h
  cuda_open/cuda_fp16.h
  cuda_open/cuda_open.h
  cuda_open/cuda_open_runtime.h
  cuda_open/device_atomic_functions.hpp
  cuda_open/device_double_functions.h
  cuda_open/device_functions.h
  cuda_open/device_functions.hpp
  cuda_open/device_runtime.h
  cuda_open/driver_types.h
  cuda_open/host_config.h
  cuda_open/host_defines.h
  cuda_open/math_functions_dbl.hpp
  cuda_open/math_functions.hpp
  cuda_open/texture_indirect_functions.h
  cuda_open/vector_types.h
)

set(hip_files
  hip/hip_host_runtime_api.h
  hip/hip_common.h
  hip/driver_types.h
  hip/hcc_detail/driver_types.h
  hip/clang_detail/hip_surface_types.h
  cuda_runtime.h
)

set(hip_hcc_files
  hip/hcc_detail/driver_types.h
)

set(ppc_wrapper_files
  ppc_wrappers/mmintrin.h
  ppc_wrappers/xmmintrin.h
  ppc_wrappers/mm_malloc.h
  ppc_wrappers/emmintrin.h
  ppc_wrappers/pmmintrin.h
  ppc_wrappers/tmmintrin.h
  ppc_wrappers/smmintrin.h
)

set(openmp_wrapper_files
  openmp_wrappers/math.h
  openmp_wrappers/cmath
  openmp_wrappers/__clang_openmp_math.h
  openmp_wrappers/__clang_openmp_math_declares.h
)

set(output_dir ${LLVM_LIBRARY_OUTPUT_INTDIR}/clang/${CLANG_VERSION}/include)
set(out_files)
set(generated_files)

function(copy_header_to_output_dir src_dir file)
  set(src ${src_dir}/${file})
  set(dst ${output_dir}/${file})
  add_custom_command(OUTPUT ${dst}
    DEPENDS ${src}
    COMMAND ${CMAKE_COMMAND} -E copy_if_different ${src} ${dst}
    COMMENT "Copying clang's ${file}...")
  list(APPEND out_files ${dst})
  set(out_files ${out_files} PARENT_SCOPE)
endfunction(copy_header_to_output_dir)

function(clang_generate_header td_option td_file out_file)
  clang_tablegen(${out_file} ${td_option}
  -I ${CLANG_SOURCE_DIR}/include/clang/Basic/
  SOURCE ${CLANG_SOURCE_DIR}/include/clang/Basic/${td_file})

  copy_header_to_output_dir(${CMAKE_CURRENT_BINARY_DIR} ${out_file})
  set(out_files ${out_files} PARENT_SCOPE)
  list(APPEND generated_files "${CMAKE_CURRENT_BINARY_DIR}/${out_file}")
  set(generated_files ${generated_files} PARENT_SCOPE)
endfunction(clang_generate_header)


# Copy header files from the source directory to the build directory
foreach( f ${files} ${cuda_wrapper_files} ${ppc_wrapper_files} ${openmp_wrapper_files} ${cuda_open_files} ${hip_files})
  copy_header_to_output_dir(${CMAKE_CURRENT_SOURCE_DIR} ${f})
endforeach( f )

# Generate header files and copy them to the build directory
# Generate arm_neon.h
clang_generate_header(-gen-arm-neon arm_neon.td arm_neon.h)
# Generate arm_fp16.h
clang_generate_header(-gen-arm-fp16 arm_fp16.td arm_fp16.h)

add_custom_target(clang-resource-headers ALL DEPENDS ${out_files})
set_target_properties(clang-resource-headers PROPERTIES
  FOLDER "Misc"
  RUNTIME_OUTPUT_DIRECTORY "${output_dir}")

set(header_install_dir lib${LLVM_LIBDIR_SUFFIX}/clang/${CLANG_VERSION}/include)

install(
  FILES ${files} ${generated_files}
  DESTINATION ${header_install_dir}
  COMPONENT clang-resource-headers)

install(
  FILES ${cuda_wrapper_files}
  DESTINATION ${header_install_dir}/cuda_wrappers
  COMPONENT clang-resource-headers)

install(
  FILES ${hip_files}
  DESTINATION ${header_install_dir}/hip
  COMPONENT clang-resource-headers)

install(
  FILES ${hip_hcc_files}
  DESTINATION ${header_install_dir}/hip/hcc_detail
  COMPONENT clang-resource-headers)

install(
  FILES ${cuda_open_files}
  DESTINATION ${header_install_dir}/cuda_open
  COMPONENT clang-resource-headers)


install(
  FILES ${ppc_wrapper_files}
  DESTINATION ${header_install_dir}/ppc_wrappers
  COMPONENT clang-resource-headers)

install(
  FILES ${openmp_wrapper_files}
  DESTINATION ${header_install_dir}/openmp_wrappers
  COMPONENT clang-resource-headers)

if (NOT LLVM_ENABLE_IDE)
  add_llvm_install_targets(install-clang-resource-headers
                           DEPENDS clang-resource-headers
                           COMPONENT clang-resource-headers)
endif()
