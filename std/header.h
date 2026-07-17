


/* Core Libraries
 ******************************/
#include <gc.h>
#include <cstdint>
#include <cstdlib>
#include <atomic>
#include <bit>
#include <cstddef>
#include <immintrin.h>
#include <string.h>


/* Simpler Type Names
*******************************/
typedef uint32_t u32;
typedef uint64_t u64;
typedef uint8_t u8;
typedef int8_t s8;
typedef int32_t s32;
typedef int64_t s64;
typedef float f32;
typedef double f64;

typedef const void* const __restrict__ any;
typedef void* __restrict__ many;



/* Debug Printing
 ******************************/
#include <iostream>
#include <sstream>

#define ATOMIC_PRINT(content) \
    do { \
        std::ostringstream ss_; \
        ss_ << content << '\n'; \
        std::cout << ss_.str() << std::flush; \
    } while(0)

#ifdef DEBUG 
    #include <unordered_map>
    const std::unordered_map<u64, std::string> DEBUG_TAG_MAP = {
      { 0, "function pointer" },
      { 1, "heap object" },
      { 2, "slice" },
      { 3, "unused" },
      { 4, "unused" },
      { 5, "unused" },
      { 6, "subword" },
      { 7, "unused" }
    };
    #define DBG(x) ATOMIC_PRINT(x)
    #define DBG_VALUE(x) \
      x << " (tag: " << ((u64)x & (u64)7) << ", " << DEBUG_TAG_MAP.at((u64)x & (u64)7) << ")"
    // Assuming any is 64 bits
    #define DBG_VALUE_BASE10(x) ((u64)x)
#else // Or no-op
    #define DBG(x) do {} while(0)
    #define DBG_VALUE(x) ""
    #define DBG_VALUE_BASE10(x) ""
#endif


/* Basic Declarations
 **************************/

#define must_inline inline __attribute__((always_inline))
#define tailcall [[clang::musttail]] return
#define reg_passing __attribute__((preserve_none))
#define alignup(x, align) (((uintptr_t)(x) + (align) - 1) & -(uintptr_t)(align))


/* AVX-based 4-value return idiom
 **************************/

struct AVXRet
{
  __m256i data;
  
  static must_inline AVXRet a1m3(any a, many b, many c, many d)
  {
    return AVXRet  // NB: _mm256_set_epi64x uses reverse order
    {  
      _mm256_set_epi64x((uintptr_t)d, (uintptr_t)c, (uintptr_t)b, (uintptr_t)a)
    };
  }
  
  must_inline any a0() const
  {
    return (any)((uintptr_t*)&data)[0];
  }

  must_inline many m0() const
  {
    return (many)((uintptr_t*)&data)[1];
  }

  must_inline many m1() const
  {
    return (many)((uintptr_t*)&data)[2];
  }
  
  must_inline many m2() const
  {
    return (many)((uintptr_t*)&data)[3];
  }
};


/* Compiled (blessed) functions:
 **************************/

typedef AVXRet (reg_passing *blessed_t)
(   // calls follow a strict call/ret convention:
    many alloc_fr, many alloc_bk, many stack_fr, 
    any a0, any a1, any a2, any a3, any a4, 
    any a5, any a6, any a7
);


/* Macro for inlining a soft barrier
 **************************/

must_inline any freeze(many v)
{
  // Ensures the transition from many->any is not optimized across
  asm volatile("" ::: "memory");
  return (any)v;
}



/* v_equal wrapper that may dispatch to _u_0003d
 **********************************/

extern reg_passing AVXRet _u_0003d(many, many, many, any, any, any, any, any, any, any, any);
extern const void* _true;
extern const void* _false; 
must_inline reg_passing AVXRet v_equal(
    many alloc_fr, many alloc_bk, many stack_fr, any fbk,
    any a0, any a1, any a2, any a3, any a4, any a5, any a6)
{
  DBG("Checking equality of values " << a1 << ", " << a2);
  if ((u64)a1 == (u64)a2)
  { // Short circuit with _true 
    many* s = (many*)stack_fr;
    blessed_t cont = (blessed_t)s[-1];
    tailcall cont(alloc_fr, alloc_bk, (many)(s - 1), 0, (any)1, _true, 0, 0, 0, 0, 0);
  }
  else // Dispatch to = method
    tailcall _u_0003d(alloc_fr, alloc_bk, stack_fr, 0, a0, a1, a2, a3, a4, a5, a6);
}





