


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
    return (any)(uintptr_t)_mm256_extract_epi64(data, 0);
  }

  must_inline many m0() const
  {
    return (many)(uintptr_t)_mm256_extract_epi64(data, 1);
  }

  must_inline many m1() const
  {
    return (many)(uintptr_t)_mm256_extract_epi64(data, 2);
  }
  
  must_inline many m2() const
  {
    return (many)(uintptr_t)_mm256_extract_epi64(data, 3);
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

    extern const std::unordered_map<u64, std::string> DEBUG_OBJ_TAG_MAP; // Generated inside link.cpp
    extern reg_passing AVXRet _main(many,many,many,any,any,any,any,any,any,any,any);

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

    // Helper to get a value from an unordered map given the key or if the key doesn't exist return the default value.
    template <typename K, typename V>
    V get_or_default(const std::unordered_map<K, V>& map, const K& key, const V& default_val)
    {
      auto it = map.find(key);
      if (it != map.end()) {
          return it->second;
      }
      return default_val;
    }

    // Translated from `lookup_object_tag` in base.ti
    #define DBG_LOOKUP_OBJ_TAG(x) \
      (((u64)(((u64)(((u64)(*((many*)((u64)x & ((u64)0xfffffffffffffff8))))) >> ((u32)8))) & ((u64)0x00000000ffffffff))) | \
	     ((u64)(((u64)((blessed_t)_main)) & ((u64)0xffffffff00000000))))

    // Gets x's object tag and returns it as a nicely formatted parenthetical string.
    template <typename T>
    std::string get_obj_tag_string(T x)
    {
      std::ostringstream oss;
      oss << "(heap object tag: " << (any)(DBG_LOOKUP_OBJ_TAG(x)) << ", " << get_or_default(DEBUG_OBJ_TAG_MAP, (u64)(DBG_LOOKUP_OBJ_TAG(x)), std::string("unknown obj tag")) << ")";
      return oss.str();
    }

    #define DBG_GET_TAG(x) ((u64)x & (u64)7)

    #define DBG(x) ATOMIC_PRINT(x)
    #define DBG_VALUE(x) \
      x << " (tag: " << DBG_GET_TAG(x) << ", " << DEBUG_TAG_MAP.at(DBG_GET_TAG(x)) << ") " << ((DBG_GET_TAG(x) == 1) ? get_obj_tag_string(x) : " ") << " "
    // Assuming any is 64 bits
    #define DBG_VALUE_BASE10(x) ((u64)x)

#else // Or no-op
    #define DBG(x) do {} while(0)
    #define DBG_VALUE(x) ""
    #define DBG_VALUE_BASE10(x) ""
#endif



/**
 * Helpers to handle blessed function pointers being stored in a u64.
 * This is in order to circumvent the strict pointer aliasing and avoid
 * undefined behavior with object-pointer/function-pointer casts.
 */

must_inline u64 blessed_to_bits(blessed_t f)
{
  static_assert(sizeof(blessed_t) <= sizeof(u64));
  u64 bits = 0;
  memcpy(&bits, &f, sizeof(f));
  return bits;
}

must_inline blessed_t bits_to_blessed(u64 bits)
{
  blessed_t f;
  memcpy(&f, &bits, sizeof(f));
  return f;
}

must_inline blessed_t any_to_blessed(any a)
{
  u64 bits = (u64)a;
  asm volatile("" : "+r"(bits) : : "memory");
  return bits_to_blessed(bits);
}

must_inline any blessed_to_any(blessed_t f)
{
  u64 bits = blessed_to_bits(f);
  asm volatile("" : "+r"(bits) : : "memory");
  return (any)bits;
}

template <typename Fn>
must_inline blessed_t fn_to_blessed(Fn f)
{
  static_assert(sizeof(Fn) == sizeof(blessed_t));
  blessed_t out;
  memcpy(&out, &f, sizeof(out));
  return out;
}

must_inline void stack_store_blessed(many stack_fr, s64 idx, blessed_t f)
{
  u64 bits = blessed_to_bits(f);
  volatile u64* vslot = (volatile u64*)&((u64*)stack_fr)[idx];
  *vslot = bits;
}

must_inline blessed_t stack_load_blessed(many stack_fr, s64 idx)
{
  volatile u64* vslot = (volatile u64*)&((u64*)stack_fr)[idx];
  return bits_to_blessed(*vslot);
}


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
extern const void* _u__noarg; 
must_inline reg_passing AVXRet v_equal(
    many alloc_fr, many alloc_bk, many stack_fr, any fbk,
    any a0, any a1, any a2, any a3, any a4, any a5, any a6)
{
  DBG("Checking equality of values " << a1 << ", " << a2);
  if ((u64)a1 == (u64)a2)
  { // Short circuit with _true 
    blessed_t cont = stack_load_blessed(stack_fr, -1);
    tailcall cont(alloc_fr, alloc_bk, (many)((many*)stack_fr - 1), 0, (any)1, _true, _u__noarg, _u__noarg, _u__noarg, _u__noarg, _u__noarg);
  }
  else // Dispatch to = method
    tailcall _u_0003d(alloc_fr, alloc_bk, stack_fr, 0, a0, a1, a2, a3, a4, a5, a6);
}





