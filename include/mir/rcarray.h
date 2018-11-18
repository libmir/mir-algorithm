
#include <stdexcept>
#include "mir/ndslice.h"

template <typename T>
struct mir_rcarray
{
private:

    void* _context;

public:

    ~mir_rcarray();
    mir_rcarray(mir_rcarray& rhs);
    bool initialize(size_t length, uint alignment = 16, bool deallocate, bool initialize);

    mir_slice<mir_rci<T>> asSlice();

    inline mir_rcarray(size_t length, uint alignment = alignof(T), bool deallocate = true, bool initialize = true)
    {
        if (!initialize(length, alignment, deallocate, initialize)
        {
            throw runtime_error("mir_rcarray: out of memory arror.");
        }
    }
};


template <typename T>
struct mir_rci
{
    T* _iterator;
    mir_rcarray<T> _array;

public:

    ~mir_rci() = default;
    mir_rci(mir_rci& rhs) = default;
}
