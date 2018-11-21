#include <cassert> 
#include <cstdio>
#include <cstdlib>
#include "mir/rcarray.h"
#include "mir/ndslice.h"

namespace Space
{
    mir_slice<double*, 2> eye(size_t n);
    void printMatrix(mir_slice<double*, 2> matrix);
    void initWithIota(mir_rcarray<double> &a);
    void reverseRcSlice(mir_slice<mir_rci<double>>& a);
}

int main()
{
    mir_slice<double*, 2> matrix = Space::eye(3);
    Space::printMatrix(matrix);
    std::free(matrix._iterator);


    // test rcarray constructors and destructors
    mir_rcarray<double> a(3); // [NaN, NaN, NaN]
    assert(a.size() == 3);

    Space::initWithIota(a); //[0, 1, 2]
    auto b = a; // check copy constructor
    auto c = b.asSlice();
    auto d = c; // check copy constructor
    Space::reverseRcSlice(d); //[2, 1, 0]

    // reversed 0 1 2 (iota)
    assert(a[0] == 2);
    assert(a[1] == 1);
    assert(a[2] == 0);

    assert(d._iterator._iterator == a.data());

    // check foreach loops
    for (auto& elem : a)
    {
        elem = 0;
    }

    const auto e = a;
    for (auto& elem : e)
    {
        assert(elem == 0);
    }

    return 0;
}
