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
    mir_rcarray<double> a(3);
    Space::initWithIota(a);
    auto b = a;
    auto c = b.asSlice();
    auto d = c;
    Space::reverseRcSlice(d);
    auto e = a.asSlice();

    printf("%f %f %f",
        e._iterator._iterator[0],
        e._iterator._iterator[1],
        e._iterator._iterator[2]);

    return 0;
}
