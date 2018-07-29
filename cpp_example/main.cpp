#include <cstdlib>
#include "mir/ndslice.h"

namespace Space
{
    mir_slice<double*, 2> eye(size_t n);
    void printMatrix(mir_slice<double*, 2> matrix);
}

int main()
{
    auto matrix = Space::eye(3);
    Space::printMatrix(matrix);
    std::free(matrix._iterator);
    return 0;
}
