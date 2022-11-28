#pragma once

namespace mir {
    namespace interpolate
    {
        enum class SplineType
        {
            c2,
            cardinal,
            monotone,
            doubleQuadratic,
            akima,
            makima
        };

        enum class SplineBoundaryType
        {
            periodic = -1,
            notAKnot,
            firstDerivative,
            secondDerivative,
            parabolic,
            monotone,
            akima,
            makima
        };

        template<class T>
        struct SplineBoundaryCondition
        {
            SplineBoundaryType type = SplineBoundaryType::notAKnot;
            T value = 0;
        };
    }
}
