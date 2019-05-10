#ifndef MIR_NUMERIC

#define MIR_NUMERIC

#include <functional>
#include <limits>

enum class mir_find_root_status
{
    /// Success
    success,
    ///
    badBounds,
    /// 
    nanX,
    ///
    nanY,
};

template<class T>
struct mir_find_root_result
{
    /// Left bound
    T ax = 0;
    /// Rifht bound
    T bx = 0;
    /// `f(ax)` or `f(axfabs()).fmin(T.max / 2).copysign(f(ax))`.
    T ay = 0;
    /// `f(bx)` or `f(bxfabs()).fmin(T.max / 2).copysign(f(bx))`.
    T by = 0;
    /// Amount of target function calls.
    unsigned int iterations = 0;

    /**
    Returns: self
    Required_versions:`D_Exceptions`
    Throws: `Exception` if $(LREF FindRootResult.status) isn't $(LREF mir_find_root_status.success).
    */
    const mir_find_root_result& validate() const
    {
        switch(status())
        {
            case mir_find_root_status::success: return *this;
            case mir_find_root_status::badBounds: throw std::domain_error("findRoot: f(ax) and f(bx) must have opposite signs to bracket the root.");
            case mir_find_root_status::nanX: throw std::domain_error("findRoot: ax or bx is NaN.");
            case mir_find_root_status::nanY: throw std::domain_error("findRoot: f(x) returned NaN.");
            default: throw std::domain_error("findRoot: unknown error.");
        }
    }

    /**
    Returns: $(LREF mir_find_root_status)
    */
    mir_find_root_status status() const noexcept;

    /**
    A bound that corresponds to the minimal absolute function value.

    Returns: `!(fabs(ay) > fabs(by)) ? ax : bx`
    */
    T x() const noexcept;

    /**
    The minimal of absolute function values.

    Returns: `!(fabs(ay) > fabs(by)) ? ay : by`
    */
    T y() const noexcept;
};

template<class T>
T mir_internal_find_root_f(const void* ctx, T x)
{
    return (*((const std::function<T(T)>*)ctx))(x);
}

template<class T>
bool mir_internal_find_root_tolerance(const void* ctx, T a, T b)
{
    return (*((const std::function<bool(T, T)>*)ctx))(a, b);
}

mir_find_root_result<float> mir_find_root(
    float ax,
    float bx,
    float fax,
    float fbx,
    float lower_bound,
    float upper_bound,
    unsigned int maxIterations,
    float (*f)(const void* ctx, float x),
    const void* f_ctx = NULL,
    bool (*tolerance)(const void* ctx, float a, float b) = NULL,
    const void* tolerance_ctx = NULL
);

mir_find_root_result<double> mir_find_root(
    double ax,
    double bx,
    double fax,
    double fbx,
    double lower_bound,
    double upper_bound,
    unsigned int maxIterations,
    double (*f)(const void* ctx, double x),
    const void* f_ctx = NULL,
    bool (*tolerance)(const void* ctx, double a, double b) = NULL,
    const void* tolerance_ctx = NULL
);

mir_find_root_result<long double> mir_find_root(
    long double ax,
    long double bx,
    long double fax,
    long double fbx,
    long double lower_bound,
    long double upper_bound,
    unsigned int maxIterations,
    long double (*f)(const void* ctx, long double x),
    const void* f_ctx = NULL,
    bool (*tolerance)(const void* ctx, long double a, long double b) = NULL,
    const void* tolerance_ctx = NULL
);

template<class T>
mir_find_root_result<T> mir_find_root(
    const std::function<T(T)>& f,
    const std::function<bool(T, T)>& tolerance,
    const T a,
    const T b,
    const T fa = std::numeric_limits<T>::quiet_NaN(),
    const T fb = std::numeric_limits<T>::quiet_NaN(),
    const T lower_bound = std::numeric_limits<T>::quiet_NaN(),
    const T upper_bound = std::numeric_limits<T>::quiet_NaN(),
    int maxIterations = sizeof(T) * 16
)
{
    return mir_find_root(
        a,
        b,
        fa,
        fb,
        lower_bound,
        upper_bound,
        maxIterations,
        &mir_internal_find_root_f<T>,
        &f,
        &mir_internal_find_root_tolerance<T>,
        &tolerance
    );
}

#endif
