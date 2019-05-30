#include <cassert> 
#include <cstdio>
#include <cstdlib>
#include <vector>
#include <map>
#include "mir/series.h"
#include "mir/rcarray.h"
#include "mir/rcptr.h"
#include "mir/ndslice.h"
#include "mir/numeric.h"

namespace Space
{
    mir_slice<double*, 2> eye(size_t n);
    void printMatrix(mir_slice<double*, 2> matrix);
    void initWithIota(mir_rcarray<double> &a);
    void reverseRcSlice(mir_slice<mir_rci<double>>& a);
}

void testSeries();
void testRCPtr();
void testPM();
void testFindRoot();
void testStringView();
void testDestructorView();

int main()
{
    mir_slice<double*, 2> matrix = Space::eye(3);
    matrix(1, 2) = 4;
    assert(matrix.row(1)[2] == 4);
    assert(matrix.col(2)[1] == 4);
    Space::printMatrix(matrix);
    std::free(matrix._iterator);


    // test rcarray constructors and destructors
    mir_rcarray<double> a(3); // [NaN, NaN, NaN]
    mir_rcarray<double> al = {5, 6, 4}; // [5, 6, 4]
    mir_rcarray<double> av = std::vector<int>({5, 6, 4}); // [5, 6, 4]
    assert(a.size() == 3);
    assert(al.size() == 3);
    assert(av.size() == 3);

    assert(al[0] == 5);
    assert(al[1] == 6);
    assert(al[2] == 4);

    assert(av[0] == 5);
    assert(av[1] == 6);
    assert(av[2] == 4);

    Space::initWithIota(a); //[0, 1, 2]
    auto b = a; // check copy constructor
    auto c = b.asSlice();
    auto d = c; // check copy constructor
    Space::reverseRcSlice(d); //[2, 1, 0]

    // reversed 0 1 2 (iota)
    assert(a[0] == 2);
    assert(a[1] == 1);
    assert(a[2] == 0);

    assert(c[0] == 2);
    assert(c[1] == 1);
    assert(c[2] == 0);

    assert(&c[1] == &a[1]);

    assert(d._iterator._iterator == a.data());

    // check foreach loops for rcarray
    for (auto& elem : a)
    {
        elem = 0;
    }

    const auto e = a;
    for (auto& elem : e)
    {
        assert(elem == 0);
    }

    for (auto& elem : c)
    {
        elem = 1;
    }

    for (auto& elem : c)
    {
        assert(elem == 1);
    }

    a = b;
    al = a;

    testSeries();
    testRCPtr();
    testPM();
    testStringView();
    testDestructorView();

    return 0;
}

void testSeries()
{
    std::map<int, double> map;
    map[1] = 4.0;
    map[2] = 5.0;
    map[3] = 6.0; // index 5 replaced with index 4 below
    map[5] = 10.0;
    map[10] = 11.0;

    auto series = mir_make_series(map);

    assert(series[1].first == 2);
    assert(series[1].second == 5);

    double sum = 0;
    for (auto&& [key, value] : series)
    {
        sum += value;
    }

    assert(sum == 36);

    series.index()[2] = 4;
    series.data()[2] = 10;

    assert(series[2].first == 4);
    assert(series[2].second == 10);
    
    auto s = std::move(series);
    auto s2 = s;
    s2 = s;

    double value;
    int key;
    assert(s.try_get(2, value) && value == 5.0);
    assert(*s.try_get_ptr(2) == 5.0);
    // printf("%ld\n", s.index()[s.transition_index_less(4)]);
    assert(!s.try_get(8, value));

    assert(s.try_get_next(2, value) && value == 5.0);
    assert(s.try_get_prev(2, value) && value == 5.0);
    assert(s.try_get_next(8, value) && value == 11.0);
    assert(s.try_get_prev(8, value) && value == 10.0);
    assert(!s.try_get_first(8, 9, value));
    assert(s.try_get_first(2, 10, value) && value == 5.0);
    assert(s.try_get_last(2, 10, value) && value == 11.0);
    assert(s.try_get_last(2, 8, value) && value == 10.0);

    key = 2; assert(s.try_get_next_update_key(key, value) && key == 2 && value == 5.0);
    key = 2; assert(s.try_get_prev_update_key(key, value) && key == 2 && value == 5.0);
    key = 8; assert(s.try_get_next_update_key(key, value) && key == 10 && value == 11.0);
    key = 8; assert(s.try_get_prev_update_key(key, value) && key == 5 && value == 10.0);
    key = 2; assert(s.try_get_first_update_lower(key, 10, value) && key == 2 && value == 5.0);
    key = 10; assert(s.try_get_last_update_upper(2, key, value) && key == 10 && value == 11.0);
    key = 8; assert(s.try_get_last_update_upper(2, key, value) && key == 5 && value == 10.0);
}

struct S { double d = 0; S() {}; S(double e) : d(e) {} };
struct C : S { double j = 3; C(double d, double k) : S(d) { k = j; }; };

void testRCPtr()
{
    auto s = mir_make_shared<S>(3.0);
    auto e = mir_make_shared<S>(5.0);
    s = e;
    (*e).d = 4;
    assert(s->d == 4);
    assert(s.getContext()->counter == 2);
    s = nullptr;
    assert(e.getContext()->counter == 1);
}

void testPM()
{
    auto c = mir_make_shared<C>(3.0, 4);
    assert(c.getContext()->counter == 1);
    auto s = mir_rcptr<S>(c);
    assert(c.getContext()->counter == 2);
    assert(s->d == 3);
}

void testFindRoot()
{
    std::function<double(double)> func = [](double x)  { return x * x - 1; };
    std::function<bool(double, double)> tolerance = [](double a, double b) { return b - a < 1e-6; };
    double a = 0;
    double b = 10e100;
    auto result = mir_find_root(func, tolerance, a, b);
    assert(result.validate().x() == 1);

    // with relative tolerance
    assert(mir_find_root(func, 1e-6, a, b).validate().x());
}

void testStringView()
{
    auto ref = std::string_view("Hi");
    auto b = mir_rcarray_from_string(ref);
    mir_rcarray<char> c = mir_rcarray_from_string(std::string("Hi"));
    mir_rcarray<const char> d = mir_rcarray_from_string("Hi");
    assert(ref == mir_get_string_view(b));
    assert(ref == mir_get_string_view(c));
    assert(ref == mir_get_string_view(d));
    assert(typeid((mir_get_string_view(c))) == typeid((mir_get_string_view(d))));
    ref = c; // implicit conversion
    ref = d; // implicit conversion
}

static int CD_i;

struct CD
{
    double d;
    ~CD() noexcept
    {
        CD_i++;
    }
};

void testDestructorView()
{
    auto s = new mir_rcarray<CD>(10);
    delete s;
    printf("%d\n", CD_i);
    assert(CD_i == 10);
}
