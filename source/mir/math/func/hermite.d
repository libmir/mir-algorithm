/++
Hermite Polynomial Coefficients

License: $(HTTP www.apache.org/licenses/LICENSE-2.0, Apache-2.0)
Authors: John Hall

+/

module mir.math.func.hermite;

/++
Statistician's Hermite polynomial coefficients

Params:
    N = Degree of polynomial

See_also:
    $(LINK2 https://en.wikipedia.org/wiki/Hermite_polynomials, Hermite polynomials)
+/
template hermiteCoefficientsStatistician(size_t N)
{
    import std.meta: AliasSeq;

    alias G = int[N + 1];
    static if (N == 0) {
        enum G hermiteCoefficientsStatistician = [1];
    } else static if (N == 1) {
        enum G hermiteCoefficientsStatistician = [0, 1];
    } else static if (N >= 2) {
        alias x = AliasSeq!(-(cast(int) N - 1) * hermiteCoefficientsStatistician!(N - 2)[0]);
        static foreach (i; 1..(N + 1)) {
            static if (i < (N - 1)) {
                x = AliasSeq!(x, hermiteCoefficientsStatistician!(N - 1)[i - 1] - (cast(int) N - 1) * hermiteCoefficientsStatistician!(N - 2)[i]);
            } else {
                x = AliasSeq!(x, hermiteCoefficientsStatistician!(N - 1)[i - 1]);
            }
        }
        enum G hermiteCoefficientsStatistician = [x];
    }
}

///
version(mir_test)
@safe pure nothrow @nogc
unittest
{
    import mir.polynomial: polynomial;
    import mir.rc.array: rcarray;
    import mir.test: should;

    auto h1 = hermiteCoefficientsStatistician!1.rcarray!(const double).polynomial;
    auto h2 = hermiteCoefficientsStatistician!2.rcarray!(const double).polynomial;
    auto h3 = hermiteCoefficientsStatistician!3.rcarray!(const double).polynomial;
    auto h4 = hermiteCoefficientsStatistician!4.rcarray!(const double).polynomial;
    auto h5 = hermiteCoefficientsStatistician!5.rcarray!(const double).polynomial;
    auto h6 = hermiteCoefficientsStatistician!6.rcarray!(const double).polynomial;
    auto h7 = hermiteCoefficientsStatistician!7.rcarray!(const double).polynomial;
    auto h8 = hermiteCoefficientsStatistician!8.rcarray!(const double).polynomial;
    auto h9 = hermiteCoefficientsStatistician!9.rcarray!(const double).polynomial;
    auto h10 = hermiteCoefficientsStatistician!10.rcarray!(const double).polynomial;
    
    h1(3).should == 3;
    h2(3).should == 8;
    h3(3).should == 18;
    h4(3).should == 30;
    h5(3).should == 18;
    h6(3).should == -96;
    h7(3).should == -396;
    h8(3).should == -516;
    h9(3).should == 1_620;
    h10(3).should == 9_504;
}

/++
Physicist's Hermite polynomial coefficients

Params:
    N = Degree of polynomial

See_also:
    $(LINK2 https://en.wikipedia.org/wiki/Hermite_polynomials, Hermite polynomials)
+/
template hermiteCoefficientsPhysicist(size_t N)
    if (N <= 10)
{
    import std.meta: AliasSeq;

    alias G = int[N + 1];
    static if (N == 0) {
        enum G hermiteCoefficientsPhysicist = [1];
    } else static if (N == 1) {
        enum G hermiteCoefficientsPhysicist = [0, 2];
    } else static if (N >= 2) {
        alias x = AliasSeq!(-hermiteCoefficientsPhysicist!(N - 1)[1]);
        static foreach (i; 1..(N + 1)) {
            static if ((i + 1) < N) {
                x = AliasSeq!(x, 2 * hermiteCoefficientsPhysicist!(N - 1)[i - 1] - (cast(int) i + 1) * hermiteCoefficientsPhysicist!(N - 1)[i + 1]);
            } else {
                x = AliasSeq!(x, 2 * hermiteCoefficientsPhysicist!(N - 1)[i - 1]);
            }
        }
        enum G hermiteCoefficientsPhysicist = [x];
    }
}

///
version(mir_test)
@safe pure nothrow @nogc
unittest
{
    import mir.polynomial: polynomial;
    import mir.rc.array: rcarray;
    import mir.test: should;

    auto h1 = hermiteCoefficientsPhysicist!1.rcarray!(const double).polynomial;
    auto h2 = hermiteCoefficientsPhysicist!2.rcarray!(const double).polynomial;
    auto h3 = hermiteCoefficientsPhysicist!3.rcarray!(const double).polynomial;
    auto h4 = hermiteCoefficientsPhysicist!4.rcarray!(const double).polynomial;
    auto h5 = hermiteCoefficientsPhysicist!5.rcarray!(const double).polynomial;
    auto h6 = hermiteCoefficientsPhysicist!6.rcarray!(const double).polynomial;
    auto h7 = hermiteCoefficientsPhysicist!7.rcarray!(const double).polynomial;
    auto h8 = hermiteCoefficientsPhysicist!8.rcarray!(const double).polynomial;
    auto h9 = hermiteCoefficientsPhysicist!9.rcarray!(const double).polynomial;
    auto h10 = hermiteCoefficientsPhysicist!10.rcarray!(const double).polynomial;
    
    h1(3).should == 6;
    h2(3).should == 34;
    h3(3).should == 180;
    h4(3).should == 876;
    h5(3).should == 3_816;
    h6(3).should == 14_136;
    h7(3).should == 39_024;
    h8(3).should == 36_240;
    h9(3).should == -406_944;
    h10(3).should == -3_093_984;
}
