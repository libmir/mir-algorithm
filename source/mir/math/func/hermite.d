/++
Hermite Polynomial Coefficients

License: $(HTTP www.apache.org/licenses/LICENSE-2.0, Apache-2.0)
Authors: John Hall

+/

module mir.math.func.hermite;

/++
Normalized (probabilist's) Hermite polynomial coefficients

Params:
    N = Degree of polynomial

See_also:
    $(LINK2 https://en.wikipedia.org/wiki/Hermite_polynomials, Hermite polynomials)
+/
template hermiteCoefficientsNorm(size_t N)
{
    import std.meta: AliasSeq;

    alias G = int[N + 1];
    static if (N == 0) {
        enum G hermiteCoefficientsNorm = [1];
    } else static if (N == 1) {
        enum G hermiteCoefficientsNorm = [0, 1];
    } else static if (N >= 2) {
        alias x = AliasSeq!(-(cast(int) N - 1) * hermiteCoefficientsNorm!(N - 2)[0]);
        static foreach (i; 1..(N + 1)) {
            static if (i < (N - 1)) {
                x = AliasSeq!(x, hermiteCoefficientsNorm!(N - 1)[i - 1] - (cast(int) N - 1) * hermiteCoefficientsNorm!(N - 2)[i]);
            } else {
                x = AliasSeq!(x, hermiteCoefficientsNorm!(N - 1)[i - 1]);
            }
        }
        enum G hermiteCoefficientsNorm = [x];
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

    auto h1 = hermiteCoefficientsNorm!1.rcarray!(const double).polynomial;
    auto h2 = hermiteCoefficientsNorm!2.rcarray!(const double).polynomial;
    auto h3 = hermiteCoefficientsNorm!3.rcarray!(const double).polynomial;
    auto h4 = hermiteCoefficientsNorm!4.rcarray!(const double).polynomial;
    auto h5 = hermiteCoefficientsNorm!5.rcarray!(const double).polynomial;
    auto h6 = hermiteCoefficientsNorm!6.rcarray!(const double).polynomial;
    auto h7 = hermiteCoefficientsNorm!7.rcarray!(const double).polynomial;
    auto h8 = hermiteCoefficientsNorm!8.rcarray!(const double).polynomial;
    auto h9 = hermiteCoefficientsNorm!9.rcarray!(const double).polynomial;
    auto h10 = hermiteCoefficientsNorm!10.rcarray!(const double).polynomial;
    
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
template hermiteCoefficients(size_t N)
    if (N <= 10)
{
    import std.meta: AliasSeq;

    alias G = int[N + 1];
    static if (N == 0) {
        enum G hermiteCoefficients = [1];
    } else static if (N == 1) {
        enum G hermiteCoefficients = [0, 2];
    } else static if (N >= 2) {
        alias x = AliasSeq!(-hermiteCoefficients!(N - 1)[1]);
        static foreach (i; 1..(N + 1)) {
            static if ((i + 1) < N) {
                x = AliasSeq!(x, 2 * hermiteCoefficients!(N - 1)[i - 1] - (cast(int) i + 1) * hermiteCoefficients!(N - 1)[i + 1]);
            } else {
                x = AliasSeq!(x, 2 * hermiteCoefficients!(N - 1)[i - 1]);
            }
        }
        enum G hermiteCoefficients = [x];
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

    auto h1 = hermiteCoefficients!1.rcarray!(const double).polynomial;
    auto h2 = hermiteCoefficients!2.rcarray!(const double).polynomial;
    auto h3 = hermiteCoefficients!3.rcarray!(const double).polynomial;
    auto h4 = hermiteCoefficients!4.rcarray!(const double).polynomial;
    auto h5 = hermiteCoefficients!5.rcarray!(const double).polynomial;
    auto h6 = hermiteCoefficients!6.rcarray!(const double).polynomial;
    auto h7 = hermiteCoefficients!7.rcarray!(const double).polynomial;
    auto h8 = hermiteCoefficients!8.rcarray!(const double).polynomial;
    auto h9 = hermiteCoefficients!9.rcarray!(const double).polynomial;
    auto h10 = hermiteCoefficients!10.rcarray!(const double).polynomial;
    
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
