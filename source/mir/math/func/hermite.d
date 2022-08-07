/++
Hermite Polynomial Coefficients

License: $(HTTP www.apache.org/licenses/LICENSE-2.0, Apache-2.0)
Authors: John Hall

+/

module mir.math.func.hermite;

/++
Statistician's Hermite polynomial coefficients

Params:
    N = Polynomial Order

See_also:
    $(LINK2 https://en.wikipedia.org/wiki/Hermite_polynomials, Hermite polynomials)
+/
template hermiteCoefficientsStatistician(size_t N)
    if (N <= 10)
{
    alias G = int[N + 1];
    static if (N == 0) {
        enum G hermiteCoefficientsStatistician = [1];
    } else static if (N == 1) {
        enum G hermiteCoefficientsStatistician = [0, 1];
    } else static if (N == 2) {
        enum G hermiteCoefficientsStatistician = [-1, 0, 1];
    } else static if (N == 3) {
        enum G hermiteCoefficientsStatistician = [0, -3, 0, 1];
    } else static if (N == 4) {
        enum G hermiteCoefficientsStatistician = [3, 0, -6, 0, 1];
    } else static if (N == 5) {
        enum G hermiteCoefficientsStatistician = [0, 15, 0, -10, 0, 1];
    } else static if (N == 6) {
        enum G hermiteCoefficientsStatistician = [-15, 0, 45, 0, -15, 0, 1];
    } else static if (N == 7) {
        enum G hermiteCoefficientsStatistician = [0, -105, 0, 105, 0, -21, 0, 1];
    } else static if (N == 8) {
        enum G hermiteCoefficientsStatistician = [105, 0, -420, 0, 210, 0, -28, 0, 1];
    } else static if (N == 9) {
        enum G hermiteCoefficientsStatistician = [0, 945, 0, -1260, 0, 378, 0, -36, 0, 1];
    } else static if (N == 10) {
        enum G hermiteCoefficientsStatistician = [-945, 0, 4725, 0, -3150, 0, 630, 0, -45, 0, 1];
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
    N = Polynomial Order

See_also:
    $(LINK2 https://en.wikipedia.org/wiki/Hermite_polynomials, Hermite polynomials)
+/
template hermiteCoefficientsPhysicist(size_t N)
    if (N <= 10)
{
    alias G = int[N + 1];
    static if (N == 0) {
        enum G hermiteCoefficientsPhysicist = [1];
    } else static if (N == 1) {
        enum G hermiteCoefficientsPhysicist = [0, 2];
    } else static if (N == 2) {
        enum G hermiteCoefficientsPhysicist = [-2, 0, 4];
    } else static if (N == 3) {
        enum G hermiteCoefficientsPhysicist = [0, -12, 0, 8];
    } else static if (N == 4) {
        enum G hermiteCoefficientsPhysicist = [12, 0, -48, 0, 16];
    } else static if (N == 5) {
        enum G hermiteCoefficientsPhysicist = [0, 120, 0, -160, 0, 32];
    } else static if (N == 6) {
        enum G hermiteCoefficientsPhysicist = [-120, 0, 720, 0, -480, 0, 64];
    } else static if (N == 7) {
        enum G hermiteCoefficientsPhysicist = [0, -1680, 0, 3360, 0, -1344, 0, 128];
    } else static if (N == 8) {
        enum G hermiteCoefficientsPhysicist = [1680, 0, -13440, 0, 13440, 0, -3584, 0, 256];
    } else static if (N == 9) {
        enum G hermiteCoefficientsPhysicist = [0, 30240, 0, -80640, 0, 48384, 0, -9216, 0, 512];
    } else static if (N == 10) {
        enum G hermiteCoefficientsPhysicist = [-30240, 0, 302400, 0, -403200, 0, 161280, 0, -23040, 0, 1024];
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
