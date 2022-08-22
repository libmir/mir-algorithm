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
@safe pure nothrow
long[] hermiteCoefficientsNorm(size_t N)
{
    if (N == 0) {
      return [1];  
    } else {
        typeof(return) output = [0, 1];
        if (N > 1) {
            output.length = N + 1;
            int K;
            typeof(return) h_N_minus_1 = hermiteCoefficientsNorm(0); // to be copied to h_N_minus_2 in loop
            h_N_minus_1.length = N;
            typeof(return) h_N_minus_2; //value replaced later
            h_N_minus_2.length = N - 1;

            foreach (size_t j; 2..(N + 1)) {
                h_N_minus_2[0..(j - 1)] = h_N_minus_1[0..(j - 1)];
                h_N_minus_1[0..j] = output[0..j];
                K = -(cast(int) j - 1);
                output[0] = K * h_N_minus_2[0];
                foreach (size_t i; 1..(j - 1)) {
                    output[i] = h_N_minus_1[i - 1] + K * h_N_minus_2[i];
                }
                foreach (size_t i; (j - 1)..(j + 1)) {
                    output[i] = h_N_minus_1[i - 1];
                }
            }
        }
        return output;
    }
}

///
version(mir_test)
@safe pure nothrow
unittest
{
    import mir.polynomial: polynomial;
    import mir.rc.array: rcarray;
    import mir.test: should;

    auto h0 = hermiteCoefficientsNorm(0).rcarray!(const double).polynomial;
    auto h1 = hermiteCoefficientsNorm(1).rcarray!(const double).polynomial;
    auto h2 = hermiteCoefficientsNorm(2).rcarray!(const double).polynomial;
    auto h3 = hermiteCoefficientsNorm(3).rcarray!(const double).polynomial;
    auto h4 = hermiteCoefficientsNorm(4).rcarray!(const double).polynomial;
    auto h5 = hermiteCoefficientsNorm(5).rcarray!(const double).polynomial;
    auto h6 = hermiteCoefficientsNorm(6).rcarray!(const double).polynomial;
    auto h7 = hermiteCoefficientsNorm(7).rcarray!(const double).polynomial;
    auto h8 = hermiteCoefficientsNorm(8).rcarray!(const double).polynomial;
    auto h9 = hermiteCoefficientsNorm(9).rcarray!(const double).polynomial;
    auto h10 = hermiteCoefficientsNorm(10).rcarray!(const double).polynomial;

    h0(3).should == 1;
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

/// Also works with @nogc CTFE
version(mir_test)
@safe pure nothrow @nogc
unittest
{
    import mir.ndslice.slice: sliced;
    import mir.test: should;

    static immutable result = [-1, 0, 1];

    static immutable hc2 = hermiteCoefficientsNorm(2);
    hc2.sliced.should == result;
}

/++
Physicist's Hermite polynomial coefficients

Params:
    N = Degree of polynomial

See_also:
    $(LINK2 https://en.wikipedia.org/wiki/Hermite_polynomials, Hermite polynomials)
+/
@safe pure nothrow
long[] hermiteCoefficients(size_t N)
{
    if (N == 0) {
      return [1];  
    } else {
        typeof(return) output = [0, 2];
        if (N > 1) {
            output.length = N + 1;
            typeof(return) h_N_minus_1 = hermiteCoefficients(0);
            h_N_minus_1.length = N;

            foreach (size_t j; 2..(N + 1)) {
                h_N_minus_1[0..j] = output[0..j];
                output[0] = -h_N_minus_1[1];
                foreach (size_t i; 1..(j - 1)) {
                    output[i] = 2 * h_N_minus_1[i - 1] - (cast(int) i + 1) * h_N_minus_1[i + 1];
                }
                foreach (size_t i; (j - 1)..(j + 1)) {
                    output[i] = 2 * h_N_minus_1[i - 1];
                }
            }
        }
        return output;
    }
}

///
version(mir_test)
@safe pure nothrow
unittest
{
    import mir.polynomial: polynomial;
    import mir.rc.array: rcarray;
    import mir.test: should;

    auto h0 = hermiteCoefficients(0).rcarray!(const double).polynomial;
    auto h1 = hermiteCoefficients(1).rcarray!(const double).polynomial;
    auto h2 = hermiteCoefficients(2).rcarray!(const double).polynomial;
    auto h3 = hermiteCoefficients(3).rcarray!(const double).polynomial;
    auto h4 = hermiteCoefficients(4).rcarray!(const double).polynomial;
    auto h5 = hermiteCoefficients(5).rcarray!(const double).polynomial;
    auto h6 = hermiteCoefficients(6).rcarray!(const double).polynomial;
    auto h7 = hermiteCoefficients(7).rcarray!(const double).polynomial;
    auto h8 = hermiteCoefficients(8).rcarray!(const double).polynomial;
    auto h9 = hermiteCoefficients(9).rcarray!(const double).polynomial;
    auto h10 = hermiteCoefficients(10).rcarray!(const double).polynomial;

    h0(3).should == 1;
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

/// Also works with @nogc CTFE
version(mir_test)
@safe pure nothrow @nogc
unittest
{
    import mir.ndslice.slice: sliced;
    import mir.test: should;

    static immutable result = [-2, 0, 4];

    static immutable hc2 = hermiteCoefficients(2);
    hc2.sliced.should == result;
}
