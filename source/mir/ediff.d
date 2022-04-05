/++
$(H1 Expression differentiation)

The module provides API for rapid evaluation of a user-requested set of partial derivatives of any order.

The implementation operates with double precision numbers.

$(BOOKTABLE $(H2 Expression construction),
$(TR $(TH Name) $(TH Description))
$(T2 $(LREF Const), A double precision constant with an immidiate value)
$(T2 $(LREF Var), A double precision named variable with an immidiate value)
$(T2 `+`, Constructs the sum of two expressions)
$(T2 `-`, Constructs the difference of two expressions)
$(T2 `*`, Constructs the product of two expressions)
$(T2 `/`, Constructs the quotient of two expressions)
$(T2 $(LREF derivativeOf), Constructs a partial derivative of one order.
    The function can be applied in any stage any number of times.
    The function does NOT evaluate the expression.)
$(T2 $(LREF powi), Constructs of the expression raised to the specified (positive or negative) compile-time integral power.)
$(T2 $(LREF log), Constructs the natural logarithm of the expression.)
$(T2 $(LREF exp), Constructs the natural exponent of the expression.)
$(T2 $(LREF sqrt), Constructs the square root of the expression.)
$(T2 $(LREF normalDistribution), Constructs the cumulative normal distribution function of the expression.)
)

$(BOOKTABLE $(H2 Expression composition),
$(TR $(TH Name) $(TH Description))
$(T2 $(LREF composeAt), Given a compiletime variable name `v` and two expressions `F(v, U)` and `G(Y)`,
    constructs a composition `F ∘ G (U, Y)` as `v = G`)
)

$(BOOKTABLE $(H2 Derivative set definition),
$(TR $(TH Name) $(TH Description))
$(T2 $(LREF Derivative), User defined attribute that should applied on a struct member definition of a user-defined set of derivatives.
    The attribute holds an unordered set with duplicates of variables names to reflect which partial derivative this member contains.)
$(T2 $(LREF Minus), User-defined attribute that can be applied on struct member definition along with $(LREF Derivative) to denote
    that the member holds a negative value of the partial derivative.
    This attribute is useful for financial code where verbal definitions may denote negative partial derivatives.)
)

$(BOOKTABLE $(H2 Function definition),
$(TR $(TH Name) $(TH Description))
$(T2 $(LREF DependsOn), User defined attribute that should applied on struct definition of a user-defined expression function)
$(T2 $(LREF Dependencies), Fetchs a set of variables the expression is depends on.
    First, it checks if the expression has $(LREF DependsOn) UDA
    ; otherwise, iterates over members with $(LREF Derivative) UDA and collects variable names. )
$(T2 .getDerivative, The generic method, which a user expression function should define.
    The method should accept a compile-time array of variable names and evaluate the corresponding partial derivative.)
$(T2 $(LREF ediffOperators, Mixin template that propagates `+`, `-`, `*`, and `/` binary operators for user defined expression functions.))
)

$(BOOKTABLE $(H2 Expression evaluation),
$(TR $(TH Name) $(TH Description))
$(T2 $(LREF getFunctionValue), Evaluates function value. It is shortcut for $(LREF getDerivative) of zero order.)
$(T2 $(LREF getDerivative), Evaluates partial derivative for user-defined compiletime set of variables.
    First, it checks if the expression has `.getDerivative` methods and uses it,
    otherwise iterates over members with $(LREF Derivative) UDA and tries to find a member that holds the required partial derivative.)
$(T2 $(LREF setDerivatives), Evaluates partial derivatives and function value, if any, for a user-provided set of partial derivatives.
    The derivative set can be defined with $(LREF Derivative) and $(LREF Minus) UDAs.)
)

$(H2 Optimization note)

During function differentiation, the resulting set of expressions likely contains a lot of
identical calls of elementary functions. LLVM  efficiently eliminates equivalent calls of intrinsic
functions such as `powi`, `log`, `exp`, and `sqrt`.
On the other hand, it can't eliminate identical calls of complex functions.
It is highly recommended to evaluate a set of partial derivatives immediately after constructing
a complex expression such as $(LREF normalDistribution).

Authors: Ilya Yaroshenko
+/
module mir.ediff;

///
version(mir_test)
unittest
{
    ///
    static struct D
    {
        @Derivative()
        double _;
        @Derivative("a")
        double a;
        @Derivative("b")
        double b;
        @Minus @Derivative("a", "b") 
        double mab;
    }

    auto d = D(3, 4, 5, -6);
    assert(d.powi!2.setDerivatives!D == D(9, 24, 30, -76));
}
///
version(mir_test)
unittest
{
    ///
    static struct Greeks
    {
        @Derivative("spot")
        double delta;
        @Derivative("spot", "spot")
        double gamma;
        @Minus @Derivative("time", "spot") 
        double charm;
    }

    auto greeks = Greeks(2, 3, 4);

    auto dspot = derivativeOf!"spot"(&greeks);

    assert(greeks.delta is dspot.getFunctionValue);
    assert(greeks.gamma is dspot.getDerivative!(["spot"]));
    assert(greeks.charm is -dspot.getDerivative!(["time"]));
}

///
version(mir_test)
unittest
{
    import mir.math;

    // Test Const
    static assert(Dependencies!Const == [].DependsOn);
    auto c = 5.Const;
    static assert(c.getDerivative!(["any"]) == 0);
    assert(c.getFunctionValue == 5);

    // Test Var
    auto spot = 7.Var!"spot";
    static assert(Dependencies!(Var!"spot") == ["spot"].DependsOn);
    static assert(spot.getDerivative!(["spot"]) == 1);
    static assert(spot.getDerivative!(["other"]) == 0);
    assert(spot.getFunctionValue == 7);

    // Test integer power and exponent
    auto f1 = exp(3.Const * spot.powi!(-2));
    static assert(Dependencies!(typeof(f1)) == ["spot"].DependsOn);
    assert(f1.getFunctionValue == mir.math.exp(3 * 7.0 ^^ -2));
    assert(f1.getDerivative!(["spot"]) == 3 * -2 * 7.0 ^^ -3 * mir.math.exp(3 * 7.0 ^^ -2));
    // Test DerivativeOf
    assert(f1.derivativeOf!"spot".getFunctionValue == f1.getDerivative!(["spot"]));
    // Test product and sum
    assert(f1.derivativeOf!"spot".derivativeOf!"spot".getFunctionValue.approxEqual((3 * (-2 * 7.0 ^^ -3)) ^^ 2 * mir.math.exp(3 * 7.0 ^^ -2) + 3 * (6 * 7.0 ^^ -4)* mir.math.exp(3 * 7.0 ^^ -2)));

    auto strike = 9.Var!"strike";

    auto f2 = strike * f1 + strike;
    assert(f2.getDerivative!(["strike"]).approxEqual(1 + f1.getFunctionValue));
    // Test log
    assert(f2.log.getFunctionValue == mir.math.log(f2.getFunctionValue));
    assert(f2.log.getDerivative!(["strike"]) == getFunctionValue(f2.powi!(-1) * (1.Const + f1)));
    assert(f2.sqrt.getFunctionValue == mir.math.sqrt(f2.getFunctionValue));
    assert(f2.sqrt.getDerivative!(["strike"]) == getFunctionValue(f2.sqrt.powi!(-1)  * 0.5.Const * (1.Const + f1)));

    // Compose
    auto barrier = 13.Var!"barrier";
    auto fc = barrier.powi!2 / strike;
    auto f3 = f2.composeAt!"strike"(fc);
    assert(f3.getFunctionValue == f2.getFunctionValue);
    assert(f3.getDerivative!(["vol"]) == f2.getDerivative!(["vol"]));
    assert(f3.getDerivative!(["strike"]) == f2.getDerivative!(["strike"]) * fc.getDerivative!(["strike"]));
    assert(f3.getDerivative!(["barrier"]) == f2.getDerivative!(["strike"]) * fc.getDerivative!(["barrier"]));
    assert(getDerivative!(["barrier"])(f3 + barrier) == f2.getDerivative!(["strike"]) * fc.getDerivative!(["barrier"]) + 1);
    assert(f3.getDerivative!(["strike", "barrier"]) == 
        f2.getDerivative!(["strike", "strike"]) * fc.getDerivative!(["strike"]) * fc.getDerivative!(["barrier"]) +
        f2.getDerivative!(["strike"]) * fc.getDerivative!(["strike", "barrier"]));

    /// normalDistribution
    import mir.math.func.normal: constantNormalCDF = normalCDF, normalPDF;
    assert(barrier.powi!2.normalCDF.getFunctionValue == constantNormalCDF(13.0 ^^ 2));
    assert(barrier.powi!2.normalCDF.getDerivative!(["barrier"]) == normalPDF(13.0 ^^ 2) * (2 * 13));
}
    
version(mir_test_deprecated)
unittest
{
    import mir.math.func.normal: constantNormalCDF = normalCDF, normalPDF;
    assert(barrier.powi!2.normalDistribution.getFunctionValue == constantNormalCDF(13.0 ^^ 2));
    assert(barrier.powi!2.normalDistribution.getDerivative!(["barrier"]) == normalPDF(13.0 ^^ 2) * (2 * 13));
}

import mir.algorithm.iteration: uniq;
import mir.array.allocation;
import mir.math.common;
import mir.ndslice.sorting: sort;
import std.traits: Unqual, getUDAs, hasUDA, isPointer, PointerTarget;

@optmath:

/++
+/
mixin template ediffOperators()
{
const:
    auto opBinary(string op, R)(const R rhs)
        if ((op == "+" || op == "-") && is(R == struct))
    {
        return Sum!(Unqual!(typeof(this)), R, op == "-")(this, rhs);
    }

    auto opBinary(string op, R)(const R rhs)
        if (op == "*" && is(R == struct))
    {
        alias L = Unqual!(typeof(this));
        static if  (is(R == Const) && is(L == Const))
        {
            return Const(this.value * rhs.value);
        }
        else
        static if (is(R == Const) && is(L == Powi!(_power, _LT), size_t _power, _LT))
        {
            return L(this.value, this.coefficient * rhs.value);
        }
        else
        static if (is(L == Const) && is(R == Powi!(_power, _RT), size_t _power, _RT))
        {
            return R(rhs.value, rhs.coefficient * this.value);
        }
        else
        {
            return Product!(L, R)(this, rhs);
        }
    }

    auto opBinaryRight(string op, L)(const L lhs)
        if ((op == "+" || op == "*") && is(L == struct))
    {
        return this.opBinary!op(lhs);
    }

    auto opBinaryRight(string op, L)(const L lhs)
        if ((op == "-") && is(L == struct))
    {
        return Sum!(L, Unqual!(typeof(this)), true)(lhs, this);
    }

    auto opBinary(string op, R)(const R rhs)
        if (op == "/" && is(R == struct))
    {
        alias L = Unqual!(typeof(this));
        alias A = L;
        alias B = R;
        alias a = this;
        alias b = rhs;
        mixin _div;
        return result;
    }

    auto opBinaryRight(string op, L)(const L lhs)
        if ((op == "/") && is(L == struct))
    {
        alias R = Unqual!(typeof(this));
        alias A = L;
        alias B = R;
        alias a = lhs;
        alias b = this;
        mixin _div;
        return result;
    }
}

private mixin template _div()
{
    // A / B
    static if (is(A == Const) && is(B == Const))
        auto result = Const(a.value / b.value);
    else
    static if (is(A == Const))
        auto result = Powi!(-1, B)(b, a.value);
    else
    static if (is(B == Const))
        auto result = Const(1.0 / b.value) * a;
    else
        auto result = b.powi!(-1) * a;
}

private template Sum(A, B, bool diff = false)
{

    @(Dependencies!A ~ Dependencies!B)
    struct Sum
    {
        A a;
        B b;

    @optmath:

        template getDerivative(string[] variables, bool strict = true)
        {
            static if (Dependencies!(typeof(this)).containsAll(variables))
                auto getDerivative() const @property
                {
                    double ret = 0;
                    static if (Dependencies!A.containsAll(variables))
                        ret = a.getDerivative!(variables, strict);
                    static if (Dependencies!B.containsAll(variables))
                    {
                        static if (diff)
                            ret -= b.getDerivative!(variables, strict);
                        else
                            ret += b.getDerivative!(variables, strict);
                    }
                    return ret;
                }
            else
                enum double getDerivative = 0;
        }

        mixin ediffOperators;
    }
}

private template Product(A, B)
{
    @(Dependencies!A ~ Dependencies!B)
    struct Product
    {
        A a;
        B b;

        template getDerivative(string[] variables, bool strict = true)
        {
        @optmath:
            static if (Dependencies!(typeof(this)).containsAll(variables))
                auto getDerivative() const @property
                {
                    static if (variables.length == 0)
                    {
                        return a.getFunctionValue!strict * b.getFunctionValue!strict;
                    }
                    else
                    {
                        enum variable = variables[0];
                        static if (!Dependencies!A.contains(variable))
                            return (a * b.derivativeOf!variable).getDerivative!(variables[1 .. $], strict);
                        else
                        static if (!Dependencies!B.contains(variable))
                            return (a.derivativeOf!variable * b).getDerivative!(variables[1 .. $], strict);
                        else
                            return (a * b.derivativeOf!variable + a.derivativeOf!variable * b).getDerivative!(variables[1 .. $], strict);
                    }
                }
            else
                enum double getDerivative = 0;
        }

        mixin ediffOperators;
    }
}

/++
User defined attribute that should applied on struct definition of a user-defined expression function.
+/
struct DependsOn
{
    ///
    string[] variables;

@safe pure nothrow:
    ///
    auto contains(string variable) const @nogc
    {
        foreach (v; variables)
            if (v == variable)
                return true;
        return false;
    }

    ///
    auto containsAll(string[] variables) const @nogc
    {
        foreach (v; variables)
            if (!contains(v))
                return false;
        return true;
    }

    ///
    auto containsAny(string[] variables) const @nogc
    {
        foreach (v; variables)
            if (contains(v))
                return true;
        return false;
    }

    /// Set union
    DependsOn opBinary(string op : "~")(DependsOn rhs)
    {
        return (this.variables ~ rhs.variables).sort.uniq.array.DependsOn;
    }
}

/++
Fetchs a set of variables the expression is depends on.
    First, it checks if the expression has $(LREF DependsOn) UDA
    ; otherwise, iterates over members with $(LREF Derivative) UDA and collects variable names.
+/
template Dependencies(T)
{
    static if (isPointer!T)
        enum Dependencies = Dependencies!(PointerTarget!T);
    else
    static if (hasUDA!(T, DependsOn))
        enum DependsOn Dependencies = getUDAs!(T, DependsOn)[0];
    else
    {
        enum DependsOn Dependencies = () {
            string[] variables;
            static foreach (member; __traits(allMembers, T))
            {
                static if (hasUDA!(__traits(getMember, T, member), Derivative))
                {
                    variables ~= getUDAs!(__traits(getMember, T, member), Derivative)[0].variables;
                }
            }
            return variables.sort.uniq.array.DependsOn;
        } ();
    }
}

/++
User defined attribute that should applied on a struct member definition of a user-defined set of derivatives.
    The attribute holds an unordered set with duplicates of variables names to reflect which partial derivative this member contains.
+/
struct Derivative
{
    ///
    string[] variables;

@trusted pure nothrow @nogc:

    ///
    this(string[] variables...)
    {
        this.variables = variables.sort;
    }
}

/++
User-defined attribute that can be applied on struct member definition along with $(LREF Derivative) to denote
    that the member holds a negative value of the partial derivative.
    This attribute is useful for financial code where verbal definitions may denote negative partial derivatives.
+/
enum Minus;

/++
Evaluates function value. It is shortcut for $(LREF getDerivative) of zero order.
Params:
    strict = The parameter is used when the expression can't evaluate the function. If true, prints error at compile-time; otherwise, `getFunctionValues` returns NaN.
+/
alias getFunctionValue(bool strict = true) = getDerivative!(string[].init, strict);

/++
Evaluates partial derivative for user-defined compiletime set of variables.
    First, it checks if the expression has `.getDerivative` methods and uses it,
    otherwise iterates over members with $(LREF Derivative) UDA and tries to find a member that holds the required partial derivative.
Params:
    variables = array that denotes partial derivative
    strict = The parameter is used when the expression can't evaluate the derivative. If true, prints error at compile-time; otherwise, `getDerivative` returns NaN.
+/
template getDerivative(string[] variables, bool strict = true)
{
    import mir.ndslice.topology: pairwise;
    import mir.algorithm.iteration: all;

@optmath:

    static if (variables.length == 0 || variables.pairwise!"a <= b".all)
    {
        auto ref getDerivative(T)(auto ref T value)
        {
            static if (__traits(hasMember, T, "getDerivative"))
                return value.getDerivative!(variables, strict);
            else
            {
                import std.meta: anySatisfy;

                static if (isPointer!T)
                    alias V = PointerTarget!T;
                else
                    alias V = T;
                template hasDerivative(string member)
                {
                    static if (hasUDA!(__traits(getMember, V, member), Derivative))
                        enum hasDerivative = variables == getUDAs!(__traits(getMember, V, member), Derivative)[0].variables;
                    else
                        enum hasDerivative = false;
                }
                static if (anySatisfy!(hasDerivative, __traits(allMembers, V)))
                {
                    static foreach (member; __traits(allMembers, V))
                    {
                        static if (hasDerivative!member)
                        {
                            static if (hasUDA!(__traits(getMember, V, member), Minus))
                                return -__traits(getMember, value, member);
                            else
                                return __traits(getMember, value, member);
                        }
                    }
                }
                else
                static if (strict)
                {
                    static assert(0, Unqual!V.stringof ~ "'_" ~ variables.stringof ~ " not found");
                }
                else
                {
                    return double.nan;
                }
            }
        }
    }
    else
    {
        import mir.ndslice.sorting: sort;
        alias getDerivative = .getDerivative!(variables.sort, strict);
    }
}

/++
Evaluates partial derivatives and function value, if any, for a user-provided set of partial derivatives.
    The derivative set can be defined with $(LREF Derivative) and $(LREF Minus) UDAs.
Params:
    D = type of the requested set of partial derivatives
    strict = The parameter is used when the expression can't evaluate the derivative. If true, prints error at compile-time; otherwise, the corresponding member is set to NaN.
    derivatives = a structure that holds set of partial derivatives (optional)
    expression = expression
+/
void setDerivatives(bool strict = true, D, E)(scope ref D derivatives, E expression)
{
    static if (__traits(hasMember, D, "setDerivatives"))
        return derivatives.setDerivatives!strict(expression);
    else
    {
        import std.traits: getUDAs, hasUDA, isPointer, PointerTarget;

        static foreach (member; __traits(allMembers, D))
        {
            static if (hasUDA!(__traits(getMember, D, member), Derivative))
            {
                static if (hasUDA!(__traits(getMember, derivatives, member), Minus))
                    __traits(getMember, derivatives, member) = -expression.getDerivative!(getUDAs!(__traits(getMember, derivatives, member), Derivative)[0].variables, strict);
                else
                    __traits(getMember, derivatives, member) = expression.getDerivative!(getUDAs!(__traits(getMember, derivatives, member), Derivative)[0].variables, strict);
            }
        }
    }
}

/// ditto
template setDerivatives(D, bool strict = true)
{
    ///
    D setDerivatives(E)(E expression)
    {
        D ret;
        .setDerivatives!strict(ret, expression);
        return ret;
    }
}

private auto removeVariable(DependsOn variables, string variable)
{
    string[] ret;
    foreach (v; variables.variables)
        if (v != variable)
            ret ~= v;
    return ret.DependsOn;
}

private template ComposeAt(F, G, string position)
    if (Dependencies!F.contains(position))
{
    @(Dependencies!F.removeVariable(position) ~ Dependencies!G)
    struct ComposeAt
    {
        ///
        F f;
        ///
        G g;

        ///
        template getDerivative(string[] variables, bool strict = true)
        {
            static if (Dependencies!(typeof(this)).containsAll(variables))
                ///
                auto ref getDerivative() const @property
                {
                    static if (!Dependencies!G.containsAny(variables))
                        return f.getDerivative!(variables, strict);
                    else
                    {
                        static if (Dependencies!F.contains(variables[0]) && variables[0] != position)
                            auto a = f.derivativeOf!(variables[0]).composeAt!position(g).getDerivative!(variables[1 .. $], strict);
                        else
                            enum a = 0;
                        static if (Dependencies!G.contains(variables[0]))
                            auto b = (f.derivativeOf!position.composeAt!position(g) * g.derivativeOf!(variables[0])).getDerivative!(variables[1 .. $], strict);
                        else
                            enum b = 0;
                        return a + b;
                    }
                }
            else
                enum double getDerivative = 0;
        }

        mixin ediffOperators;
    }
}

/++
Given a compiletime variable name `v` and two expressions `F(v, U)` and `G(Y)`,
    constructs a composition `F ∘ G (U, Y)` as `v = G`.

Params:
    position = name of the variable to compose functions at.
+/
template composeAt(string position)
{
    /++
    Params:
        f = F expression
        g = G expression
    +/
    auto composeAt(F, G)(const F f, const G g)
    {
        return ComposeAt!(F, G, position)(f, g);
    }
}

private template DerivativeOf(T, string variable)
{
    @Dependencies!T
    struct DerivativeOf
    {
        // Underlying expression
        T underlying;

    @optmath:

        ///
        auto ref getDerivative(string[] variables, bool strict = true)() const @property
        {
            return underlying.getDerivative!(variable ~ variables, strict);
        }

        mixin ediffOperators;
    }
}

/++
Constructs a partial derivative of one order.
    The function can be applied in any stage any number of times.
    The function does NOT evaluate the expression.
+/
template derivativeOf(string variable)
{
@optmath:

    /++
    Params:
        value = expression
    +/
    auto derivativeOf(T)(const T value) @property
    {
        static if (isPointer!T)
            return DerivativeOf!(const(PointerTarget!T)*, variable)(value);
        else
            return DerivativeOf!(T, variable)(value);
    }
}

/++
A double precision constant with an immidiate value
+/
@DependsOn()
struct Const
{
    /// Immidiate value
    double value;

    template getDerivative(string[] variables, bool strict = true)
    {
        static if (variables.length == 0)
            alias getDerivative = value;
        else
            enum double getDerivative = 0;
    }

    mixin ediffOperators;
}

/++
A double precision named variable with an immidiate value
+/
template Var(string name)
{
    ///
    @DependsOn([name])
    struct Var
    {
        /// Immidiate value
        double value;

        template getDerivative(string[] variables, bool strict = true)
        {
            static if (variables.length == 0)
                alias getDerivative = value;
            else
                enum double getDerivative = variables == [name];
        }

        mixin ediffOperators;
    }
}

private template Powi(int power, T)
    if (power)
{
    @Dependencies!T
    struct Powi
    {
        T value;
        double coefficient = 1;

        template getDerivative(string[] variables, bool strict = true)
        {
        @optmath:
            static if (Dependencies!(typeof(this)).containsAll(variables))
                auto getDerivative() const @property
                {
                    static if (variables.length == 0)
                    {
                        static if (power == 0)
                            return coefficient;
                        else
                        static if (power == 1)
                            return coefficient * value.getFunctionValue!strict;
                        else
                        static if (power == 2)
                            return coefficient * value.getFunctionValue!strict ^^ 2;
                        else
                        static if (power == -1)
                            return coefficient / value.getFunctionValue!strict;
                        else
                        static if (power == -2)
                            return coefficient / value.getFunctionValue!strict ^^ 2;
                        else
                            return coefficient * mir.math.common.powi(value.getFunctionValue!strict, power);
                    }
                    else
                    {
                        static if (power == 1)
                            auto v = coefficient.Const;
                        else
                            auto v = Powi!(power - 1, T)(value, coefficient * power);
                        static if (is(T == Var!(variables[0])))
                            return v.getDerivative!(variables[1 .. $], strict);
                        else
                            return (v * value.derivativeOf!(variables[0])).getDerivative!(variables[1 .. $], strict);
                    }
                }
            else
                enum double getDerivative = 0;
        }

        mixin ediffOperators;
    }
}

/++
Constructs of the expression raised to the specified (positive or negative) compile-time integral power.

Params:
    power = integral power (compile-time)
    value = expression
+/
auto powi(int power, T)(const T value)
    if (is(T == struct))
{
    static if (power == 0)
        return 1.Const;
    else
        return Powi!(power, T)(value);
}

private template Exp(T)
{
    @Dependencies!T
    struct Exp
    {
        /// Power function
        T power;

        template getDerivative(string[] variables, bool strict = true)
        {
        @optmath:
            static if (Dependencies!(typeof(this)).containsAll(variables))
                auto getDerivative() const @property
                {
                    static if (variables.length == 0)
                        return mir.math.common.exp(power.getFunctionValue!strict);
                    else
                        return (this * power.derivativeOf!(variables[0])).getDerivative!(variables[1 .. $], strict);
                }
            else
                enum double getDerivative = 0;
        }

        mixin ediffOperators;
    }
}

/++
Constructs the natural exponent of the expression.

Params:
    power = expression
+/
auto exp(T)(const T power)
    if (is(T == struct))
{
    return Exp!T(power);
}

private template Log(T)
{
    @Dependencies!T
    struct Log
    {
        T value;

        template getDerivative(string[] variables, bool strict = true)
        {
        @optmath:
            static if (Dependencies!(typeof(this)).containsAll(variables))
                auto getDerivative() const @property
                {
                    static if (variables.length == 0)
                        return mir.math.common.log(value.getFunctionValue!strict);
                    else
                        return (value.derivativeOf!(variables[0]) / value).getDerivative!(variables[1 .. $], strict);
                }
            else
                enum double getDerivative = 0;
        }

        mixin ediffOperators;
    }
}

/++
Constructs the natural logarithm of the expression.

Params:
    value = expression
+/
auto log(T)(const T value)
    if (is(T == struct))
{
    return Log!T(value);
}

private template Sqrt(T)
{
    @Dependencies!T
    struct Sqrt
    {
        T value;

        template getDerivative(string[] variables, bool strict = true)
        {
        @optmath:
            static if (Dependencies!(typeof(this)).containsAll(variables))
                auto getDerivative() const @property
                {
                    static if (variables.length == 0)
                        return mir.math.common.sqrt(value.getFunctionValue!strict);
                    else
                        return (Powi!(-1, Sqrt!T)(this, 0.5) * value.derivativeOf!(variables[0])).getDerivative!(variables[1 .. $], strict);
                }
            else
                enum double getDerivative = 0;
        }

        mixin ediffOperators;
    }
}

/++
Constructs the square root of the expression.

Params:
    value = expression
+/
auto sqrt(T)(const T value)
    if (is(T == struct))
{
    return Sqrt!T(value);
}

private template NormalCDF(T)
{
    @Dependencies!T
    struct NormalCDF
    {
        /// Square root argument function
        T value;

        template getDerivative(string[] variables, bool strict = true)
        {
        @optmath:
            static if (Dependencies!(typeof(this)).containsAll(variables))
                auto getDerivative() const @property
                {
                    import mir.math.func.normal: normalCDF, SQRT2PIINV;
                    static if (variables.length == 0)
                        return normalCDF(value.getFunctionValue!strict);
                    else
                        return (SQRT2PIINV.Const * Powi!(2, T)(value, -0.5).exp * value.derivativeOf!(variables[0])).getDerivative!(variables[1 .. $], strict);
                }
            else
                enum double getDerivative = 0;
        }

        mixin ediffOperators;
    }
}

/++
Constructs the cumulative normal distribution function of the expression

Params:
    value = expression
+/
deprecated("normalDistribution renamed, use normalCDF instead")
auto normalDistribution(T)(const T value)
    if (is(T == struct))
{
    return NormalCDF!T(value);
}

/++
Constructs the cumulative normal distribution function of the expression

Params:
    value = expression
+/
auto normalCDF(T)(const T value)
    if (is(T == struct))
{
    return NormalCDF!T(value);
}
