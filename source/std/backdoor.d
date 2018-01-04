module std.backdoor;

auto ref emplaceRef(UT, Args...)(ref UT to, auto ref Args args)
{
    static import std.conv;
    return std.conv.emplaceRef(to, args);
}

auto ref emplaceRef(T, UT, Args...)(ref UT to, auto ref Args args)
{
    static import std.conv;
    return std.conv.emplaceRef!(T, UT)(to, args);
}
