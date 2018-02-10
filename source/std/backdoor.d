///
module std.backdoor;

template emplaceRef(T...)
    if (T.length <= 1)
{
    ///
    auto ref emplaceRef(UT, Args...)(ref UT to, auto ref Args args)
    {
        static import std.conv;
        return std.conv.emplaceRef!(T, UT)(to, args);
    }
}
