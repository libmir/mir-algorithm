// Self contained generic small string implementaton.
#include <cstring>
#include <cstddef>
#include <ostream>
#include <stdexcept>
#include <string_view>
#include <string>

namespace mir
{
    template <unsigned int maxLength>                                 
    struct SmallString
    {
        SmallString() noexcept {}

        SmallString(std::string_view str)
        {
            auto length = str.size();
            if (length > sizeof(SmallString))
                throw std::range_error("Cannot create SmallString: input string exceeds maximum allowed length.");
            std::memcpy(_data, str.data(), length);
        }

        SmallString(const std::string& str) : SmallString((std::string_view)str) {}
        SmallString(const char* str) : SmallString(std::string_view(str)) {}
        std::string_view str() const noexcept { return std::string_view(_data, _data[maxLength] ? maxLength : std::strlen(_data)); }
        operator std::string_view() const noexcept { return str(); }
        operator bool() const noexcept { return _data[0] != 0; }
        bool operator !() const noexcept { return _data[0] == 0; }
        bool operator==(const SmallString& rhs) const noexcept { return memcmp(_data, rhs._data, maxLength) == 0; }
        bool operator!=(const SmallString& rhs) const noexcept { return memcmp(_data, rhs._data, maxLength) != 0; }
        bool operator<(const SmallString& rhs) const noexcept { return memcmp(_data, rhs._data, maxLength) < 0; }
        bool operator<=(const SmallString& rhs) const noexcept { return memcmp(_data, rhs._data, maxLength) <= 0; }
        bool operator>(const SmallString& rhs) const noexcept { return memcmp(_data, rhs._data, maxLength) > 0; }
        bool operator>=(const SmallString& rhs) const noexcept { return memcmp(_data, rhs._data, maxLength) >= 0; }
    private:
        char _data[maxLength] = {0};
    };
}

namespace std
{
    template<unsigned int maxlength>
    std::ostream &operator<<(std::ostream &os, const mir::SmallString<maxlength>& ss)
    {
        return os << ss.str();
    }

    template <unsigned int maxLength>                                 
    struct hash<mir::SmallString<maxLength>>
    {
        inline size_t operator()(const mir::SmallString<maxLength>& s) const noexcept
        {
            return std::hash<string_view>()(s.str());
        }
    };
}
