/*
 *  Copyright (C) 2004-2005 by Digital Mars, www.digitalmars.com
 *  Written by Walter Bright
 *
 *  This software is provided 'as-is', without any express or implied
 *  warranty. In no event will the authors be held liable for any damages
 *  arising from the use of this software.
 *
 *  Permission is granted to anyone to use this software for any purpose,
 *  including commercial applications, and to alter it and redistribute it
 *  freely, in both source and binary form, subject to the following
 *  restrictions:
 *
 *  o  The origin of this software must not be misrepresented; you must not
 *     claim that you wrote the original software. If you use this software
 *     in a product, an acknowledgment in the product documentation would be
 *     appreciated but is not required.
 *  o  Altered source versions must be plainly marked as such, and must not
 *     be misrepresented as being the original software.
 *  o  This notice may not be removed or altered from any source
 *     distribution.
 */

module std.typeinfo.ti_Adouble;

private import std.typeinfo.ti_double;

// double[]

class TypeInfo_Ad : TypeInfo
{
    string toString() { return "double[]"; }

    hash_t getHash(in void *p)
    {	double[] s = *cast(double[]*)p;
	size_t len = s.length;
	auto str = s.ptr;
	hash_t hash = 0;

	while (len)
	{
	    hash *= 9;
	    hash += (cast(uint *)str)[0];
	    hash += (cast(uint *)str)[1];
	    str++;
	    len--;
	}

	return hash;
    }

    int equals(in void *p1, in void *p2)
    {
	double[] s1 = *cast(double[]*)p1;
	double[] s2 = *cast(double[]*)p2;
	size_t len = s1.length;

	if (len != s2.length)
	    return 0;
	for (size_t u = 0; u < len; u++)
	{
	    int c = TypeInfo_d._equals(s1[u], s2[u]);
	    if (c == 0)
		return 0;
	}
	return 1;
    }

    int compare(in void *p1, in void *p2)
    {
	double[] s1 = *cast(double[]*)p1;
	double[] s2 = *cast(double[]*)p2;
	size_t len = s1.length;

	if (s2.length < len)
	    len = s2.length;
	for (size_t u = 0; u < len; u++)
	{
	    int c = TypeInfo_d._compare(s1[u], s2[u]);
	    if (c)
		return c;
	}
	return cast(int)s1.length - cast(int)s2.length;
    }

    size_t tsize()
    {
	return (double[]).sizeof;
    }

    uint flags()
    {
	return 1;
    }

    TypeInfo next()
    {
	return typeid(double);
    }
}

// idouble[]

class TypeInfo_Ap : TypeInfo_Ad
{
    string toString() { return "idouble[]"; }

    TypeInfo next()
    {
	return typeid(idouble);
    }
}
