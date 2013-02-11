// Written in the D programming language.
/**
   std.units is a D implementation of Boost.Units library.
   
   Authors:    Arlen Avakian
   Copyright:  Copyright (c) 2012, Arlen Avakian
   License:    $(WEB boost.org/LICENSE_1_0.txt, Boost License 1.0)
   Source:     $(PHOBOSSRC std/_units.d)
   Acknowledgements: Thanks to Matthias Christian Schabel, Steven Watanabe, and all the people who have contributed to Boost.units.

   Synopsis:
   ---
   import std.units, std.complex, std.stdio;

   Quantity!(si.Energy) work(Quantity!(si.Force) F, Quantity!(si.Length) dx)
   {
       return F * dx;
   }

   void main()
   {
       Quantity!(si.Force)  F  = 2.0 * si.newton;
       Quantity!(si.Length) dx = 2.0 * si.meter;
       Quantity!(si.Energy) E  = work(F, dx);
       writefln("F  = %s\ndx = %s\nE  = %s\n", F, dx, E);

       alias Complex!double ComplexType;

       Quantity!(si.ElectricPotential, ComplexType) v = complex(12.5, 0) * si.volts;
       Quantity!(si.Current, ComplexType)           i = complex(3, 4) * si.amperes;
       Quantity!(si.Resistance, ComplexType)        z = complex(1.5, -2) * si.ohms;
       writefln("V   = %s\nI   = %s\nZ   = %s\nI*Z = %s\nI*Z == V? %s",
                v, i, z, i*z, i*z == v);
   }
   ---
   <pre class=console>
   F  = 2 N
   dx = 2 m
   E  = 4 J

   V   = 12.5+0i V
   I   = 3+4i A
   Z   = 1.5-2i Ohm
   I*Z = 12.5+0i V
   I*Z == V? true
   </pre>

*/
module std.units;

import std.rational;

import std.stdio;
import std.conv      : to;
import std.math      : abs, PI, approxEqual;
import std.format    : formattedWrite, FormatSpec;
import std.algorithm : map, filter, uniq, stdsort = sort, reduce, swap, isSorted, canFind, copy, cmp;
import std.array     : appender;
import std.range     : walkLength, isInputRange, ElementType, take, sequence, iota, isInfinite, isRandomAccessRange, hasLength, hasSlicing, front, popFront, drop, retro;
import std.typetuple : TypeTuple;
import std.typecons  : Flag, Tuple;
import std.exception : enforce;
import std.traits    : isNumeric, isIntegral, EnumMembers, isIterable, isNarrowString, ForeachType;
import std.string    : xformat;

/*
  Making std.array work at compile-time.
*/
private ForeachType!Range[] array(Range)(Range r)
if (isIterable!Range && !isNarrowString!Range)
{
    auto a = appender!(ForeachType!Range[])();
    foreach (e; r)
    {
        a.put(e);
    }
    // return a.data; // D_BUG_1  http://stackoverflow.com/q/14418475/554075
    return a.data.length ? a.data : [];
}

/// QQ be thy name.
public alias Rational!long QQ;

private string rawString(QQ r)
{
    return xformat("QQ(%s,%s)", r.num, r.den);
}

unittest
{
    static assert(rawString(QQ(-2,3)) == "QQ(-2,3)");
    static assert(mixin(rawString(QQ(2,4))) == QQ(1,2));
}

// base_dimension.hpp
private alias string BaseDimension;

/**
  Defines a base dimension.

  Examples:
  ---
  alias baseDimension!"length" lengthBaseDimension;
  static assert(lengthBaseDimension == "length_bd()");
  ---
*/
public template baseDimension(string name)
{
    static assert(name.length > 0, "Expected a string of length 1 or greater.");
    enum BaseDimension baseDimension = name ~ "_bd()";
}

/**
   Check to see if $(B T) is a BaseDimension.
*/
public template isBaseDimension(T)
{
    enum bool isBaseDimension = is(T == BaseDimension);
}

version (unittest)
{
    alias baseDimension!"alpha"   alphaBaseDimension;
    alias baseDimension!"beta"    betaBaseDimension;
    alias baseDimension!"gamma"   gammaBaseDimension;
    alias baseDimension!"delta"   deltaBaseDimension;
    alias baseDimension!"epsilon" epsilonBaseDimension;
    alias baseDimension!"zeta"    zetaBaseDimension;
    alias baseDimension!"eta"     etaBaseDimension;
    alias baseDimension!"theta"   thetaBaseDimension;
    alias baseDimension!"iota"    iotaBaseDimension;

    alias alphaBaseDimension   _bd1;
    alias betaBaseDimension    _bd2;
    alias gammaBaseDimension   _bd3;
    alias deltaBaseDimension   _bd4;
    alias epsilonBaseDimension _bd5;
    alias zetaBaseDimension    _bd6;
    alias etaBaseDimension     _bd7;
    alias thetaBaseDimension   _bd8;
    alias iotaBaseDimension    _bd9;
}

unittest
{
    static assert(alphaBaseDimension == "alpha_bd()");
    static assert(isBaseDimension!(typeof(betaBaseDimension)));
}

/*
   A fundamental dimension is a pair of a base dimension and a rational exponent.
*/
// dim.hpp
private struct FundamentalDimension
{
    BaseDimension baseDimension;   // tag_type
    QQ exponent;                   // value_type

    FundamentalDimension opBinary(string op)(FundamentalDimension other)
    @safe pure if (op == "+" || op == "-")
    {
        assert(this.baseDimension == other.baseDimension);
        return FundamentalDimension(
            this.baseDimension,
            mixin("this.exponent" ~ op ~ "other.exponent"));
    }

    FundamentalDimension opBinary(string op)(QQ r) @safe pure
    if (op == "*" || op == "/")
    {
        return FundamentalDimension(
            this.baseDimension,
            mixin("this.exponent" ~ op ~ "r"));
    }

    FundamentalDimension opBinaryRight(string op)(QQ r) @safe pure
    if (op == "*" || op == "/")
    {
        return this.opBinary!(op)(r);
    }

    FundamentalDimension opUnary(string op)() @safe pure if (op == "-")
    {
        return FundamentalDimension(this.baseDimension, -this.exponent);
    }

    // detail/dim_impl.hpp
    int opCmp(FundamentalDimension other) @safe const pure nothrow
    {
        if (this.baseDimension == other.baseDimension)
        {
            return 0;
        }
        return this.baseDimension < other.baseDimension ? -1 : 1;
    }

    bool opEquals(FundamentalDimension other) @safe const pure nothrow
    {
        return this.baseDimension == other.baseDimension;
    }

    void toString(scope void delegate(const(char)[]) sink) const
    {
        formattedWrite(sink, baseDimension);
        formattedWrite(sink, "^%s", exponent);
    }
}

version (unittest)
{
    alias FundamentalDimension FunDim;

    enum FunDim funDim1 = FunDim(alphaBaseDimension, QQ( 2));
    enum FunDim funDim2 = FunDim(betaBaseDimension,  QQ( 3));
    enum FunDim funDim3 = FunDim(alphaBaseDimension, QQ( 4));
    enum FunDim funDim4 = FunDim(betaBaseDimension,  QQ(-2));
}

unittest
{
    enum r1 = funDim1 + funDim1;
    static assert(r1.baseDimension == alphaBaseDimension);
    static assert(r1.exponent == QQ(4));
    enum r2 = funDim1 + funDim3;
    static assert(r2.baseDimension == alphaBaseDimension);
    static assert(r2.exponent == QQ(6));

    enum r3 = funDim1 - funDim1;
    static assert(r3.baseDimension == alphaBaseDimension);
    static assert(r3.exponent == QQ(0));
    enum r4 = funDim1 - funDim3;
    static assert(r4.baseDimension == alphaBaseDimension);
    static assert(r4.exponent == QQ(-2));

    enum r5 = funDim2 * QQ(2);
    static assert(r5.baseDimension == betaBaseDimension);
    static assert(r5.exponent == QQ(6));

    enum r6 = funDim2 / QQ(2);
    static assert(r6.baseDimension == betaBaseDimension);
    static assert(r6.exponent == QQ(3,2));

    enum r7 = -funDim3;
    static assert(r7.baseDimension == alphaBaseDimension);
    static assert(r7.exponent == QQ(-4));

    static assert(funDim1 == funDim3);
    static assert(funDim1 != funDim2);
    static assert(funDim3 != funDim2);

    static assert(funDim1 < funDim2);
    static assert(funDim3 < funDim2);

    static assert(funDim2 > funDim1);
    static assert(funDim2 > funDim3);
}

private string rawString(FundamentalDimension fd)
{
    return xformat(`FundamentalDimension("%s",%s)`,
                   fd.baseDimension, rawString(fd.exponent));
}

unittest
{
    static assert(rawString(funDim1) == 
                  `FundamentalDimension("alpha_bd()",QQ(2,1))`);
    static assert(mixin(rawString(funDim1)) == funDim1);
}

// detail/dim_impl.hpp
private template isFundamentalDimension(T)
{
    enum bool isFundamentalDimension = is(T == FundamentalDimension);
}

private struct Dimension
{
    FundamentalDimension[] fd;

    @property static Dimension dimensionless()
    {
        return Dimension([]);
    }

    this(FundamentalDimension[] xs)
    {
        assert(xs.stdsort.uniq.walkLength == xs.length,
               "Expected a list of unique fundemental dimensions.");
        this.fd = xs.stdsort.array;
    }

    Dimension opBinary(string op)(QQ ex) if (op == "^")
    {
        return Dimension(this.fd.map!(a => a * ex).array);
    }

    Dimension opBinary(string op)(QQ ex) if (op == "^^")
    {
        return Dimension(this.fd.map!(a => a / ex).array);
    }

    Dimension opBinary(string op)(Dimension other) @safe pure nothrow
    if (op == "+" || op == "-")
    {
        assert(this == other);
        return this;
    }

    Dimension opBinary(string op)(Dimension other) if (op == "*")
    {
        return Dimension(merge(this.fd, other.fd));
    }

    Dimension opBinary(string op)(Dimension other) if (op == "/")
    {
        return Dimension(merge(this.fd, other.fd.inverse));
    }

    FundamentalDimension opIndex(size_t i) @safe pure nothrow
    {
        return this.fd[i];
    }

    auto opSlice(size_t i, size_t j) @safe pure nothrow
    {
        return this.fd[i..j];
    }

    @property auto length() @safe pure nothrow
    {
        return fd.length;
    }

    void toString(scope void delegate(const(char)[]) sink) const
    {
        formattedWrite(sink, "{%(%s, %)}", this.fd);
    }
}

/**
   Given one or more $(B pairs) of base dimensions and exponents, this template
   creates a composite dimension, or simply put, a dimension.  The resulting
   dimension is in the form of a reduced dimension.  The exponents can be either
   of type integer or Rational.

   Examples:
   ---
   alias dimension!(lengthBaseDimension, QQ(2)) areaDimension;
   alias dimension!(massBaseDimension,    1,
                    lengthBaseDimension,  2,
                    timeBaseDimension,   -2) energyDimension;
   ---
*/
// derived_dimension.hpp
public template dimension(pairs...)
{
    private template buildList(BaseDimension bd, alias ex, pairs...)
    if (isRational!(typeof(ex)))
    {
        static if (pairs.length)
        {
            alias TypeTuple!(FundamentalDimension(bd, ex),
                             buildList!(pairs)) buildList;
        }
        else
        {
            alias TypeTuple!(FundamentalDimension(bd, ex)) buildList;
        }
    }

    private template buildList(BaseDimension bd, alias ex, pairs...)
    if (isIntegral!(typeof(ex)))
    {
        alias buildList!(bd, QQ(ex), pairs) buildList;
    }

    private Dimension _dimension(Range)(Range range)
    if (isInputRange!Range && isFundamentalDimension!(ElementType!Range))
    {
        Dimension ret;
        auto p = appender!(FundamentalDimension[])();
        FundamentalDimension prev = range.front;
        range.popFront();

        foreach (e; range)
        {
            if (prev == e)
            {
                prev = prev + e;
            }
            else
            {
                if (prev.exponent != 0)
                {
                    p.put(prev);
                }
                prev = e;
            }
        }

        if (prev.exponent != 0)
        {
            p.put(prev);
        }

        ret.fd = p.data;
        return ret;
    }

    static if (pairs.length == 0)
    {
        enum Dimension dimension = Dimension([]);
    }
    else
    {
        enum Dimension dimension = _dimension([buildList!pairs].stdsort);
    }
}

version (unittest)
{
    alias dimension!(alphaBaseDimension,     2) dim1;
    alias dimension!(betaBaseDimension,      1,
                     alphaBaseDimension,     2,
                     gammaBaseDimension,    -2) dim2;
    alias dimension!(betaBaseDimension,     -1,
                     alphaBaseDimension,    -2,
                     gammaBaseDimension,     2) dim3;
    alias dimension!(alphaBaseDimension,     1,
                     gammaBaseDimension,    -1) dim4;
    alias dimension!(alphaBaseDimension,     3) dim5;
    alias dimension!(alphaBaseDimension,     2,
                     alphaBaseDimension,     4) dim6;
    alias dimension!(betaBaseDimension,      2,
                     alphaBaseDimension,     3) dim7;
    alias dimension!(betaBaseDimension,      2,
                     gammaBaseDimension, QQ(7),
                     betaBaseDimension,     -2) dim8;
    alias dimension!(gammaBaseDimension,     1) dim9;
    alias dimension!(betaBaseDimension,      1) dim10;

    alias dimension!()       dimless;
    alias dimension!(_bd1, 1) amountDim;
    alias dimension!(_bd2, 1) currentDim;
    alias dimension!(_bd3, 1) lengthDim;
    alias dimension!(_bd4, 1) luminousIntensityDim;
    alias dimension!(_bd5, 1) massDim;
    alias dimension!(_bd6, 1) planeAngleDim;
    alias dimension!(_bd7, 1) solidAngleDim;
    alias dimension!(_bd8, 1) temperatureDim;
    alias dimension!(_bd9, 1) timeDim;
    alias dimension!(_bd3, 1, _bd5,  1, _bd9, -2) forceDim;
    alias dimension!(_bd3, 2, _bd5,  1, _bd9, -2) energyDim;
    alias dimension!(_bd3, 3) volumeDim;
}

unittest
{
    // Testing dimension
    static assert(dim6.fd.length == 1);
    static assert(dim6.fd[0].baseDimension == alphaBaseDimension &&
                  dim6.fd[0].exponent == QQ(6));

    static assert(dim7.fd.length == 2);
    static assert(dim7.fd[0].baseDimension == alphaBaseDimension &&
                  dim7.fd[0].exponent == QQ(3));
    static assert(dim7.fd[1].baseDimension == betaBaseDimension &&
                  dim7.fd[1].exponent == QQ(2));

    static assert(dim8.fd.length == 1);
    static assert(dim8.fd[0].baseDimension == gammaBaseDimension &&
                  dim8.fd[0].exponent == QQ(7));

    // Testing Dimension
    enum r1 = dim4 ^ QQ(2);
    static assert(r1.fd.length == 2);
    static assert(r1.fd[0].baseDimension == alphaBaseDimension &&
                  r1.fd[1].baseDimension == gammaBaseDimension);
    static assert(r1.fd[0].exponent == QQ(2) && r1.fd[1].exponent == QQ(-2));

    enum r2 = dim7 ^^ QQ(3);
    static assert(r2.fd.length == 2);
    static assert(r2.fd[0].baseDimension == alphaBaseDimension &&
                  r2.fd[1].baseDimension == betaBaseDimension);
    static assert(r2.fd[0].exponent == QQ(1) && r2.fd[1].exponent == QQ(2,3));

    enum r3 = dim2 + dim2;
    static assert(r3 == dim2);

    enum r4 = dim1 - dim1;
    static assert(r4 == dim1);

    enum r5 = dim1 * dim2;
    static assert(r5.fd.length == 3);
    static assert(r5.fd[0].baseDimension == alphaBaseDimension &&
                  r5.fd[1].baseDimension == betaBaseDimension &&
                  r5.fd[2].baseDimension == gammaBaseDimension);
    static assert(r5.fd[0].exponent == QQ(4) &&
                  r5.fd[1].exponent == QQ(1) &&
                  r5.fd[2].exponent == QQ(-2));

    enum r6 = dim1 / dim2;
    static assert(r6.fd.length == 2);
    static assert(r6.fd[0].baseDimension == betaBaseDimension &&
                  r6.fd[1].baseDimension == gammaBaseDimension);
    static assert(r6.fd[0].exponent == QQ(-1) && r6.fd[1].exponent == QQ(2));
}

private string rawString(Dimension d)
{
    return xformat("Dimension([%-(%s,%)])", d.fd.map!(a => rawString(a)));
}

unittest
{
    enum Dimension d1 = Dimension([funDim1, funDim2]);
    static assert(rawString(d1) ==
                  `Dimension([FundamentalDimension("alpha_bd()",QQ(2,1)),`
                  `FundamentalDimension("beta_bd()",QQ(3,1))])`);
    static assert(mixin(rawString(d1)) == d1);

    enum Dimension d2 = Dimension([]);
    static assert(rawString(d2) == "Dimension([])");
    static assert(mixin(rawString(d2)) == d2);
}

public template isDimension(T)
{
    enum bool isDimension = is(T == Dimension);
}

/*
  Merges two sorted arrays of FundamentalDimensions, HeterogeneousDimensions, or
  Scales.
*/
// detail/dimension_impl.hpp
private T[] merge(T)(T[] a, T[] b) @safe pure
{
    if (a.length == 0 && b.length == 0)
    {
        return [];
    }
    else if (a.length == 0)
    {
        return b;
    }
    else if (b.length == 0)
    {
        return a;
    }
    else if (a[0] < b[0])
    {
        return a[0] ~ merge(a[1..$], b);
    }
    else if (a[0] > b[0])
    {
        return b[0] ~ merge(a, b[1..$]);
    }
    else
    {
        auto combined = a[0] + b[0];
        if (combined.exponent.num != 0)
        {
            return combined ~ merge(a[1..$], b[1..$]);
        }
        else
        {
            return merge(a[1..$], b[1..$]);
        }
    }
}

unittest
{
    enum r1 = merge(dim1.fd, dim1.fd);
    static assert(r1.length == 1);
    static assert(r1[0].baseDimension == alphaBaseDimension);
    static assert(r1[0].exponent == QQ(4));

    enum r2 = merge(dim1.fd, dim4.fd);
    static assert(r2.length == 2);
    static assert(r2[0].baseDimension == alphaBaseDimension);
    static assert(r2[1].baseDimension == gammaBaseDimension);
    static assert(r2[0].exponent == QQ( 3));
    static assert(r2[1].exponent == QQ(-1));

    enum r3 = merge(dim2.fd, dim8.fd);
    static assert(r3.length == 3);
    static assert(r3[0].baseDimension == alphaBaseDimension);
    static assert(r3[1].baseDimension == betaBaseDimension);
    static assert(r3[2].baseDimension == gammaBaseDimension);
    static assert(r3[0].exponent == QQ(2));
    static assert(r3[1].exponent == QQ(1));
    static assert(r3[2].exponent == QQ(5));
}

/*
  Returns an array of which elements are obtained by applying
  $(B opUnary!("-")(x)) for all $(B x) in $(B xs).
*/
private T[] inverse(T)(T[] xs) @safe pure
{
    T[] dp = xs.dup;
    foreach (i, x; xs)
    {
        dp[i] = -x;
    }
    return dp;
}

unittest
{
    enum r1 = inverse(dim2.fd);
    static assert(r1.length == 3);
    static assert(r1[0].exponent == QQ(-2));
    static assert(r1[1].exponent == QQ(-1));
    static assert(r1[2].exponent == QQ( 2));
}

/**
   Helper function that returns a scale with the specified $(B base) and
   $(B exponent).  The $(B name) and the $(B symbol) are optional.  Internally
   if a scale value matches one of the predefined prefixes, the
   $(B DecimalPrefix) and the $(B BinaryPrefix), it will be used instead.
*/
Scale scale()(uint base, QQ exponent, string name, string symbol)
@safe pure nothrow
{
    return Scale(base, exponent, name, symbol);
}

/// ditto
Scale scale(G)(uint base, G exponent, string name, string symbol)
@safe pure nothrow if (is(G : long))
{
    return Scale(base, QQ(exponent), name, symbol);
}

/// ditto
Scale scale(E)(uint base, E exponent) @safe pure nothrow
if (is(E : long) || isRational!E)
{
    return scale(base, exponent, "", "");
}

/**
   A struct representing a scaling factor.
*/
// scale.hpp
private struct Scale
{
    uint base;
    QQ exponent;
    string name;
    string symbol;

    @disable this();

    this(uint base, QQ exponent, string name, string symbol) @safe pure nothrow
    {
        this.base = base;
        this.exponent = exponent;
        this.name = name;
        this.symbol = symbol;
    }

    @property real value() @safe pure
    {
        return exponent.den == 1 && exponent.num >= 0
            ? std.math.pow(base, exponent.num)
            : std.math.pow(base, exponent.value!real);
    }

    // opBinary and opUnary, all three of scale_list_dim in detail/unscale.hpp
    Scale opBinary(string op)(Scale other) @safe pure if (op == "+")
    {
        assert(this.base == other.base);
        return scale(this.base, this.exponent + other.exponent);
    }
  
    Scale opBinary(string op)(QQ r) @safe pure if (op == "*")
    {
        return scale(this.base, this.exponent * r);
    }

    Scale opUnary(string op)() @safe pure if (op == "-")
    {
        return scale(this.base, -this.exponent);
    }

    int opCmp(Scale other) @safe const pure nothrow
    {
        if (this.base < other.base) return -1;
        if (this.base > other.base) return  1;
        return 0;
    }

    bool opEquals(Scale other) @safe const pure nothrow
    {
        return this.opCmp(other) == 0 ? true : false;
    }

    void toString(scope void delegate(const(char)[]) sink,
                  FormatSpec!char fmt) const
    {
        if (exponent.num == 0)
        {
            return;
        }

        auto m = matchDefinedPrefix(this);
        /*
          FIXME_1:
          We wish there was a way for client code to provide custom `match-prefix`
          methods to print symbols or names for scales that aren't defined in
          this module.  Because Scale is used at compile-time, any approach that
          deals with pointers or anything static is out of the question.  We
          also don't want to make Scale polymorphic because it will complicate
          things.  What else can we do?
        */

        final switch (fmt.spec)
        {
        case 'r':
            goto case;
        case 'y':
            assert(m.symbol.length,"scale symbol empty when it should not be.");
            sink(m.symbol);
            break;
        case 'n':
            assert(m.name.length, "scale name empty when it should not be.");
            sink(m.name);
            break;      
        case 's':
            sink(xformat("%s^%s", m.base, m.exponent));
            break;
        }
    }
}

unittest
{
    enum s1 = scale(10, 3);
    enum s2 = scale(10, -3);
    enum s3 = scale(2, 10);
    enum s4 = -s1;

    enum r1 = s1 + s1;
    static assert(r1.base == 10);
    static assert(r1.exponent == 6);

    enum r2 = s2 * QQ(3);
    static assert(r2.base == 10);
    static assert(r2.exponent == -9);

    static assert(s3 < s1);
    static assert(s4 == s2);
}

private string rawString(Scale s)
{
    return xformat(`Scale(%s,%s,"%s","%s")`,
                   s.base, rawString(s.exponent), s.name, s.symbol);
}

unittest
{
    static assert(rawString(scale(10, -3)) == `Scale(10,QQ(-3,1),"","")`);
    static assert(mixin(rawString(DecimalPrefix.Yocto)) == DecimalPrefix.Yocto);
}

/**
   Check to see if $(B T) is a Scale.
*/
private template isScale(T)
{
    enum bool isScale = is(T == Scale);
}

public const Scale no_scale = scale(0, 0);

///
public enum DecimalPrefix : Scale
{
    Yocto = Scale(10, QQ(-24), "yocto", "y"), ///
    Zepto = Scale(10, QQ(-21), "zepto", "z"), ///
    Atto  = Scale(10, QQ(-18), "atto",  "a"), ///
    Femto = Scale(10, QQ(-15), "femto", "f"), ///
    Pico  = Scale(10, QQ(-12), "pico",  "p"), ///
    Nano  = Scale(10, QQ(-9),  "nano",  "n"), ///
    Micro = Scale(10, QQ(-6),  "micro", "u"), ///
    Milli = Scale(10, QQ(-3),  "milli", "m"), ///
    Centi = Scale(10, QQ(-2),  "centi", "c"), ///
    Deci  = Scale(10, QQ(-1),  "deci",  "d"), ///
    Deka  = Scale(10, QQ(1),   "deka", "da"), ///
    Hecto = Scale(10, QQ(2),   "hecto", "h"), ///
    Kilo  = Scale(10, QQ(3),   "kilo",  "k"), ///
    Mega  = Scale(10, QQ(6),   "mega",  "M"), ///
    Giga  = Scale(10, QQ(9),   "giga",  "G"), ///
    Tera  = Scale(10, QQ(12),  "tera",  "T"), ///
    Peta  = Scale(10, QQ(15),  "peta",  "P"), ///
    Exa   = Scale(10, QQ(18),  "exa",   "E"), ///
    Zetta = Scale(10, QQ(21),  "zetta", "Z"), ///
    Yotta = Scale(10, QQ(24),  "yotta", "Y")  ///
}

///
public enum BinaryPrefix : Scale
{
    Kibi = Scale(2, QQ(10), "kibi", "Ki"), ///
    Mebi = Scale(2, QQ(20), "mebi", "Mi"), ///
    Gibi = Scale(2, QQ(30), "gibi", "Gi"), ///
    Tebi = Scale(2, QQ(40), "tebi", "Ti"), ///
    Pebi = Scale(2, QQ(50), "pebi", "Pi"), ///
    Exbi = Scale(2, QQ(60), "exbi", "Ei")  ///
}

Scale matchDefinedPrefix(Scale src) @safe pure nothrow
{
    foreach (x; EnumMembers!(DecimalPrefix))
    {
        if (x.base == src.base && x.exponent == src.exponent)
        {
            return x;
        }
    }

    foreach (x; EnumMembers!(BinaryPrefix))
    {
        if (x.base == src.base && x.exponent == src.exponent)
        {
            return x;
        }
    }
    return src;
}

unittest
{
    static assert(matchDefinedPrefix(scale(10, 3)) == DecimalPrefix.Kilo);
    static assert(matchDefinedPrefix(scale(10, 4)) == scale(10, 4));
    static assert(matchDefinedPrefix(scale(2, 8, "Name", "sym")) ==
                  scale(2, 8, "Name", "sym"));
}

/*
   Evaluate an array of scales.
*/
private real evalScales(Scale[] sc)
{
    return reduce!((a, b) => a * b.value)(1.0L, sc);
}

unittest
{
    enum Scale[] s1 = [DecimalPrefix.Hecto, DecimalPrefix.Kilo];
    static assert(evalScales(s1) == 100000);
}

/*
  destination is raw string representation of a Unit!(D, S).
  factor is any mathematical expression.
*/
// base_unit.hpp
private alias Tuple!(string, "destination", string, "factor") Conversion;

private string rawString(Conversion c)
{
    return xformat(`Conversion("%s","%s")`, c.destination, c.factor);
}

unittest
{
    enum Conversion c1 = Conversion("str", "QQ(5,7)");
    static assert(rawString(c1) == `Conversion("str","QQ(5,7)")`);

    enum Conversion c2 = Conversion("str", "QQ(3,6)");
    enum Conversion c3 = mixin(rawString(c2));
    static assert(c2.destination == c3.destination);
    static assert(c2.factor == c3.factor);
}

private string rawString(Conversion[] cs)
{
    return xformat("[%-(%s,%)]", cs.map!(a => rawString(a)));
}

unittest
{
    enum Conversion[] c1 = [];
    enum Conversion[] c2 = [Conversion("str", "QQ(2,3)")];
    enum Conversion[] c3 = [Conversion("str", "QQ(1,3)"),
                            Conversion("str", "QQ(4,7)")];
    static assert(rawString(c1) == "[]");
    static assert(rawString(c2) == `[Conversion("str","QQ(2,3)")]`);
    static assert(mixin(rawString(c2)) == c2);
    static assert(rawString(c3) == `[Conversion("str","QQ(1,3)"),`
                  `Conversion("str","QQ(4,7)")]`);
    static assert(mixin(rawString(c3)) == c3);
}

/*
  Defines a base unit.
*/
private struct BaseUnit
{
    string name;
    string symbol;
    string ordinal;
    Scale scale;
    Dimension dimension; // DimensionType
    Conversion[] conversions;

    /*
      If no default conversion is given, this stays empty.  The template
      getDefaultConversion returns MakeHeterogeneousUnit() if there is no default
      conversion.
      If default conversin is given, note that the unit is not reduced.
    */
    string defaultConversion;

    @disable this();

    this(string name, string symbol, Scale scale, Dimension dimension,
         Conversion[] convs = null, string dc = "")
    {
        this.name = name;
        this.symbol = symbol;
        this.scale = scale;
        this.dimension = dimension;
        this.conversions = convs;
        this.defaultConversion = dc;
        this.ordinal = 
            xformat("=_%s__%s__%s__%s__%s__%s_=",
                    name, symbol, scale, dimension, rawString(conversions),
                    defaultConversion);
    }

    int opCmp(BaseUnit other) @safe const pure nothrow
    {
        if (this.ordinal < other.ordinal) return -1;
        if (this.ordinal > other.ordinal) return  1;
        return 0;
    }

    bool opEquals(BaseUnit other) @safe const pure nothrow
    {
        return this.ordinal == other.ordinal && this.scale == other.scale;
    }

    void toString(scope void delegate(const(char)[]) sink,
                  FormatSpec!char fmt) const
    {
        final switch (fmt.spec)
        {
        case 'r':
            goto case;
        case 'y':
            if (scale != no_scale)
                sink(xformat("%y", scale));
            sink(symbol);
            break;
        case 'n':
            if (scale != no_scale)
                sink(xformat("%n", scale));
            sink(name);
            break;
        case 's':
            sink(ordinal);
            break;
        }
    }
}

private string rawString(BaseUnit bu)
{
    return xformat(`BaseUnit("%s","%s",%s,%s,%s,"%s")`,
                   bu.name, bu.symbol, rawString(bu.scale),
                   rawString(bu.dimension), rawString(bu.conversions),
                   bu.defaultConversion);
}

unittest
{
    enum BaseUnit bu1 =
        BaseUnit("bu1", "1ub", no_scale, dim1,
                 [Conversion("U1", "QQ(2)")], "none");

    static assert(rawString(bu1) ==
                  `BaseUnit("bu1","1ub",Scale(0,QQ(0,1),"",""),`
                  `Dimension([FundamentalDimension("alpha_bd()",QQ(2,1))]),`
                  `[Conversion("U1","QQ(2)")],"none")`);
    static assert(mixin(rawString(bu1)) == bu1);
}

/*
  Check to see if $(B T) is a BaseUnit.
*/
private template isBaseUnit(T)
{
    enum bool isBaseUnit = is(T == BaseUnit);
}

/**
   Defines a base unit.

   Examples:
   ---
   alias baseUnit!(lengthDimension, "meter", "m") meterBaseUnit;
   ---
*/
public template baseUnit(alias dimension, string name, string symbol)
if (isDimension!(typeof(dimension)))
{
    enum BaseUnit baseUnit = BaseUnit(name, symbol, no_scale, dimension);
}

version (unittest)
{
    alias baseUnit!(dim1, "baseUnit1", "bu1")  baseUnit1;
    alias baseUnit!(dim2, "baseUnit2", "bu2")  baseUnit2;
    alias baseUnit!(dim9, "baseUnit3", "bu3")  baseUnit3;
    alias baseUnit!(dim10, "baseUnit4", "bu4") baseUnit4;

    alias baseUnit!(planeAngleDim, "radian", "rad")        angleRadianBaseUnit;
    alias baseUnit!(solidAngleDim, "steradian", "sr")      angleSteradianBaseUnit;
    alias baseUnit!(massDim, "gram", "g")                  cgsGramBaseUnit;
    alias baseUnit!(currentDim, "ampere", "A")             siAmpereBaseUnit;
    alias baseUnit!(luminousIntensityDim, "candela", "cd") siCandelaBaseUnit;
    alias baseUnit!(temperatureDim, "kelvin", "K")         siKelvinBaseUnit;
    alias baseUnit!(lengthDim, "meter", "m")               siMeterBaseUnit;
    alias baseUnit!(amountDim, "mole", "mol")              siMoleBaseUnit;
    alias baseUnit!(timeDim, "second", "s")                siSecondBaseUnit;
}

/**
   Defines a base unit that is a multiple of base unit $(B bu).

   Examples:
   ---
   alias scaledBaseUnit!(cgs.gramBaseUnit, DecimalPrefix.Kilo) kilogramBaseUnit;
   ---
*/

public template scaledBaseUnit(alias bu, alias scale)
if (isBaseUnit!(typeof(bu)) 
    && (isScale!(typeof(scale)) ||
        is(typeof(scale) == DecimalPrefix) ||
        is(typeof(scale) == BinaryPrefix))
    )
{
    static assert(scale != no_scale,
                  "A scale is required when creating a scaled base unit.");

    static if (bu.scale == no_scale)
    {
        alias scale addScales;
    }
    else
    {
        static assert(
            bu.scale.base == scale.base,
            "bu.scale.base and scale.base must be equal.");
        enum Scale addScales = bu.scale + scale;
    }

    enum BaseUnit scaledBaseUnit =
        BaseUnit(bu.name, bu.symbol, addScales, bu.dimension,
                 bu.conversions, bu.defaultConversion);
}

/**
   Defines a base unit, named $(B name) and having the symbol $(B symbol), that
   is a multiple of base unit $(B bu).

   Examples:
   ---
   alias baseUnit!(cgs.gramBaseUnit, scale(10, 3), "", "グラム") newKilogramBaseUnit;
   writeln(2.0 * UnitOf!(newKilogramBaseUnit)());
   ---
   <pre class=console>
   2 kグラム
   </pre>
*/
public template scaledBaseUnit(alias bu, alias scale, string name, string symbol)
if (isBaseUnit!(typeof(bu))
    && (isScale!(typeof(scale)) ||
        is(typeof(scale) == DecimalPrefix) ||
        is(typeof(scale) == BinaryPrefix))
    )
{
   static assert(scale != no_scale,  /* make sure there is a scale. */
                  "You must provide a scale.");

    static if (bu.scale == no_scale)
    {
        alias scale addScales;
    }
    else
    {
        static assert(
            bu.scale.base == scale.base,
            "bu.scale.base and scale.base must be equal.");
        enum Scale addScales = bu.scale + scale;
    }

    enum BaseUnit scaledBaseUnit =
        BaseUnit(name, symbol, addScales, bu.dimension,
                 bu.conversions, bu.defaultConversion);
}

version (unittest)
{
    alias scaledBaseUnit!(baseUnit1, scale(10, 3), "キロ", "k") kiloBaseUnit1;
    alias scaledBaseUnit!(cgsGramBaseUnit, DecimalPrefix.Kilo) siKilogramBaseUnit;
}

private template isValidFactor(string factor)
{
    mixin("alias typeof(" ~ factor ~ ") Factor;");
    enum bool isValidFactor = isNumeric!Factor || isRational!Factor;
}

/**
   Defines a base unit and conversion to a dimensionally-consistent unit $(B U)
   or a base unit $(B bu).  $(B factor) is string representation of a numeric
   value, be it an integer, real, or rational.
   This does what BOOST_UNITS_DEFINE_BASE_UNIT_WITH_CONVERSIONS in BOOST.units does.

   Examples:
   ---
   alias baseUnitWithConversion!("pint", "pt", si.volume, "QQ(946353, 2000000000)") pintBaseUnit;
   alias baseUnitWithConversion!("pound", "lb", cgs.gramBaseUnit, "453.592") poundBaseUnit;
   ---
*/
public template baseUnitWithConversion(string name, string symbol, U,
                                       string factor)
if (isUnit!U && isValidFactor!factor)
{
    private alias rawUnitString!(ReduceUnit!(U)) dst;
    enum BaseUnit baseUnitWithConversion = 
        BaseUnit(name, symbol, no_scale, U.dimension,
                 [Conversion(dst, factor)], dst);
}

/// ditto
public template baseUnitWithConversion
(string name, string symbol, alias bu, string factor)
//if (isBaseUnit!(typeof(bu)) && isValidFactor!factor) // D_BUG_2 ?
if (is(typeof(bu) == BaseUnit) && isValidFactor!factor)
{
    enum BaseUnit baseUnitWithConversion =
        baseUnitWithConversion!(name, symbol, UnitOf!(bu), factor);
}

unittest
{
    alias baseUnitWithConversion!("pint", "pt", SiVolume, "QQ(946353, 2000000000)") imperialPintBaseUnit;
    alias baseUnitWithConversion!("pound", "lb", cgsGramBaseUnit, "453.592") imperialPoundBaseUnit;

    alias UnitOf!(imperialPintBaseUnit) SourceUnit1;
    alias SiVolume TargetUnit1;
    alias convert!(Quantity!(SourceUnit1), Quantity!(TargetUnit1)) C1;
    assert(approxEqual!()(C1(1.0 * SourceUnit1()).value, QQ(946353, 2000000000).value!real));

    alias UnitOf!(imperialPoundBaseUnit) SourceUnit2;
    alias UnitOf!(cgsGramBaseUnit) TargetUnit2;
    alias convert!(Quantity!(SourceUnit2), Quantity!(TargetUnit2)) C2;
    assert(approxEqual(C2(1.0 * SourceUnit2()).value, 453.592));
}

/**
   Defines a base unit and conversions to other units or to other base units
   with the correct dimensions.

   Examples:
   ---
   alias DefineBaseUnit!(lengthDimension, "ABC", "abc") Abc;
   ---
*/
public template DefineBaseUnit(alias dimension, string name, string symbol)
{
    private template buildList(U, string factor, conversions...)
    if (isUnit!U && isValidFactor!factor)
    {
        alias rawUnitString!(ReduceUnit!(U)) dst;
        static if (conversions.length)
        {
            alias TypeTuple!(Conversion(dst, factor),
                             buildList!(conversions)) buildList;
        }
        else
        {
            alias TypeTuple!(Conversion(dst, factor)) buildList;
        }
    }

    private template buildList(alias bu, string factor, conversions...)
    //if(isBaseUnit!(typeof(bu)) && isValidFactor!factor)  // D_BUG_3 ?
    if (is(typeof(bu) == BaseUnit) && isValidFactor!factor)
    {
        enum Dimension dimension = bu.dimension;
        alias rawUnitString!(ReduceUnit!(MakeHeterogeneousUnit!(bu,dimension))) dst;
        static if (conversions.length)
        {
            alias TypeTuple!(Conversion(dst, factor),
                             buildList!(conversions)) buildList;
        }
        else
        {
            alias TypeTuple!(Conversion(dst, factor)) buildList;
        }
    }

    /**
       with conversion factors $(B Pairs), where each pair is either a unit and
       a factor or a base unit and a factor.
       Examples:
       ---
       alias Abc.WithConversionFactors!(cgs.centimeterBaseUnit, "QQ(2,3)") AbcBaseUnit1;
       ---
    */
    public template WithConversionFactors(Pairs...)
    {
        enum BaseUnit WithConversionFactors =
            BaseUnit(name, symbol, no_scale, dimension, [buildList!Pairs]);
    }

    /**
       with a default conversion $(B U) which is applied when no direct
       conversion is available.  $(B U) is any unit with the same dimensions.

       Examples:
       ---
       alias Abc.WithDefaultConversion!(si.Length) AbcBaseUnit2;
       ---
    */
    // FIXME_2: do we enforce the fact that U has same dimensions?
    public template WithDefaultConversion(U) if (isUnit!U)
    {
        enum BaseUnit WithDefaultConversion =
            BaseUnit(name, symbol, no_scale, dimension, [], rawUnitString!U);
    }

    /**
       with a default conversion $(B U) and conversion factors $(B Pairs).

       Examples:
       ---
       alias Abc.WithConversions!(si.Length, cgs.centimeterBaseUnit, "QQ(2,3)") AbcBaseUnit3;
       ---
    */
    public template WithConversions(U, Pairs...) if (isUnit!U)
    {
        enum BaseUnit WithConversions =
            BaseUnit(name, symbol, no_scale, dimension, [buildList!Pairs],
                     rawUnitString!U);
    }
}

unittest
{
    // TODO
}

// struct UnitInfo
// {
//   string name;
//   string symbol;

//   void toString(scope void delegate(const(char)[]) sink,
//                 FormatSpec!char fmt) const
//   {
//     final switch (fmt.spec)
//     {
//     case 'y':
//       sink(symbol);
//       break;
//     case 'n':
//       sink(name);
//       break;
//     }
//   }
// }

/*
  D_BUG_4
  We have to use a Tuple because DMD dies if UnitInfo is a struct.
*/
private alias Tuple!(string, "name", string, "symbol") UnitInfo;

private string toString(UnitInfo info, FormatSpec!char fmt) @safe pure nothrow
{
    final switch (fmt.spec)
    {
    case 'y':
        return info.symbol;
    case 'n':
        return info.name;
    }
}

/**
   Use this to define a $(B name) and a $(B symbol) for derived unit $(B U).
   Subsequent calls will override the previous definition.

   Examples:
   ---
   writeln(2.0 * si.Energy());
   ---
   <pre class=console>
   2 J
   </pre>
   ---
   defineUnitInfo!(si.Energy)("XYZ", "xyz");
   writeln(2.0 * si.Energy());
   ---
   <pre class=console>
   2 xyz
   </pre>
*/
public static void defineUnitInfo(U)(string name, string symbol) if (isUnit!U)
{
    alias ReduceUnit!U ReducedUnit;
    ReducedUnit.info = UnitInfo(name, symbol);
}


/**
   struct representing a model-dependent unit with no associated value.
*/
public struct Unit(alias dim, alias sys)
if (isHomogeneousSystem!(typeof(sys)) || isHeterogeneousSystem!(typeof(sys)))
{
    alias typeof(sys) System; ///
    
    enum Dimension dimension = dim; ///
    enum System system       = sys; ///

    // expensive. enable in unittests only.
    // static if(isHomogeneousSystem!(System))
    // {
    //   static assert(checkSystem(system, dimension));
    // }

    static if (isHeterogeneousSystem!System)
    {
        ///
        static UnitInfo info = UnitInfo("", "");
        ///
        enum bool hasDimensionlessSystem = system == HeterogeneousSystem.dimensionless;
    }
    else
    {
        enum bool hasDimensionlessSystem = true;
    }

    ///
    Unit opUnary(string op)() @safe pure nothrow
    if (op == "+" || op == "-")
    {
        return this;
    }

    ///
    Unit opBinary(string op)(Unit other) @safe pure nothrow
    if (op == "+" || op == "-")
    {
        return this;
    }

    ///
    auto opBinary(string op, U)(U other) nothrow
    if ((op == "*"  || op == "/") && isUnit!U)
    {
        alias makeHeterogeneousSystem mHS;

        static if (isHomogeneousSystem!System && isHomogeneousSystem!(U.System))
        {
            static if (system.bu == other.system.bu)
            {
                return Unit!(mixin("dimension"~op~"other.dimension"), system)();
            }
            else
            {
                return Unit!(
                    mixin("dimension"~op~"other.dimension"),
                    mixin("mHS(dimension, system.bu)"~op~
                          "mHS(other.dimension, other.system.bu)"))();
            }
        }
        else static if (isHomogeneousSystem!System &&
                        isHeterogeneousSystem!(U.System))
        {
            return Unit!(
                mixin("dimension"~op~"other.dimension"),
                mixin("mHS(dimension, system.bu)"~op~"other.system"))();
        }
        else static if (isHeterogeneousSystem!System &&
                        isHomogeneousSystem!(U.System))
        {
            return Unit!(
                mixin("dimension"~op~"other.dimension"),
                mixin("system"~op~"mHS(other.dimension, other.system.bu)"))();
        }
        else
        {
            return Unit!(
                mixin("dimension"~op~"other.dimension"),
                mixin("system"~op~"other.system"))();
        }
    }

    ///
    template power(alias r)
    {
        alias Unit!(dimension ^ r, system ^ r) power;
    }

    ///
    template root(alias r)
    {
        alias Unit!(dimension ^^ r, system ^^ r) root;
    }

    ///
    Quantity!(Unit, N) opBinary(string op, N)(N n)
    if ((op == "*" || op == "/") && !isUnit!N && !isQuantity!N)
    {
        enum N one = N.min / N.min;
        return Quantity!(Unit, N)(mixin("one" ~ op ~ "n"));
    }

    ///
    auto opBinaryRight(string op, N)(N n)
    if ((op == "*" || op == "/") && !isUnit!N && !isQuantity!N)
    {
        static if (op == "/")
        {
            return Quantity!(Unit.power!(QQ(-1)), N)(n);
        }
        else
        {
            return Quantity!(Unit, N)(n);
        }
    }

    static if (isHeterogeneousSystem!System)
    {
        enum bool cnd1 = dimension.fd.length != 0;
        enum bool cnd2 = system.hd.length    != 0;
        enum bool cnd3 = system.fd.length    != 0;
        enum bool cnd4 = system.sc.length    != 0;
    }

    static if (isHomogeneousSystem!System) {
        /**
           Converts the unit to a string representation.
           Supported_Formats:

           $(B 'y') for symbol format;  reduces unit names to known symbols for
           both base and derived units.
           Examples:
           ---
           writefln("%y", si.Force() * si.Length());
           writefln("%y", si.Force() * si.Energy()); // unknown
           ---
           <pre class=console>
           J
           kg^2 m^3 s^-4
           </pre>

           $(B 'n') for name format; outputs full unit names for base and
           derived units.
           Examples:
           ---
           writefln("%n", si.Force() * si.Length());
           ---
           <pre class=console>
           joule
           </pre>

           $(B 'r') for raw format; outputs only symbols for base units but not
           derived units.
           Examples:
           ---
           writefln("%r", si.Force() * si.Length());
           ---
           <pre class=console>
           kg m^2 s^-2
           </pre>

           $(B 's') defaults to symbol format.
           Examples:
           ---
           writeln(si.Force() * si.Length());
           ---
           <pre class=console>
           J
           </pre>
         */
        void toString(scope void delegate(const(char)[]) sink,
                      FormatSpec!char fmtspec) const
        {
            alias ReduceUnit!(Unit) ReducedUnit;

            string fmt;
            final switch (fmtspec.spec)
            {
            case 'r':
                fmt = "%r";
                break;
            case 's':
                goto case;
            case 'y':
                fmt = "%y";
                break;
            case 'n':
                fmt = "%n";
            }
            sink(xformat(fmt, ReducedUnit()));
        }
    } else {
        void toString(scope void delegate(const(char)[]) sink,
                      FormatSpec!char fmtspec) const
        {
            string fmt;
            final switch (fmtspec.spec)
            {
            case 'r':
                fmt = "%r";
                break;
            case 's':
                goto case;
            case 'y':
                fmt = "%y";
                break;
            case 'n':
                fmt = "%n";
            }

            enum shd = system.hd;
            enum sfd = system.fd;
            enum ssc = system.sc;

            static if (cnd1 && cnd2 && cnd3 && !cnd4) { // #2
                static if (shd.length == 1 &&
                           shd[0].baseUnit.scale != no_scale) { // #7
                    sink(xformat("%(" ~ fmt ~ " %)", shd));
                } else {
                    if (info != UnitInfo("", "") &&
                        (fmtspec.spec == 'n' || fmtspec.spec == 'y'))
                    {
                        sink(.toString(info, fmtspec));
                    }
                    else
                    {
                        sink(xformat("%(" ~ fmt ~ " %)", shd));
                    }
                }
            } else static if (!cnd1 && !cnd2 && !cnd3 && !cnd4) { // #1
                sink("dimensionless");
            } else static if (!cnd1 && !cnd2 && !cnd3 && cnd4) { // #3
                sink(xformat("%(" ~ fmt ~ "%)", ssc));
            } else static if (cnd1 && cnd2 && cnd3 && cnd4) { // #4 and #5
                static if (shd.length == 1 &&
                           shd[0].baseUnit.scale != no_scale
                           && shd[0].exponent == QQ(1)) { // #6
                    enum BaseUnit bu1 = shd[0].baseUnit;
                    enum BaseUnit bu2 =
                        BaseUnit(bu1.name, bu1.symbol, no_scale, bu1.dimension,
                                 bu1.conversions, bu1.defaultConversion);
                    alias Unit!(dimension,
                                HeterogeneousSystem(
                                    [HeterogeneousDimension(bu2, QQ(1))],
                                    sfd,
                                    merge(ssc, [bu1.scale]))) NewUnit;
                    sink(xformat(fmt, NewUnit()));
                    return;
                }
                sink(xformat("%(" ~ fmt ~ "%)", ssc));
                alias Unit!(dimension,
                            HeterogeneousSystem(shd, sfd, [])) WithoutScale;
                string withoutScale = xformat(fmt, WithoutScale());

                static if (sfd.length == 1 && sfd[0].exponent == QQ(1)) { // #5
                    sink(withoutScale);
                } else { // #4
                    if (withoutScale == xformat("%" ~ fmt, WithoutScale()))
                    {
                        sink("(");
                        sink(withoutScale);
                        sink(")");
                    }
                    else
                    {
                        sink(withoutScale);
                    }
                }
            }
        }
    }
}

version (unittest)
{
    alias Unit!(dimless, siSystem)   SiDimensionless;
    alias Unit!(lengthDim, siSystem) SiLength;
    alias Unit!(massDim, siSystem)   SiMass;
    alias Unit!(energyDim, siSystem) SiEnergy;
    alias Unit!(forceDim, siSystem)  SiForce;
    alias Unit!(volumeDim, siSystem) SiVolume;
}

/**
   Defines a unit that is a multiple of unit $(B U).

   Examples:
   ---
   alias ScaledUnit!(si.Time, scale(10, -9)) Nanosecond;
   Quantity!(Nanosecond) t = 1.0 * si.seconds;
   writeln(t1);
   ---
   <pre class=console>
   1e9 ns
   </pre>
*/
public template ScaledUnit(U, alias scale)
if (isUnit!U && isHomogeneousSystem!(U.System))
{
    alias ScaledUnit!(ReduceUnit!U, scale) ScaledUnit;
}

/// ditto
public template ScaledUnit(U, alias scale)
if (isUnit!U && isHeterogeneousSystem!(U.System))
{
    static if (scale.exponent == QQ(0))
    {
        alias U ScaledUnit;
    }
    else
    {
        private enum Scale newScale = scale;

        alias Unit!(
            U.dimension,
            HeterogeneousSystem(
                U.system.hd,
                U.system.fd,
                merge(U.system.sc, [newScale]))) ScaledUnit;
    }
}

unittest
{
    alias ScaledUnit!(si.Time, scale(10, -9)) Nanosecond;
    /*
      TODO: error because it can't implicityly convert.  Do we want to enable this feature?
      So far it is enabled; see commented out line 'isImplicitlyConvertible' in
      the ctor and opAssign of Quantity.
     */

    // Quantity!(Nanosecond) t1; t1 = 2.0 * si.seconds;
    // writeln(t1);
    //Quantity!(Nanosecond) t1 = convert!(Quantity!(si.Time), Quantity!(Nanosecond))(1.0 * si.seconds);
    //writeln(t1);
}

/*
{
    0  :: convert; (0,1)
    1  :: conversion_factor; (1,2)
    2  :: conversion_impl; (2,3)
    3  :: makeCBUC; (3,7)
    4  :: isConversionDefined;
    5  :: converterValue;
    6  :: getDefaultConversion; 
    7  :: call_base_unit_converter; (7,4), (7,8), (7,9), (7,3), (7,1),
    8  :: do_call_base_unit_converter; (8,5), 
    9  :: get_default_conversion_impl; (9,6), (9,3), 
}
*/

private template rawUnitString(U) if (isUnit!U)
{
    enum string rawUnitString =
        xformat("Unit!(%s,%s)", rawString(U.dimension), rawString(U.system));
}

private string rawUnitString2(U)() if (isUnit!U)
{
    return xformat("Unit!(%s,%s)", rawString(U.dimension), rawString(U.system));
}

/**
   Check to see if $(B T) is a Unit.
*/
public template isUnit(T)
{
    static if (is(T U == Unit!(A), A...))
    {
        enum bool isUnit = true;
    }
    else
    {
        enum bool isUnit = false;
    }
}

/**
   Check to see if $(B U) is a dimensionless unit.
*/
public template isDimensionlessUnit(U) if (isUnit!U)
{
    enum bool isDimensionlessUnit = U.dimension == Dimension.dimensionless;
}

// unit.hpp
private template ReduceUnit(U)
if (isUnit!U && isHomogeneousSystem!(typeof(U.system)))
{
    alias Unit!(U.dimension,
                makeHeterogeneousSystem(U.dimension, U.system.bu)) ReduceUnit;
}

private template ReduceUnit(U)
if (isUnit!U && isHeterogeneousSystem!(typeof(U.system)))
{
    alias U ReduceUnit;
}

private template ReduceUnit(T) if (isAbsolute!T)
{
    alias ReduceUnit!(T.ValueType) ReduceUnit;
}

// linear_algebra.hpp
private bool isBaseDimensionUnit(Dimension a) @safe pure nothrow
{
    return a.length == 1 && a[0].exponent == QQ(1);
}

unittest
{
    static assert(isBaseDimensionUnit(dim9));
    static assert(!isBaseDimensionUnit(dim1));
}

private bool isSimpleSystem(BaseUnit[] system) @safe pure nothrow
in
{
    assert(system.length > 0);
}
body
{
    if (!isBaseDimensionUnit(system[0].dimension))
    {
        return false;
    }

    for (size_t i = 1; i < system.length; ++i)
    {
        if (isBaseDimensionUnit(system[i].dimension))
        {
            if (system[i-1].dimension.fd[0].baseDimension <
                system[i].dimension.fd[0].baseDimension)
            {
                continue;
            }
            else
            {
                return false;
            }
        }
        else
        {
            return false;
        }
    }
    return true;
}

unittest
{
    static assert(!isSimpleSystem([baseUnit1]));
    static assert(isSimpleSystem([baseUnit3]));
    static assert(isSimpleSystem([baseUnit4, baseUnit3]));
    static assert(!isSimpleSystem([baseUnit3, baseUnit4]));
}

/*
  Returns the transpose of the 2D array $(B mat).
*/
private T[][] transpose(T)(T[][] mat) @safe pure nothrow
in
{
    bool isRectangle = true;
    size_t rowLength;

    if (mat.length)
    {
        rowLength = mat[0].length;
    }

    foreach (row; mat)
    {
        if (row.length != rowLength)
        {
            isRectangle = false;
            break;
        }
    }
    assert(isRectangle, "The 2D array must have rows of equal length.");
}
body
{
    if (mat.length == 0 || mat[0].length == 0)
    {
        return [];
    }

    T[][] res = new T[][](mat[0].length, mat.length);
    foreach (r, row; mat)
    {
        foreach (c, col; row)
        {
            res[c][r] = col;
        }
    }
    return res;
}

unittest
{
    enum int[][] a1 = [[1,2,3],[4,5,6]];
    enum int[][] a2 = [[1],[4]];
    enum int[][] a3 = [];
    enum QQ[][] a4 = [[QQ(1),QQ(2)],[QQ(3),QQ(4)]];

    static assert(transpose(a1) == [[1,4],[2,5],[3,6]]);
    static assert(transpose(a2) == [[1,4]]);
    static assert(transpose(a3) == []);
    static assert(transpose(a4) == [[QQ(1),QQ(3)],[QQ(2),QQ(4)]]);
}

private T[] multiplyAddUnits(T)(T[] vec, T[][] mat) @safe pure nothrow
in
{
    transpose(mat);
    assert(vec.length == mat.length);
}
body
{
    T[][] tr = transpose(mat);
    T[] res = new T[tr.length];

    foreach (r, row; tr)
    {
        T s = 0;
        foreach (c, col; row)
        {
            s += col * vec[c];
        }
        res[r] = s;
    }
    return res;
}

unittest
{
    enum QQ[] v1 = [QQ(1),QQ(2)];
    enum QQ[][] m1 = [[QQ(1),QQ(2)],[QQ(3),QQ(4)]];
    static assert(multiplyAddUnits(v1, m1) == [QQ(7),QQ(10)]);

    enum QQ[][] m2 = [[QQ(1),QQ(2),QQ(3)],[QQ(4),QQ(5),QQ(6)]];
    static assert(multiplyAddUnits(v1, m2) == [QQ(9),QQ(12),QQ(15)]);
    multiplyAddUnits(v1, m2);
}

private alias Flag!"inconsistent" Inconsistent;

/*
  Tries to strip $(B n) zeroes from the front of $(B xs) and write the remaining
  to $(B result).  If successful, it return $(B Inconsistent.no).
*/
private Inconsistent stripZeroes(T)(T[] xs, size_t n, out T[] result)
{
    if (reduce!((a,b) => a + b)(0, xs.take(n).map!(x => x == 0 ? 1 : 0)) == n)
    {
        result = xs.drop(n)[];
        return Inconsistent.no;
    }
    return Inconsistent.yes;
}

unittest
{
    enum int[] a1 = [0,0,0,1,2,3];
    enum int[] a2 = [1,2,3];
    enum int[] a3 = [];
    int[] o1;

    assert(stripZeroes(a1, 0, o1) == Inconsistent.no);
    assert(o1 == [0,0,0,1,2,3]);

    assert(stripZeroes(a1, 2, o1) == Inconsistent.no);
    assert(o1 == [0,1,2,3]);

    assert(stripZeroes(a1, 3, o1) == Inconsistent.no);
    assert(o1 == [1,2,3]);

    assert(stripZeroes(a1, 4, o1) == Inconsistent.yes);
    assert(o1 == []);

    assert(stripZeroes(a2, 1, o1) == Inconsistent.yes);
    assert(o1 == []);

    assert(stripZeroes(a2, 0, o1) == Inconsistent.no);
    assert(o1 == [1,2,3]);

    assert(stripZeroes(a3, 1, o1) == Inconsistent.yes);
    assert(o1 == []);

    assert(stripZeroes(a3, 0, o1) == Inconsistent.no);
    assert(o1 == []);
}

/*
  Given $(B bd), a sorted array of base dimensions, returns the exponents of the
  reduced dimension $(B ds).  $(B bd) is assumed to be a superset of the base
  dimensions of $(B ds).
*/
private QQ[] expandDimensions(BaseDimension[] bd, Dimension ds)
in
{
    /*
      FIXME_3: we can't have a superset that's empty, can we?
    */
    assert(bd.length > 0);
    assert(isSorted(bd));
    assert(reduce!((a,b) => a && b)
           (true, ds.fd.map!(a => canFind(bd, a.baseDimension))),
           "bd is not a superset of the base dimensions of ds.");
}
body
{
    FundamentalDimension[] fd = ds.fd;
    auto p = appender!(QQ[])();

    p.put(
        bd.map!((a) {
                if (fd.length == 0 || fd.front.baseDimension != a)
                {
                    return QQ(0);
                }
                else
                {
                    QQ r = fd.front.exponent;
                    fd.popFront();
                    return r;
                }
            }));
    assert(fd.length == 0);
    return p.data;
}

unittest
{
    enum e1 = expandDimensions([_bd1], dim1);
    enum e4 = expandDimensions([_bd1, _bd2], dim1);
    enum e5 = expandDimensions([_bd1, _bd3], dim4);

    static assert(e1 == [QQ(2)]);
    static assert(e4 == [QQ(2), QQ(0)]);
    static assert(e5 == [QQ(1), QQ(-1)]);
}

private QQ[][] createUnitMatrix(BaseUnit[] bu, BaseDimension[] bd)
{
    /*
      D_BUG_5
      This code gives compile error when compiled with -inline.
      return bu.map!(a => expandDimensions(bd, a.dimension)).array;
    */

    // using this for now...
    QQ[][] res = new QQ[][](bu.length, 0);
    foreach (i, x; bu)
    {
        res[i] = expandDimensions(bd, x.dimension);
    }
    return res;
}

unittest
{
    enum u1 = createUnitMatrix([baseUnit1, baseUnit2], [_bd1, _bd2, _bd3]);
    static assert(u1 == [[QQ(2/1),QQ(0/1),QQ(0/1)],[QQ(2/1),QQ(1/1),QQ(-2/1)]]);

    enum u2 = createUnitMatrix([], [_bd1, _bd2, _bd3]);
    static assert(u2 == []);
}

private BaseDimension[] findBaseDimensions(BaseUnit[] bu)
{
    return reduce!((a,b) => a ~ b)(
        (BaseDimension[]).init,
        bu.map!(a => a.dimension.fd.map!(a => a.baseDimension).array)
        ).stdsort.uniq.array;
}

unittest
{
    enum f1 = findBaseDimensions([baseUnit1]);
    static assert(f1 == [_bd1]);

    enum f2 = findBaseDimensions([baseUnit1, baseUnit2]);
    static assert(f2 == [_bd1, _bd2, _bd3]);

    enum f3 = findBaseDimensions([baseUnit2, baseUnit2]);
    static assert(f3 == [_bd1, _bd2, _bd3]);

    static assert(findBaseDimensions([]) == []);
}

private QQ[][] identityMatrix(size_t n)
in
{
    assert(n > 0);
}
body
{
    // D_BUG_6
    // we get compile error when compiling with -inline.
    return iota(0,n)
        .map!(r => iota(0,n).map!(c => c == r ? QQ(1) : QQ(0)).array)
        .array;
}

unittest
{
    enum id1 = identityMatrix(1);
    static assert(id1 == [[QQ(1)]]);

    enum id2 = identityMatrix(2);
    static assert(id2 == [[QQ(1),QQ(0)],[QQ(0),QQ(1)]]);

    enum id3 = identityMatrix(3);
    static assert(id3 == [[QQ(1),QQ(0),QQ(0)]
                          ,[QQ(0),QQ(1),QQ(0)]
                          ,[QQ(0),QQ(0),QQ(1)]]);
}

private QQ[][] makeSquareAndInvert(QQ[][] matrix)
in
{
    assert(matrix.length > 0);
}
body
{
    QQ[][] minv = identityMatrix(matrix[0].length).array;
    copy(retro(matrix).array, minv);
    minv = minv.retro.array;

    // Gauss-Jordan elimination from Numerical Recipes in C.
    auto mrow = minv[0].length;
    int[] indxc = new int[](mrow),
        indxr = new int[](mrow),
        ipiv  = new int[](mrow);

    for (int i; i < mrow; ++i)
    {
        int irow = -1, icol = -1;
        QQ big;
        for (int j; j < mrow; ++j)
        {
            if (ipiv[j] != 1)
            {
                for (int k; k < mrow; ++k)
                {
                    if (ipiv[k] == 0)
                    {
                        if (std.rational.abs(minv[j][k]) >= big)
                        {
                            big = std.rational.abs(minv[j][k]);
                            irow = j;
                            icol = k;
                        }
                    }
                    else
                    {
                        enforce(!(ipiv[k] > 1), "Singular Matrix.");
                    }
                }
            }
        }

        ++ipiv[icol];
        if (irow != icol)
        {
            for (int k; k < mrow; ++k)
            {
                swap(minv[irow][k], minv[icol][k]);
            }
        }

        indxr[i] = irow;
        indxc[i] = icol;
        enforce(minv[icol][icol] != 0, "Singular Matrix.");

        QQ pivinv = 1 / minv[icol][icol];
        minv[icol][icol] = QQ(1);
        for (int j; j < mrow; ++j)
        {
            minv[icol][j] = minv[icol][j] * pivinv;
        }

        for (int j; j < mrow; ++j)
        {
            if (j != icol)
            {
                QQ save = minv[j][icol];
                minv[j][icol] = QQ(0);
                for (int k; k < mrow; ++k)
                {
                    minv[j][k] = minv[j][k] - (minv[icol][k] * save);
                }
            }
        }
    }

    for (auto j = mrow-1; ; --j)
    {
        if (indxr[j] != indxc[j])
        {
            for (int k; k < mrow; ++k)
            {
                swap(minv[k][indxr[j]], minv[k][indxc[j]]);
            }
        }

        if (j == 0)
        {
            break;
        }
    }
    return minv;
}

unittest
{
    alias makeSquareAndInvert msi;

    enum QQ[][] m1 = [[QQ(1),QQ(2)],[QQ(3),QQ(4)]];
    static assert(msi(m1) == [[QQ(-2),  QQ(1)],
                              [QQ(3,2), QQ(-1,2)]]);

    enum QQ[][] m2 = [[QQ(3),QQ(5),QQ(7)]];
    static assert(msi(m2) == [[QQ(-7,3), QQ(-5,3), QQ(1,3)],
                              [QQ(0),    QQ(1),    QQ(0)],
                              [QQ(1),    QQ(0),    QQ(0)]]);
}

// TODO: unittest
private QQ[][] normalizeUnits(BaseUnit[] bu)
{
    return makeSquareAndInvert(createUnitMatrix(bu, findBaseDimensions(bu)));
}

// TODO: unittest
private Inconsistent calculateBaseUnitExponents(BaseUnit[] bu, Dimension ds,
                                                out QQ[] result)
{
    if (isSimpleSystem(bu))
    {
        result = expandDimensions(findBaseDimensions(bu), ds);
        return Inconsistent.no;
    }
    else
    {
        auto bsd = findBaseDimensions(bu);
        auto normalized = makeSquareAndInvert(createUnitMatrix(bu, bsd));
        auto units = multiplyAddUnits(expandDimensions(bsd, ds), normalized);
        auto extra = normalized.length - bu.length;
        return stripZeroes(units, extra, result);
    }
}

// homogeneous_system.hpp
private struct HomogeneousSystem
{
    BaseUnit[] bu;

    HomogeneousSystem opBinary(string op)(QQ r) @safe pure nothrow
    if (op == "^" || op == "^^")
    {
        return this;
    }

    void toString(scope void delegate(const(char)[]) sink) const
    {
        sink(xformat("Homogeneous< %-(%s_bu(..)%|, %) >",
                     map!(a => a.name)(bu)));
    }
}

private template isHomogeneousSystem(T)
{
    enum bool isHomogeneousSystem = is(T == HomogeneousSystem);
}

// TODO: unittest
private string rawString(HomogeneousSystem hs)
{
    return xformat("HomogeneousSystem([%-(%s,%)])",
                   hs.bu.map!(a => rawString(a)));
}

/**
   Returns a homogeneous system that can represent any combination of the base
   units.  There must be no way to represent any of the base units in terms of
   the others.
*/
/*
  FIXME_4: I think in Boost.units this is enforced when check_system is called.
  Enabling checkSystem in Unit is expensive.
*/
// make_system.hpp
public template makeSystem(BU...)
{
    enum HomogeneousSystem makeSystem = HomogeneousSystem([BU].stdsort.array);
}

version (unittest)
{
    alias makeSystem!( siMeterBaseUnit
                     , siKilogramBaseUnit
                     , siSecondBaseUnit
                     , siAmpereBaseUnit
                     , siKelvinBaseUnit
                     , siMoleBaseUnit
                     , siCandelaBaseUnit
                     , angleRadianBaseUnit
                     , angleSteradianBaseUnit
                     ) siSystem;
}

unittest
{
    alias makeSystem!(baseUnit2, baseUnit1) System1;
    static assert(System1.bu == [baseUnit1, baseUnit2]);
}

// TODO: unittest
private bool checkSystem(HomogeneousSystem s, Dimension d)
{
    QQ[] result;
    return calculateBaseUnitExponents(s.bu, d, result) == Inconsistent.yes
        ? false : true;
}

// heterogeneous_system.hpp
private struct HeterogeneousDimension
{
    BaseUnit baseUnit; // tag_type
    QQ exponent;        // value_type

    HeterogeneousDimension opBinary(string op)(HeterogeneousDimension other)
    @safe pure if (op == "+")
    {
        assert(this.baseUnit == other.baseUnit);
        return HeterogeneousDimension(other.baseUnit,
                                      this.exponent + other.exponent);
    }
    
    HeterogeneousDimension opBinary(string op)(QQ r) @safe pure
    if (op == "*" || op == "/")
    {
        return HeterogeneousDimension(this.baseUnit,
                                      mixin("this.exponent" ~ op ~ "r"));
    }

    HeterogeneousDimension opUnary(string op)() @safe pure
    if (op == "-")
    {
        return HeterogeneousDimension(this.baseUnit, -this.exponent);
    }

    int opCmp(HeterogeneousDimension d) @safe pure
    {
        return this.baseUnit.opCmp(d.baseUnit);
    }

    bool opEquals(HeterogeneousDimension d) @safe pure
    {
        return this.baseUnit.opEquals(d.baseUnit);
    }

    void toString(scope void delegate(const(char)[]) sink,
                  FormatSpec!char fmt) const
    {
        sink(xformat("%" ~ fmt.spec, this.baseUnit));
        if (this.exponent != QQ(1))
        {
            if (this.exponent.den == 1)
            {
                sink(xformat("^%s", this.exponent.num));
            }
            else
            {
                sink(xformat("^%s", this.exponent));
            }
        }
    }
}

unittest
{
    // TODO: finish the unittests
    enum HeterogeneousDimension h1 = HeterogeneousDimension(baseUnit1, QQ(2));
    enum HeterogeneousDimension h2 = HeterogeneousDimension(baseUnit1, QQ(3));
    enum h3 = h1 / QQ(3);
    enum h4 = h1 + h2;
    enum h5 = -h1;
}

private string rawString(HeterogeneousDimension hd)
{
    return xformat("HeterogeneousDimension(%s,%s)",
                   rawString(hd.baseUnit), rawString(hd.exponent));
}

unittest
{
  // TODO:
}


/*
  A system that can represent any possible combination of units at the expense
  of not preserving information about how it was created.
*/
private struct HeterogeneousSystem
{
    HeterogeneousDimension[] hd;
    FundamentalDimension[] fd;
    Scale[] sc;

    @property static HeterogeneousSystem dimensionless()
    {
        return HeterogeneousSystem([], [], []);
    }

    HeterogeneousSystem opBinary(string op)(HeterogeneousSystem other) @safe pure
    if (op == "*")
    {
        return HeterogeneousSystem(merge(this.hd, other.hd),
                                   merge(this.fd, other.fd),
                                   merge(this.sc, other.sc));
    }

    HeterogeneousSystem opBinary(string op)(HeterogeneousSystem other) @safe pure
    if (op == "/")
    {
        return HeterogeneousSystem(merge(this.hd, inverse(other.hd)),
                                   merge(this.fd, inverse(other.fd)),
                                   merge(this.sc, inverse(other.sc)));
    }

    HeterogeneousSystem opBinary(string op)(QQ ex) if (op == "^")
    {
        return HeterogeneousSystem(
            this.hd.map!(a => a * ex).array,
            this.fd.map!(a => a * ex).array,
            this.sc.map!(a => a * ex).array);
    }

/*
  This is implemented in Boost.units, but never used as far as I can tell. And
  it doesn't work, either.  The problem is with Scale[]^r, because it is not
  implemented, not here nor in Boost.units.

  HeterogeneousSystem opBinary(string op)(QQ ex) if (op == "^^")
  {
    auto p1 = appender!(HeterogeneousDimension[])();
    p1.put(map!(a => a / ex)(this.hd));
    auto p2 = appender!(FundamentalDimension[])();
    p2.put(map!(a => a / ex)(this.fd));
    auto p3 = appender!(Scale[])();
    p3.put(map!(a => a / ex)(this.sc));

    return HeterogeneousSystem(p1.data, p2.data, p3.data);
  }
*/

    void toString(scope void delegate(const(char)[]) sink) const
    {
        sink(xformat("Heterogeneous< {%(%s, %)}, {%(%s, %)}, {%(%s, %)} >",
                     hd, fd, sc));
    }
}

unittest
{
    // TODO: finish unittest
    enum h1 = HeterogeneousSystem([],[],[]);
    enum h2 = HeterogeneousSystem([],[],[]);
    enum h3 = h1 * h2;

    enum h4 = h1 ^ QQ(3);
}

private string rawString(HeterogeneousSystem hs)
{
    return xformat("HeterogeneousSystem([%-(%s,%)],[%-(%s,%)],[%-(%s,%)])",
                   hs.hd.map!(a => rawString(a)).array,
                   hs.fd.map!(a => rawString(a)).array,
                   hs.sc.map!(a => rawString(a)).array);
}

/*
   Check to see if $(B T) is a HeterogeneousSystem.
*/
private template isHeterogeneousSystem(T)
{
    enum bool isHeterogeneousSystem = is(T == HeterogeneousSystem);
}

private HeterogeneousSystem makeHeterogeneousSystem(Dimension dimension,
                                                    BaseUnit[] system)
{
    HeterogeneousDimension[] impl(BaseUnit[] units, QQ[] exs)
    {
        auto p = appender!(HeterogeneousDimension[])();
        foreach (i, e; units)
        {
            if (exs[i].num == 0)
            {
                continue;
            }
            p.put(HeterogeneousDimension(e, exs[i]));
        }
        //return p.data;
        return p.data.length ? p.data : []; // D_BUG_1
    }

    QQ[] exponents;
    auto isInconsistent =
        calculateBaseUnitExponents(system, dimension, exponents);
    assert(!isInconsistent,
           "The Specified Dimension Is Not Representible In The Given System.");
    HeterogeneousDimension[] unitList = impl(system, exponents);
    return HeterogeneousSystem(unitList, dimension.fd, []);
}

unittest
{
  // TODO:
}

private template MakeHeterogeneousUnit(alias bu, alias dimensions)
if (isBaseUnit!(typeof(bu)) && isDimension!(typeof(dimensions)))
{
    alias Unit!(dimensions,
                HeterogeneousSystem(
                    [HeterogeneousDimension(bu, QQ(1))],
                    dimensions.fd,
                    [])) MakeHeterogeneousUnit;
}

unittest
{
  // TODO:
}

/**
   Returns the unit corresponding to base unit $(B bu).
*/
public template UnitOf(alias bu) if (isBaseUnit!(typeof(bu)))
{
    enum dimension = bu.dimension;
    alias MakeHeterogeneousUnit!(bu, dimension) UnitOf;
}

// detail/heterogeneous_conversion.hpp
// http://rosettacode.org/wiki/Reduced_row_echelon_form#D
private T[][] toReducedRowEchelonForm(T)(T[][] mat)
{
    if (mat.length == 0)
    {
        return [];
    }

    T[][] ret = mat.map!(a => a.dup).array;
    immutable nrows = ret.length;
    immutable ncols = ret[0].length;
 
    size_t lead;
    foreach (r; 0 .. nrows)
    {
        if (ncols <= lead)
        {
            return ret;
        }

        size_t i = r;
        while (ret[i][lead] == 0)
        {
            i++;
            if (nrows == i)
            {
                i = r;
                lead++;
                if (ncols == lead)
                {
                    return ret;
                }
            }
        }
        swap(ret[i], ret[r]);
        ret[r] = ret[r].map!(a => a /= ret[r][lead]).array;

        foreach (j; filter!(j => j != r)(iota(0, ret.length)))
        {
            ret[j] = iota(0, ret[j].length)
                .map!(c => ret[j][c] - (ret[r][c] * ret[j][lead])).array;
        }
        lead++;
    }
    return ret;
}

unittest
{
    enum int[][] m1 = [[ 1, 2, -1, -4 ]
                       ,[ 2, 3, -1, -11]
                       ,[-2, 0, -3,  22]];

    enum int[][] r1 = [[1, 0, 0, -8]
                       ,[0, 1, 0,  1]
                       ,[0, 0, 1, -2]];

    static assert(toReducedRowEchelonForm(m1) == r1);

    enum QQ[][] m2 = [[QQ( 1), QQ(2), QQ(-1), QQ(-4) ]
                      ,[QQ( 2), QQ(3), QQ(-1), QQ(-11)]
                      ,[QQ(-2), QQ(0), QQ(-3), QQ( 22)]];

    enum QQ[][] r2 = [[QQ(1), QQ(0), QQ(0), QQ(-8)]
                      ,[QQ(0), QQ(1), QQ(0), QQ( 1)]
                      ,[QQ(0), QQ(0), QQ(1), QQ(-2)]];

    static assert(toReducedRowEchelonForm(m2) == r2);
}

private bool isLinearlyIndependent1(T)(T[][] mat)
in
{
    assert(mat.length > 0);
}
body
{
    foreach (row; toReducedRowEchelonForm(mat))
    {
        if (reduce!"a + b"(row) == 0)
        {
            return false;
        }
    }
    return true;
}

/*
  FIXME_5:
  This uses the Bareiss algorithm.  It produces correct results with square
  matrices only, and I can't figure out why.  As far as I can tell, this is the
  algorithm used in BOOST.units (see detail/heterogeneous_conversion.hpp),
  and it would be preferable to use this.
*/
private bool isLinearlyIndependent2(T)(T[][] mat)
in
{
    assert(mat.length > 0);
    //assert(mat.length == mat[0].length);
}
body
{
    T[][] _mat = mat.map!(a => a.dup).array;
    immutable nrows = _mat.length;
    immutable ncols = _mat[0].length;

    foreach (k; 0 .. nrows-1)
    {
        foreach (i; k+1 .. nrows)
        {
            foreach (j; k+1 .. ncols)
            {
                _mat[i][j] = _mat[k][k] * _mat[i][j] - _mat[k][j] * _mat[i][k];
                if (_mat[i][j] == 0)
                {
                    return false;
                }
            }
        }
    }
    return true;
}

unittest
{
    enum QQ[][] a = [[QQ(2), QQ( 5), QQ(3)]
                     ,[QQ(1), QQ( 1), QQ(1)]
                     ,[QQ(4), QQ(-2), QQ(0)]];

    static assert(isLinearlyIndependent1(a));
    //static assert(isLinearlyIndependent2(a));

    enum QQ[][] b = [[QQ( 4), QQ( 1), QQ(-2)]
                     ,[QQ(-3), QQ( 0), QQ( 1)]
                     ,[QQ( 1), QQ(-2), QQ( 1)]];

    static assert(!isLinearlyIndependent1(b));
    //static assert(!isLinearlyIndependent2(b));

    enum QQ[][] c = [[QQ(2), QQ(-2), QQ(4)]
                     ,[QQ(3), QQ(-5), QQ(4)]
                     ,[QQ(0), QQ( 1), QQ(1)]];

    static assert(!isLinearlyIndependent1(c));
    //static assert(!isLinearlyIndependent2(c));

    enum int[][] d = [[1,2,3]
                      ,[4,5,6]];

    static assert(!isLinearlyIndependent1(d));
    //static assert(!isLinearlyIndependent2(d));

    enum int[][] e = [[1,2,3]
                      ,[4,5,1]];

    static assert(isLinearlyIndependent1(e));
    //static assert(isLinearlyIndependent2(e));
}

private BaseUnit[] extractBaseUnits(HeterogeneousDimension[] hd)
{
    return hd.map!(a => a.baseUnit).array;
}

private HomogeneousSystem makeHomogeneousSystem(BaseUnit[] bu)
{
    BaseDimension[] bd = findBaseDimensions(bu);
    BaseUnit[] result;

    foreach (x; bu)
    {
        BaseUnit[] tmp = result ~ x;
        QQ[][] dims = tmp.map!(a => expandDimensions(bd, a.dimension)).array;
        result = dims.length && dims.isLinearlyIndependent1 ? tmp : result;
    }
    return HomogeneousSystem(result.stdsort.array);
}

unittest
{
    version (none) {
        enum HomogeneousSystem s1 =
            makeHomogeneousSystem([si.kilogramBaseUnit,
                                   cgs.centimeterBaseUnit,
                                   cgs.gramBaseUnit,
                                   si.meterBaseUnit]);
        // TODO: check results against BOOST.units
        static assert(s1.bu == [cgs.centimeterBaseUnit, si.kilogramBaseUnit]);
    }
}

// quantity.hpp
/// struct representing a quantity.
public struct Quantity(U, Y = double)
if ((isUnit!U || isAbsolute!U) && !isUnit!Y && !isAbsolute!Y)
{
    static if (!isAbsolute!U)
    {
        alias U UnitType; ///
    }
    else
    {
        alias U.ValueType UnitType;
    }
    alias Y ValueType; ///

    private ValueType val;

    private enum bool isDimensionless = isDimensionlessUnit!UnitType &&
        UnitType.hasDimensionlessSystem;

    static if (isDimensionless)
    {
        ///
        this()(ValueType val) @safe pure nothrow // 314
        {
            this.val = val;
        }

        ///
        //this(V : ValueType, U2)(Quantity!(U2, V) source) @safe pure nothrow // 380
        //if (UnitType.system != U2.system && U2.hasDimensionlessSystem)
        this(Qu)(Qu source) @safe pure nothrow
        if (isQuantity!Qu && is(Qu.ValueType : ValueType) &&
            UnitType.system != Qu.UnitType.system &&
            Qu.UnitType.hasDimensionlessSystem)
        {
            this.val = source.val;
        }

        ///
        //this(V, U2)(Quantity!(U2, V) source) @safe pure nothrow // 436
        //if (isDimensionlessUnit!U2 && !U2.hasDimensionlessSystem)
        this(Qu)(Qu source) @safe pure nothrow
        if (isQuantity!Qu && isDimensionlessUnit!(Qu.UnitType) &&
            !Qu.UnitType.hasDimensionlessSystem)
        {
            //this.val = convert!(Quantity!(U2, V), Quantity)(source).val;
            this.val = convert!(Qu, Quantity)(source).val;
        }

        ///
        ref Quantity opAssign(T : ValueType)(T val) @safe pure nothrow
        {
            this.val = val;
            return this;
        }

        ///
        ref Quantity opAssign(Qu)(Qu source) @safe pure nothrow
        if (isQuantity!Qu && is(Qu.ValueType : ValueType) &&
            isDimensionlessUnit!(Qu.UnitType) &&
            Qu.UnitType.hasDimensionlessSystem)
        // 367, 447
        {
            this.val = source.val;
            return this;
        }

        ///
        ref Quantity opOpAssign(string op)(Quantity source) @safe pure nothrow
        if (op == "+" || op == "-")
        {
            mixin("this.val" ~ op ~ "= source.val;");
            return this;
        }
    }
    else
    {
        private this()(ValueType val) @safe pure nothrow // 287
        {
            this.val = val;
        }

        ///
        //this(V : ValueType, U2)(Quantity!(U2, V) source) @safe pure nothrow // 200
        //if (!is(U2 == UnitType) && isImplicitlyConvertible!(U2, UnitType))
        this(Qu)(Qu source)
        if (isQuantity!Qu && is(Qu.ValueType : ValueType) &&
            !is(Qu.UnitType == UnitType)
            //&& isImplicitlyConvertible!(Qu.UnitType, UnitType)
            )
        {
            //this.val = convert!(Quantity!(U2, V), Quantity)(source).val;
            this.val = convert!(Qu, Quantity)(source).val;
        }

        ///
        //ref Quantity opAssign(T : ValueType)(Quantity!(UnitType, T) source) @safe pure nothrow
        ref Quantity opAssign(T : ValueType)(Quantity!(U, T) source) @safe pure nothrow
        // 168, also covers 127
        {
            this.val = source.val;
            return this;
        }

        ///
        //ref Quantity opOpAssign(string op, U2, V)(Quantity!(U2, V) source)
        //@safe pure nothrow if (op == "+" || op == "-" || op == "*" || op == "/")
        ref Quantity opOpAssign(string op, Qu)(Qu source) @safe pure nothrow
        if ((op == "+" || op == "-" || op == "*" || op == "/") && isQuantity!Qu)
        {
            static assert(is(typeof(mixin("UnitType()"~op~"Qu.UnitType()")) == UnitType),
                          op ~ "= produces incompatible unit types.");
            mixin("this.val" ~ op ~ "= source.val;");
            return this;
        }

        ///
        //ref Quantity opAssign(V : ValueType, U2)(Quantity!(U2, V) source) //@safe pure nothrow
        // 230
        //if (!is(U2 == UnitType) && isImplicitlyConvertible!(U2, UnitType))
        ref Quantity opAssign(Qu)(Qu source)
        if (isQuantity!Qu && is(Qu.ValueType : ValueType) &&
            !is(Qu.UnitType == UnitType)
            //&& isImplicitlyConvertible!(Qu.UnitType, UnitType)
            )
        {
            this.val = convert!(Qu, Quantity)(source).val;
            return this;
        }
    }

    ///
    //this(T : ValueType)(Quantity!(UnitType, T) source) //@safe pure nothrow // 137, 336
    this(T : ValueType)(Quantity!(U, T) source) @safe pure nothrow
    {
        this.val = source.val;
    }

    ///
    @property ValueType value() @safe const pure nothrow // 242, 460
    {
        return this.val;
    }

    ///
    ref opOpAssign(string op)(ValueType source) @safe pure nothrow
    if (op == "*" || op == "/")
    {
        mixin("this.val"~op~"= source;");
        return this;
    }

    /// Used to apply a function to the value of this quantity.
    @property Quantity opDispatch(string fn)()
    {
        return Quantity(mixin(fn ~ "(value)"));
    }

    ///
    Quantity opUnary(string op)() @safe const pure nothrow if (op == "-")
    {
        return Quantity(-value);
    }

    /// quantity * value and quantity / value
    Quantity opBinary(string op, N)(N x) @safe const pure nothrow
    if ((op == "*" || op == "/") && !isUnit!N && !isQuantity!N)
    {
        return Quantity(mixin("this.val" ~ op ~ "x"));
    }

    /// value * quantity and value / quantity
    auto opBinaryRight(string op, N)(N val) @safe const pure nothrow
    if ((op == "*" || op == "/") && !isUnit!N && !isQuantity!N)
    {
        static if (op == "/")
        {
            return Quantity!(UnitType.power!(QQ(-1)),
                             ValueType)(val / this.val);
        }
        else
        {
            return Quantity(val * this.val);
        }
    }

    /// quantity * unit and quantity / unit
    auto opBinary(string op, U)(U u) @safe const pure nothrow
    if ((op == "*" || op == "/") && isUnit!U)
    {
        return Quantity!(mixin("typeof(UnitType()" ~ op ~ "U())"),
                         ValueType)(this.val);
    }

    /// unit * quantity and unit / quantity
    auto opBinaryRight(string op, U)(U u) @safe const pure nothrow
    if ((op == "*" || op == "/") && isUnit!U)
    {
        static if (op == "/")
        {
            enum ValueType one = 1;
            return Quantity!(typeof(U() / UnitType()),
                             ValueType)(one / this.val);
        }
        else
        {
            return Quantity!(mixin("typeof(U()" ~ op ~ "UnitType())"),
                             ValueType)(this.val);
        }
    }

    /// quantityA + quantityA and quantityA - quantityA
    Quantity opBinary(string op)(Quantity other) @safe const pure nothrow
    if (op == "+" || op == "-")
    {
        return Quantity(mixin("this.val" ~ op ~ "other.val"));
    }

    /// quantity * quantity and quantity / quantity
    auto opBinary(string op, Qu)(Qu other) @safe const pure nothrow
    if ((op == "*" || op == "/") && isQuantity!Qu)
    {
        return Quantity!(
            mixin("typeof(UnitType()" ~ op ~ "Qu.UnitType())"),
            CommonType!(ValueType, Qu.ValueType)
            )(mixin("this.val" ~ op ~ "other.val"));
    }

    /// Raises the quantity as a whole to the power of $(B r).
    @property auto power(alias r)() @safe const pure nothrow
    if (isRational!(typeof(r)) || isIntegral!(typeof(r)))
    {
        static if (isRational!(typeof(r)))
        {
            alias r R;
        }
        else
        {
            /*
              D_BUG_7
              either r needs to be cast to long or use QQ directory when
              r is an integer.
              enum QQ R = rational(r); // error
            */
            enum QQ R = QQ(r);
        }
        static assert(
            __traits(compiles,std.math.pow(ValueType.init,
                                           R.value!ValueType)),
            "Value type YY in Quantity not supported by std.math.pow().");

        return Quantity!(UnitType.power!R, ValueType)
            (std.math.pow(this.val, R.value!ValueType));
    }

    /// Returns the root value of the quantity as a whole.
    @property auto root(alias r)() @safe const pure nothrow
    if (isRational!(typeof(r)) || isIntegral!(typeof(r)))
    {
        static if (isRational!(typeof(r)))
        {
            alias r R;
            enum QQ _1_R = 1 / R;
        }
        else
        {
            enum QQ R = QQ(r);
            enum QQ _1_R = 1 / R;
        }

        static assert(
            __traits(compiles,std.math.pow(ValueType.init,
                                           _1_R.value!ValueType)),
            "Value type YY in Quantity not supported by std.math.pow().");

        return Quantity!(UnitType.root!R, ValueType)
            (std.math.pow(this.val, _1_R.value!ValueType));
    }

    void toString(scope void delegate(const(char)[]) sink, string fmt) const
    {
        /*
          FIXME_6: ValueType is supported by all the FormatChars already in
          phobos, and we have implemented three new FormatChars 'y', 'n', 'r'
          for UnitType.  Creating new FormatChars to support all the
          different combinations seems impractical.  For now we'll hardcode
          to use 'y' for UnitTypes.
         */
        sink(xformat(fmt ~ " %y", this.val, U()));
    }
}

unittest // TODO:
{
    alias siSystem Homo;
    enum Hete = makeHeterogeneousSystem(lengthDim, Homo.bu);

    alias Unit!(Dimension.dimensionless, Homo) Unit1;
    alias Unit!(Dimension.dimensionless, Hete) Unit2;
    alias Unit!(lengthDim, Homo) Unit3;

    alias Absolute!(Unit3) Abs1;

    alias Quantity!(Unit1) Qu1;
    alias Quantity!(Unit2) Qu2;
    alias Quantity!(Unit3) Qu3;
    alias Quantity!(Abs1) Qu4;

    /*
      FIXME_7:
      Waiting for Boost.units devs to confirm which ones are bugs.

      Qu4 a = 3.2 * Abs1();
      writeln(a);
      writeln(a * a);
      writeln(a * Unit3());
      //writeln(a * Abs1()); // error
    */


    // TODO
    // (-q1);
    // (q1 - q1);
    // (q1 + q1);
    // (q1 * 4);
    // (q1 / 4);
    // (4 * q1);
    // (4 / q1);
  
    // (q1 * meters);
    // (q1 / meters);
    // (meters * q1);
    // (meters / q1);
    // (q1 * q1);
    // (q1 / q1);
    // (q1.power!(3));
    // (q1.power!(QQ(3)));
    // (q1.root!(4));
    // (q1.root!(QQ(4)));
}

/**
   Check to see if $(B T) is a Quantity.
*/
public template isQuantity(T)
{
    static if(is(T X == Quantity!(U, S), U, S))
    {
        enum bool isQuantity = true;
    }
    else
    {
        enum bool isQuantity = false;
    }
}

/**
   Check to see if $(B Q) is a dimensionless quantity.
*/
public template isDimensionlessQuantity(Q) if (isQuantity!Q)
{
    enum bool isDimensionlessQuantity = isDimensionlessUnit!(Q.UnitType);
}

private template isImplicitlyConvertible(T1, T2)
{
  enum bool isImplicitlyConvertible = is(ReduceUnit!(T1) == ReduceUnit!(T2));
}

/**
   A wrapper to represent absolute units (points rather than vectors).
*/
public struct Absolute(Y)
{
    alias Y ValueType;
    private ValueType val;

    @property ValueType value() const
    {
        return this.val;
    }

    Absolute opBinary(string op)(ValueType val) if (op == "+" || op == "-")
    {
        return Absolute(mixin("this.val" ~ op ~ "val"));
    }

    Absolute opBinaryRight(string op)(ValueType val) if (op == "+")
    {
        return this.opBinary!(op)(val);
    }

    ValueType opBinary(string op)(Absolute other) if (op == "-")
    {
        return this.val - other.val;
    }

    Quantity!(Absolute, T) opBinary(string op, T)(T t) @safe pure nothrow
    if (op == "*" )
    {
        return Quantity!(Absolute, T)(t);
    }

    Quantity!(Absolute, T) opBinaryRight(string op, T)(T t) @safe pure nothrow
    if (op == "*")
    {
        return this.opBinary!(op, T)(t);
    }

    // only for non-Unit ValueTypes.
    ref Absolute opOpAssign(string op)(ValueType val) @safe pure nothrow
    if (op == "+" || op == "-")
    {
        mixin("this.val" ~ op ~ "= val;");
        return this;
    }

    void toString(scope void delegate(const(char)[]) sink,
                  FormatSpec!char fmt) const
    {
        sink(xformat("absolute %" ~ fmt.spec, this.val));
    }
}


/**
   Check to see if $(B T) is an Absolute.
*/
public template isAbsolute(T)
{
    static if (is(T X == Absolute!(U), U))
    {
        enum bool isAbsolute = true;
    }
    else
    {
        enum bool isAbsolute = false;
    }
}


//physical_dimensions/*.hpp
// base dimensions.
alias baseDimension!"amount"            amountBaseDimension;
alias baseDimension!"current"           currentBaseDimension;
alias baseDimension!"length"            lengthBaseDimension;
alias baseDimension!"luminousIntensity" luminousIntensityBaseDimension;
alias baseDimension!"mass"              massBaseDimension;
alias baseDimension!"planeAngle"        planeAngleBaseDimension;
alias baseDimension!"solidAngle"        solidAngleBaseDimension;
alias baseDimension!"temperature"       temperatureBaseDimension;
alias baseDimension!"time"              timeBaseDimension;

private alias amountBaseDimension            bd1;
private alias currentBaseDimension           bd2;
private alias lengthBaseDimension            bd3;
private alias luminousIntensityBaseDimension bd4;
private alias massBaseDimension              bd5;
private alias planeAngleBaseDimension        bd6;
private alias solidAngleBaseDimension        bd7;
private alias temperatureBaseDimension       bd8;
private alias timeBaseDimension              bd9;

// dimensions.
alias dimension!(bd3,  2, bd9, -2)                            absorbedDoseDimension;
alias dimension!(bd3,  1, bd9, -2)                            accelerationDimension;
alias dimension!(bd3,  2, bd5,  1, bd9, -1)                   actionDimension;
alias dimension!(bd9, -1)                                     activityDimension;
alias dimension!(bd1,  1)                                     amountDimension;
alias dimension!(bd9, -2, bd6,  1)                            angularAccelerationDimension;
alias dimension!(bd3,  2, bd5,  1, bd9, -1, bd6, -1)          angularMomentumDimension;
alias dimension!(bd9, -1, bd6,  1)                            angularVelocityDimension;
alias dimension!(bd3,  2)                                     areaDimension;
alias dimension!(bd3, -2, bd5, -1, bd9,  4, bd2,  2)          capacitanceDimension;
alias dimension!(bd9, -1, bd1,  1)                            catalyticActivityDimension;
alias dimension!(bd3, -2, bd5, -1, bd9,  3, bd2,  2)          conductanceDimension;
alias dimension!(bd3, -3, bd5, -1, bd9,  3, bd2,  2)          conductivityDimension;
alias dimension!(bd2,  1)                                     currentDimension;
alias dimension!(bd3,  2, bd9, -2)                            doseEquivalentDimension;
alias dimension!(bd5,  1, bd3, -1, bd9, -1)                   dynamicViscosityDimension;
alias dimension!(bd9,  1, bd2,  1)                            electricChargeDimension;
alias dimension!(bd3,  2, bd5,  1, bd9, -3, bd2, -1)          electricPotentialDimension;
alias dimension!(bd3, -1, bd5,  1, bd9, -2)                   energyDensityDimension;
alias dimension!(bd3,  2, bd5,  1, bd9, -2)                   energyDimension;
alias dimension!(bd3,  1, bd5,  1, bd9, -2)                   forceDimension;
alias dimension!(bd9, -1)                                     frequencyDimension;
alias dimension!(bd3,  2, bd5,  1, bd9, -2, bd8, -1)          heatCapacityDimension;
alias dimension!(bd3, -2, bd4,  1, bd7,  1)                   illuminanceDimension;
alias dimension!(bd3,  2, bd5,  1, bd9, -3, bd2, -2)          impedanceDimension;
alias dimension!(bd3,  2, bd5,  1, bd9, -2, bd2, -2)          inductanceDimension;
alias dimension!(bd3,  2, bd9, -1)                            kinematicViscosityDimension;
alias dimension!(bd3,  1)                                     lengthDimension;
alias dimension!(bd3, -2, bd4,  1)                            luminanceDimension;
alias dimension!(bd4,  1, bd7,  1)                            luminousFluxDimension;
alias dimension!(bd4,  1)                                     luminousIntensityDimension;
alias dimension!(bd3, -1, bd2,  1)                            magneticFieldIntensityDimension;
alias dimension!(bd5,  1, bd9, -2, bd2, -1)                   magneticFluxDensityDimension;
alias dimension!(bd3,  2, bd5,  1, bd9, -2, bd2, -1)          magneticFluxDimension;
alias dimension!(bd3, -3, bd5,  1)                            massDensityDimension;
alias dimension!(bd5,  1)                                     massDimension;
alias dimension!(bd3,  2, bd5,  1, bd9, -2, bd1, -1)          molarEnergyDimension;
alias dimension!(bd3,  2, bd5,  1, bd9, -2, bd8, -1, bd1, -1) molarHeatCapacityDimension;
alias dimension!(bd3,  2, bd5,  1, bd6, -2)                   momentOfInertiaDimension;
alias dimension!(bd3,  1, bd5,  1, bd9, -1)                   momentumDimension;
alias dimension!(bd3,  1, bd5,  1, bd9, -2, bd2, -2)          permeabilityDimension;
alias dimension!(bd3, -3, bd5, -1, bd9,  4, bd2,  2)          permittivityDimension;
alias dimension!(bd6,  1)                                     planeAngleDimension;
alias dimension!(bd3,  2, bd5,  1, bd9, -3)                   powerDimension;
alias dimension!(bd3, -1, bd5,  1, bd9, -2)                   pressureDimension;
alias dimension!(bd3, -2, bd5, -1, bd9,  2, bd2,  2)          reluctanceDimension;
alias dimension!(bd3,  2, bd5,  1, bd9, -3, bd2, -2)          resistanceDimension;
alias dimension!(bd3,  3, bd5,  1, bd9, -3, bd2, -2)          resistivityDimension;
alias dimension!(bd7,  1)                                     solidAngleDimension;
alias dimension!(bd3,  2, bd9, -2)                            specificEnergyDimension;
alias dimension!(bd3,  2, bd9, -2, bd8, -1)                   specificHeatCapacityDimension;
alias dimension!(bd3,  3, bd5, -1)                            specificVolumeDimension;
alias dimension!(bd3, -1, bd5,  1, bd9, -2)                   stressDimension;
alias dimension!(bd3, -2, bd5,  1)                            surfaceDensityDimension;
alias dimension!(bd5,  1, bd9, -2)                            surfaceTensionDimension;
alias dimension!(bd8,  1)                                     temperatureDimension;
alias dimension!(bd3,  1, bd5,  1, bd9, -3, bd8, -1)          thermalConductivityDimension;
alias dimension!(bd9,  1)                                     timeDimension;
alias dimension!(bd3,  2, bd5,  1, bd9, -2, bd6, -1)          torqueDimension;
alias dimension!(bd3,  1, bd9, -1)                            velocityDimension;
alias dimension!(bd3,  3)                                     volumeDimension;
alias dimension!(bd3, -1)                                     wavenumberDimension;

private string instanceOf(string unit)(string i1, string[] nth...)
{
    string res = "enum " ~ unit ~ " " ~ i1 ~ " = " ~ unit ~ "()";
    foreach (i; nth)
    {
        res ~= ", " ~ i ~ " = " ~ unit ~ "()";
    }
    return res ~= ";";
}

struct angle
{
    alias scaledBaseUnit!(degreeBaseUnit, scale(60, -1), "arcminute", `'`)     arcminuteBaseUnit;
    alias scaledBaseUnit!(degreeBaseUnit, scale(3600, -1), "arcsecond", `"`)   arcsecondBaseUnit;
    alias baseUnitWithConversion!("degree", "deg", radianBaseUnit, "PI/180")   degreeBaseUnit;
    alias baseUnitWithConversion!("gradian", "grad", radianBaseUnit, "PI/200") gradianBaseUnit;
    alias baseUnit!(planeAngleDimension, "radian", "rad")                      radianBaseUnit;
    alias scaledBaseUnit!(degreeBaseUnit, scale(360, 1), "revolution", "rev")  revolutionBaseUnit;
    alias baseUnit!(solidAngleDimension, "steradian", "sr")                    steradianBaseUnit;

    // struct degree
    // {
    //     alias makeSystem!(degreeBaseUnit) system;

    //     alias Unit!(planeAngleDimension, system) PlaneAngle;

    //     mixin(instanceOf!"PlaneAngle"("degree", "degrees"));
    // }

    // struct gradian
    // {
    //     alias makeSystem!(gradianBaseUnit) system;

    //     alias Unit!(planeAngleDimension, system) PlaneAngle;

    //     mixin(instanceOf!"PlaneAngle"("gradian", "gradians"));
    // }

    // struct revolution
    // {
    //     alias makeSystem!(revolutionBaseUnit) system;

    //     alias Unit!(planeAngleDimension, system) PlaneAngle;

    //     mixin(instanceOf!"PlaneAngle"("revolution", "revolutions"));
    // }
}


struct astronomical
{
    alias baseUnitWithConversion!( "astronomical unit"
                                 , "a.u."
                                 , si.meterBaseUnit
                                 , "149597870691.0L"
                                 ) astronomicalUnitBaseUnit;

    alias baseUnitWithConversion!( "light second"
                                 , "lsc"
                                 , si.meterBaseUnit
                                 , "2.99792458e8L"
                                 ) lightSecondBaseUnit;

    alias baseUnitWithConversion!( "parsec"
                                 , "psc"
                                 , si.meterBaseUnit
                                 , "3.0856775813e16L"
                                 ) parsecBaseUnit;

    alias scaledBaseUnit!(lightSecondBaseUnit, scale(86400, 1), "light day", "ldy")    lightDayBaseUnit;
    alias scaledBaseUnit!(lightSecondBaseUnit, scale(3600, 1), "light hour", "lhr")    lightHourBaseUnit;
    alias scaledBaseUnit!(lightSecondBaseUnit, scale(60, 1), "light minute", "lmn")    lightMinuteBaseUnit;
    alias scaledBaseUnit!(lightSecondBaseUnit, scale(31557600, 1), "light year", "ly") lightYearBaseUnit;
}


struct si
{
    alias baseUnit!(currentDimension, "ampere", "A")             ampereBaseUnit;
    alias baseUnit!(luminousIntensityDimension, "candela", "cd") candelaBaseUnit;
    alias baseUnit!(temperatureDimension, "kelvin", "K")         kelvinBaseUnit;
    alias scaledBaseUnit!(cgs.gramBaseUnit, DecimalPrefix.Kilo)        kilogramBaseUnit;
    alias baseUnit!(lengthDimension, "meter", "m")               meterBaseUnit;
    alias baseUnit!(amountDimension, "mole", "mol")              moleBaseUnit;
    alias baseUnit!(timeDimension, "second", "s")                secondBaseUnit;

    alias makeSystem!( meterBaseUnit
                     , kilogramBaseUnit
                     , secondBaseUnit
                     , ampereBaseUnit
                     , kelvinBaseUnit
                     , moleBaseUnit
                     , candelaBaseUnit
                     , angle.radianBaseUnit
                     , angle.steradianBaseUnit
                     ) system;

    alias Unit!(Dimension.dimensionless,            system) Dimensionless;

    // alias Unit!(absorbedDoseDimension,           system) AbsorbedDose;
    // alias Unit!(accelerationDimension,           system) Acceleration;
    // alias Unit!(actionDimension,                 system) Action;
    // alias Unit!(activityDimension,               system) Activity;
    // alias Unit!(amountDimension,                 system) Amount;
    // alias Unit!(angularAccelerationDimension,    system) AngularAcceleration;
    // alias Unit!(angularMomentumDimension,        system) AngularMomentum;
    // alias Unit!(angularVelocityDimension,        system) AngularVelocity;
    alias Unit!(areaDimension,                   system) Area;
    // alias Unit!(capacitanceDimension,            system) Capacitance;
    // alias Unit!(catalyticActivityDimension,      system) CatalyticActivity;
    // alias Unit!(conductanceDimension,            system) Conductance;
    // alias Unit!(conductivityDimension,           system) Conductivity;
    alias Unit!(currentDimension,                system) Current;
    // alias Unit!(doseEquivalentDimension,         system) DoseEquivalent;
    // alias Unit!(dynamicViscosityDimension,       system) DynamicViscosity;
    // alias Unit!(electricChargeDimension,         system) ElectricCharge;
    alias Unit!(electricPotentialDimension,      system) ElectricPotential;
    alias Unit!(energyDimension,                 system) Energy;
    alias Unit!(forceDimension,                  system) Force;
    // alias Unit!(frequencyDimension,              system) Frequency;
    // alias Unit!(illuminanceDimension,            system) Illuminance;
    // alias Unit!(impedanceDimension,              system) Impedance;
    // alias Unit!(inductanceDimension,             system) Inductance;
    // alias Unit!(kinematicViscosityDimension,     system) KinematicViscosity;
    alias Unit!(lengthDimension,                 system) Length;
    // alias Unit!(luminousFluxDimension,           system) LuminousFlux;
    // alias Unit!(luminousIntensityDimension,      system) LuminousIntensity;
    // alias Unit!(magneticFieldIntensityDimension, system) MagneticFieldIntensity;
    // alias Unit!(magneticFluxDimension,           system) MagneticFlux;
    // alias Unit!(magneticFluxDensityDimension,    system) MagneticFluxDensity;
    // alias Unit!(massDimension,                   system) Mass;
    // alias Unit!(massDensityDimension,            system) MassDensity;
    // alias Unit!(momentOfInertiaDimension,        system) MomentOfInertia;
    // alias Unit!(momentumDimension,               system) Momentum;
    // alias Unit!(permeabilityDimension,           system) Permeability;
    // alias Unit!(permittivityDimension,           system) Permittivity;
    // alias Unit!(planeAngleDimension,             system) PlaneAngle;
    // alias Unit!(powerDimension,                  system) Power;
    alias Unit!(pressureDimension,               system) Pressure;
    // alias Unit!(reluctanceDimension,             system) Reluctance;
    alias Unit!(resistanceDimension,             system) Resistance;
    // alias Unit!(resistivityDimension,            system) Resistivity;
    // alias Unit!(solidAngleDimension,             system) SolidAngle;
    // alias Unit!(surfaceDensityDimension,         system) SurfaceDensity;
    // alias Unit!(surfaceTensionDimension,         system) SurfaceTension;
    // alias Unit!(temperatureDimension,            system) Temperature;
    alias Unit!(timeDimension,                   system) Time;
    // alias Unit!(torqueDimension,                 system) Torque;
    alias Unit!(velocityDimension,               system) Velocity;
    alias Unit!(volumeDimension,                 system) Volume;
    // alias Unit!(wavenumberDimension,             system) Wavenumber;

    // alias ScaledUnit!(Dimensionless, DecimalPrefix.Yocto) Yocto;
    // alias ScaledUnit!(Dimensionless, DecimalPrefix.Zepto) Zepto;
    // alias ScaledUnit!(Dimensionless,  DecimalPrefix.Atto) Atto;
    // alias ScaledUnit!(Dimensionless, DecimalPrefix.Femto) Femto;
    // alias ScaledUnit!(Dimensionless,  DecimalPrefix.Pico) Pico;
    // alias ScaledUnit!(Dimensionless,  DecimalPrefix.Nano) Nano;
    // alias ScaledUnit!(Dimensionless, DecimalPrefix.Micro) Micro;
    // alias ScaledUnit!(Dimensionless, DecimalPrefix.Milli) Milli;
    // alias ScaledUnit!(Dimensionless, DecimalPrefix.Centi) Centi;
    // alias ScaledUnit!(Dimensionless,  DecimalPrefix.Deci) Deci;
    // alias ScaledUnit!(Dimensionless,  DecimalPrefix.Deka) Deka;
    // alias ScaledUnit!(Dimensionless, DecimalPrefix.Hecto) Hecto;
    // alias ScaledUnit!(Dimensionless,  DecimalPrefix.Kilo) Kilo;
    // alias ScaledUnit!(Dimensionless,  DecimalPrefix.Mega) Mega;
    // alias ScaledUnit!(Dimensionless,  DecimalPrefix.Giga) Giga;
    // alias ScaledUnit!(Dimensionless,  DecimalPrefix.Tera) Tera;
    // alias ScaledUnit!(Dimensionless,  DecimalPrefix.Peta) Peta;
    // alias ScaledUnit!(Dimensionless,   DecimalPrefix.Exa) Exa;
    // alias ScaledUnit!(Dimensionless, DecimalPrefix.Zetta) Zetta;
    // alias ScaledUnit!(Dimensionless, DecimalPrefix.Yotta) Yotta;

    static this()
    {
        // defineUnitInfo!(AbsorbedDose)("gray", "Gy");
        // defineUnitInfo!(Capacitance)("farad", "F");
        // defineUnitInfo!(CatalyticActivity)("katal", "kat");
        // defineUnitInfo!(Conductance)("siemen", "S");
        // defineUnitInfo!(ElectricCharge)("coulomb", "C");
        defineUnitInfo!(ElectricPotential)("volt", "V");
        defineUnitInfo!(Energy)("joule", "J");
        defineUnitInfo!(Force)("newton", "N");
        // defineUnitInfo!(Frequency)("hertz", "Hz");
        // defineUnitInfo!(Illuminance)("lux", "lx");
        // defineUnitInfo!(Inductance)("henry", "H");
        // defineUnitInfo!(LuminousFlux)("lumen", "lm");
        // defineUnitInfo!(MagneticFlux)("weber", "Wb");
        // defineUnitInfo!(MagneticFluxDensity)("tesla", "T");
        // defineUnitInfo!(Power)("watt", "W");
        // defineUnitInfo!(Pressure)("pascal", "Pa");
        defineUnitInfo!(Resistance)("ohm", "Ohm");
    }


    // mixin(instanceOf!"AbsorbedDose"("gray", "grays"));
    // mixin(instanceOf!"Acceleration"("meterPerSecondSquared", "metersPerSecondSquared",
    //                                 "metrePerSecondSquared", "metresPerSecondSquared"));
    // mixin(instanceOf!"Activity"("becquerel", "becquerels"));
    // mixin(instanceOf!"Amount"("mole", "moles"));
    // mixin(instanceOf!"AngularVelocity"("radianPerSecond", "radiansPerSecond"));
    // mixin(instanceOf!"Area squareMeter"("squareMeters", "squareMetre", "squareMetres"));
    // mixin(instanceOf!"Capacitance"("farad", "farads"));
    // mixin(instanceOf!"CatalyticActivity"("katal", "katals"));
    // mixin(instanceOf!"Conductance"("siemen", "siemens", "mho", "mhos"));
    mixin(instanceOf!"Current"("ampere", "amperes"));
    // mixin(instanceOf!"DoseEquivalent"("sievert", "sieverts"));
    // mixin(instanceOf!"ElectricCharge"("coulomb", "coulombs"));
    mixin(instanceOf!"ElectricPotential"("volt", "volts"));
    mixin(instanceOf!"Energy"("joule", "joules"));
    mixin(instanceOf!"Force"("newton", "newtons"));
    // mixin(instanceOf!"Frequency"("hertz"));
    // mixin(instanceOf!"Illuminance"("lux"));
    // mixin(instanceOf!"Inductance"("henry", "henrys"));
    mixin(instanceOf!"Length"("meter", "meters", "metre", "metres"));
    // mixin(instanceOf!"LuminousFlux"("lumen", "lumens"));
    // mixin(instanceOf!"LuminousIntensity"("candela", "candelas"));
    // mixin(instanceOf!"MagneticFlux"("weber", "webers"));
    // mixin(instanceOf!"MagneticFluxDensity"("tesla", "teslas"));
    // mixin(instanceOf!"Mass kilogram"("kilograms", "kilogramme", "kilogrammes"));
    // mixin(instanceOf!"MassDensity"("kilogramPerCubicMeter", "kilogramsPerCubicMeter",
    //                                "kilogrammePerCubicMetre", "kilogrammesPerCubicMetre"));
    // mixin(instanceOf!"PlaneAngle"("radian", "radians"));
    // mixin(instanceOf!"Power"("watt", "watts"));
    // mixin(instanceOf!"Pressure"("pascal", "pascals"));
    mixin(instanceOf!"Resistance"("ohm", "ohms"));
    // mixin(instanceOf!"SolidAngle"("steradian", "steradians"));
    // mixin(instanceOf!"SurfaceDensity"("kilogramPerSquareMeter", "kilogramsPerSquareMeter",
    //                                   "kilogrammePerSquareMetre", "kilogrammesPerSquareMetre"));
    // mixin(instanceOf!"SurfaceTension"("newtonPerMeter", "newtonsPerMeter"));
    // mixin(instanceOf!"Temperature"("kelvin", "kelvins"));
    mixin(instanceOf!"Time"("second", "seconds"));
    // mixin(instanceOf!"Torque"("newtonMeter", "newtonMeters"));
    // mixin(instanceOf!"Velocity"("meterPerSecond", "metersPerSecond",
    //                             "metrePerSecond", "metresPerSecond"));
    // mixin(instanceOf!"Volume"("cubicMeter", "cubicMeters", "cubicMetre", "cubicMetres"));
    // mixin(instanceOf!"Wavenumber"("reciprocalMeter", "reciprocalMeters", "reciprocalMetre",
    //                               "reciprocalMetres"));
}


struct cgs
{
    alias scaledBaseUnit!(si.ampereBaseUnit, DecimalPrefix.Deci) biotBaseUnit;
    alias scaledBaseUnit!(si.meterBaseUnit, DecimalPrefix.Centi) centimeterBaseUnit;
    alias baseUnit!(massDimension, "gram", "g")            gramBaseUnit;

    // alias makeSystem!( centimeterBaseUnit
    //                  , gramBaseUnit
    //                  , si.secondBaseUnit
    //                  , biotBaseUnit
    //                  ) system;


    // alias Unit!(accelerationDimension,       system) Acceleration;
    // alias Unit!(areaDimension,               system) Area;
    // alias Unit!(currentDimension,            system) Current;
    // alias Unit!(dynamicViscosityDimension,   system) DynamicViscosity;
    // alias Unit!(energyDimension,             system) Energy;
    // alias Unit!(forceDimension,              system) Force;
    // alias Unit!(frequencyDimension,          system) Frequency;
    // alias Unit!(kinematicViscosityDimension, system) KinematicViscosity;
    // alias Unit!(lengthDimension,             system) Length;
    // alias Unit!(massDimension,               system) Mass;
    // alias Unit!(massDensityDimension,        system) MassDensity;
    // alias Unit!(momentumDimension,           system) Momentum;
    // alias Unit!(powerDimension,              system) Power;
    // alias Unit!(pressureDimension,           system) Pressure;
    // alias Unit!(timeDimension,               system) Time;
    // alias Unit!(velocityDimension,           system) Velocity;
    // alias Unit!(volumeDimension,             system) Volume;
    // alias Unit!(wavenumberDimension,         system) Wavenumber;

    // static this()
    // {
    //     defineUnitInfo!(Acceleration)("galileo", "Gal");
    //     defineUnitInfo!(Current)("biot", "Bi");
    //     defineUnitInfo!(DynamicViscosity)("poise", "P");
    //     defineUnitInfo!(Energy)("erg", "erg");
    //     defineUnitInfo!(Force)("dyne", "dyn");
    //     defineUnitInfo!(KinematicViscosity)("stoke", "St");
    //     defineUnitInfo!(Pressure)("barye", "Ba");
    //     defineUnitInfo!(Wavenumber)("kayser", "K");
    // }


    // mixin(instanceOf!"Acceleration"("gal", "gals"));
    // mixin(instanceOf!"Area"("squareCentimeter", "squareCentimeters",
    //                         "squareCentimetre", "squareCentimetres"));
    // mixin(instanceOf!"Current"("biot", "biots"));;
    // mixin(instanceOf!"DynamicViscosity"("poise"));
    // mixin(instanceOf!"Energy"("erg", "ergs"));
    // mixin(instanceOf!"Force"("dyne", "dynes"));
    // mixin(instanceOf!"KinematicViscosity"("stoke", "stokes"));
    // mixin(instanceOf!"Length"("centimeter", "centimeters",
    //                           "centimetre", "centimetres"));
    // mixin(instanceOf!"Mass"("gram", "grams", "gramme", "grammes"));
    // mixin(instanceOf!"Pressure"("barye", "baryes"));
    // mixin(instanceOf!"Time"("second", "seconds"));
    // mixin(instanceOf!"Velocity"("centimeterPerSecond", "centimetersPerSecond",
    //                             "centimetrePerSecond", "centimetresPerSecond"));
    // mixin(instanceOf!"Volume"("cubicCentimeter", "cubicCentimeters",
    //                           "cubicCentimetre", "cubicCentimetres"));
    // mixin(instanceOf!"Wavenumber"("kayser", "kaysers"));
    // mixin(instanceOf!"Wavenumber"("reciprocalCentimeter",
    //                               "reciprocalCentimeters",
    //                               "reciprocalCentimetre",
    //                               "reciprocalCentimetres"));
}


// struct imperial
// {
//   /*
//     TODO: boost/units/base_units/imperial/conversions.hpp
//     contains several conversions that have been commented out. What do we do?
//   */
//   alias scaledBaseUnit!(poundBaseUnit, scale(16, -2), "drachm", "drachm")                drachmBaseUnit;
//   alias scaledBaseUnit!(pintBaseUnit, scale(20, -1), "fluid ounce (imp.)", "fl oz")      fluidOunceBaseUnit;
//   alias scaledBaseUnit!(yardBaseUnit, scale(3, -1), "foot", "ft")                        footBaseUnit;
//   alias scaledBaseUnit!(yardBaseUnit, scale(220, 1), "furlong", "furlong")               furlongBaseUnit;
//   alias scaledBaseUnit!(pintBaseUnit, scale(8, 1), "gallon (imp.)", "gal")               gallonBaseUnit;
//   alias scaledBaseUnit!(pintBaseUnit, scale(4, -1), "gill (imp.)", "gill")               gillBaseUnit;
//   alias scaledBaseUnit!(poundBaseUnit, scale(7000, -1), "grain", "grain")                grainBaseUnit;
//   alias scaledBaseUnit!(poundBaseUnit, scale(112, 1), "hundredweight", "cwt")            hundredweightBaseUnit;
//   alias scaledBaseUnit!(yardBaseUnit, scale(36, -1), "inch", "in")                       inchBaseUnit;
//   alias scaledBaseUnit!(yardBaseUnit, scale(5280, 1), "league", "league")                leagueBaseUnit;
//   alias scaledBaseUnit!(yardBaseUnit, scale(1760, 1), "mile", "mi")                      mileBaseUnit;
//   alias scaledBaseUnit!(poundBaseUnit, scale(2, -4), "ounce", "oz")                      ounceBaseUnit;
//   alias baseUnitWithConversion!("pint (imp.)", "pt", si.Volume, "4.54609e-3L/8")   pintBaseUnit;
//   /*
//     TODO: boost/units/base_units/imperial/pound.hpp
//     pound is defined in terms of cgs::gram_base_unit.  I have tested it, and it
//     works in terms of kilogram.  Do more testing to see if we've missed something.
//    */
//   alias baseUnitWithConversion!("pound", "lb", si.kilogramBaseUnit, "0.45359237L") poundBaseUnit;
//   alias scaledBaseUnit!(pintBaseUnit, scale(2, 1), "quart (imp.)", "qt")                 quartBaseUnit;
//   alias scaledBaseUnit!(poundBaseUnit, scale(28, 1), "quarter", "quarter")               quarterBaseUnit;
//   alias scaledBaseUnit!(poundBaseUnit, scale(14, 1), "stone", "st")                      stoneBaseUnit;
//   alias scaledBaseUnit!(yardBaseUnit, scale(36000, -1), "thou", "thou")                  thouBaseUnit;
//   alias scaledBaseUnit!(poundBaseUnit, scale(2240, 1), "long ton", "t")                  tonBaseUnit;
//   alias baseUnitWithConversion!("yard", "yd", si.meterBaseUnit, "0.9144L")         yardBaseUnit;
// }


// struct metric
// {
//   alias scaledBaseUnit!(si.meterBaseUnit, scale(10, -10), "angstrom", "A")                    angstromBaseUnit;
//   alias baseUnitWithConversion!("are", "a", si.Area, "1.0e2L")                          areBaseUnit;
//   alias baseUnitWithConversion!("atmosphere", "atm", si.Pressure, "1.01325e5L")         atmosphereBaseUnit;
//   alias baseUnitWithConversion!("bar", "bar", si.Pressure, "1.0e5L")                    barBaseUnit;
//   alias baseUnitWithConversion!("barn", "b", si.Area, "1.0e-28L")                       barnBaseUnit;
//   alias scaledBaseUnit!(si.secondBaseUnit, scale(86400, 1), "day", "d")                       dayBaseUnit;
//   alias scaledBaseUnit!(si.meterBaseUnit, scale(10, -15), "fermi", "fm")                      fermiBaseUnit;
//   alias baseUnitWithConversion!("hectare", "ha", si.Area, "1.0e4L")                     hectareBaseUnit;
//   alias scaledBaseUnit!(si.secondBaseUnit, scale(60, 2), "hour", "h")                         hourBaseUnit;
//   alias baseUnitWithConversion!("knot", "kt", si.Velocity, "1852.0L/3600")              knotBaseUnit;
//   alias baseUnitWithConversion!("liter", "L", si.Volume, "1.0e-3L")                     literBaseUnit;
//   alias scaledBaseUnit!(si.meterBaseUnit, scale(10, -6), "micron", "u")                       micronBaseUnit;
//   alias scaledBaseUnit!(si.secondBaseUnit, scale(60, 1), "minute", "min")                     minuteBaseUnit;
//   alias baseUnitWithConversion!("millimeters mercury", "mmHg", si.Pressure, "133.322L") mmHgBaseUnit;
//   alias scaledBaseUnit!(si.meterBaseUnit, scale(1852, 1), "nautical mile", "nmi")             nauticalMileBaseUnit;
//   alias scaledBaseUnit!(si.kilogramBaseUnit, scale(10, 3), "metric ton", "t")                 tonBaseUnit;
//   alias baseUnitWithConversion!("torr", "Torr", si.Pressure, "1.01325e5L/760")          torrBaseUnit;
//   alias scaledBaseUnit!(si.secondBaseUnit, scale(31557600, 1), "Julian year", "yr")           yearBaseUnit;
// }


// struct temperature
// {
//     /*
//       TODO: boost/units/base_units/temperature/conversions.hpp
//       define the conversions once we have finished Absolute.
//     */
//     alias baseUnit!(temperatureDimension, "fahrenheit", "F") fahrenheitBaseUnit;
//     alias baseUnit!(temperatureDimension, "celsius", "C") celsiusBaseUnit;

//     struct celsius
//     {
//         alias makeSystem!(celsiusBaseUnit) system;

//         alias Unit!(temperatureDimension, system) Temperature;

//         mixin(instanceOf!"Temperature"("degree", "degrees"));
//     }

//     struct fahrenheit
//     {
//         alias makeSystem!(fahrenheitBaseUnit) system;

//         alias Unit!(temperatureDimension, system) Temperature;

//         mixin(instanceOf!"Temperature"("degree", "degrees"));
//     }
// }


// struct us
// {
//     alias scaledBaseUnit!(pintBaseUnit, scale(2, -1), "cup", "c") cupBaseUnit;
//     alias scaledBaseUnit!(poundBaseUnit, scale(16, -2), "dram (U.S.)", "dr") dramBaseUnit;
//     alias scaledBaseUnit!(pintBaseUnit, scale(2, -7), "fluid dram (U.S.)", "fl dr") fluidDramBaseUnit;
//     alias scaledBaseUnit!(pintBaseUnit, scale(16, -1), "fluid ounce (U.S.)", "fl oz") fluidOunceBaseUnit;
//     alias scaledBaseUnit!(yardBaseUnit, scale(3, -1), "foot", "ft") footBaseUnit;
//     alias scaledBaseUnit!(pintBaseUnit, scale(2, 3), "gallon (U.S.)", "gal") gallonBaseUnit;
//     alias scaledBaseUnit!(pintBaseUnit, scale(2, -2), "gill (U.S.)", "gi") gillBaseUnit;
//     alias scaledBaseUnit!(poundBaseUnit, scale(7000, -1), "grain", "gr") grainBaseUnit;
//     alias scaledBaseUnit!(poundBaseUnit, scale(10, 2), "hundredweight (U.S.)", "cwt") hundredweightBaseUnit;
//     alias scaledBaseUnit!(yardBaseUnit, scale(36, -1), "inch", "in") inchBaseUnit;
//     alias scaledBaseUnit!(yardBaseUnit, scale(1760, 1), "mile", "mi") mileBaseUnit;
//     alias scaledBaseUnit!(yardBaseUnit, scale(36000, 1), "mil", "mil") milBaseUnit;
//     alias scaledBaseUnit!(pintBaseUnit, scale(7680, -1), "minim (U.S.)", "minim") minimBaseUnit;
//     alias scaledBaseUnit!(poundBaseUnit, scale(2, -4), "ounce", "oz") ounceBaseUnit;
//     alias baseUnitWithConversion!("pint (U.S.)", "pt", si.Volume, "0.4731765e-3L") pintBaseUnit;
//     alias baseUnitWithConversion!("pound-force", "lbf", si.Force, "4.4482216152605L") poundForceBaseUnit;
//     alias baseUnitWithConversion!("pound", "lb", cgs.gramBaseUnit, "453.59237L") poundBaseUnit;
//     alias scaledBaseUnit!(pintBaseUnit, scale(2, 1), "quart (U.S.)", "qt") quartBaseUnit;
//     alias scaledBaseUnit!(pintBaseUnit, scale(2, -5), "tablespoon", "tbsp") tablespoonBaseUnit;
//     alias scaledBaseUnit!(pintBaseUnit, scale(96, -1), "teaspoon", "tsp") teaspoonBaseUnit;
//     alias scaledBaseUnit!(poundBaseUnit, scale(2000, 1), "short ton", "t") tonBaseUnit;
//     alias baseUnitWithConversion!("yard", "yd", si.meterBaseUnit, "0.9144L") yardBaseUnit;
// }


// heterogeneous_system.hpp
private Scale getScale(HeterogeneousDimension hd)
{
  return hd.baseUnit.scale * hd.exponent;
}

private Scale[] getScaleList(BaseUnit bu)
{
    return bu.scale == no_scale ? [] : [bu.scale];
}

private Scale[] getScaleList(HeterogeneousSystem hs)
{
  Scale[] s1;
  foreach (x; hs.hd)
  {
    Scale tmp = getScale(x);
    if (tmp.exponent.num != 0)
    {
      s1 ~= tmp;
    }
  }

  Scale[] s2;

  foreach (s; s1)
  {
      s2 = merge(s2, [s]);
  }

  return merge(s2, hs.sc);
}


// conversion_impl.hpp
Q2 convert(Q1, Q2)(Q1 src) if(isQuantity!Q1 && isQuantity!Q2)
{
  // Q1 is source
  // Q2 is destination
  alias conversion_factor!(Q1.UnitType, Q2.UnitType) cf;
  //return Q2(cast(Q2.ValueType)(src.value * cf.value));
  Q2 ret;
  ret.val = src.value * cf.value;
  return ret;
}

template conversion_factor(U1, U2) if (isUnit!U1 && isUnit!U2)
{
    static if (isHeterogeneousSystem!(U1.System))
    {
        alias U1 From;
    }
    else
    {
        alias ReduceUnit!U1 From;
    }

    static if (isHeterogeneousSystem!(U2.System))
    {
        alias U2 To;
    }
    else
    {
        alias ReduceUnit!U2 To;
    }

    enum fromBaseUnits = extractBaseUnits(From.system.hd);
    enum allBaseUnits  = extractBaseUnits(To.system.hd) ~ fromBaseUnits;
    enum HomogeneousSystem system = makeHomogeneousSystem(allBaseUnits);

    // conversion_impl
    enum FromSystemHd = From.system.hd;
    enum ToSystemHd = To.system.hd;
    alias conversion_impl!(FromSystemHd, system) conversion1;
    alias conversion_impl!(ToSystemHd, system) conversion2;
    enum real scale = evalScales(merge(From.system.sc, inverse(To.system.sc)));

    @property auto value()
    {
        return conversion1.value * (scale / conversion2.value);
    }
}


//HeterogeneousDimension[] hds
//HomogeneousSystem system
template conversion_impl(alias hds, alias system) 
{
    static if(hds.length == 0)
    {
        @property auto value() { return 1; }
    }
    else
    {
        alias conversion_impl!(hds[1..$], system) nextIteration;
        enum hds0 = hds[0];
        enum bu1 = hds0.baseUnit;
        enum dim1 = bu1.dimension;
        alias ReduceUnit!(Unit!(dim1, system)) reducedUnit;
        alias makeCBUC!(bu1, reducedUnit) converter;

        // TODO: is the static-if really needed?  check back later.
        @property auto value()
        {
            static if (hds[0].exponent.den == 1 && hds[0].exponent.num >= 0)
            {
                return std.math.pow(converter.value, hds[0].exponent.num) *
                    nextIteration.value;
            }
            else
            {
                return std.math.pow(converter.value, hds[0].exponent.value!real) * nextIteration.value;
            }
        }
    }
}

private bool isConversionDefined(alias bu)(string unit)
if (isBaseUnit!(typeof(bu)))
{
    foreach (c; bu.conversions)
    {
        if (c.destination == unit)
        {
            return true;
        }
    }
    return rawUnitString2!(UnitOf!(bu)) == unit;
}


private string converterValue(alias bu)(string unit) if (isBaseUnit!(typeof(bu)))
{
    string hunit = rawUnitString2!(UnitOf!(bu));
    string result = hunit == unit ? "1" : "real.init";

    foreach (c; bu.conversions)
    {
        if (c.destination == unit)
        {
            result = c.factor;
        }
    }
    return result;
}


string getDefaultConversion(alias bu)() if (isBaseUnit!(typeof(bu)))
{
    static if (bu.defaultConversion.length > 0)
    {
        static assert(isUnit!(mixin(bu.defaultConversion)),
                      "default conversion in bu is not a valid Unit.");
        return bu.defaultConversion;
    }
    else
    {
        return rawUnitString2!(UnitOf!(bu));
    }
}

template makeCBUC(alias src, D) if (isHeterogeneousSystem!(D.System))
{
    enum srcDimension = src.dimension;

    enum D_system = D.system;
    enum D_system_hd0 = D_system.hd[0];
    enum D_system_hd0_bu = D_system_hd0.baseUnit;
    alias MakeHeterogeneousUnit!(D_system_hd0_bu, srcDimension) M;

    static if (is(D == M))
    {
        alias call_base_unit_converter!(src, D, true) makeCBUC;
    }
    else
    {
        alias call_base_unit_converter!(src, D) makeCBUC;
    }
}

// src is baseUnit, and dst is Unit
template call_base_unit_converter(alias src, Dst) if(isUnit!(Dst))
{
    static if(isConversionDefined!(src)(rawUnitString!(Dst)))
    {
        alias do_call_base_unit_converter!(src, Dst) call_base_unit_converter;
    }
    else
    {
        alias ReduceUnit!(mixin(getDefaultConversion!(src))) NewSource;
        enum fuck1 = Dst.system;
        enum fuck2 = fuck1.hd;
        alias get_default_conversion_impl!(fuck2) impl;
        alias impl.UnitType NewDst;
        alias makeCBUC!(src, NewSource) start;
        alias conversion_factor!(NewSource, NewDst) conversion;
        
        @property auto value()
        {
            return start.value * conversion.value / impl.value;
        }
    }
}

//template call_base_unit_converter(alias src, M : X, X)
//  if(is(X == MakeHeterogeneousUnit!(M.system.hd[0].baseUnit, src.dimension)))
template call_base_unit_converter(alias src, D, bool X : true)
{
    enum d_system = D.system;
    enum d_system_hd0 = d_system.hd[0];
    enum d_system_hd0_bu = d_system_hd0.baseUnit;
    enum d_system_hd0_bu_dim = d_system_hd0_bu.dimension;

    alias d_system_hd0_bu dest;
    alias d_system_hd0_bu_dim destDimension;

    alias MakeHeterogeneousUnit!(dest, destDimension) DestUnitType;

    enum srcDimension = src.dimension;
    alias MakeHeterogeneousUnit!(src, srcDimension) SrcUnitType;

    static if(isConversionDefined!(src)(rawUnitString!(DestUnitType)))
    {
        alias do_call_base_unit_converter!(src, DestUnitType) call_base_unit_converter;
    }
    else static if(isConversionDefined!(dest)(rawUnitString!(SrcUnitType)))
    {
        alias do_call_base_unit_converter!(dest, SrcUnitType) converter;
        @property auto value()
        {
            return 1 / converter.value;
        }
    }
    else
    {
        alias ReduceUnit!(mixin(getDefaultConversion!(src))) NewSource;
        alias ReduceUnit!(mixin(getDefaultConversion!(dest))) NewDest;
        alias makeCBUC!(src, NewSource) start;
        alias conversion_factor!(NewSource, NewDest) conversion;
        alias makeCBUC!(dest, NewDest) end;
        @property auto value()
        {
            return start.value * conversion.value / end.value;
        }
    }
}

// we are sure that first is baseUnit and second is Unit
private template do_call_base_unit_converter(alias src, Dst)
{
    enum real evalFactor =
        evalScales(merge(getScaleList(src),
                         inverse(getScaleList(Dst.system))));
    enum t = mixin(converterValue!(src)(rawUnitString2!(Dst)));
    static if (isRational!(typeof(t)))
    {
        enum real converter = t.value!real;
    }
    else
    {
        enum real converter = t;
    }

    @property real value()
    { 
        return converter * evalFactor;
    }
}

template get_default_conversion_impl(alias hd) // hd is HeterogeneousDimension[]
{
    static if (hd.length == 0)
    {
        alias Unit!(Dimension.dimensionless,
                    HeterogeneousSystem.dimensionless) UnitType;
        @property auto value()
        {
            return 1;
        }
    }
    else
    {
        alias ReduceUnit!(mixin(getDefaultConversion!(hd[0].baseUnit))) NewSource;
        alias get_default_conversion_impl!(hd[1..$]) NextIteration;

        alias NewSource.power!(hd[0].exponent) NewSourcePower;
        alias NextIteration.UnitType NextUnitType;
        alias typeof(NewSourcePower() * NextUnitType()) UnitType;
        alias makeCBUC!(hd[0].baseUnit, NewSource) conversion;

        @property auto value()
        {
            static if (hd[0].exponent.den == 1 && hd[0].exponent.num >= 0)
            {
                return std.math.pow(conversion.value, hd[0].exponent.num) *
                    NextIteration.value;
            }
            else
            {
                return
                    std.math.pow(conversion.value, hd[0].exponent.value!real) *
                    NextIteration.value;
            }
        }
    }
}

// TODO:
/*
 3. boost/units/systems/detail/constants.hpp and all constants in
 units/systems/si/codata
*/



/*
  POSSIBLE BUGS IN BOOST.UNITS

  #1:
  http://stackoverflow.com/q/12879363/554075

  #2:
  http://stackoverflow.com/q/13832925/554075

  #3:
  http://stackoverflow.com/q/14027742/554075

  #4:
  Given
  quantity<absolute<si::length> > x = 3.0 * absolute<si::length>();

  This gives compile error.  Is this correct behaviour?
  cout << x * x << endl;

  This compiles.  Is this correct? If so, should it not print '3 absolute m^2' instead?
  cout << x * si::length() << endl;  // 3 absolute m m

  This also compiles.  Is this correct?  If so, what about the output?
  cout << x * absolute<si::length>() << endl;  // 3 absolute m absolute m

  #5:
  Given
  typedef scaled_base_unit<cgs::gram_base_unit, scale<10, static_rational<3> > > sbu1;
  typedef scaled_base_unit<sbu1, scale<10, static_rational<3> > > sbu2;

  Are recursive definitions legal?  If so, shouldn't this print '2 Mg' instead of '2 kkg' ?
  cout << 2.0 * sbu2::unit_type() << endl;
*/
