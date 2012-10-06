// Written in the D programming language.

/**
   This module contains the $(LREF TypeList) type and related metafunctions.

   Authors:    Arlen Avakian
   Copyright:  Copyright (c) 2012, Arlen Avakian
   License:    $(WEB boost.org/LICENSE_1_0.txt, Boost License 1.0)
   Source:     $(PHOBOSSRC std/_typelist2.d)
*/
module std.typelist;

import std.array     : replace;
import std.algorithm : balancedParens, count, countUntil;

version(unittest)
{
  import std.traits : isFloatingPoint, Unqual, Largest, isIntegral, CommonType;
  import std.string : xformat;
  import std.conv   : to;
}


/**
   Boolean and.

   Examples:
   ---
   static assert(_and!(true, false) == false);
   ---
*/
template _and(bool A, bool B)
{
  enum _and = A && B;
}

unittest
{
  alias _and!(true, true) R1;
  alias _and!(true, false) R2;
  alias _and!(false, true) R3;
  alias _and!(false, false) R4;

  static assert(R1 == true);
  static assert(R2 == false);
  static assert(R3 == false);
  static assert(R4 == false);
}

/**
   Boolean or.

   Examples:
   ---
   static assert(_or!(true, false) == true);
   ---   
*/
template _or(bool A, bool B)
{
  enum _or = A || B;
}

unittest
{
  alias _or!(true, true) R1;
  alias _or!(true, false) R2;
  alias _or!(false, true) R3;
  alias _or!(false, false) R4;

  static assert(R1 == true);
  static assert(R2 == true);
  static assert(R3 == true);
  static assert(R4 == false);
}

/**
   Boolean not.

   Examples:
   ---
   static assert(_not!(false));
   ---
*/
template _not(bool A)
{
  enum _not = !A;
}

unittest
{
  alias _not!true R1;
  alias _not!false R2;

  static assert(R1 == false);
  static assert(R2 == true);
}

/**
   Determines if all elements of the typetuple satisfy the predicate.
   
   Examples:
   ---
   static assert(_all!(isFloatingPoint, int, float, char) == false);
   ---
*/
template _all(alias Pred, T...)
{
  static if(T.length == 0)
    enum _all = true;
  else static if(Pred!(T[0]) == false)
    enum _all = false;
  else
    enum _all = _all!(Pred, T[1..$]);
}

unittest
{
  static assert(_all!(isFloatingPoint, int, float, char) == false);
  static assert(_all!(isFloatingPoint, float, double, float) == true);
  static assert(_all!(isFloatingPoint, int) == false);
  static assert(_all!(isFloatingPoint) == true);
}

/**
   Determine if any element of the typetuple satisfies the predicate.

   Examples:
   ---
   static assert(_any!(isFloatingPoint, int, float, char) == true);
   ---
*/
template _any(alias Pred, T...)
{
  static if(T.length == 0)
    enum _any = false;
  else static if(Pred!(T[0]) == true)
    enum _any = true;
  else
    enum _any = _any!(Pred, T[1..$]);
}

unittest
{
  static assert(_any!(isFloatingPoint, int, float, char) == true);
  static assert(_any!(isFloatingPoint, int, char, long) == false);
  static assert(_any!(isFloatingPoint, int) == false);
  static assert(_any!(isFloatingPoint) == false);
}

/**
   Identity metafunction.

   Examples:
   ---
   static assert(Id!int == int);
   ---
*/
template Id(T)
{
  alias T Id;
}

unittest
{
  static assert(is(Id!int == int));
}

/**
   Curries $(B Fun) by tying its first Args.length arguments to $(B Args).

   Examples:
   ---
   alias Curry!(_and, true) true_and;
   static assert(true_and!true == true);
   static assert(true_and!false == false);
   ---
*/
template Curry(alias Fun, Args...)
{
/*
  template Impl(Ts...)
  {
    alias Fun!(Args, Ts) Impl;
  }
  alias Impl Curry;
*/

  private enum string fname = Fun.stringof[0..countUntil(Fun.stringof, "(")];

  mixin(xformat(
"   alias Fun %1$s;
    template %1$sCurried(Ts...)
    {
      alias %1$s!(Args, Ts) %1$sCurried;
    }
    alias %1$sCurried Curry;
", fname));
}

version(unittest)
{
  private template areEqual(alias A, alias B)
  {
    static if(A == B)
      enum areEqual = true;
    else
      enum areEqual = false;
  }
  private template areEqual(T1, T2)
  {
    enum areEqual = is(T1 == T2);
  }
}

unittest
{
  alias Curry!(areEqual, 3) Equals3;
  alias Curry!(areEqual, int) IsInt;

  static assert(Equals3!4 == false);
  static assert(Equals3!3 == true);
  static assert(IsInt!double == false);
  static assert(IsInt!int == true);
}

// -----------------------------------------------------------------------------
//   TypeList.
// -----------------------------------------------------------------------------
/*
  Determines if two typelists have the same dimension.
*/
private template equalDimension(TL1, TL2)
{
  enum bool equalDimension = TL1.dim == TL2.dim;
}

/**
   Creates a typelist out of a sequence of zero or more types.

   Examples:
   ---
   alias TypeList!(int, float, long*) TL1;
   static assert(is(TL1.items == TypeTuple!(int, float, long*)));
   static assert(TL1.dim == 1);
   static assert(is(TL1.head == int));
   static assert(is(TL1.tail == TypeList!(float, long*)));
   static assert(toString!TL1 == "[int,float,long*]");
   ---
*/
struct TypeList(T...)
{
  static if(!_any!(isTypeList, T))
  {
    enum dim = 1;
  }
  else static if(_all!(isTypeList, T))
  {
    static if(T.length > 1)
    {
      alias Curry!(equalDimension, T[0]) HaveSameDimension;
      static assert(_all!(HaveSameDimension, T),
        "Elements in the typelist must have the same dimension");
    }
    enum dim = 1 + T[0].dim;
  }
  else
  {
    static assert(false, "Cannot have a TypeList of different kinds.");
  }

  /// A typetuple of all the elements of the typelist.
  alias T items;

  static if(T.length != 0)
  {
    /// The first element of the typelist.
    alias T[0] head;
    /// The last element of the typelist.
    alias T[$-1] last;
    /// The elements after the head of the typelist.
    alias TypeList!(T[1..$]) tail;
    /// All the elements of the typelist except the last one.
    alias TypeList!(T[0..$-1]) init;
    /// The length of the typelist.
    enum length = T.length;
    /// Whether the typelist is empty.
    enum empty = false;
  }
  else
  {
    enum length = 0;
    enum empty = true;
  }

  /// Converts the typelist to a string representation.
  static string toString()
  {
    return .toString!(TypeList);
  }
}

unittest
{
  alias TypeList!(int, float, long*) TL1;
  alias TypeList!(TL1, TL1) TL2;
  alias TypeList!(TL2, TL2) TL3;
  alias TypeList!(char) TL4;
  alias TypeList!() TL5;

  static assert(isTypeList!TL1);
  static assert(TL1.dim == 1);
  static assert(is(TL1.head == int));
  static assert(is(TL1.last == long*));
  static assert(is(TL1.tail == TypeList!(float, long*)));
  static assert(is(TL1.init == TypeList!(int, float)));
  static assert(TL1.length == 3);
  static assert(!TL1.empty);
  static assert(TL2.dim == 2);
  static assert(TL2.init.dim == 2);
  static assert(TL2.tail.dim == 2);
  static assert(TL2.head.dim == 1);
  static assert(TL2.last.dim == 1);
  static assert(TL3.dim == 3);
  static assert(TL3.init.dim == 3);
  static assert(TL3.tail.dim == 3);
  static assert(TL3.head.dim == 2);
  static assert(TL3.last.dim == 2);
  static assert(TL4.tail.dim == 1);
  static assert(TL4.tail.length == 0);
  static assert(TL4.init.dim == 1);
  static assert(TL4.init.length == 0);
  static assert(is(TL4.head == char));
  static assert(is(TL4.last == char));
  static assert(TL5.dim == 1);
  static assert(TL5.length == 0);
  static assert(TypeList!(TL5).dim == 2);
  static assert(TypeList!(TypeList!(TL5)).dim == 3);
  static assert(TypeList!(TypeList!(TL5)).length == 1);
}

/**
   Check to see if $(B T) is a TypeList.
*/
template isTypeList(T)
{
  static if(is(T U == TypeList!(A), A...))
    enum bool isTypeList = true;
  else
    enum bool isTypeList = false;
}

unittest
{
  alias TypeList!(int, double) TL1;

  static assert(isTypeList!TL1 == true);
  static assert(isTypeList!int == false);
}

/**
   Constructs a typelist. EXPERIMENTAL.

   Examples:
   ---
   alias _!"[int, double, uint]" TL1;
   static assert(is(TL1 == TypeList!(int, double, uint)));

   alias _!"[[char],[float,double]]" TL2;
   static assert(is(TL2 == TypeList!(TypeList!(char), TypeList!(float, double))));
   ---
*/
template _(string TL)
{
  static assert(count(TL, "[") > 0 && count(TL, "]") > 0);
  static assert(balancedParens(TL, '[', ']') == true,
                "'" ~ TL ~ "' does not have balanced square brackets.");
  mixin("alias " ~ replace(replace(TL, "[", "TypeList!("), "]", ")") ~ " _;");
}

unittest
{
  alias _!"[int, double, uint]" R1;
  alias _!"[[int, char]]" R2;
  alias _!"[]" R3;

  static assert(is(R1 == TypeList!(int, double, uint)));
  static assert(is(R2 == TypeList!(TypeList!(int, char))));
  static assert(is(R3 == TypeList!()));
}

/**
   Extract the first element of a typelist.
*/
template Head(TL) if(isTypeList!TL)
{
  alias TL.head Head;
}

/**
   Extract the last element of a typelist.
*/
template Last(TL) if(isTypeList!TL)
{
  alias TL.last Last;
}

/**
   Extract the elements after the head of a typelist.
*/
template Tail(TL) if(isTypeList!TL)
{
  alias TL.tail Tail;
}

/**
   Return all the elements of a typelist except the last one.
*/
template Init(TL) if(isTypeList!TL)
{
  alias TL.init Init;
}

/**
   Test whether a typelist is empty.
*/
template Empty(TL) if(isTypeList!TL)
{
  alias TL.empty Empty;
}

/**
   Returns the length of a typelist.
*/
template Length(TL) if(isTypeList!TL)
{
  alias TL.length Length;
}

/**
   Append two typelists.

   Examples:
   ---
   alias TypeList!(int) TL1;
   alias TypeList!(char) TL2;
   alias Append!(TL1, TL2) R1;
   static assert(is(R1 == TypeList!(int, char)));
   ---
*/
template Append(TL1, TL2) if(isTypeList!TL1 && isTypeList!TL2)
{
  alias TypeList!(TL1.items, TL2.items) Append;
}

unittest
{
  alias TypeList!(float, double) TL1;
  alias TypeList!() TL2;
  alias TypeList!(TL1) TL3;

  static assert(is(Append!(TL1, TL2) == TypeList!(float, double)));
  static assert(is(Append!(TL2, TL1) == TypeList!(float, double)));
  static assert(is(Append!(TL2, TL2) == TypeList!()));
  static assert(Append!(TL2, TL2).empty);
  static assert(Append!(TL2, TL2).dim == 1);
  static assert(Append!(TL2, TL2).length == 0);
  static assert(Append!(TL1, TL1).dim == 1);
  static assert(Append!(TL1, TL1).length == 4);
  static assert(is(Append!(TL1, TL1) ==
                   TypeList!(float, double, float, double)));
  static assert(!is(Append!(TL3, TL1)));
  static assert(is(Append!(TL3, TL2)));
}

/**
   Append a type to a typelist.

   Examples:
   ---
   alias TypeList!(float, double) TL1;
   alias Append!(TL1, real) R1;
   static assert(is(R1 == TypeList!(float, double, real)));
   ---
*/
template Append(TL, T) if(isTypeList!TL && !isTypeList!T)
{
  alias TypeList!(TL.items, T) Append;
}

unittest
{
  alias TypeList!(float, double) TL1;
  alias TypeList!() TL2;
  alias TypeList!(TL1) TL3;

  static assert(is(Append!(TL1, int) == TypeList!(float, double, int)));
  static assert(is(Append!(TL2, int) == TypeList!(int)));
  static assert(!is(Append!(TL3, int)));
}                

/**
   Prepend a type to a typelist.

   Examples:
   ---
   alias TypeList!(float) TL1;
   alias Cons!(char, TL1) R1;
   static assert(is(R1 == TypeList!(char, float)));
   ---
*/
template Cons(A, B) if(isTypeList!B)
{
  alias TypeList!(A, B.items) Cons;
}

unittest
{
  alias TypeList!() TL1;
  alias TypeList!(TL1) TL2;
  alias TypeList!(TL2) TL3;
  alias TypeList!(char) TL4;
  alias TypeList!(TypeList!(int)) TL5;

  static assert(!is(Cons!(int, int)));
  static assert(is(Cons!(int, TL1) == TypeList!(int)));
  static assert(is(Cons!(int, TL4) == TypeList!(int, char)));
  static assert(!is(Cons!(int, TL2)));

  static assert(!is(Cons!(TL4, int)));
  static assert(!is(Cons!(TL4, TL4)));
  static assert(is(Cons!(TL4, TL1) == TypeList!(TypeList!(char))));
  static assert(is(Cons!(TL4, TL5) == TypeList!(TL4, TypeList!(int))));
  static assert(!is(Cons!(TL4, TypeList!(TL5))));

  static assert(!is(Cons!(TL1, int)));
  static assert(is(Cons!(TL1, TL1) == TypeList!(TypeList!())));
  static assert(is(Cons!(TL1, TL2) == TypeList!(TL1, TL1)));
  static assert(!is(Cons!(TL1, TL3)));
  static assert(is(Cons!(TL3, TL1)));
  static assert(!is(Cons!(TL3, TL2)));

  // the unittests from the other two.
  // _1
  alias TypeList!(int, double) TL6;

  alias Cons!(char, TL1) R1;
  alias Cons!(char, TL6) R2;

  static assert(R1.dim == 1 && R1.length == 1);
  static assert(is(R1 == TypeList!(char)));
  static assert(R2.dim == 1 && R2.length == 3);
  static assert(is(R2 == TypeList!(char, int, double)));

  // _2
  alias TypeList!(int) TL7;
  alias TypeList!(TL7, TL7) TL8;

  alias Cons!(TL1, TL1) R3;
  alias Cons!(TL1, TL8) R4;
  alias Cons!(TL7, TL1) R5;
  alias Cons!(TL7, TL8) R6;
  alias Cons!(TL1, Cons!(TL1, TL1)) R7;
  alias Cons!(Cons!(TL1, TL1), TL1) R8;

  static assert(R3.dim == 2 && R3.length == 1 && R3.head.dim == 1 && R3.head.empty);
  static assert(R4.dim == 2 && R4.length == 3);
  static assert(R5.dim == 2 && R5.length == 1);
  static assert(R6.dim == 2 && R6.length == 3);
  static assert(R7.dim == 2 && R7.length == 2);
  static assert(R8.dim == 3 && R8.length == 1);
}

/**
   Converts a TypeList to string.

   Examples:
   ---
   static assert(toString!(TypeList!(float, real)) == "[float,real]");
   ---
*/
template toString(TL) if(isTypeList!TL)
{
  private template Shows(A)
  {
    static if(isTypeList!A)
      enum string Shows = toString!A;
    else
      enum string Shows = A.stringof;
  }

  private template Showl(TL2) if(isTypeList!TL2)
  {
    static if(TL2.empty)
      enum string Showl = "]";
    else
      enum string Showl =  "," ~ Shows!(TL2.head) ~ Showl!(TL2.tail);
  }
  static if(TL.empty)
    enum string toString = "[]";
  else
    enum string toString = "[" ~ Shows!(TL.head) ~ Showl!(TL.tail);
}

unittest
{
  alias TypeList!(int, char) TL1;
  alias TypeList!(float, long) TL2;
  alias TypeList!(TL1, TL2, TL1) TL3;
  alias TypeList!(TL3, TL3) TL4;
  alias TypeList!(TypeList!()) TL5;

  static assert(toString!TL1 == "[int,char]");
  static assert(toString!TL3 == "[[int,char],[float,long],[int,char]]");
  static assert(toString!TL4 == "[[[int,char],[float,long],[int,char]],"~
                "[[int,char],[float,long],[int,char]]]");
  static assert(toString!TL5 == "[[]]");
}

/**
   Returns true if $(B T1) and $(B T2) are of the same type.
*/
template sameTypes(T1, T2)
{
  enum sameTypes = is(T1 == T2);
}

/**
   Returns true if and only if the two typelists compare equal element for
   element, according to binary predicate Pred.
*/
template equal(alias Pred, TL1, TL2) if(isTypeList!TL1 && isTypeList!TL2)
{
  private template Impl(A, B)
  {
    static if(A.empty)
      enum Impl = true;
    else static if(Pred!(A.head, B.head) == false)
      enum Impl = false;
    else
      enum Impl = Impl!(A.tail, B.tail);
  }

  static if(TL1.length != TL2.length || TL1.dim != TL2.dim)
    enum equal = false;
  else static if(TL1.dim == 1)
    enum equal = Impl!(TL1, TL2);
  else static if(equal!(Pred, TL1.head, TL2.head) == false)
    enum equal = false;
  else
    enum equal = equal!(Pred, TL1.tail, TL2.tail);
}

unittest
{
  alias TypeList!() TL1;
  alias TypeList!(TL1, TL1) TL2;
  alias TypeList!(int, char, float) TL3;
  alias TypeList!(float, double) TL4;
  alias TypeList!(TL3, TL4) TL5;
  alias TypeList!(TL4, TL3) TL6;

  alias equal!(sameTypes, TL1, TL1) R1;
  alias equal!(sameTypes, TL1, TL2) R2;
  alias equal!(sameTypes, TL2, TL2) R3;
  alias equal!(sameTypes, TL3, TL4) R4;
  alias equal!(sameTypes, TL3, TL1) R5;
  alias equal!(sameTypes, TL4, TL4) R6;
  alias equal!(sameTypes, TL5, TL6) R7;

  static assert(R1 == true);
  static assert(R2 == false);
  static assert(R3 == true);
  static assert(R4 == false);
  static assert(R5 == false);
  static assert(R6 == true);
  static assert(R7 == false);
}

// -----------------------------------------------------------------------------
//   TypeList transformations.
// -----------------------------------------------------------------------------
/**
   A new typelist is obtained by applying $(B Fun) to each item of $(B TL).

   Examples:
   ---
   alias TypeList!(immutable double, int, const char) TL1;
   alias Map!(Unqual, TL1) R1;
   static assert(is(R1 == TypeList!(double, int, char)));
   ---
*/
template Map(alias Fun, TL) if(isTypeList!TL)
{
  static if(TL.empty)
    alias TypeList!() Map;
  else
    alias Cons!(Fun!(TL.head), Map!(Fun, TL.tail)) Map;
}

unittest
{
  alias TypeList!(immutable double, int, const char) TL1;
  alias TypeList!(TL1, TL1) TL2;

  alias Map!(Unqual, TL1) R1;
  alias Map!(Head, TL2) R2;

  static assert(is(R1 == TypeList!(double, int, char)));
  static assert(is(R2 == TypeList!(immutable double, immutable double)));
}

/**
   Returns the elements of a typelist in reverse order.

   Examples:
   ---
   alias TypeList!(int, double, char) TL1;
   alias Reverse!TL1 R1;
   static assert(is(R1 == TypeList!(char, double, int)));
   ---
*/
template Reverse(TL) if(isTypeList!TL)
{
  static if(TL.length == 0)
    alias TL Reverse;
  else
    alias Cons!(TL.last, Reverse!(TL.init)) Reverse;
}

unittest
{
  alias TypeList!(int, double, char) TL1;
  alias TypeList!(float, byte) TL2;
  alias TypeList!(TL1, TL2) TL3;

  alias Reverse!TL1 R1;
  alias Reverse!TL3 R2;

  static assert(is(R1 == TypeList!(char, double, int)));
  static assert(is(R2 == TypeList!(TL2, TL1)));
}

/**
   Intersperses $(B T) between the elements of the typelist.

   Examples:
   ---
   alias TypeList!(float, double, real) TL1;
   alias Intersperse!(string, TL1) R1;
   static assert(is(R1 == TypeList!(float, string, double, string, real)));
   ---
*/
template Intersperse(T, TL) if(isTypeList!TL)
{
  private template PrependToAll(S, TL2)
  {
    static if(TL2.length == 0)
      alias TL2 PrependToAll;
    else
      alias Cons!(S, Cons!(TL2.head, PrependToAll!(S, TL2.tail))) PrependToAll;
  }

  static if(TL.length == 0)
    alias TL Intersperse;
  else
    alias Cons!(TL.head, PrependToAll!(T, TL.tail)) Intersperse;
}

unittest
{
  alias TypeList!() TL1;
  alias TypeList!(float) TL2;
  alias TypeList!(int, long) TL3;

  alias Intersperse!(char, TL1) R1;
  alias Intersperse!(char, TL2) R2;
  alias Intersperse!(char, TL3) R3;

  static assert(is(R1 == TL1));
  static assert(is(R2 == TL2));
  static assert(is(R3 == TypeList!(int, char, long)));
}

/**
   Transposes the rows and columns of its argument.

   Examples:
   ---
   alias TypeList!(TypeList!(float, double), TypeList!(int, long)) TL1;
   alias Transpose!(TL1) R1;
   static assert(is(R1 == TypeList!(TypeList!(float, int), TypeList!(double, long))));
   ---
*/
template Transpose(TL) if(isTypeList!TL)
{
  static if(TL.empty)
    alias TypeList!() Transpose;
  else static if(TL.head.empty)
    alias Transpose!(TL.tail) Transpose;
  else 
    alias Cons!(Cons!(TL.head.head, Map!(Head, TL.tail)),
                Transpose!(Cons!(TL.head.tail, Map!(Tail, TL.tail)))) Transpose;
}

unittest
{
  alias TypeList!() TL1;
  alias TypeList!(TL1) TL2;
  alias TypeList!(TL1, TL1) TL3;
  alias TypeList!(int, char) TL4;
  alias TypeList!(TL4) TL5;
  alias TypeList!(TypeList!(float, double), TypeList!(int, long)) TL6;

  alias Transpose!TL1 R1;
  alias Transpose!TL2 R2;
  alias Transpose!TL3 R3;
  alias Transpose!TL5 R4;
  alias Transpose!TL6 R5;

  static assert(is(R1 == TL1));
  static assert(is(R2 == TL1));
  static assert(is(R3 == TL1));
  static assert(is(R4 == TypeList!(TypeList!(int), TypeList!(char))));
  static assert(is(R5 == TypeList!(TypeList!(float, int),
                                   TypeList!(double, long))));
}

/**
   Returns the typelist of all subsequences of the types.

   Examples:
   ---
   alias TypeList!(char, int) TL1;
   alias Subsequences!TL1 R1;
   static assert(is(R1 == TypeList!(TypeList!(), TypeList!char, TypeList!int, TypeList!(char, int))));
   ---
*/
template Subsequences(TL) if(isTypeList!TL)
{
  private template NonEmptySubsequences(TL2)
  {
    template Fun(YS, R)
    {
      alias Cons!(YS, Cons!(Cons!(TL2.head, YS), R)) Fun;
    }
    static if(TL2.empty)
      alias TypeList!() NonEmptySubsequences;
    else
      alias Cons!(TypeList!(TL2.head),
                  Foldr!(Fun,
                         TypeList!(),
                         NonEmptySubsequences!(TL2.tail))) NonEmptySubsequences;
  }
  alias Cons!(TypeList!(), NonEmptySubsequences!TL) Subsequences;
}

unittest
{
  alias TypeList!() TL1;
  alias TypeList!(TL1) TL2;
  alias TypeList!(char, int) TL3;

  alias Subsequences!TL1 R1;
  alias Subsequences!TL2 R2;
  alias Subsequences!TL3 R3;

  static assert(is(R1 == TL2));
  static assert(is(R2 == TypeList!(TL1, TL2)));
  static assert(is(R3 == TypeList!(TL1, TypeList!(char), TypeList!(int), TL3)));
}

/**
   Returns the typelist of all permutations of the argument.

   Examples:
   ---
   alias Permutations!(TypeList!(int, uint, char)) R1;
   static assert(toString!R1 == "[[int,uint,char],[uint,int,char],[char,uint,int],[uint,char,int],[char,int,uint],[int,char,uint]]");
   ---
*/
template Permutations(xs0) if(isTypeList!xs0)
{
  private template Tuple(A, B)
  {
    alias A fst;
    alias B snd;
  }

  private template Perms(TL1, Is)
  {
    template Interleave(Xs, R)
    {
      alias Interleave_!(Id, Xs, R).snd Interleave;
    }

    template Interleave_(alias Fun, Yys, R)
    {
      template FY(TL2) { alias Fun!(Cons!(Yys.head, TL2)) FY; }

      static if(Yys.empty)
        alias Tuple!(TL1.tail, R) Interleave_;
      else
      {
        alias Interleave_!(FY, Yys.tail, R) _us_zs;
        alias Tuple!(Cons!(Yys.head, _us_zs.fst),
                     Cons!(Fun!(Cons!(TL1.head, Cons!(Yys.head, _us_zs.fst))),
                           _us_zs.snd)) Interleave_;
      }
    }

    static if(TL1.empty)
      alias TypeList!() Perms;
    else
      alias Foldr!(Interleave, Perms!(TL1.tail, Cons!(TL1.head, Is)),
                   Permutations!Is) Perms;
  }

  alias Cons!(xs0, Perms!(xs0, TypeList!())) Permutations;
}

unittest
{
   alias Permutations!(TypeList!()) R1;
   alias Permutations!(TypeList!(int, float)) R2;
   alias Permutations!(TypeList!(int, uint, char)) R3;

   static assert(is(R1 == TypeList!(TypeList!())));
   static assert(is(R2 == TypeList!(TypeList!(int,float),TypeList!(float,int))));
   static assert(is(R3 == TypeList!(TypeList!(int,uint,char),
   	  	       	  TypeList!(uint,int,char),TypeList!(char,uint,int),
			  TypeList!(uint,char,int),TypeList!(char,int,uint),
			  TypeList!(int,char,uint))));
}

// -----------------------------------------------------------------------------
//   Reducing TypeLists.
// -----------------------------------------------------------------------------
/**
   Reduces a n-dimensional typelist from left to right.
   $(B Fun) is the binary operator, and $(B Z) is the starting type.

   Examples:
   ---
   struct C(int n) { enum cardinal = n; }
   
   template Minus(A, B)
   {
     alias C!(A.cardinal - B.cardinal) Minus;
   }

   alias TypeList!(C!2, C!3, C!7, C!4) TL1;
   alias Foldl!(Minus, C!0, TL1) R1;
   static assert(is(R1 == C!(-16)));
   ---
*/
template Foldl(alias Fun, Z, TL) if(isTypeList!TL)
{
  static if(TL.empty)
    alias Z Foldl;
  else
    alias Foldl!(Fun, Fun!(Z, TL.head), TL.tail) Foldl;
}

version(unittest)
{
  private template Shortest(TL1, TL2)
  {
    static if(TL1.length <= TL2.length)
      alias TL1 Shortest;
    else
      alias TL2 Shortest;
  }

  struct C(int n) { enum cardinal = n; }

  template Minus(A, B)
  {
    alias C!(A.cardinal - B.cardinal) Minus;
  }
}

unittest
{
  alias TypeList!(byte, float, char) TL1;
  alias TypeList!(double, byte) TL2;
  alias TypeList!() TL3;
  alias TypeList!(TL1, TL2) TL4;
  alias TypeList!(C!2, C!3, C!7, C!4) TL5;

  alias Foldl!(Largest, long, TL1) R1;
  alias Foldl!(Largest, int, TL2) R2;
  alias Foldl!(Shortest, TL1, TL4) R3;
  alias Foldl!(Shortest, TL3, TL4) R4;
  alias Foldl!(Minus, C!0, TL5) R5;

  // 1-dimensional
  static assert(is(R1 == long));
  static assert(is(R2 == double));
  static assert(is(R5 == C!(-16)));

  // n-dimensional
  static assert(is(R3 == TL2));
  static assert(is(R4 == TL3));
}

/**
   Foldl1 is a variant of $(LREF Foldl) that has no starting type argument.
*/
template Foldl1(alias Fun, TL) if(isTypeList!TL)
{
  static assert(TL.length > 0, "TL cannot be an empty TypeList.");
  static if(TL.length == 1)
    alias TL.head Foldl1;
  else
   alias Foldl!(Fun, TL.head, TL.tail) Foldl1;
}

unittest
{
  alias TypeList!(int, double, char) TL1;
  alias TypeList!(int) TL2;

  alias Foldl1!(Largest, TL1) R1;
  alias Foldl1!(Largest, TL2) R2;

  static assert(is(R1 == double));
  static assert(is(R2 == int));
}

/**
   Reduces a n-dimensional typelist from right to left.
   $(B Fun) is the binary operator, and $(B Z) is the starting type.

   Examples:
   ---
   alias TypeList!(C!2, C!3, C!7, C!4) TL1;
   alias Foldr!(Minus, C!0, TL1) R1;
   static assert(is(R1 == C!(2)));
   ---
*/
template Foldr(alias Fun, Z, TL) if(isTypeList!TL)
{
  static if(TL.empty)
    alias Z Foldr;
  else
    alias Fun!(TL.head, Foldr!(Fun, Z, TL.tail)) Foldr;
}

unittest
{
  alias TypeList!(byte, float, char) TL1;
  alias TypeList!(double, byte) TL2;
  alias TypeList!() TL3;
  alias TypeList!(TL1, TL2) TL4;
  alias TypeList!(C!2, C!3, C!7, C!4) TL5;

  alias Foldr!(Largest, long, TL1) R1;
  alias Foldr!(Largest, int, TL2) R2;
  alias Foldr!(Shortest, TL1, TL4) R3;
  alias Foldr!(Shortest, TL3, TL4) R4;
   alias Foldr!(Minus, C!0, TL5) R5;

  // 1-dimensional
  static assert(is(R1 == long));
  static assert(is(R2 == double));
  static assert(is(R5 == C!(2)));

  // n-dimensional
  static assert(is(R3 == TL2));
  static assert(is(R4 == TL3));
}

/**
   Foldr1 is a variant of $(LREF Foldr) that has no starting type argument.
 */
template Foldr1(alias Fun, TL) if(isTypeList!TL)
{
  static assert(TL.length > 0, "Empty TypeList.");
  static if(TL.length == 1)
    alias TL.head Foldr1;
  else
    alias Foldr!(Fun, TL.head, TL.tail) Foldr1;
}

unittest
{
  alias TypeList!(int, double, char) TL1;
  alias TypeList!(int) TL2;

  alias Foldr1!(Largest, TL1) R1;
  alias Foldl1!(Largest, TL2) R2;

  static assert(is(R1 == double));
  static assert(is(R2 == int));
}

// -----------------------------------------------------------------------------
//   Special folds.
// -----------------------------------------------------------------------------
/**
   Concatenate a typelist of typelists.

   Examples:
   ---
   alias Concat!(TypeList!(TypeList!(int, uint), TypeList!char, TypeList!(long,ulong))) R1;
   static assert(is(R1 == TypeList!(int, uint, char, long, ulong)));
   ---
*/
template Concat(TL) if(isTypeList!TL)
{
  static assert(TL.dim > 1);
  alias Foldr!(Append, TypeList!(), TL) Concat;
}

unittest
{
  alias TypeList!(int, double, char) TL1;
  alias TypeList!(char, long, float) TL2;
  alias TypeList!(TL1, TL2) TL3;

  alias Concat!(TL3) R1;

  static assert(is(R1 == TypeList!(int, double, char, char, long, float)));
  static assert(!is(Concat!(TL1)));
}

/**
   Map a metafunction over a typelist and concatenate the results.

   Examples:
   ---
   template Twice(T)
   {
     alias TypeList!(T, T) Twice;
   }

   alias TypeList!(char, int, long) TL1;
   alias ConcatMap!(Twice, TL1) R1;
   static assert(is(R1 == TypeList!(char, char, int, int, long, long)));
   ---
*/
// Fun must return a typelist. How do we enforce this?
// uses composition.
template ConcatMap(alias Fun, TL) if(isTypeList!TL)
{
  private template AF(T, TL1)
  {
    alias Append!(Fun!T, TL1) AF;
  }
  alias Foldr!(AF, TypeList!(), TL) ConcatMap;
}

version(unittest)
{
  private template Twice(T)
  {
    alias TypeList!(T, T) Twice;
  }
}

unittest
{
  alias TypeList!(char, int, long) TL1;
  alias TypeList!(TL1, TL1) TL2;

  alias ConcatMap!(Twice, TL1) R1;
  alias ConcatMap!(Id, TL2) R2;

  static assert(is(R1 == TypeList!(char, char, int, int, long, long)));
  static assert(is(R2 == TypeList!(char,int,long,char,int,long)));
}

/**
   Determines if all elements of the typelist satisfy the predicate.

   Examples:
   ---
   static assert(all!(isFloatingPoint, TypeList!(int, float, char)) == false);
   ---
*/
template all(alias Pred, TL) if(isTypeList!TL)
{
  static if(TL.empty)
    enum all = true;
  else static if(Pred!(TL.head) == false)
    enum all = false;
  else
    enum all = all!(Pred, TL.tail);
}

unittest
{
  static assert(all!(isFloatingPoint, TypeList!(int, float, char)) == false);
  static assert(all!(isFloatingPoint, TypeList!(float, double)) == true);
}

/**
   Determines if any element of the typelist satisfies the predicate.

   Examples:
   ---
   static assert(any!(isFloatingPoint, TypeList!(int, float, char)) == true);
   ---
*/
template any(alias Pred, TL) if(isTypeList!TL)
{
  static if(TL.empty)
    enum any = false;
  else static if(Pred!(TL.head) == true)
    enum any = true;
  else
    enum any = any!(Pred, TL.tail);
}

unittest
{
  static assert(any!(isFloatingPoint, TypeList!(int, float, char)) == true);
  static assert(any!(isFloatingPoint, TypeList!(int, byte, char)) == false);
}

// -----------------------------------------------------------------------------
//   Building lists.
// -----------------------------------------------------------------------------
/**
   Returns a n-dimensional typelist of successive reduced types from the left.

   Examples:
   ---
   alias TypeList!(C!1, C!2, C!3) TL1;
   alias Scanl!(Minus, C!4, TL1) R1;
   static assert(is(R1 == TypeList!(C!4, C!3, C!1, C!(-2))));
   ---
*/
template Scanl(alias Fun, Q, TL) if(isTypeList!TL)
{
  static if(TL.empty)
    alias TypeList!(Q) Scanl;
  else
    alias Cons!(Q, Scanl!(Fun, Fun!(Q, TL.head), TL.tail)) Scanl;
}

unittest
{
  alias TypeList!() TL1;
  alias TypeList!(char, int, uint, long, ulong, double) TL2;
  alias TypeList!(C!1, C!2, C!3) TL3;

  alias Scanl!(Largest, char, TL1) R1;
  alias Scanl!(Largest, int, TL2) R2;
  alias Scanl!(Minus, C!4, TL3) R3;

  // 1-dimensional
  static assert(is(R1 == TypeList!(char)));
  static assert(is(R2 == TypeList!(int, int, int, int, long, long, long)));
  static assert(is(R3 == TypeList!(C!4, C!3, C!1, C!(-2))));

  // n-dimensional NEEDS UNITTESTS
}

/**
   Scanl1 is a variant of $(LREF Scanl) that has no starting type argument.
*/
template Scanl1(alias Fun, TL) if(isTypeList!TL)
{
  static if(TL.empty)
    alias TypeList!() Scanl1;
  else
    alias Scanl!(Fun, TL.head, TL.tail) Scanl1;
}

unittest
{
  alias TypeList!(char, int, long) TL1;

  alias Scanl1!(Largest, TL1) R1;

  static assert(is(R1 == TypeList!(char, int, long)));
}

/**
   Returns a n-dimensional typelist of successive reduced typess from the right.

   Examples:
   ---
   alias TypeList!(C!1, C!2, C!3) TL1;
   alias Scanl!(Minus, C!4, TL1) R1;
   static assert(is(R1 == TypeList!(C!(-2), C!3, C!(-1), C!4)));
   ---
*/
template Scanr(alias Fun, Q0, TL) if(isTypeList!TL)
{
  static if(TL.empty)
    alias TypeList!(Q0) Scanr;
  else
  {
    alias Scanr!(Fun, Q0, TL.tail) Qs;
    alias Cons!(Fun!(TL.head, Qs.head), Qs) Scanr;
  }
}

unittest
{
  alias TypeList!() TL1;
  alias TypeList!(char, int, uint, long, ulong, double) TL2;
   alias TypeList!(C!1, C!2, C!3) TL3;

  alias Scanr!(Largest, char, TL1) R1;
  alias Scanr!(Largest, int, TL2) R2;
  alias Scanr!(Minus, C!4, TL3) R3;

  // 1-dimensional
  static assert(is(R1 == TypeList!(char)));
  static assert(is(R2 == TypeList!(long, long, long, long, ulong, double, int)));
  static assert(is(R3 == TypeList!(C!(-2), C!3, C!(-1), C!4)));

  // n-dimensional NEEDS UNITTESTS
}

/**
   Scanr1 is a variant of $(LREF Scanr) that has no starting type argument.
*/
template Scanr1(alias Fun, TL) if(isTypeList!TL)
{
  static if(TL.empty)
    alias TypeList!() Scanr1;
  else static if(TL.length == 1)
    alias TypeList!(TL.head) Scanr1;
  else
  {
    alias Scanr1!(Fun, TL.tail) Qs;
    alias Cons!(Fun!(TL.head, Qs.head), Qs) Scanr1;
  }
}

unittest
{
  alias TypeList!(char, int, long) TL1;

  alias Scanr1!(Largest, TL1) R1;

  static assert(is(R1 == TypeList!(long, long, long)));
}

// -----------------------------------------------------------------------------
//   Finite typelists.
// -----------------------------------------------------------------------------
/**
   Returns a typelist of length $(B N) of repeated applications of $(B Fun) to $(B T).

   Examples:
   ---
   struct _1 { enum value = 1; }

   template TimesTwo(T)
   {
     enum string result = to!string(T.value * 2);
     mixin(xformat("struct _%1$s { enum value = %1$s; } alias _%1$s TimesTwo;", result));
   }
   
   alias IterateN!(6, TimesTwo, _1) R1;
   static assert(toString!R1 == "[_1,_2,_4,_8,_16,_32]");
   ---
*/
template IterateN(int N, alias Fun, T)
{
  static if(N <= 0)
    alias TypeList!() IterateN;
  else
    alias Cons!(T, IterateN!(N-1, Fun, Fun!(T))) IterateN;
}

version(unittest)
{
  private struct S(T) { }

  private template Fun1(T) { alias S!T Fun1; }

  private template AppendReverse(TL)
  {
    alias Append!(TL, Reverse!(TL)) AppendReverse;
  }

  struct _1 { enum value = 1; }

  template TimesTwo(T)
  {
    enum string result = to!string(T.value * 2);
    mixin(xformat("struct _%1$s { enum value = %1$s; } alias _%1$s TimesTwo;", result));
  }
}

unittest
{
  alias TypeList!(int, char) TL1;

  alias IterateN!(3, Fun1, int) R1;
  alias IterateN!(3, AppendReverse, TL1) R2;
  alias IterateN!(6, TimesTwo, _1) R3;

  // 1-dimensional
  static assert(is(R1 == TypeList!(int, S!int, S!(S!int))));

  // n-dimensional
  static assert(is(R2 == TypeList!(TypeList!(int,char),
                                              TypeList!(int,char,char,int),
                                 TypeList!(int,char,char,int,int,char,char,int))));

  static assert(toString!R3 == "[_1,_2,_4,_8,_16,_32]");
}

/**
   Returns a typelist of length $(B N) with $(B T) the type of every element.

   Examples:
   ---
   alias Replicate!(3, char) R1;
   static assert(is(R1 == TypeList!(char, char, char)));
   ---
*/
template Replicate(int N, T)
{
  static if(N <= 0)
    alias TypeList!() Replicate;
  else
    alias Cons!(T, Replicate!(N-1, T)) Replicate;
}

unittest
{
  alias TypeList!(float, double) TL1;

  alias Replicate!(3, char) R1;
  alias Replicate!(2, TL1) R2;

  static assert(is(R1 == TypeList!(char, char, char)));
  static assert(is(R2 == TypeList!(TL1, TL1)));
}

// -----------------------------------------------------------------------------
//   Subtypelists.
// -----------------------------------------------------------------------------
/**
   Returns the prefix of $(B TL) of length $(B N), or $(B TL) itself if $(B N > TL.length).

   Examples:
   ---
   alias TakeN!(3, TypeList!(C!1, C!2, C!3, C!4, C!5)) R1;
   static assert(is(R1 == TypeList!(C!1, C!2, C!3)));
   ---
*/
template TakeN(int N, TL) if(isTypeList!TL)
{
  static if(N <= 0 || TL.empty)
    alias TypeList!() TakeN;
  else
    alias Cons!(TL.head, TakeN!((N-1), TL.tail)) TakeN;
}

unittest
{
  alias TakeN!(4, Replicate!(2, char)) R1;
  alias TakeN!(2, Replicate!(4, int)) R2;
  alias TakeN!(0, Replicate!(3, float)) R3;

  static assert(is(R1 == TypeList!(char, char)));
  static assert(is(R2 == TypeList!(int, int)));
  static assert(is(R3 == TypeList!()));
}

/*
  Returns the suffix of $(B TL) after the first $(B N) elements, or $(B TypeList!()) if
  $(B N > TL.length).

  Examples:
  ---
  alias DropN!(3, TypeList!(C!1, C!2, C!3, C!4, C!5)) R1;
  static assert(is(R1 == TypeList!(C!4, C!5)));
  ---
*/
template DropN(int N, TL) if(isTypeList!TL)
{
  static if(TL.empty)
    alias TypeList!() DropN;
  else static if(N <= 0)
    alias TL DropN;
  else
    alias DropN!(N-1, TL.tail) DropN;
}

unittest
{
  alias TypeList!(int, char, double, char) TL1;
  alias TypeList!() TL2;

  alias DropN!(2, TL1) R1;
  alias DropN!(5, TL1) R2;
  alias DropN!(0, TL1) R3;
  alias DropN!(3, TL2) R4;

  static assert(is(R1 == TypeList!(double, char)));
  static assert(is(R2 == TypeList!()));
  static assert(is(R3 == TypeList!(int, char, double, char)));
  static assert(is(R4 == TypeList!()));
}

/**
   Returns the longest prefix of $(B TL) of elements that satisfy $(B Pred).

   Examples:
   ---
   alias TypeList!(int, long, char, uint, float) TL1;
   alias TakeWhile!(isIntegral, TL1) R1;
   static assert(is(R1 == TypeList!(int, long)));
   ---
*/
template TakeWhile(alias Pred, TL) if(isTypeList!TL)
{
  static if(TL.empty || !Pred!(TL.head))
    alias TypeList!() TakeWhile;
  else
    alias Cons!(TL.head, TakeWhile!(Pred, TL.tail)) TakeWhile;
}

unittest
{
  alias TypeList!(int, long, char, uint, float) TL1;
  alias TypeList!(float, char, double) TL2;

  alias TakeWhile!(isIntegral, TL1) R1;
  alias TakeWhile!(isIntegral, TL2) R2;

  static assert(is(R1 == TypeList!(int, long)));
  static assert(is(R2 == TypeList!()));
}

/**
   Returns the suffix remaining after $(B TakeWhile!(Pred, TL)).

   Examples:
   ---
   alias TypeList!(int, uint, long, float, double, int) TL1;
   alias DropWhile!(isIntegral, TL1) R1;
   static assert(is(R1 == TypeList!(float, double, int)));
   ---
*/
template DropWhile(alias Pred, TL) if(isTypeList!TL)
{
  static if(TL.empty)
    alias TypeList!() DropWhile;
  else static if(!Pred!(TL.head))
    alias TL DropWhile;
  else
    alias DropWhile!(Pred, TL.tail) DropWhile;
}

unittest
{
  alias TypeList!(int, uint, long, float, double, int) TL1;
  alias TypeList!(float, double, real) TL2;
  alias TypeList!() TL3;

  alias DropWhile!(isIntegral, TL1) R1;
  alias DropWhile!(isIntegral, TL2) R2;
  alias DropWhile!(isIntegral, TL3) R3;

  static assert(is(R1 == TypeList!(float, double, int)));
  static assert(is(R2 == TypeList!(float, double, real)));
  static assert(is(R3 == TypeList!()));
}

// -----------------------------------------------------------------------------
//   Searching typelists.
// -----------------------------------------------------------------------------
/**
   Returns the typelist of those elements that satisfy the predicate.

   Examples:
   ---
   alias TypeList!(int, double, uint, float, long, ulong) TL1;
   alias Filter!(isIntegral, TL1) R1;
   static assert(is(R1 == TypeList!(int, uint, long, ulong)));
   ---
*/
template Filter(alias Pred, TL) if(isTypeList!TL)
{
  static if(TL.empty)
    alias TypeList!() Filter;
  else static if(Pred!(TL.head))
    alias Cons!(TL.head, Filter!(Pred, TL.tail)) Filter;
  else
    alias Filter!(Pred, TL.tail) Filter;
}

unittest
{
  alias TypeList!(int, double, uint, float, long, ulong) TL1;

  alias Filter!(isIntegral, TL1) R1;

  static assert(is(R1 == TypeList!(int, uint, long, ulong)));
}

// -----------------------------------------------------------------------------
//   Zipping typelists.
// -----------------------------------------------------------------------------
/**
   Takes two typelists and zips with the metafunction $(B Fun).

   Examples:
   ---
   alias TypeList!(int, char, double) TL1;
   alias TypeList!(float, long) TL2;
   
   alias ZipWith!(CommonType, TL1, TL2) R1;
   
   static assert(is(R1 == TypeList!(float, long)));
  ---
*/
template ZipWith(alias Fun, TL1, TL2) if(isTypeList!TL1 && isTypeList!TL2)
{
  static if(TL1.empty || TL2.empty)
    alias TypeList!() ZipWith;
  else
    alias Cons!(Fun!(TL1.head, TL2.head), ZipWith!(Fun, TL1.tail, TL2.tail)) ZipWith;
}

unittest
{
  alias TypeList!(int, char, double) TL1;
  alias TypeList!(float, long) TL2;

  alias ZipWith!(CommonType, TL1, TL2) R1;

  static assert(is(R1 == TypeList!(float, long)));
}

// -----------------------------------------------------------------------------
//   The By operations, many of which are EXPERIMENTAL and may be removed.
// -----------------------------------------------------------------------------
/**
   Removes duplicate elements from a typelist.

   Examples:
   ---
   alias TypeList!(int, double, float, int, double, double, char) TL1;

   alias NubBy!(sameTypes, TL1) R1;

   static assert(is(R1 == TypeList!(int, double, float, char)));
   ---
 */
template NubBy(alias Pred, TL) if(isTypeList!TL)
{
  private template Impl(Y)
  {
    alias _not!(Pred!(TL.head, Y)) Impl;
  }

  static if(TL.empty)
    alias TypeList!() NubBy;
  else
    alias Cons!(TL.head, NubBy!(Pred, Filter!(Impl, TL.tail))) NubBy;
}

unittest
{
  alias TypeList!(int, double, float, int, double, double, char) TL1;

  alias NubBy!(sameTypes, TL1) R1;

  static assert(is(R1 == TypeList!(int, double, float, char)));
}

/**
   Removes the first occurrence of $(B X) from its typelist argument using $(B Pred).

   Examples:
   ---
   alias TypeList!(int, float, char, double) TL1;

   alias DeleteBy!(sameTypes, float, TL1) R1;

   static assert(is(R1 == TypeList!(int, char, double)));
   ---
*/
template DeleteBy(alias Pred, X, TL) if(isTypeList!TL)
{
  static if(TL.empty)
    alias TypeList!() DeleteBy;
  else static if(Pred!(X, TL.head))
    alias TL.tail DeleteBy;
  else
    alias Cons!(TL.head, DeleteBy!(Pred, X, TL.tail)) DeleteBy;
}

unittest
{
  alias TypeList!(int, float, char, double) TL1;
  alias TypeList!(char, int) TL2;
  alias TypeList!(double, float) TL3;
  alias TypeList!(TL1, TL2, TL3) TL4;

  alias DeleteBy!(sameTypes, float, TL1) R1;

  alias Curry!(equal, sameTypes) equalTL;
  alias DeleteBy!(equalTL, TL2, TL4) R2;

  static assert(is(R1 == TypeList!(int, char, double)));
  static assert(is(R2 == TypeList!(TypeList!(int, float, char, double),
                                   TypeList!(double, float))));
}

/**
   Returns the typelist union of the two typelists.

   Examples:
   ---
   alias TypeList!(int, double, float) TL1;
   alias TypeList!(char, double, int) TL2;

   alias UnionBy!(sameTypes, TL1, TL2) R1;

   static assert(is(R1 == TypeList!(int, double, float, char)));
   ---
*/
template UnionBy(alias Pred, TL1, TL2) if(isTypeList!TL1 && isTypeList!TL2)
{
  alias NubBy!(Pred, TL2) R1;

  private template FlipDeleteBy(TL, X)
  {
    alias DeleteBy!(Pred, X, TL) FlipDeleteBy;
  }
  alias Append!(TL1, Foldl!(FlipDeleteBy, NubBy!(Pred, TL2), TL1)) UnionBy;
}

unittest
{
  alias TypeList!(int, double, float) TL1;
  alias TypeList!(char, double, int) TL2;

  alias UnionBy!(sameTypes, TL1, TL2) R1;

  static assert(is(R1 == TypeList!(int, double, float, char)));
}

/**
   Returns the typelist intersection of two typelists.

   Examples:
   ---
   alias TypeList!(int, char, float, double) TL1;
   alias TypeList!(double, double, uint) TL2;

   alias IntersectBy!(sameTypes, TL1, TL2) R1;

   static assert(is(R1 == TypeList!(double)));
   ---
*/
template IntersectBy(alias Pred, TL1, TL2) if(isTypeList!TL1 && isTypeList!TL2)
{
  private template Eq(T)
  {
    alias any!(Curry!(Pred, T), TL2) Eq;
  }

  static if(TL1.empty || TL2.empty)
    alias TypeList!() IntersectBy;
  else
    alias Filter!(Eq, TL1) IntersectBy;
}

unittest
{
  alias TypeList!(int, char, float, double) TL1;
  alias TypeList!(double, double, uint) TL2;
  alias TypeList!() TL3;

  alias IntersectBy!(sameTypes, TL1, TL2) R1;
  alias IntersectBy!(sameTypes, TL1, TL3) R2;
  alias IntersectBy!(sameTypes, TL3, TL1) R3;

  static assert(is(R1 == TypeList!(double)));
  static assert(is(R2 == TypeList!()));
  static assert(is(R3 == TypeList!()));
}

private template SpanL(alias Pred, TL)
{
  static if(TL.empty)
    alias TypeList!() SpanL;
  else static if(Pred!(TL.head))
    alias Cons!(TL.head, SpanL!(Pred, TL.tail)) SpanL;
  else
    alias TypeList!() SpanL;
}

private template SpanR(alias Pred, TL)
{
  static if(TL.empty)
    alias TypeList!() SpanR;
  else static if(Pred!(TL.head))
    alias SpanR!(Pred, TL.tail) SpanR;
  else
    alias TL SpanR;
}

/**
   Splits $(B TL) into a typelist of typelists.  $(B Pred) provides the equality test.

   Examples:
   ---
   alias TypeList!(int, int, char, float, float) TL1;

   alias GroupBy!(sameTypes, TL1) R1;

   static assert(is(R1 == TypeList!(TypeList!(int, int), TypeList!(char), TypeList!(float, float))));
   ---
*/
template GroupBy(alias Pred, TL) if(isTypeList!TL)
{
  static if(TL.empty)
    alias TypeList!() GroupBy;
  else
  {
    alias Curry!(Pred, TL.head) P;
    alias Cons!(Cons!(TL.head, SpanL!(P, TL.tail)),
                GroupBy!(Pred, SpanR!(P, TL.tail))) GroupBy;
  }
}

unittest
{
  alias TypeList!(int, int, char, float, float) TL1;

  alias GroupBy!(sameTypes, TL1) R1;

  static assert(is(R1 == TypeList!(TypeList!(int, int), TypeList!(char),
                                   TypeList!(float, float))));
}

/**
   Returns a sorted typelist.

   Examples:
   ---
   struct S1 { enum ordinal = 1; }
   struct S2 { enum ordinal = 2; }
   struct S3 { enum ordinal = 3; }
   struct S4 { enum ordinal = 4; }

   template Less(T1, T2)
   {
     static if(T1.ordinal < T2.ordinal)
       enum Less = true;
     else
       enum Less = false;
   }

   alias TypeList!(S1, S3, S2, S4, S1, S2, S4) TL1;

   alias SortBy!(Less, TL1) R1;

   static assert(is(R1 == TypeList!(S1, S1, S2, S2, S3, S4, S4)));
   ---
*/
template SortBy(alias Less, TL) if(isTypeList!TL)
{
  private template QuickSort(TL1)
  {
    static if(TL1.empty)
      alias TypeList!() QuickSort;
    else
    {
      alias Curry!(Less, TL1.head) GT;
      template LT(T) { enum LT = !GT!(T); }
      
      alias Append!(QuickSort!(Filter!(LT, TL1.tail)),
                    Append!(TypeList!(TL1.head),
                            QuickSort!(Filter!(GT, TL1.tail)))) QuickSort;
    }
  }
  alias QuickSort!TL SortBy;
}

version(unittest)
{
  private struct S1 { enum ordinal = 1; }
  private struct S2 { enum ordinal = 2; }
  private struct S3 { enum ordinal = 3; }
  private struct S4 { enum ordinal = 4; }

  private template Less1(T1, T2)
  {
    static if(T1.ordinal < T2.ordinal)
      enum Less1 = true;
    else
      enum Less1 = false;
  }

  private template Less2(T1, T2)
  {
    static if(isFloatingPoint!T1)
      enum Less2 = true;
    else
      enum Less2 = false;
  }
}

unittest
{
  alias TypeList!(S1, S3, S2, S4, S1, S2, S4) TL1;
  alias TypeList!(int, float, char, double, uint, long, float, int) TL2;

  alias SortBy!(Less1, TL1) R1;
  alias SortBy!(Less2, TL2) R2;

  static assert(is(R1 == TypeList!(S1, S1, S2, S2, S3, S4, S4)));
  static assert(is(R2 == TypeList!(float,double,float,int,long,uint,char,int)));
}
