#			The Biquaternion toolbox
#
# This worksheet generates the package "Biquaternions" with basic functionality
# for working with quaternionic algebras (Hamiltonian quaternions, split
# quaternions, dual quaternions, ...) and certain polynomials over these
# algebras. Focus is on usability, not on efficiency.

# This package is inspired by original code from Josef Schicho, Johannes Kepler
# University Linz, RISC Research Institute for Symbolic Computation.
#
# Authors:
# Daniel Scharler
# University of Innsbruck
# Institute for Basic Sciences in Engineering
# Unit Geometry and Surveying
#
# Hans-Peter Schröcker
# University of Innsbruck
# Institute for Basic Sciences in Engineering
# Unit Geometry and Surveying
#
# Johannes Siegele
# Austrian Academy of Sciences
# RICAM Johann Radon Institute for Computational and Applied Mathematics
#
# Daren A. Thimm
# University of Innsbruck
# Institute for Basic Sciences in Engineering
# Unit Geometry and Surveying


Biquaternions := module()

export init, DefineAlgebra, Mul, Cj, Ej, Quadrance, BQNorm, ScalarInverse, Inv, lQR, rQR, rQuo, rRem, lQuo, lRem, RandR, RandQ, RandBQ, RandL, Primal, Dual, ScalarPart, VectorPart, BQ2L, L2BQ, V2BQ, BQ2V, BQ2Plucker, Plucker2BQ, Act, ActOnLine, ActOnPlane, `&*`, EvalR, EvalL, IP, CP, FiberProject, gcdCPD, LowDegRep, mrpf, IndetBQ:

option package:

global i, j, k, e:

# Some procedures are just used internally and shall not be exposed to regular users.
local EvalRL, pQR, Ugly, Pretty:

# Default to dual quaternions.
# (Dual) split-quaternions are obtained by DefineAlgebra(-1, 1, 0).
init := proc()
  DefineAlgebra(-1, -1, 0):
end:

# protect('i'):
# protect('j'):
# protect('k'):
e := epsilon:
# protect('e'):

DefineAlgebra := proc(a := -1, b := -1, c := 0)
description "Define (bi-)quaternion algebra by relations i^2 = a, j^2 = b, i*j=-j*i over the ring of real polynomials in e modulo e^2 - c.":
  global _BQa, _BQb, _BQc:
  _BQa := a:
  _BQb := b:
  _BQc := c:
  return NULL:
end proc:

Ugly := proc(h)
  # TODO: Make this work for vectors.
  if type(h, list) then
    if nops(h) = 8 then
      return [h[1] + e * h[5], h[2] + e * h[6], h[3] + e * h[7], h[4] + e * h[8]]:
    end if:
    return h:
  end if:
  return [subs(i = 0, j = 0, k = 0, h), coeff(h, i, 1), coeff(h, j, 1), coeff(h, k, 1)]:
  # TODO: Error message?
end proc:

Pretty := proc(h)
  return h[1] + h[2] * i + h[3] * j + h[4] * k;
end proc:

Mul := proc(ap, bp, prettify::boolean := true)
description "Product of two (bi-)quaternions. Depends on global variables _BQa, _BQb, _BQc.":
  # Product of biquaternions.
  global _BQa, _BQb, _BQc, e:
  local raw, T, a, b:
  a := Ugly(ap):
  b := Ugly(bp):
  raw :=
    [ a[1]*b[1] + _BQa*a[2]*b[2] + _BQb*a[3]*b[3] - _BQa*_BQb*a[4]*b[4],
      a[1]*b[2] +      a[2]*b[1] - _BQb*a[3]*b[4] +      _BQb*a[4]*b[3],
      a[1]*b[3] + _BQa*a[2]*b[4] +      a[3]*b[1] -      _BQa*a[4]*b[2],
      a[1]*b[4] +      a[2]*b[3] -      a[3]*b[2] +           a[4]*b[1]
    ]:
  raw := map(T->rem(expand(T), e^2 - _BQc, e), raw):
  if prettify then
    return Pretty(raw):
  end if:
  return raw:
end proc:

Cj := proc(a)
description "(Bi-)Quaternion conjugation. Multiply coefficients of i, j, and k with -1.":
  return subs(i = -i, j = -j, k = -k, a):
end proc:

Ej := proc(a)
description "(Biquaternion epsilon conjugation. Multiply coefficient of e with -1.":
  return subs(e = -e, a):
end proc:

Quadrance := proc(a)
description "The quadrance (norm) of a biquaternion, defined as a &* Cj(a).":
  return Mul(a, Cj(a)):
end proc:

BQNorm := Quadrance:
# BQNorm := proc(a)
# description "The norm (quadrance) of a biquaternion, defined as a &* Cj(a).":
#   return Quadrance(a):
# end proc:

ScalarInverse := proc(a)
description "Inverse of a scalar a = a0 + e * a1 with real a0, a1.":
global _BQc:
local a0, a1:
  a0 := coeff(a, e, 0):
  a1 := coeff(a, e, 1):
  return (a0 - a1 * e) / (a0^2 - _BQc * a1^2):
end proc:

Inv := proc(a)
description "(Bi-)Quaternion inverse.":
  return Mul(ScalarInverse(BQNorm(a)), Cj(a)):
end proc:

# Use `&*' as binary operator for quaternion multiplication.
define(`&*`, `&*`(a::algebraic, b::algebraic) = 'Mul(a, b, true)'):

pQR := proc(F, G, t, right := true)
  description "Quotient Q of polynomial left or right division: There exists a polynomial R such that F = G*Q + R or F = Q*G + R and deg(R, t) < deg(G, t).":
  local Q, R, l, m, n, F0, G0, c, ci:
  c := lcoeff(G, t):
  ci := Inv(c):
  if right then
    F0 := simplify(ci &* F):
    G0 := simplify(ci &* G):
  else
    F0 := simplify(F &* ci):
    G0 := simplify(G &* ci):
  end if:
  Q := 0:
  R := F0:
  m := degree(R, t):
  n := degree(G0, t):
  while m >= n do
    l := lcoeff(R, t):
    Q := Q + Mul(l, t^(m-n)):
    if right then
      R := simplify(R - Mul(G0, l * t^(m-n))):
    else:
      R := simplify(R - Mul(l * t^(m-n), G0)):
    end if:
    m := degree(R, t):
  end do:
  if right then
    return Q, c &* R:
  else
    return Q, R &* c:
  end if:
end proc:

rQR := proc(F, G, t)
description "Quotient Q of polynomial right division: There exists a polynomial R such that F = G*Q + R and deg(R, t) < deg(G, t).":
  return pQR(F, G, t, true):
end proc:

lQR := proc(F, G, t)
description "Quotient Q of polynomial left division: There exists a polynomial R such that F = Q*G + R and deg(R, t) < deg(G, t).":
  return pQR(F, G, t, false):
end proc:

rQuo := proc(F, G, t) description "Right quotient.": return rQR(F, G, t)[1]: end proc:

rRem := proc(F, G, t) description "Right remainder.": return rQR(F, G, t)[2]: end proc:

lQuo := proc(F, G, t) description "Left quotient.": return lQR(F, G, t)[1]: end proc:

lRem := proc(F, G, t) description "Left remainder.": return lQR(F, G, t)[2]: end proc:

RandR := proc(n := 10)
description "Rational random number with coefficients roughly of size n":
  local arb, r:
  arb := rand(-n..n):
  r := (arb() + n + 1) / (arb() + n + 1):
  if rand() < rand() then r := -r end if:
  return r:
end proc:

RandQ := proc(n := 10)
description "Random quaternion with coefficients roughly of size n.":
  return RandR(n) + RandR(n) * i + RandR(n) * j + RandR(n) * k:
end proc:

RandBQ := proc(n := 10)
description "Random bi-quaternion with coefficients roughly of size n.":
  return RandR(n) + RandR(n) * i + RandR(n) * j + RandR(n) * k
  + e * (RandR(n) + RandR(n) * i + RandR(n) * j + RandR(n) * k):
end proc:

RandL := proc(n := 10)
  description "Random Pluecker line with coefficients roughly of size n.":
  local p0,p1,p2,p3,q0,q1,q2,q3:
  p0:=RandR(n): p1:=RandR(n): p2:=RandR(n): p3:=RandR(n):
  q0:=RandR(n): q1:=RandR(n): q2:=RandR(n): q3:=RandR(n):
  return L2BQ([(p0*q1-p1*q0),(p0*q2-p2*q0),(p0*q3-p3*q0),(p2*q3-p3*q2),(p3*q1-p1*q3),(p1*q2-p2*q1)]):
end proc:

Primal := proc(q)
description "Primal part of (bi-)quaternion.":
  return subs(e = 0, q):
end proc:

Dual := proc(q)
description "Dual part of (bi-)quaternion.":
  return coeff(q, e, 1):
end proc:

ScalarPart := proc(q)
description "Scalar part of (bi-)quaternion.":
  return subs(i = 0, j = 0, k = 0, q):
end proc:

VectorPart := proc(q)
description "Vector part of (bi-)quaternion.":
  return q - ScalarPart(q):
end proc:

BQ2L := proc(q, indexlist := [1, 2, 3, 4, 5, 6, 7, 8])
description "Convert (bi-)quaternion to list. Only coefficent present in indexlist are considered. For example, BQ2L(q, [1,2,3,4]) will return the primal part. If indexlist is a positive integer, it is converted to the list [1,2,...,indexlist]. For example, BQ2L(q, 4) will also return the primal part. If negative integers are present in indexlist, the corresponding entry will be multiplied with -1. For example, BQ2L(q, [2,3,4,-6,-7,-8]) converts from biquaternions to the usual Plucker coordinates":
local l, p, d:
  if type(indexlist, posint) then
    return BQ2L(q,[seq(p, p=1..indexlist)]):
  end if:
  p := Primal(q):
  d := Dual(q):
  l := [subs(i = 0, j= 0, k = 0, p),coeff(p, i, 1), coeff(p, j, 1), coeff(p, k, 1),
        subs(i = 0, j = 0, k = 0, d), coeff(d, i, 1), coeff(d, j, 1), coeff(d, k, 1)]:
  d := []:
  for p in indexlist do
    d := [op(d), sign(p) * l[abs(p)]]:
  end do:
  return d:
end proc:

BQ2V := proc(q, indexlist := [1,2,3,4,5,6,7,8])
description "Calls BQ2L and converts result to vector.":
return Vector(BQ2L(q, indexlist)):
end proc:

L2BQ := proc(l)
description "Convert list to (bi-)quaternion.":
  if nops(l) = 4 then
    return l[1] + l[2] * i  + l[3] * j + l[4] * k:
  elif nops(l) = 6 then
    return l[1] * i  + l[2] * j + l[3] * k - e * (l[4] * i + l[5] * j + l[6] * k):
  elif nops(l) = 8 then
    return l[1] + l[2] * i  + l[3] * j + l[4] * k + e * (l[5] + l[6] * i + l[7] * j + l[8] * k):
  end if:
end proc:

V2BQ := proc(v)
description "Convert vector to (bi-)quaternion.":
  return L2BQ(convert(v, list)):
end proc:

BQ2Plucker := proc(q)
description "Convert biquaternion to Plucker coordinates by calling BQ2L(q, [2,3,4,-6,-7,-8]).":
  return BQ2L(q, [2,3,4,-6,-7,-8]):
  end proc:

Plucker2BQ := proc(l)
description "Convert Plucker coordinates (list or vector) to biquaternions":
  if type(l, list) then
    return L2BQ(l):
  end if:
  return V2BQ(l):
end proc:

Act := proc(q, x)
description "Action of (bi-)quaternion q on point x. Some effort is made to identify the type of x (list, vector, quaternion). The return value is of the same type. It is also possible that x represents a line. In this case, action is deferred to procedure ActOnLine.":
local y:
  if type(x, list) then
    if nops(x) = 3 then # Cartesian coordinates
      y := Act(q, 1 + e * (x[1] * i + x[2] * j + x[3] * k)):
      y := BQ2L(y, [1, 6, 7, 8]):
      return [y[2]/y[1], y[3]/y[1], y[4]/y[1]]:
    elif nops(x) = 4 then # homogeneous coordinates
      y := Act(q, x[1] + e * (x[2] * i + x[3] * j + x[4] * k)):
      return BQ2L(y, [1, 6, 7, 8]):
    elif nops(x) = 6 then # assume that we are acting on line
      return ActOnLine(q, x):
    else
      return NULL: # Should not happen! Error handling?
    end if:
  elif type(x, Vector) then
    return convert(Act(q, convert(x, list)), Vector):
  else # biquaternion
    # try to detect lines
    if (expand(ScalarPart(x)) = 0) and (expand(VectorPart(Primal(x))) <> 0) then
      return ActOnLine(q, x):
    end if:
    # ordinary action on dual quaternion
    return Ej(q) &* x &* Cj(q):
  end if:
end proc:

ActOnLine := proc(q, l)
description "Action of biquaternion q on line l, represented as biquaternion, list, or vector.":
  local h:
  if type(l, list) then
    return BQ2L(ActOnLine(q, L2BQ(l)), [2,3,4,-6,-7,-8]):
  elif type(l, Vector) then
    return BQ2V(ActOnLine(q, V2BQ(l)), [2,3,4,-6,-7,-8]):
  end if:
  return q &* l &* Cj(q):
end proc:

ActOnPlane := proc(q, u)
    description "Action of biquaternion q on plane u, represented as biquaternion, list, or vector."
    if type(u, list) then
        return BQ2L(ActOnPlane(q, L2BQ(u))):
    elif type(u, Vector) then
        return BQ2V(ActOnPlane(q, L2BQ(u))):
    end if:
    return Ej(q) &* u &* Cj(q):
end proc:

EvalRL := proc(P, t, h, right := true)
description "Evaluation (right or left) of (bi-)quaternion polynomnial P in indeterminate C at h.":
local n, r, p, l:
  r := coeff(P, t, 0):
  p := 1:
  for l from 1 to degree(P, t) do
    p := p &* h:
    if right then
      r := r + coeff(P, t, l) &* p:
    else
      r := r + p &* coeff(P, t, l):
    end if:
  end do:
  return r:
end proc:

IP := proc(a, b)
description "Inner product, derived from quaternion algebra.":
  return 1/2 * (a &* Cj(b) + b &* Cj(a)):
end proc:

CP := proc(a, b)
description "Cross product, derived from quaternion algebra.":
  return 1/2 * (a &* b - b &* a):
end proc:

EvalR := proc(P, t, h)
description "Right evaluation of (bi-)quaternion polynomial P in indeterminate t at h. Shorthand for Eval(P, t, h, true).":
  return EvalRL(P, t, h, true):
end proc:

EvalL := proc(P, t, h)
description "Left evaluation of (bi-)quaternion polynomial P in indeterminate t at h. Shorthand for Eval(P, t, h, false).":
  return EvalRL(P, t, h, false):
end proc:

FiberProject := proc(Q)
    local p,d,Qproj:
    description "returns the projection of Q onto Studys quadric":
      p := coeff(Q,e,0);
      d := coeff(Q,e,1);
      Qproj := Mul(simplify(2*BQNorm(p)-e*(Mul(p,Cj(d))-Mul(d,Cj(p)))),p,true);
      return Qproj/2;
  end proc:

mrpf := proc(Q)
   local p, d, g, l:

   description "Returns the maximal real polynomial factor of the dual quaternion polynomial Q.":

   p := Ugly(Primal(Q)):
   d := Ugly(Dual(Q)):
   g := 0:

   for l from 1 to 4 do
     g := gcd(g, p[l]):
     g := gcd(g, d[l]):
   end do:

   return g:
end proc:

gcdCPD := proc(Q)
   local p, d, c, g, l, pcjd, cjpd :

   description "Returns the real gcd of c, P &* Cj(D) and Cj(P) &* D for the dual quaternion polynomial cP+eD.":

   c := mrpf(Primal(Q)):
   p := simplify(Primal(Q)/c):
   d := Dual(Q):

   pcjd := BQ2L(Mul(p, Cj(d)))[1..4]:
   cjpd := BQ2L(Mul(Cj(p),d))[1..4]:
   g := gcd(c,pcjd[1]):

   for l from 2 to 4 do
     g := gcd(g,pcjd[l]):
   end do:
   for l from 1 to 4 do
     g := gcd(g,cjpd[l]):
   end do:

   return g:
end proc:

LowDegRep := proc(Q)
    local p, d, c, c1, g, deg, ctemp, z, alpha1, alpha2, t, zlist, lam, h, l, dtemp, Lagr, degtemp:

    description "Returns a representation of the motion Q with the lowest degree possible, but no longer fulfilling Study's condition.":

      c := gcdCPD(Q);
      c1 := mrpf(Primal(Q)):
      p := simplify(Primal(Q)/c1);
      d := Dual(Q);
      t := op(indets(c));
      ctemp := convert(PolynomialTools[Split](c,t),radical);
      z := []:
      alpha1 := 0:
      alpha2 := 0:
      zlist := []:
      lam := 0:

      for h from 1 to nops(ctemp) do
        z := [op(z),PolynomialTools[SquareFreePart](op(h,ctemp),t)-t]:
        degtemp := degree(op(h,ctemp)):
        zlist := [op(zlist),seq(z[-1],g=1..degtemp)]:
      end do:

      zlist := sort(zlist);

      ctemp := 1:
      dtemp := d:

      for l from 1 to nops(zlist) do
        if ((zlist[l]-conjugate(zlist[l]))/I) < 0 then
          alpha1 := LinearAlgebra[DotProduct](Ugly(eval(dtemp,t=zlist[l])),Ugly(eval(p,t=zlist[l])))/LinearAlgebra[DotProduct](Ugly(eval(p,t=zlist[l])),Ugly(eval(p,t=zlist[l])));
          alpha2 := LinearAlgebra[DotProduct](Ugly(eval(dtemp,t=conjugate(zlist[l]))),Ugly(eval(p,t=conjugate(zlist[l]))))/LinearAlgebra[DotProduct](Ugly(eval(p,t=conjugate(zlist[l]))),Ugly(eval(p,t=conjugate(zlist[l]))));
          if alpha1 = alpha2 then
             dtemp := simplify((dtemp - alpha1 * p)/((t-zlist[l])*(t-conjugate(zlist[l]))));
             lam := simplify(lam + alpha1*ctemp);
          else
             Lagr := CurveFitting[PolynomialInterpolation]([[zlist[l],alpha1],[conjugate(zlist[l]),alpha2]],t,form=Lagrange);
             dtemp := simplify((dtemp - Lagr * p)/((t-zlist[l])*(t-conjugate(zlist[l]))));
             lam := simplify(lam + Lagr * ctemp);
          end if;
          ctemp := simplify(ctemp *((t-zlist[l])*(t-conjugate(zlist[l]))));
        end if:
    end do:

   return simplify((Q-e*lam*p)/c):
  end proc:

IndetBQ := proc(x, L := [0, 1, 2, 3, 4, 5, 6, 7])
description "Returns the biquaternion x0 + x1*i + x2*j + x3*k + e*(x4 + x5*i + x6 * j + x7 * k). Onle indices mentioned in the list L are used.":
local l, r, b:
  r := 0:
  b := [1, i, j, k, e, e*i, e*j, e*k]:
  for l in L do
    r := r + x||l * b[l+1]:
  end do:
  return r:
end proc:


end module:
