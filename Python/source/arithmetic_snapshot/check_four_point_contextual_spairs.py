"""Exact rational S-pair certificates and order checks; no Mathematica."""
from fractions import Fraction as F
from itertools import product
from math import isqrt
from pathlib import Path
import json
import random
import time
import check_contraction_sensitive_order as order

E = ((F(0), F(1)), (F(-1), F(0)))
Z = ((F(0), F(0)), (F(0), F(0)))


def add(*ms):
    return tuple(tuple(sum(m[i][j] for m in ms) for j in range(2)) for i in range(2))


def scale(c, m):
    return tuple(tuple(c*x for x in row) for row in m)


def mul(*ms):
    out = ((F(1), F(0)), (F(0), F(1)))
    for m in ms:
        out = tuple(tuple(sum(out[i][k]*m[k][j] for k in range(2))
                          for j in range(2)) for i in range(2))
    return out


def trans(m):
    return tuple(zip(*m))


def det(m):
    return m[0][0]*m[1][1]-m[0][1]*m[1][0]


def inverse(m):
    return scale(1/det(m), ((m[1][1], -m[0][1]), (-m[1][0], m[0][0])))


def random_frame(rng, mass):
    a, b = rng.randint(-4, 4), rng.randint(-4, 4)
    return ((F(1), F(a)), (F(b), F(mass+a*b)))


class Spinors:
    def __init__(self, masses, left, right):
        self.m = masses
        self.a = {(i,j): mul(trans(left[i]), E, left[j])
                  for i in masses for j in masses}
        self.b = {(i,j): mul(trans(right[i]), E, right[j])
                  for i in masses for j in masses}

    def p(self, i, k, j):
        return mul(self.a[i,k], E, self.b[k,j])

    def q(self, i, k, j):
        return mul(self.b[i,k], E, self.a[k,j])

    def t(self, i, k, l, j):
        return mul(self.a[i,k], E, self.b[k,l], E, self.a[l,j])

    def fp(self, i, j):
        return add(*(self.p(i,k,j) for k in self.m))

    def fq(self, i, j):
        return add(*(self.q(i,k,j) for k in self.m))

    def trace(self, i, j):
        p = self.p(i,j,i)
        return sum(E[u][v]*p[u][v] for u,v in product(range(2), repeat=2))

    def cubic(self, I, J, K, L):
        a,b,m = self.a,self.b,self.m
        return (
            a[1,2][I][J]*self.p(4,2,3)[L][K]
            -a[1,4][I][L]*self.p(2,4,3)[J][K]
            +m[4]*a[1,2][I][J]*b[3,4][K][L]
            +m[2]*a[1,4][I][L]*b[2,3][J][K]
            +m[3]*a[2,4][J][L]*a[1,3][I][K]
            +m[1]*a[2,4][J][L]*b[1,3][I][K]
        )

    def descendant(self, r, I, K, L, R):
        a,b,m = self.a,self.b,self.m
        long = mul(b[3,4], E, a[4,2], E, b[2,r])
        return (
            a[1,4][I][L]*long[K][R]
            +self.p(1,2,r)[I][R]*self.p(4,2,3)[L][K]
            +m[4]*self.p(1,2,r)[I][R]*b[3,4][K][L]
            +m[2]**2*a[1,4][I][L]*b[3,r][K][R]
            -self.p(4,2,r)[L][R]*(m[3]*a[1,3][I][K]+m[1]*b[1,3][I][K])
        )

    def descendant_at_four(self, r, I, J, K, R):
        a,b,m = self.a,self.b,self.m
        long = mul(b[3,2], E, a[2,4], E, b[4,r])
        return (
            -a[1,2][I][J]*long[K][R]
            -self.p(1,4,r)[I][R]*self.p(2,4,3)[J][K]
            -m[4]**2*a[1,2][I][J]*b[3,r][K][R]
            +m[2]*self.p(1,4,r)[I][R]*b[2,3][J][K]
            +self.p(2,4,r)[J][R]*(m[3]*a[1,3][I][K]+m[1]*b[1,3][I][K])
        )


def verify(s, physical):
    a,b,m = s.a,s.b,s.m
    for I,J,K,L in product(range(2), repeat=4):
        cert = (a[1,2][I][J]*s.fp(4,3)[L][K]
                -a[1,4][I][L]*s.fp(2,3)[J][K])
        assert s.cubic(I,J,K,L) == cert
        if physical:
            assert cert == 0
    for r in (1,3,4):
        for I,K,L,R in product(range(2), repeat=4):
            attached = sum(s.cubic(I,J,K,L)*E[J][T]*b[2,r][T][R]
                           for J,T in product(range(2), repeat=2))
            assert attached == s.descendant(r,I,K,L,R)
    for r in (1,2,3):
        for I,J,K,R in product(range(2), repeat=4):
            attached = sum(s.cubic(I,J,K,L)*E[L][T]*b[4,r][T][R]
                           for L,T in product(range(2), repeat=2))
            assert attached == s.descendant_at_four(r,I,J,K,R)
    for r in (1,2,3):
        for I,J,L,R in product(range(2),repeat=4):
            diff=(a[1,4][I][L]*s.p(2,4,r)[J][R]
                  -s.p(1,4,r)[I][R]*a[2,4][J][L])
            assert diff == -m[4]*a[1,2][I][J]*b[4,r][L][R]
        for t in (1,2,3):
            for I,J,R,T in product(range(2),repeat=4):
                diff=(s.p(1,4,r)[I][R]*s.p(2,4,t)[J][T]
                      -s.p(1,4,t)[I][T]*s.p(2,4,r)[J][R])
                assert diff == m[4]**2*a[1,2][I][J]*b[r,t][R][T]

    # Momentum--momentum shared three-bracket host <4|1 3|2>.
    raw_s = add(mul(s.fp(4,3), E, a[3,2]),
                scale(-1, mul(a[4,1], E, s.fq(1,2))))
    raw_formula = add(s.t(4,2,3,2), scale(-1,s.t(4,1,4,2)),
                      scale(m[2],s.p(4,1,2)), scale(-m[4],s.q(4,3,2)),
                      scale(m[3]**2-m[1]**2,a[4,2]))
    assert raw_s == raw_formula
    remainder = add(s.t(4,2,4,2),s.t(4,3,4,2),s.t(4,2,3,2),
                    scale(-m[2],s.p(4,3,2)),scale(-m[4],s.q(4,3,2)),
                    scale(m[4]*m[2],b[4,2]),
                    scale(m[4]**2+m[2]**2+m[3]**2-m[1]**2,a[4,2]))
    reduced_s = add(raw_s,mul(s.fp(4,4),E,a[4,2]),scale(-m[2],s.fp(4,2)))
    assert remainder == reduced_s
    g = {i:sum(s.trace(i,j) for j in m if j!=i)-2*m[i]**2 for i in m}
    trace_remainder = (s.trace(2,3)+s.trace(2,4)+s.trace(3,4)
                       -(m[2]**2+m[3]**2+m[4]**2-m[1]**2))
    assert -(g[1]-g[2]-g[3]-g[4])/2 == trace_remainder
    assert remainder == scale(-trace_remainder,a[4,2])
    # The three determinant-prepared Schouten shortening identities.
    assert s.t(4,2,4,2) == add(scale(-m[4]*m[2],b[4,2]),
                               scale(-s.trace(2,4),a[4,2]))
    assert s.t(4,3,4,2) == add(scale(m[4],s.q(4,3,2)),
                               scale(-s.trace(3,4),a[4,2]))
    assert s.t(4,2,3,2) == add(scale(m[2],s.p(4,3,2)),
                               scale(-s.trace(2,3),a[4,2]))
    if physical:
        assert remainder == Z and trace_remainder == 0
        assert all(s.fp(i,j)==Z and s.fq(i,j)==Z for i in m for j in m)


def order_checks():
    ch,cmp = order.chain,order.cmp
    result = {}
    for n in range(4,9):
        for r in range(1,n):
            B=[ch([1,n],[1]),ch([2,n,r],[1,0])]
            C=[ch([1,n,r],[1,0]),ch([2,n],[1])]
            assert cmp(B,C)==1
            for s in range(1,n):
                Cs=[ch([1,n,s],[1,0]),ch([2,n],[1])]
                assert cmp(B,Cs)==(1 if r<=s else -1)
                Drs=[ch([1,n,r],[1,0]),ch([2,n,s],[1,0])]
                Dsr=[ch([1,n,s],[1,0]),ch([2,n,r],[1,0])]
                assert cmp(Drs,Dsr)==((s>r)-(s<r))
    result["B_C_D_formulas_n4_through_n8"] = True
    left=[ch([1,2],[1]),ch([4,2,3],[1,0])]
    right=[ch([1,4],[1]),ch([2,4,3],[1,0])]
    sqleft=[ch([1,4],[0]),ch([2,4,3],[0,1])]
    sqright=[ch([1,2],[0]),ch([4,2,3],[0,1])]
    assert cmp(left,right)==1 and cmp(sqleft,sqright)==1
    for name,p,q,reverse_port in [("angle_intermediate",left,right,2),
                                  ("square_remainder",sqleft,sqright,4)]:
        records={}
        for port in range(1,5):
            u=next(u for u in p if port in (u[2][0],u[2][-1]))
            color=u[3][0] if u[2][0]==port else u[3][-1]
            for r in range(1,5):
                if r==port: continue
                cp=order.attach_at_unique_endpoint(p,port,[port,r],[1-color])
                cq=order.attach_at_unique_endpoint(q,port,[port,r],[1-color])
                comparison=cmp(cp,cq)
                assert comparison==(-1 if port==reverse_port else 1)
                records[f"port_{port}_to_{r}"]=comparison
        result[name]=records
    # Contextual Schouten head reducing the angle intermediate.
    alternate=[ch([2,4],[1]),ch([1,2,3],[1,0])]
    assert cmp(left,alternate)==1
    # Scalar trace order used in the actual trace S-pair.
    traces=[[order.trace(pair,[1,0])] for pair in [(1,2),(1,3),(1,4),(2,3),(2,4),(3,4)]]
    assert all(cmp(x,y)==1 for x,y in zip(traces,traces[1:]))
    result["trace_order_and_angle_reduction_head"]=True
    return result


def main():
    start=time.perf_counter()
    rng=random.Random(20261020)
    offshell=20
    for _ in range(offshell):
        masses={i:F(rng.randint(1,7)) for i in range(1,5)}
        left={i:random_frame(rng,masses[i]) for i in masses}
        right={i:random_frame(rng,masses[i]) for i in masses}
        verify(Spinors(masses,left,right),False)
        verify(Spinors(masses,right,left),False)
    physical_masses=[]
    trials=0
    while len(physical_masses)<6 and trials<20000:
        trials+=1
        masses={i:F(rng.randint(1,5)) for i in range(1,4)}
        left={i:random_frame(rng,masses[i]) for i in masses}
        right={i:random_frame(rng,masses[i]) for i in masses}
        p4=scale(-1,add(*(mul(left[i],E,trans(right[i])) for i in masses)))
        d=det(p4)
        if d<=0 or d.denominator!=1 or isqrt(d.numerator)**2!=d.numerator:
            continue
        masses[4]=F(isqrt(d.numerator))
        left[4]=((F(1),F(0)),(F(0),masses[4]))
        right[4]=trans(mul(inverse(mul(left[4],E)),p4))
        assert det(right[4])==masses[4]
        verify(Spinors(masses,left,right),True)
        verify(Spinors(masses,right,left),True)
        physical_masses.append([str(masses[i]) for i in range(1,5)])
    assert len(physical_masses)==6
    report={
        "scope":"Exact rational certificate and order checks; not exhaustive completion.",
        "mathematica_started":False,
        "determinant_satisfying_offshell_samples":offshell,
        "momentum_conserving_samples":6,
        "both_chiralities_checked":True,
        "all_free_components_checked":True,
        "physical_masses":physical_masses,
        "order_checks":order_checks(),
        "seconds":time.perf_counter()-start,
    }
    path=Path(__file__).with_name("FourPointContextualSPairs_checks.json")
    path.write_text(json.dumps(report,indent=2)+"\n",encoding="utf-8")
    print(json.dumps(report,indent=2))


if __name__=="__main__":
    main()
