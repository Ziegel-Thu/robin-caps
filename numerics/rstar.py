import math
from capsule_gap import gap, beta0, eigen
L = 1.0
def g(R, alpha, n, lev=2):
    Ncap, Nbulk, Nt = 24*lev, int(max(200, 12*L/R))*lev, 8*lev
    v, _ = eigen(L, R, alpha, n, Ncap, Nbulk, Nt)
    return v[1]-v[0]
for n, alpha in ((2,1.0),(2,4.0),(2,16.0),(3,4.0)):
    Ga = gap(alpha); lo, hi = 0.02, 0.2
    glo, ghi = g(lo,alpha,n), g(hi,alpha,n)
    assert glo < Ga < ghi, (glo, Ga, ghi)
    for _ in range(9):
        mid = 0.5*(lo+hi); gm = g(mid,alpha,n)
        if gm < Ga: lo = mid
        else: hi = mid
    Rs = 0.5*(lo+hi)
    slope = (g(0.01,alpha,n)-gap(beta0(n,alpha)))/0.01
    print(f"n={n} alpha={alpha:5.1f}  R_*={Rs:.4f}  (bracket {lo:.4f},{hi:.4f})  first-order estimate Delta/c={ (Ga-gap(beta0(n,alpha)))/slope:.4f}  c={slope:.3f}")
