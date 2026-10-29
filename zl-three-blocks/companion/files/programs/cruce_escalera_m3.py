# Section 5: the three-column ladder 1/2, 2/3, 1 against the published formulas.
fallos = []
for m in range(16, 2001):
    zl = 3 * m // 2 + 2
    assert zl == m + 3 + (m - 2) // 2
    zwl = m + 3 + (2 * m - 4) // 3
    z2 = 2 * m
    if z2 - zwl != (m - 3) // 3 or not (zl <= zwl <= z2):
        fallos.append(m)
print('m = 16..2000: fallos', fallos[:10], 'total', len(fallos))
print('pendientes sobre z(m,3) en m = 2000:', (3 * 2000 // 2 + 2 - 2003) / 2000, ((2 * 2000 - 4) // 3) / 2000, (4000 - 2003) / 2000)
print('z_2(m,4) - z(m,4) en m = 15..20:', [(5 * m + 6) // 2 - (m + 6) for m in range(15, 21)], '(pendiente 3/2)')
