# tiny-chess engine "B" (MIT) - built from scratch as an alternative design.
# 64-square array board with precomputed leaper/ray tables, from-scratch
# evaluation (material + PST + bishop pair + pawn structure), alpha-beta
# with a transposition table, killer + history ordering, check extensions
# and a capture quiescence search. Fixed node budget: no clock, no RNG in
# play, so the same position and history always give the same move.
import json, os, sys, urllib.request
from random import Random

VAL = {'P': 100, 'N': 300, 'B': 315, 'R': 475, 'Q': 950, 'K': 0}
# PSTs from White's side, rank 8 first (square 0 = a8). Black mirrors rows.
PST = {
 'P': [0,0,0,0,0,0,0,0,
       45,45,40,40,40,40,45,45,
       8,12,18,28,28,18,12,8,
       4,6,12,24,24,12,6,4,
       2,4,8,20,20,8,4,2,
       4,2,4,-6,-6,4,2,4,
       6,8,8,-14,-14,8,8,6,
       0,0,0,0,0,0,0,0],
 'N': [-45,-30,-20,-20,-20,-20,-30,-45,
       -30,-12,-2,-2,-2,-2,-12,-30,
       -20,-2,12,16,16,12,-2,-20,
       -20,2,16,22,22,16,2,-20,
       -20,-2,14,20,20,14,-2,-20,
       -20,2,8,12,12,8,2,-20,
       -30,-14,-2,2,2,-2,-14,-30,
       -45,-30,-20,-20,-20,-20,-30,-45],
 'B': [-15,-8,-8,-8,-8,-8,-8,-15,
       -8,2,2,2,2,2,2,-8,
       -8,2,8,10,10,8,2,-8,
       -8,4,10,12,12,10,4,-8,
       -8,2,8,10,10,8,2,-8,
       -8,6,6,6,6,6,6,-8,
       -8,2,2,2,2,2,2,-8,
       -15,-8,-8,-8,-8,-8,-8,-15],
 'R': [2,2,2,2,2,2,2,2,
       10,14,14,14,14,14,14,10,
       -4,0,0,2,2,0,0,-4,
       -4,0,0,2,2,0,0,-4,
       -4,0,0,2,2,0,0,-4,
       -4,0,0,2,2,0,0,-4,
       -4,2,2,2,2,2,2,-4,
       0,0,2,6,6,2,0,0],
 'Q': [-18,-8,-8,-4,-4,-8,-8,-18,
       -8,0,2,2,2,2,0,-8,
       -8,2,4,6,6,4,2,-8,
       -4,2,6,8,8,6,2,-4,
       -4,2,6,8,8,6,2,-4,
       -8,2,4,6,6,4,2,-8,
       -8,0,2,2,2,2,0,-8,
       -18,-8,-8,-4,-4,-8,-8,-18],
 'K': [-25,-35,-35,-45,-45,-35,-35,-25,
       -25,-35,-35,-45,-45,-35,-35,-25,
       -25,-35,-35,-45,-45,-35,-35,-25,
       -15,-25,-25,-35,-35,-25,-25,-15,
       -5,-15,-15,-20,-20,-15,-15,-5,
       15,15,2,0,0,2,15,15,
       15,25,8,0,0,8,25,15,
       15,25,8,0,0,8,25,15],
}
KEND = [-40,-25,-25,-25,-25,-25,-25,-40,
        -25,-18,-8,-8,-8,-8,-18,-25,
        -25,-8,15,22,22,15,-8,-25,
        -25,-8,22,30,30,22,-8,-25,
        -25,-8,22,30,30,22,-8,-25,
        -25,-8,15,22,22,15,-8,-25,
        -25,-18,-8,-8,-8,-8,-18,-25,
        -40,-25,-25,-25,-25,-25,-25,-40]

DIRS = ((-1,0),(1,0),(0,1),(0,-1),(-1,1),(-1,-1),(1,1),(1,-1))
KN_T = []
K_T = []
RAY = []
PAWN_FROM = {'w': [], 'b': []}
for s in range(64):
    r, f = divmod(s, 8)
    kn, kg, rays = [], [], []
    for dr, df in ((-2,-1),(-2,1),(-1,-2),(-1,2),(1,-2),(1,2),(2,-1),(2,1)):
        rr, ff = r + dr, f + df
        if 0 <= rr < 8 and 0 <= ff < 8:
            kn.append(rr * 8 + ff)
    for dr, df in DIRS:
        rr, ff = r + dr, f + df
        if 0 <= rr < 8 and 0 <= ff < 8:
            kg.append(rr * 8 + ff)
    for dr, df in DIRS:
        ray = []
        rr, ff = r + dr, f + df
        while 0 <= rr < 8 and 0 <= ff < 8:
            ray.append(rr * 8 + ff)
            rr += dr
            ff += df
        rays.append(ray)
    KN_T.append(kn)
    K_T.append(kg)
    RAY.append(rays)
    # squares from which a pawn of the given colour attacks s
    wf, bf = [], []
    if r < 7:
        if f > 0: wf.append(s + 7)
        if f < 7: wf.append(s + 9)
    if r > 0:
        if f > 0: bf.append(s - 9)
        if f < 7: bf.append(s - 7)
    PAWN_FROM['w'].append(wf)
    PAWN_FROM['b'].append(bf)

_rnd = Random(424242)
ZB = {}
for pc in 'PNBRQKpnbrqk':
    ZB[pc] = [_rnd.getrandbits(64) for _ in range(64)]
Z_SIDE = _rnd.getrandbits(64)
Z_CAST = {c: _rnd.getrandbits(64) for c in 'KQkq'}
Z_EP = [_rnd.getrandbits(64) for _ in range(8)]

MATE = 100000
NODE_CAP = 40000

bd = ['.'] * 64
turn = 'w'
cast = ''
ep = -1
half = 0
hkey = 0
undo = []
tt = {}
killers = {}
history = {}
nodes = 0
path = []
game_hist = {}

class Abort(Exception):
    pass

def is_white(p):
    return p.isupper()

def evaluate():
    # White-perspective score, computed from scratch.
    score = 0
    phase = 0
    pawns_w = [0] * 8
    pawns_b = [0] * 8
    bishops_w = bishops_b = 0
    kw = kb = -1
    for s in range(64):
        p = bd[s]
        if p == '.':
            continue
        t = p.upper()
        if t == 'K':
            if p == 'K': kw = s
            else: kb = s
            continue
        v = VAL[t] + PST[t][s if p == t else s ^ 56]
        if t == 'P':
            if p == 'P': pawns_w[s & 7] += 1
            else: pawns_b[s & 7] += 1
        elif t == 'B':
            if p == 'B': bishops_w += 1
            else: bishops_b += 1
        if t in 'NBRQ':
            phase += (1, 1, 2, 4)['NBRQ'.index(t)]
        score += v if p == t else -v
    # king: blend middlegame / endgame tables by phase (max 24)
    ph = min(phase, 24)
    score += (PST['K'][kw] * ph + KEND[kw] * (24 - ph)) // 24
    score -= (PST['K'][kb ^ 56] * ph + KEND[kb ^ 56] * (24 - ph)) // 24
    if bishops_w >= 2: score += 25
    if bishops_b >= 2: score -= 25
    for f in range(8):
        if pawns_w[f] > 1: score -= 15 * (pawns_w[f] - 1)
        if pawns_b[f] > 1: score += 15 * (pawns_b[f] - 1)
        if pawns_w[f] and not ((f > 0 and pawns_w[f - 1]) or (f < 7 and pawns_w[f + 1])):
            score -= 12
        if pawns_b[f] and not ((f > 0 and pawns_b[f - 1]) or (f < 7 and pawns_b[f + 1])):
            score += 12
    return score

def attacked(s, by_white):
    pawn = 'P' if by_white else 'p'
    for x in PAWN_FROM['w' if by_white else 'b'][s]:
        if bd[x] == pawn:
            return True
    knight = 'N' if by_white else 'n'
    for x in KN_T[s]:
        if bd[x] == knight:
            return True
    king = 'K' if by_white else 'k'
    for x in K_T[s]:
        if bd[x] == king:
            return True
    bishop = 'B' if by_white else 'b'
    rook = 'R' if by_white else 'r'
    queen = 'Q' if by_white else 'q'
    for d in range(4, 8):
        for x in RAY[s][d]:
            p = bd[x]
            if p != '.':
                if p == bishop or p == queen:
                    return True
                break
    for d in range(0, 4):
        for x in RAY[s][d]:
            p = bd[x]
            if p != '.':
                if p == rook or p == queen:
                    return True
                break
    return False

def gen_moves(captures_only=False):
    white = turn == 'w'
    ms = []
    for s in range(64):
        p = bd[s]
        if p == '.' or is_white(p) != white:
            continue
        t = p.upper()
        r, f = divmod(s, 8)
        if t == 'P':
            step = -8 if white else 8
            start_row = 6 if white else 1
            promo_row = 0 if white else 7
            for df in (-1, 1):
                if (df == -1 and f == 0) or (df == 1 and f == 7):
                    continue
                u = s + step + df
                q = bd[u]
                if q != '.' and is_white(q) != white:
                    if (u >> 3) == promo_row:
                        for pr in 'QRNB':
                            ms.append((s, u, pr))
                    else:
                        ms.append((s, u, None))
                elif u == ep:
                    ms.append((s, u, None))
            u = s + step
            if bd[u] == '.':
                if (u >> 3) == promo_row:
                    for pr in 'QRNB':
                        ms.append((s, u, pr))
                elif not captures_only:
                    ms.append((s, u, None))
                    if r == start_row and bd[s + 2 * step] == '.':
                        ms.append((s, s + 2 * step, None))
        elif t == 'N' or t == 'K':
            for u in (KN_T[s] if t == 'N' else K_T[s]):
                q = bd[u]
                if q == '.':
                    if not captures_only:
                        ms.append((s, u, None))
                elif is_white(q) != white:
                    ms.append((s, u, None))
            if t == 'K' and not captures_only:
                enemy = not white
                if white and s == 60:
                    if 'K' in cast and bd[61] == bd[62] == '.' and bd[63] == 'R' and not attacked(60, enemy) and not attacked(61, enemy) and not attacked(62, enemy):
                        ms.append((60, 62, None))
                    if 'Q' in cast and bd[59] == bd[58] == bd[57] == '.' and bd[56] == 'R' and not attacked(60, enemy) and not attacked(59, enemy) and not attacked(58, enemy):
                        ms.append((60, 58, None))
                if not white and s == 4:
                    if 'k' in cast and bd[5] == bd[6] == '.' and bd[7] == 'r' and not attacked(4, enemy) and not attacked(5, enemy) and not attacked(6, enemy):
                        ms.append((4, 6, None))
                    if 'q' in cast and bd[3] == bd[2] == bd[1] == '.' and bd[0] == 'r' and not attacked(4, enemy) and not attacked(3, enemy) and not attacked(2, enemy):
                        ms.append((4, 2, None))
        else:
            dirs = range(4, 8) if t == 'B' else range(0, 4) if t == 'R' else range(8)
            for d in dirs:
                for u in RAY[s][d]:
                    q = bd[u]
                    if q == '.':
                        if not captures_only:
                            ms.append((s, u, None))
                    else:
                        if is_white(q) != white:
                            ms.append((s, u, None))
                        break
    return ms

def do_move(m):
    global turn, cast, ep, half, hkey
    frm, to, pr = m
    p = bd[frm]
    white = is_white(p)
    cap = bd[to]
    cap_sq = to
    if p.upper() == 'P' and to == ep and cap == '.' and (frm & 7) != (to & 7):
        cap_sq = to + 8 if white else to - 8
        cap = bd[cap_sq]
    undo.append((m, cap, cap_sq, cast, ep, half, hkey))
    hkey ^= Z_SIDE
    if ep >= 0:
        hkey ^= Z_EP[ep & 7]
    ep = -1
    bd[frm] = '.'
    hkey ^= ZB[p][frm]
    if cap != '.':
        bd[cap_sq] = '.'
        hkey ^= ZB[cap][cap_sq]
        half = 0
    if pr:
        np_ = pr if white else pr.lower()
    else:
        np_ = p
    bd[to] = np_
    hkey ^= ZB[np_][to]
    if p.upper() == 'P':
        half = 0
        if abs(to - frm) == 16:
            ep = (frm + to) // 2
            hkey ^= Z_EP[ep & 7]
    elif cap == '.':
        half += 1
    if p.upper() == 'K' and abs(to - frm) == 2:
        if to > frm:
            rf, rt = frm + 3, frm + 1
        else:
            rf, rt = frm - 4, frm - 1
        rook = bd[rf]
        bd[rf] = '.'
        bd[rt] = rook
        hkey ^= ZB[rook][rf] ^ ZB[rook][rt]
    newcast = cast
    if p == 'K': newcast = newcast.replace('K', '').replace('Q', '')
    if p == 'k': newcast = newcast.replace('k', '').replace('q', '')
    if frm == 63 or to == 63: newcast = newcast.replace('K', '')
    if frm == 56 or to == 56: newcast = newcast.replace('Q', '')
    if frm == 7 or to == 7: newcast = newcast.replace('k', '')
    if frm == 0 or to == 0: newcast = newcast.replace('q', '')
    for cch in cast:
        if cch not in newcast:
            hkey ^= Z_CAST[cch]
    cast = newcast
    turn = 'b' if turn == 'w' else 'w'

def undo_move():
    global turn, cast, ep, half, hkey
    (m, cap, cap_sq, cast, ep, half, hkey) = undo.pop()
    turn = 'b' if turn == 'w' else 'w'
    frm, to, pr = m
    p = bd[to]
    if pr:
        p = 'P' if is_white(p) else 'p'
    bd[frm] = p
    bd[to] = '.'
    if cap != '.':
        bd[cap_sq] = cap
    if p.upper() == 'K' and abs(to - frm) == 2:
        if to > frm:
            rf, rt = frm + 3, frm + 1
        else:
            rf, rt = frm - 4, frm - 1
        bd[rf] = bd[rt]
        bd[rt] = '.'

def king_sq(white):
    return bd.index('K' if white else 'k')

def in_check():
    white = turn == 'w'
    return attacked(king_sq(white), not white)

def move_score(m, tt_move, ply):
    if m == tt_move:
        return 1 << 28
    frm, to, pr = m
    cap = bd[to]
    if cap != '.':
        return (1 << 24) + VAL[cap.upper()] * 16 - VAL[bd[frm].upper()]
    if pr:
        return (1 << 24) + 8000 + VAL[pr]
    kl = killers.get(ply)
    if kl and m == kl[0]:
        return 1 << 20
    if kl and m == kl[1]:
        return (1 << 20) - 1
    return history.get((turn, m), 0)

def qsearch(alpha, beta, ply):
    global nodes
    nodes += 1
    if nodes > NODE_CAP:
        raise Abort()
    if half >= 100:
        return 0
    chk = in_check()
    stand = (1 if turn == 'w' else -1) * evaluate()
    if not chk:
        if stand >= beta:
            return beta
        if stand > alpha:
            alpha = stand
    best = -MATE - 100
    n = 0
    ms = gen_moves(not chk)
    ms.sort(key=lambda m: move_score(m, None, ply), reverse=True)
    for m in ms:
        do_move(m)
        if attacked(king_sq(turn != 'w'), turn == 'w'):
            undo_move()
            continue
        s = -qsearch(-beta, -alpha, ply + 1)
        undo_move()
        n += 1
        if s > best: best = s
        if s > alpha: alpha = s
        if alpha >= beta: break
    if n == 0:
        return -MATE + ply if chk else stand
    return best

def search(depth, alpha, beta, ply):
    global nodes
    if depth <= 0:
        return qsearch(alpha, beta, ply)
    nodes += 1
    if nodes > NODE_CAP:
        raise Abort()
    if ply > 0 and half >= 100:
        return 0
    chk = in_check()
    if chk:
        depth += 1  # check extension
    tt_move = None
    ent = tt.get(hkey)
    if ent:
        ed, efl, esc, emv = ent
        tt_move = emv
        if ed >= depth and ply > 0:
            if efl == 0:
                return esc
            if efl == 1:
                alpha = max(alpha, esc)
            else:
                beta = min(beta, esc)
            if alpha >= beta:
                return esc
    ms = gen_moves(False)
    ms.sort(key=lambda m: move_score(m, tt_move, ply), reverse=True)
    best = -MATE - 100
    bm = None
    flag = 2
    n = 0
    for m in ms:
        do_move(m)
        if attacked(king_sq(turn != 'w'), turn == 'w'):
            undo_move()
            continue
        if hkey in path or (ply % 2 == 1 and game_hist.get(hkey)):
            s = 0
        else:
            path.append(hkey)
            s = -search(depth - 1, -beta, -alpha, ply + 1)
            path.pop()
        undo_move()
        n += 1
        if s > best:
            best = s
            bm = m
        if s > alpha:
            alpha = s
            flag = 0
            history[(turn, m)] = history.get((turn, m), 0) + depth * depth
        if alpha >= beta:
            flag = 1
            frm, to, pr = m
            if bd[to] == '.' and not pr:
                kl = killers.setdefault(ply, [None, None])
                if kl[0] != m:
                    kl[1] = kl[0]
                    kl[0] = m
            break
    if n == 0:
        return -MATE + ply if chk else 0
    tt[hkey] = (depth, flag, best, bm)
    return best

def set_fen(fen):
    global turn, cast, ep, half, hkey
    parts = fen.split()
    for i in range(64):
        bd[i] = '.'
    for i, row in enumerate(parts[0].split('/')):
        f = 0
        for ch in row:
            if ch.isdigit():
                f += int(ch)
            else:
                bd[i * 8 + f] = ch
                f += 1
    turn = parts[1]
    cast = '' if parts[2] == '-' else parts[2]
    if parts[3] == '-':
        ep = -1
    else:
        ep = (8 - int(parts[3][1])) * 8 + 'abcdefgh'.index(parts[3][0])
    half = int(parts[4]) if len(parts) > 4 else 0
    hkey = 0
    for s in range(64):
        p = bd[s]
        if p != '.':
            hkey ^= ZB[p][s]
    if turn == 'b':
        hkey ^= Z_SIDE
    for cch in cast:
        hkey ^= Z_CAST[cch]
    if ep >= 0:
        hkey ^= Z_EP[ep & 7]
    undo.clear()
    path.clear()

def choose():
    global nodes
    ms = [m for m in gen_moves(False) if _legal(m)]
    if not ms:
        return None
    best_move = ms[0]
    nodes = 0
    path.append(hkey)
    d = 1
    while d < 100:
        try:
            search_root(d)
            best_move = root_best
        except Abort:
            break
        d += 1
    path.pop()
    return best_move

root_best = None

def search_root(depth):
    global root_best
    alpha = -MATE - 100
    beta = MATE + 100
    ent = tt.get(hkey)
    tt_move = ent[3] if ent else None
    ms = gen_moves(False)
    ms.sort(key=lambda m: move_score(m, tt_move, 0), reverse=True)
    best = -MATE - 100
    for m in ms:
        do_move(m)
        if attacked(king_sq(turn != 'w'), turn == 'w'):
            undo_move()
            continue
        path.append(hkey)
        s = -search(depth - 1, -beta, -alpha, 1)
        path.pop()
        undo_move()
        if s > best:
            best = s
            root_best = m
        if s > alpha:
            alpha = s
    return best

def _legal(m):
    do_move(m)
    bad = attacked(king_sq(turn != 'w'), turn == 'w')
    undo_move()
    return not bad

def to_uci(m):
    frm, to, pr = m
    s = 'abcdefgh'[frm & 7] + str(8 - (frm >> 3)) + 'abcdefgh'[to & 7] + str(8 - (to >> 3))
    if pr:
        s += pr.lower()
    return s

def from_uci(u):
    frm = 'abcdefgh'.index(u[0]) + (8 - int(u[1])) * 8
    to = 'abcdefgh'.index(u[2]) + (8 - int(u[3])) * 8
    pr = u[4].upper() if len(u) > 4 else None
    return (frm, to, pr)

def post(path, body):
    req = urllib.request.Request(
        os.getenv('MAKEFUN_ENV_URL', '') + path,
        data=json.dumps(body).encode(),
        headers={'content-type': 'application/json'})
    return json.load(urllib.request.urlopen(req))

def main():
    global game_hist
    game = -1
    while True:
        g = post('/game', {})
        if g['status'] == 'done':
            break
        while g['status'] == 'your_move':
            if g['game'] != game:
                game = g['game']
                game_hist = {}
                tt.clear()
            set_fen(g['fen'])
            game_hist[hkey] = game_hist.get(hkey, 0) + 1
            try:
                mv = to_uci(choose())
            except Exception:
                mv = None
            if mv not in g['legal_moves']:
                mv = g['legal_moves'][0]
            g = post('/move', {'game': g['game'], 'move': mv})
        print('game', g['game'], g.get('outcome'), g.get('reason'), file=sys.stderr)

if __name__ == '__main__':
    main()
