#!/usr/bin/env python3
"""
infer_crc17_mapping_debug.py

Version debug de l'inférence CRC17.
- Identifie et affiche les lignes (indices + contenu) qui provoquent des contradictions.
- Optionnel : exclut automatiquement les lignes en conflit et réessaye.
Usage:
  python infer_crc17_mapping_debug.py captures.csv [--auto-exclude]

Sorties:
  - <input>_crc17_mapping_result.txt  : mapping Python + équations lisibles
  - messages console détaillant les conflits et les trames impliquées
"""

import sys, os, re

# ---------- utilitaires ----------
def byte_bit_index(col_index):
    return (col_index // 8, col_index % 8)

def bits_from_bytes(bytes8):
    mask = 0
    for bidx, b in enumerate(bytes8):
        for bit in range(8):
            if (b >> bit) & 1:
                mask |= (1 << (bidx*8 + bit))
    return mask

# ---------- parser ----------
def parse_input_file(path):
    frames = []
    raw_lines = []
    with open(path, "r", encoding="utf-8") as f:
        for raw in f:
            s = raw.rstrip("\n")
            if not s.strip():
                continue
            raw_lines.append(s)
            # try to extract last 10 hex bytes
            all_hex = re.findall(r"\b[0-9A-Fa-f]{2}\b", s)
            if len(all_hex) < 10:
                # fallback: split by separators and try last token groups
                toks = re.split(r"[|;,]", s)
                if len(toks) >= 3:
                    candidate = toks[-1]
                    toks2 = [t for t in candidate.split() if re.fullmatch(r"[0-9A-Fa-f]{2}", t)]
                    if len(toks2) >= 10:
                        all_hex = toks2[-10:]
            if len(all_hex) >= 10:
                bytes10 = [int(x,16) for x in all_hex[-10:]]
                frames.append(bytes10)
            else:
                frames.append(None)  # keep placeholder to preserve line-index mapping
    return frames, raw_lines

# ---------- solve GF(2) with trace ----------
def solve_gf2_with_trace(A_rows, y_vec, ncols):
    """
    A_rows: list of int masks (each mask has up to ncols bits)
    y_vec: list of 0/1 targets
    returns (solution_list OR None, conflict_mask OR None)
      - if solvable: (sol, None)
      - if inconsistent: (None, mask) where mask is int with bits set for original rows
        that combine to contradiction (i.e. linear combination of original rows -> 0 = 1)
    """
    m = len(A_rows)
    rows = A_rows[:]  # copy
    rhs = y_vec[:]
    # corresponding trace masks: for each current row store which original rows compose it
    trace = [0] * m
    for i in range(m):
        trace[i] = (1 << i)  # only itself initially

    pivot_cols = {}
    r = 0
    for col in range(ncols):
        pivot = None
        for i in range(r, m):
            if ((rows[i] >> col) & 1):
                pivot = i
                break
        if pivot is None:
            continue
        # swap pivot into r
        if pivot != r:
            rows[r], rows[pivot] = rows[pivot], rows[r]
            rhs[r], rhs[pivot] = rhs[pivot], rhs[r]
            trace[r], trace[pivot] = trace[pivot], trace[r]
        pivot_cols[r] = col
        # eliminate this col from all other rows (both above and below)
        for i in range(0, m):
            if i != r and ((rows[i] >> col) & 1):
                rows[i] ^= rows[r]
                rhs[i] ^= rhs[r]
                trace[i] ^= trace[r]   # update trace: XOR of contributing original rows
        r += 1
        if r >= m:
            break

    # check for inconsistency: any zero row mask with rhs==1
    for i in range(r, m):
        if rows[i] == 0 and rhs[i] == 1:
            # contradiction: trace[i] indicates combination of original rows
            return None, trace[i]

    # backsolve: set free vars to 0
    sol = [0] * ncols
    pivot_items = sorted(pivot_cols.items(), key=lambda x: x[0], reverse=True)
    for row_idx, col in pivot_items:
        rowmask = rows[row_idx]
        s = 0
        for j in range(col+1, ncols):
            if ((rowmask >> j) & 1):
                s ^= sol[j]
        sol[col] = rhs[row_idx] ^ s
    return sol, None

# ---------- inference pipeline ----------
def infer_mapping_with_diagnostics(frames_list, auto_exclude=False):
    # frames_list: list of bytes10 lists or None placeholders; preserve indices
    total = len(frames_list)
    # Build list of indices that are valid frames
    valid_indices = [i for i,b in enumerate(frames_list) if b is not None]
    if not valid_indices:
        print("Aucune trame valide fournie.")
        return

    # prepare A_rows and targets per index order (we will preserve original indices)
    def build_matrix(indices_to_use):
        A_rows = []
        targets = [[] for _ in range(17)]
        orig_idx_map = []
        for idx in indices_to_use:
            bytes10 = frames_list[idx]
            b = list(bytes10[:8])
            b[7] = b[7] & 0xFE
            mask = bits_from_bytes(b)
            A_rows.append(mask)
            orig_idx_map.append(idx)
            crc_l = bytes10[8]; crc_h = bytes10[9]
            for i in range(8):
                targets[i].append((crc_l >> i) & 1)
            for i in range(8,16):
                targets[i].append((crc_h >> (i-8)) & 1)
            targets[16].append(bytes10[7] & 1)
        return A_rows, targets, orig_idx_map

    # initial indices to use: all valid ones
    indices = valid_indices[:]

    # we will iteratively detect conflicts and optionally exclude them
    excluded = set()
    while True:
        A_rows, targets, orig_idx_map = build_matrix(indices)
        M = len(A_rows)
        Nbits = 64
        inconsistent_bits = []
        conflicts_detail = {}  # ci -> conflict_mask (original indices mask)
        mapping = {}
        for ci in range(17):
            y = targets[ci][:]
            sol, conflict_mask = solve_gf2_with_trace(A_rows[:], y[:], Nbits)
            if conflict_mask is not None:
                inconsistent_bits.append(ci)
                # translate conflict_mask (bit positions relative to A_rows list) to original frame indices
                # conflict_mask is a bitmask where bit k means A_rows[k] used
                mask = conflict_mask
                involved = []
                k = 0
                while mask:
                    if mask & 1:
                        involved.append(orig_idx_map[k])
                    mask >>= 1
                    k += 1
                conflicts_detail[ci] = involved
                mapping[ci] = None
            else:
                # convert solution list to deps
                deps = []
                for col, bitval in enumerate(sol):
                    if bitval:
                        deps.append(byte_bit_index(col))
                mapping[ci] = deps

        if not inconsistent_bits:
            # success: write mapping and return
            return mapping, excluded, []
        else:
            print("Bits CRC inconsisants détectés :", inconsistent_bits)
            # print conflicts per bit
            for ci, involved in conflicts_detail.items():
                print(f"-> c{ci} contradiction impliquant indices (dans le fichier) : {involved}")
                for idx in involved:
                    print(f"   [{idx}]  {frames_list[idx]}")
            # if auto_exclude, exclude all involved frames and retry
            if auto_exclude:
                # pick unique set of indices appearing in conflicts (smallest set heuristics possible)
                to_exclude = set()
                for v in conflicts_detail.values():
                    to_exclude.update(v)
                print("Auto-exclude ON : exclusion des indices problématiques :", sorted(to_exclude))
                excluded.update(to_exclude)
                indices = [i for i in indices if i not in to_exclude]
                if not indices:
                    print("Après exclusion, plus aucune trame valide. Arrêt.")
                    return None, excluded, inconsistent_bits
                # loop again
                continue
            else:
                # don't auto-exclude, stop and return diagnostics
                return mapping, excluded, inconsistent_bits

# ---------- écrire résultat ----------
def write_result_file(inpath, mapping, excluded, inconsistent_bits, frames_list):
    outpath = os.path.splitext(inpath)[0] + "_crc17_mapping_result.txt"
    with open(outpath, "w", encoding="utf-8") as out:
        out.write("# CRC-17 mapping inference result (debug)\n\n")
        out.write(f"# Frames analysées : {len([f for f in frames_list if f is not None])}\n")
        out.write(f"# Exclues automatiquement : {sorted(list(excluded))}\n")
        out.write(f"# Bits inconsisants (si présent): {inconsistent_bits}\n\n")
        out.write("MAPPING_COMPLETE = {\n")
        for ci in range(17):
            deps = mapping.get(ci)
            if deps is None:
                out.write(f"  {ci}: None,  # no solution / inconsistent\n")
            else:
                out.write("  %d: [%s],\n" % (ci, ", ".join("(%d,%d)"%(b,bit) for b,bit in deps)))
        out.write("}\n\n")
        out.write("# Human-readable equations:\n")
        for ci in range(17):
            deps = mapping.get(ci)
            if deps is None:
                out.write(f"c{ci} = <no solution>\n")
            elif len(deps)==0:
                out.write(f"c{ci} = 0\n")
            else:
                out.write("c%d = %s\n" % (ci, " ^ ".join("b%d_%d"%(b,bit) for b,bit in deps)))
    print("Fichier résultat écrit :", outpath)
    return outpath

# ---------- main CLI ----------
def main():
    if len(sys.argv) < 2:
        print("Usage: python infer_crc17_mapping_debug.py captures.csv [--auto-exclude]")
        sys.exit(1)
    inpath = sys.argv[1]
    auto_exclude = ("--auto-exclude" in sys.argv)
    if not os.path.isfile(inpath):
        print("Fichier introuvable:", inpath); sys.exit(2)
    frames, raw_lines = parse_input_file(inpath)
    mapping, excluded, inconsistent_bits = infer_mapping_with_diagnostics(frames, auto_exclude=auto_exclude)
    if mapping is None:
        print("Echec : aucune solution trouvée après exclusion automatique.")
        sys.exit(3)
    outpath = write_result_file(inpath, mapping, excluded, inconsistent_bits, frames)
    if inconsistent_bits:
        print("Attention : des bits CRC sont restés inconsistants :", inconsistent_bits)
        print("Consulte le fichier et/ou corrige les trames indiquées dans la console ci-dessus.")
    else:
        print("Inférence terminée sans contradiction.")

if __name__ == "__main__":
    main()
