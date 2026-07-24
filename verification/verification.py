import pathlib
import re
import ast
import subprocess
import shutil
import time
import sys
from sage.all import ZZ, prod
from sage.libs.gap.libgap import libgap
from sage.databases.cremona import class_to_int
from collections import defaultdict


data = pathlib.Path("DATA")

def sort_key(label):
    """
    Sort labels first by the order of the group, then the tiebreaker, which may be an integer, a lower case Cremona code, or an underscore then upper case Cremona code (to support MacOS's case insensitivity).
    """
    N, i = label.split(".")
    N = int(N)
    if i[0] == "_":
        return [N, 1, class_to_int(i[1:].lower())]
    if i.isdigit():
        return [N, 0, int(i)]
    return [N, 0, class_to_int(i)]

def check_var(v):
    """
    Check that a user provided variable name is a valid GAP identifier.
    """
    return re.fullmatch("[a-zA-Z][a-zA-Z0-9_]*", v)

def check_vars(x):
    """
    Check that all user provided variable names are valid GAP identifiers and return them.

    INPUT:

    - ``x`` -- a comma separated string of variable names.
    """
    variables = [v.strip() for v in x.split(",")]
    invalid = [v for v in variables if not check_var(v)]
    if invalid:
        if len(invalid) == 1:
            msg = f"{invalid[0]} is not a valid variable name"
        else:
            msg = f"{','.join(invalid)} are not valid variable names"
        raise ValueError(msg)
    return variables

def check_valid_expr(x):
    """
    Check that an expression is valid defining a group element.

    INPUT:

    - ``x`` -- an ast Expression consisting of constants, names, negation, multiplication and exponentiation (parsed by Python as BitXor.  Note that BitXor has different precedence than exponentiation, so the parsed object from ast will not be correct, but it will be valid if and only if the expression will parse correctly as a group element in GAP.

    OUTPUT:

    Raises an error if the expression is not of the correct form, otherwise returns the set of all used variable names.
    """
    if isinstance(x, ast.BinOp):
        if x.op.__class__ not in [ast.BitXor, ast.Mult]:
            raise ValueError("Only multiplication and exponentiation allowed in relation")
        return check_valid_expr(x.left).union(check_valid_expr(x.right))
    elif isinstance(x, ast.UnaryOp):
        if x.op.__class__ != ast.USub:
            raise ValueError("Only multiplication, exponentiation and negation allowed in relation")
        return check_valid_expr(x.operand)
    elif isinstance(x, ast.Name):
        return {x.id}
    elif isinstance(x, ast.Constant):
        return set()
    else:
        raise ValueError(f"Only constants, variables, multiplication and exponentiation allowed; got {x.__class__.__name__}")

def check_valid_relation(x, variables, allow_mult=False):
    """
    Check that the given expression is a valid group element in the context that a given set of variables has been defined already.

    INPUT:

    - ``x`` -- a string, expressing a group element in terms of the specified variables and the normal group operations.
    - ``variables`` -- a set of already-defined variable names
    - ``allow_mult`` -- whether to allow multiple lines in ``x``

    OUTPUT:

    Raises an error if x does not parse or if there are undefined variables; returns the lines in x as a list of strings otherwise.
    """
    try:
        parsed = ast.parse(x).body
    except Exception as err:
        raise ValueError(f"Relation does not parse: {str(err)}")
    if not allow_mult and len(parsed) > 1:
        raise ValueError("Relation must be a single expression")
    for r in parsed:
        undefined = check_valid_expr(r.value).difference(variables)
        if undefined:
            raise ValueError(f"Undefined variables: {','.join(undefined)}")
    return [line for line in x.split("\n") if line.strip()]

def check_valid_defs(x, variables):
    """
    Check that the given definition sequence is valid, and return it in a normalized form for inclusion in a GAP function.

    INPUT:

    - ``x`` -- a string, with each line defining a variable in terms of previous variables.
    - ``variables`` -- a set of initially defined variable names.

    OUTPUT:

    A normalized string, appropriate for inclusion in a GAP function.
    """
    lines = x.split("\n")
    for i, line in enumerate(lines):
        if line.count("=") != 1:
            raise ValueError("Each line in the definition section must set the value of one variable")
        pieces = line.split("=")
        v = pieces[0].rstrip(":").strip()
        if not check_var(v):
            raise ValueError(f"{v} is not a valid variable name")
        rhs = pieces[1].rstrip(";").strip()
        check_valid_relation(rhs, variables)
        variables.add(v)
        lines[i] = f"{v} := {rhs};"
    return "\n    ".join(lines), variables

def setup_gap_script(p, Fpath=None):
    """
    Converts the relation file into a GAP script defining CheckRel and LiftGal methods.
    """
    if Fpath is None:
        Fpath = data / str(p) / "rel.txt"
    with open(Fpath) as F:
        pieces = F.read().split("\n\n")
        if len(pieces) == 2:
            variables = check_vars(pieces[0])
            defs, allvars = "", set(variables)
            rels = check_valid_relation(pieces[1], allvars, allow_mult=True)
        elif len(pieces) == 3:
            variables = check_vars(pieces[0])
            defs, allvars = check_valid_defs(pieces[1], set(variables))
            rels = check_valid_relation(pieces[2], allvars, allow_mult=True)
        else:
            raise ValueError(f"Relation file {Fpath} must have either two or three sections")
    script_path = data / str(p) / "lift.g"
    with open(script_path, "w") as Fout:
        varset = "\n    ".join(f"{v} := tup[{i}];" for i,v in enumerate(variables,1))
        rels = " and ".join(f"{rel} = tup[1]^0" for rel in rels)
        _ = Fout.write(f"""CheckRel := function(tup)
    local {', '.join(sorted(allvars))};
    {varset}
    {defs}
    return {rels};
end;

""")
        with open("lift.g") as F:
            _ = Fout.write(F.read())

def make_eltstore(p, recursing):
    """
    Creates a cache folder that stores in progress computations.  Checks that the relation file hasn't changed,
    deleting the cache if it has.
    """
    datap = data / str(p)
    eltstore = datap / "eltstore"
    toppath = pathlib.Path("rel.txt")
    relpath = datap / "rel.txt"
    if toppath.exists():
        shutil.copy(toppath, relpath)
    if not relpath.exists():
        raise ValueError("No relation given in rel.txt")
    with open(relpath) as F:
        contents = F.read()
        pieces = contents.split("\n\n")
        r = pieces[0].count(",") - 1
        if r <= 0:
            raise ValueError("Must provide at least one wild generator")
        if recursing:
            # We've already dealt with clearing eltstore in the parent process
            return r, eltstore
        newhash = hash(contents)
        relhash = datap / "relhash"
        if relhash.exists():
            with open(relhash) as F:
                curhash = int(F.read())
        else:
            curhash = None
        if eltstore.exists() and curhash is not None and newhash != curhash:
            shutil.rmtree(eltstore)
    with open(relhash, "w") as F:
        _ = F.write(str(newhash))
    setup_gap_script(p)
    eltstore.mkdir(exist_ok=True)
    (datap / "race").mkdir(exist_ok=True)
    return r, eltstore

def case_label(label):
    # Ugh; MacOS is case insensitive
    N, i = label.split(".")
    if i[0] != "_" and i.isupper():
        return f"{N}._{i}"
    return label

def setup(p, qcutoff=None, ncores=None, base_limit=None, verbose=False):
    """
    This function was used in setting up the data folders, and is not directly used in verification.

    Input parameters are passed on to the main function in the case p=2.

    This function takes as input the files proj1.txt, tame1.txt, gps1.txt and cnts0.txt
    created by make_group_data.py and precompute.m and
    creates the files proj.txt, tame.txt, gps.txt and cnts.txt
    (updating LMFDB counts using the cnt_ppow function)
    """
    datap = data / str(p)
    cnt = {}
    with open(datap / "cnts0.txt") as F:
        for line in F:
            label, c = line.strip().split("|")
            label = case_label(label)
            cnt[label] = int(c)
    tame = set()
    with open(datap / "tame1.txt") as F:
        with open(datap / "tame.txt", "w") as Fout:
            for line in F:
                pieces = line.strip().split("|")
                label, elts = case_label(pieces[0]), pieces[3]
                _ = Fout.write(f"{label}|{elts}\n")
                tame.add(label)
    gpdata = {}
    with open(datap / "gps2.txt") as F:
        for line in F:
            label, desc, gens = line.strip().split("|")
            label = case_label(label)
            gpdata[label] = (desc, gens)
    proj = defaultdict(lambda: defaultdict(list))
    for ischar, fname in [(True, "projchar.txt"), (False, "proj1.txt")]:
        with open(datap / fname) as F:
            for line in F:
                lab, qlab, size, Ngens, imgs = line.strip().split("|")
                lab, qlab = case_label(lab), case_label(qlab)
                proj[lab][ischar,int(size)].append((qlab, imgs))
    paths = defaultdict(list)
    for lab, D in proj.items():
        for key, L in D.items():
            for qlab, imgs in L:
                paths[qlab].append(lab)
    accessible = set(tame)
    cur = set(tame)
    while cur:
        next = set()
        for base in cur:
            for tip in paths[base]:
                if tip not in accessible and tip in gpdata:
                    accessible.add(tip)
                    next.add(tip)
        cur = next
    def best(D):
        if len(set(x[0] for x in D)) < 2:
            return min(D)
        bestchar = min(x[1] for x in D if x[0])
        bestnorm = min(x[1] for x in D if not x[0])
        if bestchar <= 4*bestnorm:
            return True, bestchar
        return False, bestnorm
    goodproj = defaultdict(list)
    for lab, D in proj.items():
        if lab not in accessible:
            continue
        D = {key: [pair for pair in val if pair[0] in accessible] for key, val in D.items()}
        D = {key: val for key, val in D.items() if val}
        assert D
        ischar, size = best(D)
        for qlab, imgs in D[ischar, size]:
            if qlab in accessible:
                goodproj[qlab].append((lab, imgs, ischar))
    codcnt = defaultdict(list)
    for qlab, L in goodproj.items():
        if qlab not in cnt:
            codcnt[len(L)].append(qlab)
    M = max(codcnt) + 1
    for qlab, L in goodproj.items():
        if qlab in cnt:
            codcnt[M].append(qlab)
    chosen = {}
    # We try to choose projections that map to "common" codomains, in hopes of not using some codomains
    for m in sorted(codcnt, reverse=True):
        for qlab in codcnt[m]:
            for lab, imgs, ischar in goodproj[qlab]:
                if lab not in chosen:
                    chosen[lab] = (qlab, imgs, ischar)
    gps = set(proj).union(tame)
    def is_2pow(x):
        N, i = x.split(".")
        return x in chosen and ZZ(N).is_power_of(2) and (i.isdigit() or i.islower())
    gps = set(x for x in gps if x in cnt or is_2pow(x))
    cur = set(gps)
    while cur:
        new = set()
        for lab in cur:
            if lab not in tame:
                qlab, imgs, ischar = chosen[lab]
                if qlab not in gps:
                    gps.add(qlab)
                    new.add(qlab)
        cur = new
    with open(datap / "gps.txt", "w") as Fgps:
        with open(datap / "proj.txt", "w") as Fproj:
            for lab in sorted(gps, key=sort_key):
                if lab not in gpdata:
                    with open(datap / "nogp.txt", "a") as Fout:
                        _ = Fout.write(f"{lab}\n")
                    continue
                desc, gens = gpdata[lab]
                _ = Fgps.write(f"{lab}|{desc}|{gens}\n")
                if lab not in tame:
                    qlab, imgs, ischar = chosen[lab]
                    Fproj.write(f"{lab}|{qlab}|{int(ischar)}|{imgs}\n")
    with open(datap / "cnts.txt", "w") as Fout:
        for label, c in sorted(cnt.items(), key=lambda x: sort_key(x[0])):
            if label in gps:
                _ = Fout.write(f"{label}|{c}\n")
    cnt_ppow(p, qcutoff=qcutoff, ncores=ncores, base_limit=base_limit, verbose=verbose)
    setup_gap_script(p)

def expected_counts(p):
    """
    Reads the stored counts for each group into a dictionary
    """
    datap = data / str(p)
    cnt = {}
    with open(datap / "cnts.txt") as F:
        for line in F:
            label, c = line.strip().split("|")
            cnt[label] = int(c)
    return cnt

def actual_counts(p):
    """
    Reads the computed counts (from a specified presentation) into a dictionary
    """
    eltstore = data / str(p) / "eltstore"
    cnt = {}
    for path in eltstore.iterdir():
        with open(path) as F:
            c = 0
            for line in F:
                if line.strip():
                    c += 1
            cnt[path.name] = c
    return cnt

def cnt_ppow(p, qcutoff=None, ncores=None, base_limit=None, verbose=False):
    """
    Updates the file with stored counts by computing counts for groups
    whose order is a power of p.

    For odd p, this is done using a formula of Shafarevich
    (On p-extensions, Mat. Sb. 20 (1947), no. 62, 351–363).
    For even p, this is done using the same lifting method as is used for
    verification, but using the much simpler relation x^2*y^3*y^z that is
    valid for the maximal pro-2 quotient.
    """
    datap = data / str(p)
    if p == 2:
        Fpath = datap / "rel.txt"
        with open(Fpath, "w") as F:
            _ = F.write("z,tau,x,y\n\nx^2*y^3*y^z")
        main(2, qcutoff=qcutoff, qonly=True, ncores=ncores, base_limit=base_limit, verbose=verbose)
        cnt = actual_counts(p)
    else:
        libgap.Read("IO.g")
        cnt = {}
        with open(datap / "gps.txt") as F:
            for line in F:
                label, desc, gens = line.strip().split("|")
                N = ZZ(label.split(".")[0])
                if not N.is_power_of(p):
                    continue
                vprint(label, verbose)
                G = libgap.StringToGroup(desc)
                H = G.FrattiniSubgroup()
                q = ZZ(H.Order())
                d = (N // q).exact_log(p)
                if d > 2:
                    cnt[label] = 0
                else:
                    Asize = ZZ(G.AutomorphismGroup().Order())
                    c = (N // p**d)**2 * prod([p**2 - p**i for i in range(d)])
                    assert c % Asize == 0
                    cnt[label] = c // Asize
    for label, c in expected_counts(p).items():
        if ZZ(label.split(".")[0]).is_power_of(p) and c != cnt[label]:
            raise RuntimeError(f"Count for {label} ({cnt[label]}) does not agree with saved value ({c})")
    with open(datap / "cnts.txt", "w") as F:
        for label in sorted(cnt, key=sort_key):
            _ = F.write(f"{label}|{cnt[label]}\n")

def is_saved(label, datap):
    """
    Checks if tuples have been saved for the given label.

    INPUT:

    - ``label`` -- the label of a group from gps.txt
    - ``datap`` -- a Path object for ``data/p/``
    """
    return (datap / "eltstore" / label).exists()

def load_elts(label, datap, gps):
    """
    Loads saved tuples into a list of GAP elements suitable for further lifting.

    INPUT:

    - ``label`` -- the label of a group from gps.txt
    - ``datap`` -- a Path object for ``data/p/``
    - ``gps`` -- the dictionary produced by load_groups
    """
    with open(datap / "eltstore" / label) as F:
        T = gps[label]
        return [[libgap.LoadElt(ZZ(x), T) for x in line.strip().split(",")] for line in F if line.strip()]

def save_elts(elts, label, datap, gps):
    """
    INPUT:

    - ``elts`` -- a list of lists of GAP elements, storing the lifted tuples for a given group.
    - ``label`` -- the label of the group containing the elements
    - ``datap`` -- a Path object for ``data/p``
    - ``gps`` -- the dictionary produced by load_groups
    """
    race = (datap / "race" / label)
    race.touch()
    with open(datap / "eltstore" / label, "w") as F:
        T = gps[label]
        _ = F.write("\n".join(",".join(str(libgap.SaveElt(g, T)) for g in tup) for tup in elts) + "\n")
    race.unlink()

def clear_race(p):
    """
    If a verification run was interrupted in the middle of writing to disk,
    it's possible that eltstore could be corrupted.  To prevent this, a race folder exists.
    This function is called to clean up any files that were not completed correctly.
    """
    datap = data / str(p)
    eltstore = datap / "eltstore"
    for race in list((datap / "race").iterdir()):
        label = race.name
        race.unlink()
        (eltstore / label).unlink(missing_ok=True)

def vprint(s, verbose):
    """
    A utilty function that prints the string ``s`` only if ``verbose`` is true.
    """
    if verbose:
        print(s)

def set_abort(p):
    """
    Creates a file signaling that an early abort has been triggered (allowing other processes to abort).

    Also raises an error so this process stops.
    """
    fname = data / str(p) / "abort"
    fname.touch()
    raise ValueError("Aborting (mismatched count)")

def check_abort(p):
    """
    Checks whether another process has created an early abort file, raising a KeyboardInterrupt if so.
    """
    fname = data / str(p) / "abort"
    if fname.exists():
        print("Early abort: mismatched count")
        raise KeyboardInterrupt

def clear_abort(p):
    """
    Delete any created early abort file, in preparation for future runs.
    """
    fname = data / str(p) / "abort"
    fname.unlink(missing_ok=True)

def status(p, gps, expected, cache, slen):
    """
    Prints a status report, based on progress from subprocesses.

    INPUT:

    - ``p`` -- the prime being run
    - ``gps`` -- the dictionary produced by load_groups
    - ``expected `` -- the dictionary produced by expected_counts
    - ``cache`` -- a dictionary for saving counts computed by counting lines in the ``eltstore`` folder.
      This dictionary is progressively updated upon each call to this function.
    - ``slen`` -- the length of the previous status message

    OUTPUT:

    The length of this status message.
    """
    if not gps:
        return
    eltstore = data / str(p) / "eltstore"
    gnum = 0 # number of finished groups
    gden = len(gps)
    enum = 0 # number of finished elements
    eden = 0
    tnum = 0 # number of finished tuples
    tden = 0
    bad = []
    for label in gps:
        N = int(label.split(".")[0])
        eden += N
        path = eltstore / label
        if path.exists():
            gnum += 1
            enum += N
            if label in expected:
                if label not in cache:
                    c = 0
                    with open(path) as F:
                        for line in F:
                            if line.strip():
                                c += 1
                    if c == expected[label]:
                        cache[label] = c
                    else:
                        # Might have caught another process in the middle of writing, so we don't save to cache
                        bad.append(label)
                else:
                    c = cache[label]
                tnum += c
        if label in expected:
            tden += expected[label]
    if bad:
        if len(bad) > 4:
            examples = ", ".join(bad[:3]) + "..."
        else:
            examples = ", ".join(bad)
        bad = f", {len(bad)} not matching expected count ({examples})"
    else:
        bad = ""
    msg = f"{gnum}/{gden} groups done ({gnum/gden:.2%}, {enum/eden:.2%} by size, {tnum/tden:.2%} by tuple count){bad}"
    if len(msg) < slen:
        msg, slen = msg + " "*(slen - len(msg)), len(msg)
    else:
        slen = len(msg)
    print(msg, end="\r")
    return slen

def report(p, gps, expected, projelts=None, interrupted=False):
    """
    Print a final report based on comparing the computed counts with the expected ones.

    INPUT:

    - ``p`` -- the prime being run
    - ``gps`` -- the dictionary produced by ``load_groups``
    - ``expected`` -- the dictionary produced by ``expected_counts``
    - ``projelts`` -- the dictionary containing tuples constructed in ``main``.  If not provided, counts are read using ``actual_counts``.
    - ``interrupted`` -- whether this report is being issued after the main process received a KeyboardInterrupt
    """
    clear_abort(p)
    clear_race(p)
    if projelts is None:
        actual = actual_counts(p)
    else:
        actual = {label: len(L) for label,L in projelts.items()}
    bad = []
    missing = []
    for label in gps:
        if label in expected:
            if label in actual:
                if expected[label] != actual[label]:
                    bad.append(label)
            else:
                missing.append(label)
    if not bad and not missing and not interrupted:
        print("Verification successful!")
    else:
        if interrupted:
            print("Interrupted, quitting...")
        elif bad:
            print("Verification unsuccessful")
        elif missing:
            print("Verification not completely successful")
        if bad:
            bad.sort(key=sort_key)
            print("For the following groups, your presentation did not predict the correct number of extensions with the given Galois group")
            for label in bad:
                print(f"{label}: {expected[label]} predicted, {actual[label]} actual")
        if missing and not interrupted:
            missing.sort(key=sort_key)
            if len(missing) == 1:
                print(f"The verification script did not finish for {missing[0]}")
            elif len(missing) < 10:
                print(f"For the following {len(missing)} groups, the verification script did not finish: {', '.join(missing)}")
            else:
                print(f"The verification script did not finish for {len(missing)} groups: {', '.join(missing[:4])}...")

def load_tree(datap, base, verbose):
    if base is None:
        tree = None
    else:
        vprint(f"Lifting from base {base}", verbose)
        tree = {base}
    projcod = {}
    with open(datap / "proj.txt") as F:
        for line in F:
            domain, codomain, ischar, imgs = line.strip().split("|")
            projcod[domain] = codomain
            if base is not None and codomain in tree:
                tree.add(domain)
    return projcod, tree

def load_groups(p, base, tree, qonly, qcutoff, verbose):
    vprint("Loading groups...", verbose)
    from sage.libs.gap.util import GAPError
    datap = data / str(p)
    gps = {}
    gens = {}
    with open(datap / "gps.txt") as F:
        for line in F:
            label, desc, elts = line.strip().split("|")
            if base is not None and label not in tree:
                continue
            if qonly or qcutoff is not None:
                N = ZZ(label.split(".")[0])
                pp, k = N.is_prime_power(get_data=True)
                if (qonly and pp != p and N != 1) or (qcutoff is not None and pp == p and k > qcutoff):
                    continue
            if elts:
                elts = elts.split(",")
            else:
                elts = []
            gps[label] = G = libgap.StringToGroup(desc)
            gens[label] = [libgap.LoadElt(ZZ(x), G) for x in elts]
    return gps, gens

def load_proj(datap, gps, gens, base, tree, verbose):
    vprint("Loading projections...", verbose)
    proj = defaultdict(list)
    with open(datap / "proj.txt") as F:
        for line in F:
            domain, codomain, ischar, imgs = line.strip().split("|")
            if domain not in gps or base is not None and codomain not in tree:
                # qcutoff was set, or we are not above the specified base
                continue
            dom = gps[domain]
            cod = gps[codomain]
            ischar = (ischar == "1")
            pi = libgap.GroupHomomorphismByImages(dom, cod, gens[domain], [libgap.LoadElt(ZZ(x), cod) for x in imgs.split(",")])
            proj[domain].append((codomain, ischar, pi))
    return proj

def initialize_projelts(datap, gps, base, tree, r, verbose):
    vprint(f"Loading saved tuples...", verbose)
    projelts = {}
    for label in tree:
        if is_saved(label, datap):
            projelts[label] = load_elts(label, datap, gps)
    tame = set()
    if base is None:
        vprint("Loading tame elts...", verbose)
        with open(datap / "tame.txt") as F:
            for line in F:
                label, elts = line.strip().split("|")
                if label not in gps:
                    # qcutoff was set
                    continue
                tame.add(label)
                if label in projelts:
                    # Already loaded from saved data
                    continue
                T = gps[label]
                elts = elts.split(";")
                elts = [[libgap.LoadElt(ZZ(x), T) for x in y.split(",")] + [T.One() for _ in range(r)] for y in elts]
                projelts[label] = elts
                save_elts(elts, label, datap, gps)
    return projelts, tame

def prep_parallel(datap, gps, base_limit, tame, projcod, projelts):
    if base_limit is None:
        base_limit = 100
    endpoint = {t:t for t in tame}
    for domain, codomain in projcod.items():
        if domain not in gps:
            # qcutoff or qonly was set
            continue
        N = int(domain.split(".")[0])
        if N <= base_limit:
            endpoint[domain] = domain
        else:
            endpoint[domain] = endpoint[codomain]
    by_endpoint = defaultdict(list)
    for domain, ep in endpoint.items():
        by_endpoint[ep].append(domain)
    tree = [ep for ep in by_endpoint if ep not in projelts]
    bases = [ep for ep,domains in by_endpoint.items() if any(domain not in projelts for domain in domains)]
    with open(datap / "bases.txt", "w") as F:
        _ = F.write("\n".join(bases) + "\n")
    return tree

def run_lifting(p, projelts, gps, proj, tree, early_abort, expected, verbose):
    datap = data / str(p)
    vprint("Lifting tuples...", verbose)
    slen = 0
    cache = {}
    for label in tree:
        G = gps[label]
        if label not in projelts:
            vprint(f"Starting {label}...", verbose)
            codomain, ischar, pi = proj[label][0]
            projelts[label] = elts = libgap.LiftGal(projelts[codomain], pi, ischar, 0)
            if label in expected and len(elts) != expected[label]:
                # GAP has exhibited some unreproducible issues, so as a first step we try again
                vprint(f"Incorrect count for {label}; trying again", verbose)
                projelts[label] = elts = libgap.LiftGal(projelts[codomain], pi, ischar, 0)
            if early_abort and label in expected and len(elts) != expected[label]:
                set_abort(p)
            save_elts(elts, label, datap, gps)
            if not verbose:
                slen = status(p, gps, expected, cache, slen)
    if not verbose:
        print(" "*slen)

def get_subprocess_cmd(p, ncores, timeout, early_abort, qcutoff, verbose):
    datap = data / str(p)
    timeout = f" --timeout {timeout}" if timeout else ""
    e = " -e" if early_abort else ""
    k = f" -k {qcutoff}" if qcutoff is not None else ""
    v = " -v" if verbose else ""
    return "parallel -j %s%s -a %s ./verify -p %s%s%s%s -b {1}" % (ncores, timeout, datap / "bases.txt", p, e, k, v)

def run_subprocess(p, gps, expected, ncores, qcutoff, timeout, early_abort, verbose):
    cmd = get_subprocess_cmd(p, ncores, timeout, early_abort, qcutoff, verbose)
    if verbose:
        subprocess.run(cmd, shell=True)
    else:
        print("Starting parallel subprocess")
        proc = subprocess.Popen(cmd, shell=True, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
        try:
            cache = {}
            slen = 0
            while True:
                time.sleep(1) # TODO: Reset to 0.2
                code = proc.poll()
                if code is not None:
                    print(" "*slen) # Clear progress message
                    if code != 0:
                        print(f"parallel terminated with exit code {code}")
                    break
                if early_abort:
                    check_abort()
                slen = status(p, gps, expected, cache, slen)
        except KeyboardInterrupt:
            print(" "*slen)
            proc.terminate() # Stops new jobs from being created
            proc.terminate() # Kills running jobs
            report(p, gps, expected, interrupted=True)
            time.sleep(1)
            proc.kill()
            sys.exit(130)


def main(p, base=None, base_limit=None, qcutoff=None, qonly=False, ncores=None, early_abort=False, timeout=None, verbose=False):
    """
    The main counting function: loads data from appropriate files, lifts tuples to count fields, compares with expected counts and prints a final report.

    INPUT:

    - ``base`` -- a group label.  If provided, only groups mapping to the specified base will be computed.  Mainly used by subprocesses in a parallelized computation.
    - ``base_limit`` -- an integer, the limit on the size of groups computed in an initial run before splitting into subprocesses.  Only used if ncores is also provided, defaults to 100.
    - ``qcutoff`` -- if provided, p-groups whose order is larger than p^qcutoff are omitted
    - ``qonly`` -- if true, only p-groups are counted
    - ``ncores`` -- the number of cores to use
    - ``early_abort`` -- if true, the computation will stop after the first incorrect count.  If false, the computation will proceed and issue a final report showing the number of failures.
    - ``verbose`` -- if true, more details about which groups are in progress will be shown.  Note that setting verbose to true will disable the ongoing status report if run in parallel.
    - ``timeout`` -- passed on to GNU parallel, setting a maximum time used for each subprocess.  May not work on MacOS.
    """
    print("Setting up computation...")
    datap = data / str(p)
    r, eltstore = make_eltstore(p, base is not None)
    expected = expected_counts(p)
    libgap.InfoPerformance.SetInfoLevel(0) # Skip messages about "If you gave a domain and not seeds consider `OrbitsDomain' instead."
    libgap.Read("IO.g")
    libgap.Read(str(datap / "lift.g"))
    projcod, tree = load_tree(datap, base, verbose)

    gps, gens = load_groups(p, base, tree, qonly, qcutoff, verbose)

    proj = load_proj(datap, gps, gens, base, tree, verbose)
    if base is None:
        tree = list(gps)
    else:
        tree = [label for label in gps if label in tree]

    projelts, tame = initialize_projelts(datap, gps, base, tree, r, verbose)
    if base is None and ncores is not None:
        tree = prep_parallel(datap, gps, base_limit, tame, projcod, projelts)

    run_lifting(p, projelts, gps, proj, tree, early_abort, expected, verbose)

    if base is None:
        if ncores is None:
            report(p, gps, expected, projelts)
        else:
            run_subprocess(p, gps, expected, ncores, qcutoff, timeout, early_abort, verbose)
            report(p, gps, expected)

def setup_for_test(p=2):
    r = 2
    base = None
    base_limit = 1024
    qcutoff = None
    qonly = False
    ncores = None
    early_abort = False
    timeout = None
    verbose = True

    datap = data / str(p)
    libgap.Read("IO.g")
    libgap.Read(str(datap / "lift.g"))
    projcod, tree = load_tree(datap, base, verbose)

    gps, gens = load_groups(p, base, tree, qonly, qcutoff, verbose)

    proj = load_proj(datap, gps, gens, base, tree, verbose)
    tree = list(gps)

    projelts, tame = initialize_projelts(datap, gps, base, tree, r, verbose)
    X = set(x for x in projelts if x.startswith("1024."))
    Y = [label for label,ischar,y in proj.items() if y[0][0] in X]

    return gps, proj, projelts, Y

def write_chars(p):
    libgap.Read("IO.g")
    datap = data / str(p)
    gps2 = datap / "gps2.txt"
    chartxt = datap / "char.txt"
    charall = datap / "charall.txt"
    pchar = datap / "projchar.txt"
    if not gps2.exists():
        with open(datap / "gps1.txt") as F:
            with open(gps2, "w") as Fout:
                for line in F:
                    pieces = line.split("|")
                    N, i = pieces[0].split(".")
                    if i.isupper():
                        pieces[0] = f"{N}._{i}"
                        line = "|".join(pieces)
                    _ = Fout.write(line)
    if not chartxt.exists():
        print("Finding characteristic subgroups")
        gps, gens = load_groups(p, base=None, tree=None, qonly=False, qcutoff=None, verbose=False)
        for label, G in gps.items():
            write_char(label, G)
    while True:
        print("Labeling with magma")
        subprocess.run(f"magma -b p:={p} write_char.m", shell=True)
        fname = datap / "new_groups.txt"
        if fname.exists():
            with open(fname) as F:
                new_groups = [line.strip() for line in F if line.strip()]
            fname.unlink()
        else:
            new_groups = []
        fname = datap / "new_char.txt"
        if fname.exists():
            with open(fname) as F:
                projchar = [line.strip() for line in F if line.strip()]
            fname.unlink()
        else:
            projchar = []
        #projchar, new_groups = magma.GetProjChar(p, nvals=2)
        #projchar, new_groups = [str(line).strip() for line in projchar], [str(line).strip() for line in new_groups]
        print("Wiping char.txt")
        with open(charall, "a") as Fout:
            with open(chartxt) as F:
                for line in F:
                    _ = Fout.write(line)
        chartxt.unlink()
        print("Writing projchar.txt")
        with open(pchar, "a") as Fout:
            for line in projchar:
                _ = Fout.write(line + "\n")
        if new_groups:
            print("Writing new groups")
            with open(gps2, "a") as Fout:
                for line in new_groups:
                    _ = Fout.write(line + "\n")
            print("Computing characteristic subgroups")
            for line in new_groups:
                label, desc, gens = line.split("|")
                G = libgap.StringToGroup(desc)
                write_char(label, G, p)
        else:
            break

def write_char(label, G, p):
    print(label)
    datap = data / str(p)
    Cs = G.CharacteristicSubgroups()
    Cs = [N for N in Cs if ZZ(N.Order()).is_power_of(p) and N.Order() != 1]
    if Cs:
        q = min(ZZ(N.Order()) for N in Cs)
        Cs = [N for N in Cs if ZZ(N.Order()) == q]
        with open(datap / "char.txt", "a") as F:
            for N in Cs:
                Nstr = ",".join(str(g.SaveElt(G)) for g in N.GeneratorsOfGroup())
                _ = F.write(f"{label}|{q}|{Nstr}\n")
    else:
        with open(datap / "nochar.txt", "a") as F:
            _ = F.write(label + "\n")

