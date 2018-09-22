from collections import defaultdict
from itertools import combinations
from sage.misc.cachefunc import cached_method
from sage.misc.lazy_attribute import lazy_attribute
#from sage.rings.arith import primitive_root
import sage.interfaces.gap
import re, os, sys
zero_re = re.compile(r"([0-9]+)T([0-9]+) \(p=([0-9]+)\)")
count_re = re.compile(r"([0-9]+)T([0-9]+) \(p=([0-9]+)\) ([0-9]+)")
wild_re = re.compile(r" Wild p=(\d+) (\d+)G([a-z0-9]+) (\d+)([TC])(\d+)( over (\d+)G(\d+) --)?( e(\d+) f(\d+)( \(ns \d+\))?;?)*")
gid_re = re.compile(r"(\d+)G([a-z0-9]+)")
DEBUG = True


class GroupList(object):
    """
    This class organizes the computation of potentially p-realizable groups
    of order up to a given bound.

    It relies on GAP's library of small groups, and thus will skip orders divisible by 512,
    since GAP cannot identify such groups.

    The data are stored in a dictionary ``groups``, where for each order,
    groups[order] is a list of labels for that order (e.g. "6G2")

    INPUT:

    - p -- a prime
    - Gbound -- an upper bound on orders to consider
    - Gstart -- a lower bound on orders to consider
    - db -- either None or a pair giving lower and upper bounds on the gap ids to examine in testing for potential p-realizability
    - filename -- a filename to use when loading and saving groups.  Loading and saving are done during the initialization of this object.
    """
    def __init__(self, p, Gbound, Gstart=2, db=None, filename=None):
        self.p = p
        self.Gbound = Gbound
        self.db = db
        if filename is None:
            filename = "glist%s"%p
        self.filename = filename
        self.groups = defaultdict(list)
        self.load()
        for order in srange(Gstart, Gbound):
            if order in self.groups or order.valuation(2) >= 9:
                continue
            if order % p != 0 and gap.NumberSmallGroups(order) > 16:
                gps = ["%sG%s"%(order, i) for i in self._list_tame(order, verbose=True)]
            elif order.valuation(p) == 1 and gap.NumberSmallGroups(order) > 32:
                gps = ["%sG%s"%(order, i) for i in self._list_ext(order, verbose=True)]
            else:
                gps = ["%sG%s"%(order, i) for i in self._list_db(order, verbose=True)]
            self.groups[order] = sorted(list(set(gps)), key=_label_key)
            print "G%s complete"%(order)
            self.save()

    def save(self):
        """
        Save the list of groups.
        """
        with open(self.filename, 'w') as F:
            for order in sorted(self.groups.keys()):
                F.write("%s: %s\n"%(order, " ".join(self.groups[order])))

    def load(self):
        """
        Load the list of groups from the file.
        """
        if not os.path.exists(self.filename):
            return
        with open(self.filename) as F:
            for line in F:
                if not line:
                    continue
                order, gps = line.split(':')
                gps = gps.strip()
                if gps:
                    self.groups[ZZ(order)] = gps.split(' ')

    def _list_tame(self, order, verbose=False):
        """
        Compute the list of potentially p-realizable groups with trivial G_1.

        When the order is prime to p, these will exhaust the potentially p-realizable groups.
        """
        p = self.p
        ids = []
        for k in ZZ(order).divisors():
            m = order // k
            if not m.divides(p^k-1):
                continue
            for l in range(0, m, m // m.gcd(p-1)):
                G = self.metacyclic(k, l, m)
                i = int(G.IdSmallGroup()[2])
                ids.append(i)
                if verbose:
                    print "%sG%s tame %s-adic"%(order, i, p)
        return sorted(list(set(ids)))

    def _list_ext(self, order, verbose=False):
        """
        Compute the list of potentially p-realizable groups where G_1
        is either trivial or cyclic of order p.

        When the p-adic valuation of the order is 1, these will exhaust the potentially p-realizable groups.
        """
        p = self.p
        ids = []
        if order.valuation(p) != 1:
            raise RuntimeError
        tames = self._list_tame(order//p)
        C = gap.CyclicGroup(p-1)
        for i in tames:
            tame = gap.SmallGroup(order//p, i)
            Tgens = tame.GeneratorsOfGroup()
            for f in tame.AllHomomorphisms(C):
                cgen = C.MinimalGeneratingSet()[1]
                M = gap.GModuleByMats([[[gap.Z(p)^stupid_exp(f.Image(g), cgen, p)]] for g in Tgens], gap.GF(p))
                for H in tame.Extensions(M):
                    i = int(H.IdSmallGroup()[2])
                    ids.append(i)
                    if verbose:
                        print "%sG%s potentially %s-adic"%(order, i, p)
        ids.extend(self._list_tame(order,verbose=verbose))
        return sorted(list(set(ids)))

    def _list_db(self, order, verbose=False):
        """
        Compute the complete list of potentially p-realizable groups
        using GAP's small group library.

        While this function will produce all potentially p-realizable groups of a given order,
        its running time scales linearly with the number of groups of the given order.
        """
        p = self.p
        ids = []
        skipped = 0
        N = gap.NumberSmallGroups(order)
        if self.db is None:
            db0 = 1
            db1 = N+1
        else:
            db0 = max(1, self.db[0]+1)
            db1 = min(N+1, self.db[1]+1)
        for i in range(db0,db1):
            G = gap.SmallGroup(order, i).IsomorphismPermGroup().Image()
            E = ExtensionProblem(G, p)
            if E.is_potentially_padic():
                ids.append(i)
                skipped = 0
                if verbose:
                    print "%sG%s potentially %s-adic"%(order, i, p)
            else:
                skipped += 1
                if verbose and skipped % 10 == 0:
                    print "%s groups remaining in order %s"%(db1-i-1, order)
        return sorted(list(set(ids)))

    def load_ndata(self):
        for file in os.listdir('IGPdata'):
            if file.startswith("ndata_"):
                with open('IGPdata/' + file) as F:
                    #label = file[6:]
                    #size = ZZ(F.read().split(':')[0])
                    #self.groups[size].append(label)
                    for line in F:
                        self.groups[ZZ(line.strip())].append(file[6:])
                        break
        self.clean()

    def clean(self):
        """
        Canonicalize the groups dictionary: make sure that the lists of group ids are non-empty, duplicate-free, and sorted.
        """
        for order in self.groups:
            self.groups[order] = sorted(list(set(self.groups[order])), key=_label_key)
            if not self.groups[order]:
                del self.groups[order]
        self.save()

    def metacyclic(self, k, l, m):
        """
        Returns the metacyclic group with parameters k, l, m, p.

        This is the group with presentation <x, y | x^k = y^l, y^m = 1, y^x = y^p>
        """
        F = gap.FreeGroup(2)
        x, y = F.GeneratorsOfGroup()
        G = F.FactorGroupFpGroupByRels([x^k*y^(-l), y^m, x^(-1)*y*x*y^(-self.p)])
        return G.IsomorphismPermGroup().Image()

    def count_small_normals(self):
        """
        Gather statistics on the smallest nontrivial normal subgroups of potentially p-realizable groups.

        OUTPUT:

        A dictionary Ncount so that Ncount[m] is the number of groups in this
        GroupList with nontrivial p-core whose minimal normal subgroup has size m.
        """
        p = self.p
        Ncount = defaultdict(int)
        for order, L in self.groups.iteritems():
            if order % p != 0:
                continue
            for label in L:
                if 'G' not in label:
                    continue
                G = _get_group(label)
                if G.IsAbelian():
                    continue
                V = G.PCore(p)
                if V.Size() == 1:
                    continue
                print label
                m = min(ZZ(N.Size()) for N in G.MinimalNormalSubgroups())
                Ncount[m] += 1
        return Ncount

class GroupPoset(object):
    """
    This class records information on maximal quotients to be used in iteratively
    counting p-adic extensions.

    INPUT:

    - GL -- a GroupList
    - ord_bounds -- a pair of integers giving an interval [a,b) of orders to compute.
    - filename -- a filename to load and save data

    The data is stored in the maxquo dictionary, whose keys are labels of nonabelian groups
    and whose values are lists of quotients (up to isomorphism) given by their GAP label.
    """
    def __init__(self, GL, ord_bounds=None, filename=None):
        self.GL = GL
        if filename is None:
            if ord_bounds is None:
                filename = "gposet%s"%(GL.p)
            else:
                filename = "gposet%s_%s_%s"%(GL.p, ord_bounds[0], ord_bounds[1])
        self.filename = filename
        self.maxquo = defaultdict(lambda: defaultdict(int))
        self.load()
        for order in sorted(GL.groups.keys()):
            if ord_bounds is not None and (order < ord_bounds[0] or order >= ord_bounds[1]):
                continue
            for label in GL.groups[order]:
                if label in self.maxquo:
                    continue
                if self._explore(order, label):
                    # abelian
                    self.maxquo[label] = defaultdict(int)
                else:
                    self.save(label)
                    print label + " complete"

    def save(self, label=None):
        """
        Save to a file.

        If label is None, will save all the quotients.
        Otherwise, will append the data for the given label.
        """
        if label is None:
            with open(self.filename, 'w') as F:
                for label in sorted(self.maxquo.keys(), key=_label_key):
                    qlabels = sorted(self.maxquo[label].keys(), key=_label_key, reverse=True)
                    F.write("%s: %s\n"%(label, " ".join("%s^%s"%(qlabel, self.maxquo[label][qlabel]) for qlabel in qlabels)))
        else:
            with open(self.filename, 'a') as F:
                F.write("%s: %s\n"%(label, " ".join("%s^%s"%(qlabel, count) for qlabel, count in self.maxquo[label].iteritems())))

    def load_line(self, line):
        """
        Loads data from a line, in the format used by the save function.
        """
        label, quos = line.split(':')
        quos = quos.strip()
        if quos:
            quos = quos.split(' ')
            for quo in quos:
                qlabel, count = quo.split('^')
                self.maxquo[label][qlabel] = int(count)
        else:
            self.maxquo[label] = defaultdict(int)

    def load(self):
        """
        Load data from a file.
        """
        if not os.path.exists(self.filename):
            return
        with open(self.filename) as F:
            for line in F:
                self.load_line(line)

    def clean(self):
        """
        Canonicalize the data by deleting data from abelian labels.
        """
        for label in self.maxquo.keys():
            if _get_group(label).IsAbelian():
                del self.maxquo[label]
        self.save()

    def _explore(self, order, label):
        """
        Fill out the maxquo dictionary with quotients of the group given by label.

        INPUT:

        - order -- the size the group
        - label -- the GAP label for the group
        """
        subsumed = set([])
        G = _get_group(label)
        if G.IsAbelian():
            return True
        def fill_subsume(qlabel):
            for slabel in self.maxquo[qlabel]:
                if not slabel in subsumed:
                    fill_subsume(slabel)
            subsumed.add(qlabel)
        try:
            Norms = G.MinimalNormalSubgroups()
        except RuntimeError:
            Norms = G.NormalSubgroupsAbove(gap.Group(G.One()), [])
        for N in Norms:
            n = order // ZZ(N.Size())
            if n == 1 or n == order or n not in GL.groups:
                continue
            Q = G.FactorGroupNC(N)
            if n < GL.Gbound and n.valuation(2) < 9:
                i = int(Q.IdSmallGroup()[2])
                qlabel = "%sG%s"%(n, i)
                if qlabel not in subsumed:
                    self.maxquo[label][qlabel] += 1
                    for slabel in self.maxquo[qlabel]:
                        fill_subsume(slabel)
            else:
                for qlabel in GL.groups[n]:
                    if _get_group(qlabel).IsIsomorphicGroup(Q):
                        if qlabel not in subsumed:
                            self.maxquo[label][qlabel] += 1
                            for slabel in self.maxquo[qlabel]:
                                fill_subsume(slabel)
                        break

    def extension_sizes(self):
        """
        For the maximal quotients recorded in this object, counts the number with a given size.

        Namely, it will print lines "m: s[m]" where s[m] is the number of maximal quotients
        H of potentially realizable p-groups with size m.
        """
        size = defaultdict(int)
        for label, quos in self.maxquo.iteritems():
            if 'G' not in label:
                continue
            n = ZZ(label.split('G')[0])
            bigq = 0
            for qlabel in quos:
                if 'G' not in qlabel:
                    continue
                qn = ZZ(qlabel.split('G')[0])
                if qn > bigq:
                    bigq = qn
            if bigq > 0:
                size[n//bigq] += 1
                if n//bigq > 10:
                    print label, n.factor()
        for m in sorted(size.keys()):
            print "%s: %s"%(m, size[m])

def _strip_syntax_warnings(err_msg):
    """
    Loading lift_gens.g produces a lot of syntax warnings due to
    missing global variables (which are created before the relevant
    functions are called).  This function strips out these warnings.
    """
    unwrapped_lines = ['']
    for line in err_msg.split('\n'):
        if unwrapped_lines[-1].endswith('\\'):
            unwrapped_lines[-1] = unwrapped_lines[-1][:-1] + line
        else:
            unwrapped_lines.append(line)
    lines = []
    ignoring = False
    for line in unwrapped_lines[1:]:
        if line.startswith('Syntax warning: unbound global variable in lift_gens.g'):
            ignoring = True
        elif line and (line[0] != ' ' or line.startswith('   executing')):
            ignoring = False
        if not ignoring:
            lines.append(line)
    return '\n'.join(lines)

class GroupCounter(object):
    """
    An object for counting the number of field extensions of Qp with a specified Galois group.

    INPUT:

    - GP -- a GroupPoset object storing the quotient relationships between
           potentially p-realizable groups

    The data is stored in a count dictionary, whose keys are GAP labels
    for groups and whose values are the number of field extensions with that Galois group.
    """
    def __init__(self, GP):
        self.GP = GP
        self.GL = GP.GL
        self.p = GP.GL.p
        self.count = {}
        missing_file = "missing%s"%(self.p)
        self.bad_labels = set()
        if os.path.exists(missing_file):
            with open(missing_file) as F:
                self.bad_labels = set(F.read().split())
        self.load()
        # We load lift_gens.g here.  We first check to see if it has already been loaded:
        try:
            gap.GENSS_LOADED()
        except RuntimeError:
            # It has not.  Since we're relying on the presence of global variables which
            # have not yet been set, loading it produces a ton of Syntax warnings, which we
            # suppress
            try:
                gap.eval('Read("lift_gens.g");')
            except RuntimeError as err:
                try:
                    gap.GENSS_LOADED()
                except RuntimeError:
                    # Loading was unsuccessful
                    # We strip out the syntax warnings for unbound global variables
                    raise RuntimeError(_strip_syntax_warnings(str(err)))

    def summarize_counts(self, v=None):
        """
        Returns a dictionary whose keys are integers,
        and whose value at n is the number of groups G in the GroupList
        so that there are n extensions with Galois group G.
        """
        p = self.p
        Count = defaultdict(int)
        for order, L in self.GL.groups.iteritems():
            if v is not None and order.valuation(p) != v:
                continue
            for label in L:
                if 'G' not in label:
                    continue
                G = _get_group(label)
                if G.IsAbelian():
                    continue
                print label
                Count[self.count[label]] += 1
        return Count

    def missing(self):
        """
        Returns the labels that have not yet been counted.
        """
        self.load()
        return sorted([label for label in sum(self.GL.groups.values(),[]) if 'Q' not in label and label not in self.count], key=_label_key)

    def get_relation_constants(self, G):
        """
        This function produces the constants used in the wild relation.

        INPUT:

        - G -- a GAP group

        OUTPUT:

        - h -- an integer that is a (p-1)st root of unity modulo the p-part of the order of G.
        - projp -- an exponent that projects to the p-part of G and then raises to the (p-1)st power.
        - proj2 -- an exponent that projects to the 2-part of G.
        - ppartGExp -- the p-part of the order of G.
        """
        p = self.p
        GExp = ZZ(G.Exponent())
        vpGExp, upGExp = GExp.val_unit(p)
        ppartGExp = GExp // upGExp
        p1inv = -1 if ppartGExp == p else ZZ(~mod(p-1,ppartGExp))
        v2GExp, u2GExp = GExp.val_unit(2)
        twopartGExp = GExp // u2GExp
        projp = crt(0, p1inv, upGExp, ppartGExp)
        proj2 = crt(0, 1, u2GExp, twopartGExp)
        if vpGExp == 0:
            h = 1
        else:
            hmodp = primitive_root(p)
            h = ZZ(Zp(p,vpGExp).teichmuller(hmodp))
        return h, projp, proj2, ppartGExp

    def check_hom(self, G, vec):
        """
        Checks that a homomorphism from the absolute Galois group of Qp to G is valid.

        INPUT:

        - G -- a GAP group
        - vec -- a four-tuple giving the images in G of sigma, tau, x_0 and x_1.

        This function will raise an AssertionError if the homomorphism is invalid,
        and return nothing otherwise.
        """
        p = self.p
        sigma, tau, x0, x1 = vec
        V = G.PCore(p)
        assert G.Subgroup(vec).Size() == G.Size()
        assert tau^sigma == tau^p
        assert x0 in V
        assert x1 in V
        h, projp, proj2, ppartGExp = self.get_relation_constants(G)
        h2 = ZZ(mod(h, ppartGExp)^proj2)
        abelian_pcore = V.IsAbelian()
        assert gap.RelationSatisfied(sigma, tau, x0, x1, p, h, h2, projp, proj2, ppartGExp, abelian_pcore)

    def representative_quadruples(self, label):
        """
        Reads in the file generated by the `compute` method to produce
        quadruples (sigma, tau, x0, x1) corresponding to surjections
        from the absolute Galois group.

        INPUT:

        - ``label`` -- a label of the form nGt

        OUTPUT:

        - the group with that label
        - a list of quadruples, in bijection with the extensions of Qp with
        Galois group given by the label.
        """
        G = _get_group(label)
        gens = G.GeneratorsOfGroup()
        loc = {}
        for i in range(1,len(gens)+1):
            loc['f%s'%i] = gens[i]
        loc['G'] = G
        with open(self._genss_filename(label)) as F:
            s = F.read().replace('<identity> of ...', 'G.One()')
        return G, sage_eval(s, loc)

    def check_valid_genss(self, label=None):
        """
        Check that the stored generators data is valid, by checking that
        sigma, tau, x0 and x1 satisfy the required relations via the
        ``check_hom`` method.

        INPUT:

        - ``label`` -- a label to check.  If None, checks all labels.
        """
        if label is None:
            for order, L in self.GL.groups.iteritems():
                for label in L:
                    print "Checking %s..."%label
                    try:
                        self.check_valid_genss(label)
                    except IOError:
                        print "File missing for %s!"%label
        else:
            G, genss = self.representative_quadruples(label)
            for gens in genss:
                self.check_hom(G, gens)

    def check_inequivalent_genss(self, label=None):
        """
        Check that none of the stored quadruples are equivalent under
        the action of the automorphism group of G.

        INPUT:

        - ``label`` -- a label to check.  If None, checks all labels.
        """
        if label is None:
            for order, L in self.GL.groups.iteritems():
                for label in L:
                    print "Checking %s..."%label
                    self.check_inequivalent_genss(label)
        else:
            by_order = defaultdict(list)
            G, genss = self.representative_quadruples(label)
            for gens in genss:
                by_order[tuple(ZZ(g.Order()) for g in gens)].append(gens)
            for ordervec, L in by_order.items():
                if len(L) <= 1:
                    by_order.pop(ordervec)
            if by_order:
                A = G.AutomorphismGroup()
                for L in by_order.values():
                    # Without a way to produce a canonical representative in each orbit,
                    # we just check whether they're in the same orbit pairwise
                    for v, w in combinations(L, 2):
                        auts = []
                        for x,y in zip(v,w):
                            g = A.RepresentativeAction(x,y)
                            if repr(g) == 'fail':
                                break
                            auts.append(g)
                        else:
                            # the entries of v and w are pairwise conjugate by automorphisms
                            # we see if there is some single automorphism conjugating all
                            I = A
                            for x,y,g in zip(v,w,auts):
                                B = A.Stabilizer(x).RightCoset(g)
                                I = I.Intersection(B)
                                if I.Size() == 0:
                                    break
                            else:
                                raise ValueError("%s and %s conjugate by %s"%(v, w, I.AsList()[1]))

    def sigma_taus(self, G, Tproj):
        """
        Returns a list of possible pairs (sigma, tau) in G.

        INPUT:

        - G -- a GAP group
        - Tproj -- the homomorphism from G to its tame quotient G/PCore(G).

        Note that the genss file for the tame quotient must exist.
        There will be one pair (sigma, tau) for each homomorphism to the tame quotient,
        consisting of an arbitrary lift of the sigma and tau from the quotient.
        """
        p = self.p
        tlabel = "G".join(str(c) for c in Tproj.Image().IdSmallGroup())
        T = _get_group(tlabel)
        taugens = T.GeneratorsOfGroup()
        Tproj = Tproj * Tproj.Image().IsomorphismGroups(T)
        h, projp, proj2, ppartGExp = self.get_relation_constants(G)
        with open(self._genss_filename(tlabel)) as F:
            genss = [gens.split(',') for gens in F.read().replace("\n","").replace("<identity> of ...","One").replace(" ","").replace(" ","").strip()[2:-2].split("],[")]
        sigma_taus = []
        for gens in genss:
            st = []
            for a in gens[:2]:
                if a == 'One':
                    st.append([])
                else:
                    to_add = []
                    for fac in a.split('*'):
                        if '^' in fac:
                            fac = fac.split('^')
                            to_add.append((int(fac[0][1:]), int(fac[1])))
                        else:
                            to_add.append((int(fac[1:]), int(1)))
                    st.append(to_add)
            sigma_taus.append(st)
        return [tuple(map(lambda a: Tproj.PreImagesRepresentative(prod([taugens[b]^e for b,e in a], T.One())), st)) for st in sigma_taus]

    def x_constraints(self, label, x0need=None):
        """
        This function is used in analyzing whether a given group is tame decoupled
        and/or x0-constrained (in the sense of Section 5.2 of [Roe18])

        Let R = x_0^sigma * <x_0, tau>^-1.

        INPUT:

        - label -- a string, giving the label of a potentially p-realizable group G.
                   The label should be for a group with nontrivial, abelian p-core.
        - x0need -- either None or an integer.

        OUTPUT:

        The function will print "tame-decoupled" if G is tame decoupled.  Otherwise,
        the behavior depends on x0need.  If x0need is None, it will test for nontrivial values
        of x0 that make R=1.  Otherwise, it will test for nontrivial values of x0 that
        make R have order x0need.

        If there are no valid x0, it will print "x0-constrained".  Otherwise, it will
        return a list of triples (sigma, tau, x0) that produce valid R.
        """
        G = _get_group(label)
        p = self.p
        V = G.PCore(p)
        if 'G' not in label or ZZ(G.Size()).valuation(2) >= 9:
            print "Only small groups supported"
            return
        if V.Size() == 1:
            print "Trivial Pcore"
            return
        if not V.IsAbelian():
            print "Nonabelian Pcore"
            return
        Tproj = G.NaturalHomomorphismByNormalSubgroupNC(V)
        sigma_taus = self.sigma_taus(G, Tproj)
        VAsList = V.AsList()
        h, projp, proj2, ppartGExp = self.get_relation_constants(G)
        if all(all(gap.AngleBracket(x0, tau, p, h, projp) == G.One() for x0 in VAsList) for sigma, tau in sigma_taus):
            print "tame-decoupled"
        else:
            vans = []
            for x0 in VAsList:
                if x0 == G.One():
                    continue
                for sigma, tau in sigma_taus:
                    if (x0need is None and gap.X0Relation(sigma, tau, x0, p, h, projp) == G.One() or
                        x0need is not None and gap.X0Relation(sigma, tau, x0, p, h, projp).Order() == x0need):
                        vans.append((sigma, tau, x0))
            if vans:
                print "Nonzero x0"
                return vans
            else:
                print "x0-constrained"
        return []

    def z_analyze(self, label):
        """
        Analyze why a given group G does not arise as a p-adic Galois group.

        This function returns a string, of the following form.

        - "tame problem" -- if the p-core V is trivial
        - "trivial action" -- if the p-core is abelian and central in G.
        - "abelian tame(LABEL:COUNT) V(DESC) REPR TAUSTR" -- if the p-core is abelian otherwise, where
          - LABEL is the Gap label for the tame quotient
          - COUNT is the number of times the tame quotient appears as a p-adic Galois group
          - DESC is the result of StructureDescription on the p-core
          - REPR describes the decomposition of V/W (where W = V'[V,V]) into indecomposible submodules
            (with multiplicity) as a representation of G/V
          - TAUSTR describes the behavior of the possible tau: either "tau=1" if
            all tau are 1 in the tame quotient, "no tau lift" if none of the taus in the
            tame quotient lift to a valid tau in G, or "" otherwise
        - "nonabelian LABEL SIZE" -- if the p-core is nonabelian, where
          - LABEL is the Gap label for the quotient V/W
          - SIZE is the order of the quotient V/W
        """
        p = self.p
        print "Analyzing", label
        G = _get_group(label)
        V = G.PCore(p)
        if V.Size() == 1:
            return "tame problem"
        elif V.IsAbelian():
            E = ExtensionProblem(G,p)
            M = VLooper(E,True).meataxe_module
            tlabel = "G".join(str(c) for c in E.tame.IdSmallGroup())
            Mgens = M.generators()
            if len(Mgens) == 0:
                return "trivial action"
            mingened = gap.GroupWithGenerators(M.Tgens)
            writer = mingened.EpimorphismFromFreeGroup()
            T = _get_group(tlabel)
            taugens = T.GeneratorsOfGroup()
            Tiso = T.IsomorphismGroups(mingened)
            with open(self._genss_filename(tlabel)) as F:
                genss = [gens.split(',') for gens in F.read().replace("\n","").replace("<identity> of ...","One").replace(" ","").replace(" ","").strip()[2:-2].split("],[")]
            taus = []
            for gens in genss:
                tau = gens[1]
                if tau == 'One':
                    taus.append([])
                else:
                    to_add = []
                    for fac in tau.split('*'):
                        if '^' in fac:
                            fac = fac.split('^')
                            to_add.append((int(fac[0][1:]), int(fac[1])))
                        else:
                            to_add.append((int(fac[1:]), int(1)))
                    taus.append(to_add)
            taustr = ""
            for tau in taus:
                if not tau:
                    continue
                tau = Tiso.Image(prod([taugens[a]^e for a, e in tau]))
                wordvec = [int(c) for c in writer.PreImagesRepresentative(tau).ExtRepOfObj()]
                taumat = Mgens[0].parent()(1)
                for a,b in zip(wordvec[0::2], wordvec[1::2]):
                    taumat *= Mgens[a-1]^b
                if taumat != 1:
                    break
            else:
                taustr = " tau=1"
            Tproj = G.NaturalHomomorphismByNormalSubgroupNC(V)
            Tproj = Tproj * Tproj.Image().IsomorphismGroups(T)
            for tau in taus:
                if not tau:
                    break
                if any(ZZ(taulift.Order()) % p != 0 for taulift in Tproj.PreImages(prod([taugens[a]^e for a, e in tau])).AsList()):
                    break
            else:
                taustr = " no tau lift"
            return "abelian tame(%s:%s) V(%s) %s%s"%(tlabel, self.count[tlabel], str(V.StructureDescription()), M.decomposition_type(), taustr)
        else:
            W = V.PRump(p)
            return "nonabelian " + "G".join(str(c) for c in G.FactorGroupNC(W).IdSmallGroup()) + " %s"%(V.Size() / W.Size())

    def zeroes(self):
        """
        Writes out some explanation for why minimally unrealizable groups might be so,
        using the notation of the ``z_analyze`` method.  Explanations are written to a file
        ``zero3`` (replace 3 with the correct p)
        """
        p = self.p
        labels = []
        for label, count in self.count.iteritems():
            if count == 0 and all(self.count.get(qlabel,0) != 0 for qlabel in self.GP.maxquo[label]):
                labels.append(label)
        labels.sort(key=_label_key)
        justifications = []
        for label in labels:
            if 'G' not in label:
                continue
            justifications.append((label, self.z_analyze(label)))
        with open('zero%s'%(self.p), 'w') as F:
            F.write('\n'.join("%s: %s"%justification for justification in justifications))
        # Tame could fail to lift
        # Tame lifts could be very constrained (tau=1 for example)
        # Small PCore

    def _prep(self, label):
        """
        Writes out the Gap file that is loaded before lifting generators using the methods
        in ``lift_gens.g``.
        """
        p = self.p
        G = _get_group(label)
        A = G.AutomorphismGroup()
        best_cost = ZZ(G.Size())^6
        try:
            Norms = G.MinimalNormalSubgroups()
        except RuntimeError:
            if DEBUG:
                raise
            else:
                raise UnboundLocalError # to distinguish from memory errors.
        for N in Norms:
            if N.Size() == 1:
                continue
            Qsize = ZZ(G.Size() / N.Size())
            if Qsize not in self.GL.groups:
                continue
            epi = G.NaturalHomomorphismByNormalSubgroupNC(N)
            Q = epi.Image()
            if Q.Size() < self.GL.Gbound and ZZ(Q.Size()).valuation(2) < 9:
                i = int(Q.IdSmallGroup()[2])
                qlabel = "%sG%s"%(Q.Size(), i)
            else:
                for qlabel in self.GL.groups[Qsize]:
                    if _get_group(qlabel).IsIsomorphicGroup(Q):
                        break
                else:
                    continue
            if qlabel in self.bad_labels:
                print "Bad quotient %s!"%qlabel
                continue
            B = Q.AutomorphismGroup()
            cost = QQ(N.Size()^4 * B.Size() / A.Size())
            try:
                ischarsub = G.IsCharacteristicSubgroup(N)
            except RuntimeError:
                if DEBUG:
                    raise
                else:
                    raise UnboundLocalError
            if cost < best_cost or cost == best_cost and ischarsub:
                Nstr = str(N.GeneratorsOfGroup())
                best = Nstr, ischarsub, qlabel
                best_cost = cost
        Nstr, ischarsub, qlabel = best
        print "lifting %s (cost %s)... "%(qlabel, best_cost),
        sys.stdout.flush()
        nG = len(G.GeneratorsOfGroup())
        Q = _get_group(qlabel)
        nQ = len(Q.GeneratorsOfGroup())
        h, projp, proj2, ppartGExp = self.get_relation_constants(G)
        with open(self._genss_filename(qlabel)) as F:
            qgenss = F.read().replace('<identity> of ...','One(Q)').replace('f','q')
        with open(self._prep_filename(label), 'w') as F:
            F.write(_get_gap_str(label, "G"))
            F.write("ggens := GeneratorsOfGroup(G);\n")
            F.write(" ".join("f{0} := ggens[{0}];".format(i) for i in range(1,nG+1)) + "\n")
            F.write("A := AutomorphismGroup(G);\n")
            F.write("N := Subgroup(G, %s);\n"%Nstr)
            F.write("epi := NaturalHomomorphismByNormalSubgroupNC(G, N);\n")
            F.write(_get_gap_str(qlabel, "Q"))
            F.write("B := AutomorphismGroup(Q);\n")
            F.write("BPiso := IsomorphismPermGroup(B);\n")
            F.write("BP := Image(BPiso);\n")
            F.write("epi := epi * IsomorphismGroups(Image(epi), Q);\n")
            F.write("qgens := GeneratorsOfGroup(Q);\n")
            F.write(" ".join("q{0} := qgens[{0}];".format(i) for i in range(1,nQ+1)) + "\n")
            F.write("Qgenss := " + qgenss + ";\n")
            if ischarsub:
                F.write("Agens := GeneratorsOfGroup(A);\n")
                F.write("authom := GroupHomomorphismByImagesNC(A, BP, List(Agens, x -> Image(BPiso, InducedAutomorphism(epi, x))));\n")
                F.write("ischarsub := true;\n")
            else:
                F.write("AA := Stabilizer(A, Set(N), OnSets);\n")
                F.write("AAgens := GeneratorsOfGroup(AA);\n")
                F.write("authom := GroupHomomorphismByImagesNC(AA, BP, List(AAgens, x -> Image(BPiso, InducedAutomorphism(epi, x))));\n")
                F.write("Agens := GeneratorsOfGroup(A);\n")
                F.write("AP := Group(List(Agens, x -> Permutation(x, List(G), OnPoints)));\n")
                F.write("ischarsub := false;\n")
            F.write("ker_reps := List(Kernel(authom));\n")
            F.write("cok_reps := List(RightTransversal(BP, Image(authom)), x -> PreImage(BPiso, x));\n")
            F.write("ppartGExp := %s;\n"%(ppartGExp))
            F.write("projp := %s;\n"%(projp))
            F.write("proj2 := %s;\n"%(proj2))
            F.write("h := %s;\n"%(h))

    def check_tame_lift(self, label):
        """
        Runs the lifting method for lifting from the tame quotient, returning a pair
        (sigma, tau).
        """
        p = self.p
        G = _get_group(label)
        V = G.PCore(p)
        Q = G.FactorGroupNC(V)
        qlabel = "G".join(str(c) for c in Q.IdSmallGroup())
        nQ = ZZ(_get_group(qlabel).GeneratorsOfGroup().Length())
        with open(self._genss_filename(qlabel)) as F:
            qgenss = F.read().replace('<identity> of ...','One(Q)').replace('f','q')
        with open(self._tprep_filename(label), 'w') as F:
            F.write(_get_gap_str(label, "G"))
            F.write("V := PCore(G, %s);\n"%p)
            F.write("A := AutomorphismGroup(G);\n")
            F.write("epi := NaturalHomomorphismByNormalSubgroupNC(G, V);\n")
            F.write(_get_gap_str(qlabel, "Q"))
            F.write("B := AutomorphismGroup(Q);\n")
            F.write("BPiso := IsomorphismPermGroup(B);\n")
            F.write("BP := Image(BPiso);\n")
            F.write("epi := epi * IsomorphismGroups(Image(epi), Q);\n")
            F.write("qgens := GeneratorsOfGroup(Q);\n")
            F.write(" ".join("q{0} := qgens[{0}];".format(i) for i in range(1,nQ+1)) + "\n")
            F.write("Qgenss := " + qgenss + ";\n")
            F.write("Agens := GeneratorsOfGroup(A);\n")
            F.write("authom := GroupHomomorphismByImagesNC(A, BP, List(Agens, x -> Image(BPiso, InducedAutomorphism(epi, x))));\n")
            F.write("cok_reps := List(RightTransversal(BP, Image(authom)), x -> PreImage(BPiso, x));\n")
        return gap.LiftGenss_tame('"' + label + '"', p)

    def compute(self, order, label):
        """
        Calls off to Gap to actually compute the number of extensions of Qp with specified Galois group.

        INPUT:

        - ``order`` -- the size of G
        - ``label`` -- the label for G

        If there is a quotient with no fields, the function will just write to the appropriate files.
        Otherwise, it will write a single line status report as it calls off to Gap
        to compute the count.  In either case, it will save the count in the `count` dictionary.
        """
        p = self.p
        for qlabel in self.GP.maxquo[label]:
            if self.count.get(qlabel,0) == 0: # could maybe conclude 0 if qlabel not present
                self.count[label] = 0
                if not os.path.exists(self._genss_filename(qlabel)):
                    with open(self._genss_filename(qlabel), 'w') as F:
                        F.write('[ ]')
                if qlabel not in self.count:
                    self.count[qlabel] = 0
                with open(self._genss_filename(label), 'w') as F:
                    F.write('[ ]')
                break
        else:
            G = _get_group(label)
            Gab = G.IsAbelian()
            if Gab or order % p != 0 or ZZ(G.PCore(p).Size()) == 1:
                print "%s %s... "%("Abelian" if Gab else "Tame", label),
                sys.stdout.flush()
                self.count[label] = ZZ(gap.Genss_base('"' + label + '"', G, p))
            else:
                print "Prepping %s... "%(label),
                sys.stdout.flush()
                self._prep(label)
                try:
                    self.count[label] = ZZ(gap.LiftGenss('"' + label + '"', p))
                except RuntimeError:
                    if DEBUG:
                        raise
                    else:
                        raise UnboundLocalError
            print self.count[label]
        self.save_count(label)

    def test_liftgenss(self):
        """
        For each potentially p-adic group that is nonabelian with nontrivial p-core,
        checks that the output of the ``LiftGenss`` Gap method is the same as the stored count.
        """
        p = self.p
        for order in sorted(self.GL.groups.keys()):
            L = self.GL.groups[order]
            for label in L:
                G = _get_group(label)
                Gab = G.IsAbelian()
                if not Gab and order % p == 0 and ZZ(G.PCore(p).Size()) != 1:
                    print "Prepping %s... "%(label),
                    sys.stdout.flush()
                    self._prep(label)
                    assert self.count[label] == ZZ(gap.LiftGenss('"' + label + '"', p))
                    print self.count[label]

    def run(self):
        """
        Computes the counts for every potentially p-adic Galois group in the list.

        Uses claim files for a crude locking mechanism, allowing multiple processes
        to work in parallel.
        """
        p = self.p
        other_labels = []
        for order in sorted(self.GL.groups.keys()):
            L = self.GL.groups[order]
            for label in L:
                if label in self.bad_labels:
                    continue
                claimfile = self._claim_filename(label)
                if os.path.exists(claimfile):
                    if os.path.exists(self._filename(label)):
                        self.load_count(label)
                    else:
                        other_labels.append(label)
                    continue
                try:
                    with open(claimfile, 'a'):
                        os.utime(claimfile, None)
                    self.compute(order, label)
                except UnboundLocalError: # Use this to distinguish between the kinds of errors GAP can have.
                    os.remove(claimfile)
                    with open("missing%s"%(self.p), 'a') as F:
                        while '_' in label:
                            F.write(label + '\n')
                            self.bad_labels.add(label)
                            label = label[:label.rfind('_')]
                        label = label.replace('Q','T')
                        F.write(label + '\n')
                        self.bad_labels.add(label)
                    print "failed!"
                except BaseException:
                    os.remove(claimfile)
                    self.save_summary()
                    raise
            new_labels = []
            for label in other_labels:
                if os.path.exists(self._filename(label)):
                    self.load_count(label)
                    print "Loaded %s=%s"%(label, self.count[label])
                else:
                    new_labels.append(label)
            other_labels = new_labels
        self.save_summary()

    def _filename(self, label):
        return os.path.join('IGPdata','%s_%s_count'%(label, self.p))
    def _genss_filename(self, label):
        return os.path.join('IGPdata','%s_%s_genss.g'%(label, self.p))
    def _prep_filename(self, label):
        return os.path.join('IGPdata','%s_%s_prep.g'%(label, self.p))
    def _tprep_filename(self, label):
        return os.path.join('IGPdata','%s_%s_tprep.g'%(label, self.p))
    def _claim_filename(self, label):
        return os.path.join('IGPdata','%s_%s_claim'%(label, self.p))
    def _tclaim_filename(self, label):
        return os.path.join('IGPdata','%s_%s_tclaim'%(label, self.p))
    def _summary_filename(self):
        return 'gcount%s'%(self.p)
    #def clear_tclaims(self):
    #    for file in os.listdir('IGPdata'):
    #        if file.endswith("tclaim"):
    #            os.remove('IGPdata/' + file)

    def save_count(self, label, save_empty_gens=False):
        """
        Saves the count to the filesystem.
        """
        with open(self._filename(label), 'w') as F:
            F.write(str(self.count[label]))
        if save_empty_gens and self.count[label] == 0:
            with open(self._genss_filename(label), 'w') as F:
                F.write("[ ]")

    def load_count(self, label):
        """
        Loads the count from the filesystem into the ``count`` dictionary.
        """
        with open(self._filename(label)) as F:
            self.count[label] = ZZ(F.read())

    def load(self):
        """
        Loads all counts from the ``IGPdata`` folder.
        """
        p = self.p
        for order, L in self.GL.groups.iteritems():
            for label in L:
                if os.path.exists(self._filename(label)):
                    self.load_count(label)

    def save_summary(self):
        """
        Saves a summary to the summary file (e.g. "gcount3")
        """
        with open(self._summary_filename(), 'w') as F:
            for label in sorted(self.count.keys(), key=_label_key):
                F.write("%s %s\n"%(label, self.count[label]))

    def fill_transitive(self):
        """
        For counting transitive groups of order larger than the bound stored
        in the list of potentially p-adic groups.
        """
        GL = self.GL
        for order in sorted(GL.groups.keys()):
            if order < 2*GL.Gbound:
                continue
            L = GL.groups[order]
            for label in L:
                if ('Q' in label or
                    label in self.bad_labels or
                    label in self.count):
                    continue
                claimfile = self._tclaim_filename(label)
                if os.path.exists(claimfile):
                    continue
                try:
                    with open(claimfile, 'a'):
                        os.utime(claimfile, None)
                    print "Filling %s..."%(label),
                    self._fill(label)
                except BaseException:
                    os.remove(claimfile)
                    raise

    def _fill(self, label):
        """
        Computes counts for a chain of quotients until reaching the small groups computed
        in the group list.
        """
        G = _get_group(label)
        cost, blabel, sizes, lens, genss = LabelTree(label.replace("T","Q") + 'p%s'%(self.p), self, G).best_path()
        if cost is None:
            self.count[label] = 0
            self.save_count(label, save_empty_gens=True)
            print "- 0 count"
        else:
            nsizes = []
            last_size = ZZ(G.Size())
            for size in sizes:
                nsizes.append(str(last_size // size))
                last_size = size
            print " ".join(nsizes),
            while "_" in blabel:
                self.save_ndata(blabel, sizes.pop(-2), lens.pop(-1), genss.pop(-1))
                blabel = blabel[:blabel.rfind("_")]
            print "Done"

    def save_ndata(self, label, size, ngens, genstr):
        """
        Saves counts to the file system while filling in from a transitive group
        (one larger than any in the group list).
        """
        with open("IGPdata/ndata_%s"%(label), 'w') as F:
            F.write("%s\n%s\n%s"%(size, ngens, genstr))

    def clearQ(self):
        """
        Removes groups with Q in their label from the list of potentially p-realizable groups.
        """
        for order, L in self.GL.groups.iteritems():
            for label in L:
                if 'Q' in label:
                    for file in [self._filename(label), self._genss_filename(label), self._prep_filename(label), self._claim_filename(label)]:
                        if os.path.exists(file):
                            os.remove(file)
            self.GL.groups[order] = [label for label in L if 'Q' not in label]
        self.GL.clean() # also saves

    def count_fields_of_degree(self, n, TID=None):
        """
        Count the total number of fields of a given degree over Qp

        INPUT:

        - ``n`` -- a multiple of p (these are the interesting cases)
        - ``TID`` -- a TransitiveIDs object whose ``compute`` and
          ``count_generating_subfields`` methods have been run.
          If not provided, a global one will be created (so you must have
          run the appropriate methods with the default T-bounds)
        """
        if TID is None:
            TID = TransitiveIDs(self.GL)
        p = self.p
        if n % p != 0:
            raise NotImplementedError
        count = 0
        for label in TID.deg[n]:
            count += self.count[label] * TID.count[label,n]
        return count
    def count_fields_with_galgrp(self, label, n=None, TID=None):
        """
        Count the total number of fields with a specified Galois group over Qp

        INPUT:

        - ``label`` -- a label such as 6T13 or 72G40
        - ``n`` -- a degree (required if a label such as 72G40)
        - ``TID`` -- a TransitiveIDs object whose ``compute`` and
          ``count_generating_subfields`` methods have been run.
          If not provided, a global one will be created (so you must have
          run the appropriate methods with the default T-bounds)
        """
        if TID is None:
            TID = TransitiveIDs(self.GL)
        if 'T' in label:
            n = ZZ(label[:label.find('T')])
            label = TID.id[label]
        else:
            if n is None:
                raise ValueError("Specify n")
            print " ".join(TID.back[label])
        return self.count[label] * TID.count[label, n]


def _find_key(c, H, p, n, q, f):
    a, b = H.IdGroup()
    return (c, ZZ(a), ZZ(b), p, n, q, f)
@cached_function(key=_find_key)
def alpha(c, H, p, n, q, f=None):
    """
    Case 1.7.c of Yamagishi.  H is a p-group, k a finite extension of Qp with degree n,
    and q is the largest power p so that mu_q is contained in k.

    alpha(H) = |H|^n \sum_{\chi} 1/\chi(1)^n \sum_h \chi(h^{q-1}) \chi(h)
    """
    #set_verbose(1)
    #t = verbose("Starting alpha (c=%s)"%c)
    Table = H.CharacterTable()
    Irreds = Table.Irr()
    Sizes = Table.SizesConjugacyClasses()
    N = len(Irreds)
    #print "Sizes", Sizes
    ans = 0
    if c > 2: assert (f >= 2)
    if c == 1:
        Pmap = Table.PowerMap(q-1)
    elif c == 3:
        Pmap = Table.PowerMap(2^f + 1)
    else:
        ConjClasses = Table.ConjugacyClasses()
        Pmap = None
        #t = verbose("Building lookup dictionary",t)
        CClookup = H.Identity().NewDictionary('true')
        for i, C in enumerate(ConjClasses):
            for g in C.List():
                CClookup.AddDictionary(g, i+1)
    #t = verbose("Starting chi loop (N=%s)"%N,t)
    for chi in Irreds:
        vals = chi.ValuesOfClassFunction()
        #verbose("chi = %s"%(vals),t)
        if Pmap is None:
            subsum = 0
            for i in range(1,N+1):
                #verbose("i = %s"%i,t)
                h = ConjClasses[i].Representative()
                for g in H.List():
                    if c == 2:
                        subsum += vals[CClookup.LookupDictionary(g^2*h^3)] * vals[i] * Sizes[i]
                    elif c == 4:
                        subsum += vals[CClookup.LookupDictionary(g)] * vals[CClookup.LookupDictionary(g*h^(2^f-1))] * vals[i] * Sizes[i]
        else:
            subsum = sum(vals[i] * vals[Pmap[i]] * Sizes[i] for i in range(1,N+1))
        ans += subsum / vals[1]^n
    #t = verbose("alpha computation complete",t)
    return ans * H.Size()^n

class ExtensionProblem(SageObject):
    """
    An extension problem object for solving the inverse Galois problem over Qp.

    INPUT:

        - ``G`` -- a Gap group (should probably be a permutation group for speed)
        - ``p`` - a prime
    """
    def __init__(self, G, p, label=None):
        self.group = G
        self.p = p
        self.label = label
    @cached_method
    def is_potentially_padic(self):
        p = self.p
        if p > 2 and self.group.IsAbelian() and self.prank > 2:
            return False
        #if p > 2 and (self.prank > 3 or (self.prank == 3 and self.group.IsAbelian())):
        #    return False
        T = self.tame
        if T.IsCyclic():
            return True
        D = T.DerivedSubgroup()
        if not D.IsCyclic():
            return False
        for N in T.NormalSubgroupsAbove(D,[]):
            if not N.IsCyclic(): continue
            quo = T.NaturalHomomorphismByNormalSubgroupNC(N)
            H = quo.Image()
            if H.IsCyclic():
                e = ZZ(N.Size())
                f = ZZ(H.Size())
                s = quo.PreImagesRepresentative(H.MinimalGeneratingSet()[1])
                t = N.MinimalGeneratingSet()[1]
                sts = s*t*s^-1
                tpow = t
                texp = mod(1, e)
                while tpow != sts:
                    tpow *= t
                    texp += 1
                try:
                    Frobpower = mod(p, e).log(texp)
                    # check that Frobenius generates the unramified quotient
                    if Frobpower.gcd(texp.multiplicative_order()).gcd(f) == 1:
                        return True
                except ValueError:
                    pass
        return False
    @lazy_attribute
    def pcore(self):
        """Intersection of the p-Sylow subgroups of G."""
        return self.group.PCore(self.p)
    @lazy_attribute
    def prank(self):
        p = self.p
        V = self.pcore
        Prump = V.PRump(p)
        return (ZZ(V.Size()) // ZZ(Prump.Size())).exact_log(p)
    @lazy_attribute
    def tame(self):
        """The (minimal) tame quotient of G.  Note that the actual tame quotient
           could be larger if the unramified part has order a multiple of p."""
        return self.group.FactorGroupNC(self.pcore)
    @lazy_attribute
    def GExp(self):
        """The exponent of G."""
        return ZZ(self.group.Exponent())
    @lazy_attribute
    def ppartGExp(self):
        """The p-part of the exponent of G."""
        p = self.p
        return p^self.GExp.valuation(p)
    @lazy_attribute
    def d(self):
        """The minimal number of generators of G."""
        return len(self.group.MinimalGeneratingSet())
    @lazy_attribute
    def relevant_subgroups(self):
        """Subgroups containing the G^p[G,G], used for Yamagishi algorithm."""
        G = self.group
        Prump = G.PRump(self.p)
        return [H for H in G.SubgroupsSolvableGroup() if H.IsSubset(Prump)]
    @cached_method
    def count_gap(self):
        G = self.group
        p = self.p
        Free4 = gap.FreeGroup(4)
        sigma, tau, x0, x1 = Free4.GeneratorsOfGroup()
        R1 = x0^self.ppartGExp
        R2 = x1^self.ppartGExp
        R3 = sigma^-1*tau*sigma*tau^-p
        R4 = self.relation(sigma, tau, x0, x1)*sigma^-1*x0^-1*sigma
        return gap.new("GQuotients(%s / [%s, %s, %s, %s], %s)"%(Free4.name(), R1.name(), R2.name(), R3.name(), R4.name(), G.name()))
    @cached_method
    def count(self, verbose=True, algorithm=None):
        """
        Count the number of surjections from the absolute Galois group of `\Qp` to `G`.

        This function will raise a ValueError if p is even and G is not a 2-group.

        INPUT:

        - ``verbose`` -- whether to print progress and debugging statements.

        We say that `G` is *potentially p-adic* if the following conditions hold:
        - the tame quotient `T` of `G` (`T = G/V` where `V` is the intersection of all `p`-Sylow subgroups of `G`)
          has generators `s` and `t` with `sts^{-1} = t^p` and the subgroup generated by `t` is normal in `T`.
        - the p-rank of `V` (i.e. the dimension of V/V^p[V,V] as a ``GF(p)`` vector space) is at most 3 (2 if `G` is Abelian).
        If `G` is not potentially `p`-adic, this function will return 0.

        EXAMPLES::

            sage: G = gap.SmallGroup(162,10)
            sage: G.StructureDescription()
            ((C3 x C3 x C3) : C3) : C2
            sage: E = ExtensionProblem(G, 3)
            sage: E.count()
            New tau/sigma orbit found, stabilizer 36
            New tau/sigma orbit found, stabilizer 18
            New tau/sigma orbit found, stabilizer 6
            New tau/sigma orbit found, stabilizer 36
            New tau/sigma orbit found, stabilizer 18
            New tau/sigma orbit found, stabilizer 6
            New tau/sigma orbit found, stabilizer 324
            New tau/sigma orbit found, stabilizer 162
            New tau/sigma orbit found, stabilizer 54
            New tau/sigma orbit found, stabilizer 18
            New tau/sigma orbit found, stabilizer 18
            New tau/sigma orbit found, stabilizer 9
            New tau/sigma orbit found, stabilizer 36
            New tau/sigma orbit found, stabilizer 18
            New tau/sigma orbit found, stabilizer 6
            60
        """
        G = self.group
        p = self.p
        Tame = self.tame
        if Tame.Size() == 1:
            d = self.d
            A = ZZ(self.group.AutomorphismGroup().Size())
            GSize = ZZ(G.Size())
            if p != 2:
                return (GSize^2 * prod(p^2 - p^i for i in range(d))) / (A * p^(d*2))
            def mu(H):
                # Assumes that H contains G.Prump(p).  See Yamagishi, Lemma 1.3
                i = ZZ(G.Index(H)).exact_log(p)
                return (-1)^i * p^(i*(i-1)//2)
            total = 0
            for H in self.relevant_subgroups:
                if verbose:
                    print H.IdGroup()
                total += mu(H) * alpha(2, H, p, 1, 2, None) * G.Index(G.Normalizer(H))
            return total / A
        if p == 2:
            raise NotImplementedError("The absolute Galois group of Q_2 is unknown")
        GSize = G.Size()
        # For abelian groups, the relations reduce to:
        # * the order of tau divides p-1,
        # * x_0 = x_1^p
        if G.IsAbelian():
            inv = G.AbelianInvariants()
            prime_dict = defaultdict(list)
            for n in inv:
                n = ZZ(n)
                ell, kay = n.is_prime_power(get_data=True)
                prime_dict[ell].append(kay)
                if len(prime_dict[ell]) > 2:
                    return ZZ(0)
            ans = ZZ(1)
            # x_1 plays the same role at p as tau does away, so we may treat them in a unified way.
            for ell, L in prime_dict.iteritems():
                if len(L) == 1:
                    kay = L[0]
                    if ell == p or (ell^kay).divides(p-1):
                        # tau/x_1 is unrestricted
                        # sigma and tau/x_1 must together generate, so at least one is a generator (ell-power cyclic group)
                        ans *= ell^(kay - 1) * (ell+1)
                    else:
                        # sigma must generate, canceling with the size of the automorphism group
                        ans *= (ell^kay).gcd(p-1)
                else: # len(L) == 2
                    k1, k2 = L
                    if (ell == p or (ell^k2).divides(p-1)) and k1 != k2:
                        # tau/x1 and sigma can map to either generator, and they are not interchanged by any automorphism
                        ans *= 2
                    elif ell != p and not (ell^k1).divides(p-1):
                        # tau cannot map to any generator
                        return ZZ(0)
                # otherwise, the number of pairs of generators is the same as the number of automorphisms (c.f. Hillar-Rhea, Thm 3.6)
            return ans
        V = self.pcore
        #Prump = V.PRump(p)
        phiGV = G.NaturalHomomorphismByNormalSubgroupNC(V)
        TameD = Tame.DerivedSubgroup()
        #phiPrump = V.NaturalHomomorphismByNormalSubgroupNC(Prump)
        #W = phiPrump.Image()
        #if Prump.Order() == 1:
        #    use_prump = False
        #else:
        #    use_prump = True
        self.vlooper = VLooper(self, verbose)
        ans = QQ(0)
        #def increment_dict(D, x):
        #    # Gap objects aren't hashable, so we need to do this by hand.
        #    xkey = ZZ(Vkey(x))
        #    if xkey not in D:
        #        D[xkey] = [(x, 0)]
        #        i = 0
        #    else:
        #        for i in range(len(D[xkey])):
        #            if x == D[xkey][i][0]:
        #                break
        #        else:
        #            i = len(D[xkey])
        #            D[xkey].append((x, 0))
        #    D[xkey][i][1] += 1
        #def count_collisions(D1, D2):
        #    ans = ZZ(0)
        #    for m in D1.iterkeys():
        #        if m not in D2:
        #            continue
        #        for g, a in D1[m]:
        #            for h, b in D2[m]:
        #                if h == g:
        #                    ans += a*b
        #                    break
        #    return ans
        if Tame.IsCyclic():
            f = ZZ(Tame.Size())
            e = f.gcd(p-1)
            # the order of tau must be a divisor of p-1 since the tame part is abelian.
            fe = f // e
            u0 = Tame.MinimalGeneratingSet()[1]
            t0 = u0^(fe)
            for b in range(f):
                if gcd(b, fe) != 1:
                    continue
                u = u0^b
                for c in range(e):
                    if gcd(b, c*fe) != 1:
                        continue
                    t = t0^c
                    for tau in phiGV.PreImages(t).AsList():
                        if not ZZ(tau.Order()).divides(p-1):
                            continue
                        S = G.Centralizer(tau).Intersection(phiGV.PreImages(u))
                        if S.Size() > 0:
                            for sigma in S.List():
                                ans += self.vlooper.count(sigma, tau, algorithm = algorithm)
        #elif Tame.IsAbelian():
        else:
            for TameI in Tame.NormalSubgroupsAbove(TameD,[]):
                if not TameI.IsCyclic():
                    continue
                phiTU = Tame.NaturalHomomorphismByNormalSubgroupNC(TameI)
                Unram = phiTU.Image()
                if Unram.IsCyclic():
                    e = ZZ(TameI.Size())
                    f = ZZ(Unram.Size())
                    u0 = phiTU.PreImages(Unram.MinimalGeneratingSet()[1]).AsList()[1]
                    t0 = TameI.MinimalGeneratingSet()[1]
                    twist = t0^u0
                    tpow = t0
                    a = mod(1,e)
                    while tpow != twist:
                        tpow *= t0
                        a += 1
                    aorder = a.multiplicative_order()
                    try:
                        b0 = mod(p, e).log(a) % aorder
                    except ValueError:
                        continue
                    if verbose:
                        print "Starting loops: %s bs, %s cs, %s ds%s"%(f//aorder, euler_phi(e), e, " using prump" if self.vlooper.use_prump else "")
                    for b in range(b0,f,aorder):
                        # These bs are the powers of u0 that give the right commutator relation in the tame quotient.
                        if f.gcd(b) != 1:
                            continue
                        u = u0^b
                        for d in range(e):
                            extra_gen_needed = e*f // ZZ(u.Order())
                            # extra_gen_needed measures the amount of the TameI subgroup already generated by powers of sigma.
                            for c in range(e):
                                if extra_gen_needed.gcd(c) != 1:
                                    continue
                                t = t0^c
                                assert Tame.Subgroup([u,t]).Size() == Tame.Size()
                                for tau in phiGV.PreImages(t).AsList():
                                    taup = tau^p
                                    for sigma in phiGV.PreImages(u).AsList():
                                        if tau^sigma != taup:
                                            continue
                                        ans += self.vlooper.count(sigma, tau, algorithm = algorithm)
                                    #tauZ = G.Centralizer(tau)
                                    #for sigma0 in G.RightTransversal(tauZ).AsList():
                                    #    if sigma0^phiGV != u:
                                    #        continue
                                    #    if tau^sigma0 != taup:
                                    #        continue
                                    #    for sigmatrans in tauZ.List():
                                    #        sigma = sigmatrans * sigma0
                                    #        ans += inner_loop(sigma,tau)
                                    #    break
                            u = t0*u
        return ZZ(ans)

class VLooper(SageObject):
    def __init__(self, E, verbose=False):
        self.E = E
        self.G = G = E.group
        self.V = V = E.pcore
        self.abelian_pcore = bool(V.IsAbelian())
        self.p = p = E.p
        self.GSize = ZZ(G.Size())
        GExp = E.GExp
        vpGExp, upGExp = GExp.val_unit(p)
        ppartGExp = GExp // upGExp
        p1inv = -1 if ppartGExp == p else ZZ(~mod(p-1,ppartGExp))
        v2GExp, u2GExp = GExp.val_unit(2)
        twopartGExp = GExp // u2GExp
        # projp is an integer m so that raising to the mth power projects every element of the group onto its p-primary part.
        self.projp = crt(0, p1inv, upGExp, ppartGExp)
        # proj2 is an integer m so that raising to the mth power projects every element of the group onto its 2-primary part.
        self.proj2 = crt(0, 1, u2GExp, twopartGExp)
        hmodp = primitive_root(p)
        # h is an integer that is a (p-1)st root of unity modulo the p-part of the exponent of G.
        try:
            self.h = ZZ(Zp(p,vpGExp).teichmuller(hmodp))
        except ValueError:
            # Occurs if vpGExp = 0
            self.h = 1
        # h2 = h^proj2 is used in the computation of the character beta.
        self.h2 = mod(self.h,ppartGExp)^self.proj2
        self.st_seen = gap.List([G.Identity(), G.Identity()]).NewDictionary("false")
        self.A = A = G.AutomorphismGroup()
        self.ASize = ZZ(A.Size())
        self.verbose = verbose
        self.Prump = Prump = V.PRump(p)
        self.phiGV = G.NaturalHomomorphismByNormalSubgroupNC(V)
        self.phiPrump = V.NaturalHomomorphismByNormalSubgroupNC(Prump)
        self.W = self.phiPrump.Image()
        self.use_prump = (Prump.Order() == 1)
        self.stats = {'loops':[], 'meataxe':[]}
    def generates(self, sigma, tau, x0, x1):
        return self.G.Subgroup([sigma, tau, x0, x1]).Size() == self.GSize
    def angle_bracket(self, x, rho):
        """Part of the relation for the absolute Galois group of Qp."""
        xpow = x^self.h
        ans = xpow*rho
        for i in range(self.p-2):
            xpow = xpow^self.h
            ans = xpow * rho * ans
        return ans^self.projp
    def curly_bracket(self, x, rho_squared, tau2exp):
        """Another part of the relation for the absolute Galois group of Qp."""
        betarho = ZZ(self.h2^tau2exp)
        xpow = x
        ans = xpow * rho_squared
        for i in range(self.p-2):
            xpow = xpow^betarho
            ans = ans * xpow * rho_squared
        return ans^self.projp
    def x0_relation(self, sigma, tau, x0):
        return self.angle_bracket(x0, tau)^-1 * x0^sigma
    def x1_relation(self, sigma, tau, x1):
        p = self.p
        if self.abelian_pcore:
            return x1^p
        sigma2 = sigma^self.proj2
        tau2 = tau^self.proj2
        tau2pm2 = tau2^((p-1)//2)
        tau2pp2 = tau2pm2 * tau2
        tau2pp = tau2pp2^2
        stau2pm2 = sigma2 * tau2pm2
        inner_bracket = self.curly_bracket(x1, tau2pp^2, p+1)
        outer_bracket = self.curly_bracket(inner_bracket, stau2pm2^2, (p-1)//2)
        y1 = x1^tau2pp * inner_bracket^stau2pm2 * outer_bracket^(sigma2*tau2pp2) * outer_bracket^tau2pp2
        return x1^(p+1) * y1 * x1^-1 * y1^-1
    @lazy_attribute
    def meataxe_module(self):
        T = self.E.tame
        p = self.p
        phiPrump = self.phiPrump
        W = self.W
        L = []
        Wgens = W.IndependentGeneratorsOfAbelianGroup()
        Wup = [phiPrump.PreImagesRepresentative(w) for w in Wgens]
        Mingenset = T.MinimalGeneratingSet()
        Tgens = [self.phiGV.PreImagesRepresentative(t) for t in Mingenset]
        z1 = gap.Z(p)^0
        for t in Tgens:
            L.append([])
            for w in Wup:
                L[-1].append(gap.List([z1*a for a in self.W.IndependentGeneratorExponents((w^t)^phiPrump)]))
            L[-1] = gap.List(L[-1])
        if L:
            return MeataxeModule(gap.GModuleByMats(L, gap.GF(p)), Mingenset)
        else:
            return MeataxeModule(gap.GModuleByMats([], len(Wgens), gap.GF(p)), Mingenset)
    @lazy_attribute
    def wlooper(self):
        return WLooper(self)
    def count(self, sigma, tau, algorithm=None):
        """
        Counts the number of surjections with a given sigma and tau, divided by
        the number of automorphisms.
        """
        ans = QQ(0)
        st = gap.List([sigma, tau])
        if self.st_seen.KnowsDictionary(st):
            return ans
        orbit = self.A.Orbit(st, gap.OnPairs)
        stabilizer_count = self.ASize // ZZ(orbit.Size())
        for st_image in orbit:
            self.st_seen.AddDictionary(st_image)
        if self.verbose:
            print "New tau/sigma orbit found, stabilizer %s"%(stabilizer_count)
        #if algorithm != "loops":
        #    M = self.meataxe_module
        if algorithm is None:
            #algorithm = "meataxe" if M.is_multiplicity_free() else "loops"
            algorithm = "loops"
        if algorithm == "loops":
            return self._count_loops(sigma, tau, stabilizer_count)
        elif algorithm == "meataxe":
            return self._count_meataxe(sigma, tau, stabilizer_count)
        elif algorithm == "compare":
            # precompute M and wlooper so we don't screw up the statistics.
            M = self.meataxe_module
            wlooper = self.wlooper
            t = walltime()
            ans_loops = self._count_loops(sigma, tau, stabilizer_count)
            self.stats['loops'].append(walltime(t))
            t = walltime()
            ans_meataxe = self._count_meataxe(sigma, tau, stabilizer_count)
            self.stats['meataxe'].append(walltime(t))
            if ans_loops != ans_meataxe:
                loops_pairs = self._count_loops(sigma, tau, stabilizer_count, return_pairs=True)
                meataxe_pairs = self._count_meataxe(sigma, tau, stabilizer_count, return_pairs=True)
                extra_loops = [a for a in loops_pairs if a not in meataxe_pairs]
                extra_meataxe = [a for a in meataxe_pairs if a not in loops_pairs]
                raise RuntimeError
            return ans_meataxe
        else:
            raise ValueError("Unknown algorithm")
    def _count_meataxe(self, sigma, tau, stabilizer_count, return_pairs = False):
        if self.verbose:
            print "Starting meataxe count"
        t = walltime()
        V = self.V
        W = self.W
        Prump = self.Prump
        phiVW = self.phiPrump
        phiGW = self.G.NaturalHomomorphismByNormalSubgroupNC(Prump)
        sigmaW = sigma^phiGW
        tauW = tau^phiGW
        f = (sigma^self.phiGV).Order()
        #e = (tau^self.phiGV).Order()
        M = self.meataxe_module
        if not M.is_multiplicity_free():
            raise NotImplementedError("Meataxe method only available for multiplicity free modules")
        x0_counter = defaultdict(lambda: defaultdict(int))
        #samples = defaultdict(lambda: defaultdict(list))
        from_powers = self.wlooper.find_present((sigma^f)^phiVW)
        #pairs = []
        if self.verbose:
            print "Starting first loop", walltime(t)
        for w0, missing in self.wlooper:
            if self.x0_relation(sigmaW, tauW, w0) != W.Identity():
                continue
            missing = missing.difference(from_powers)
            for x0 in phiVW.PreImages(w0).AsList():
                x0rel = self.x0_relation(sigma, tau, x0)
                x0_counter[x0rel][missing] += 1
                #samples[x0rel][missing].append(x0)
        ans = QQ(0)
        if self.verbose:
            print "Starting second loop", walltime(t)
        for w1, missing in self.wlooper:
            missing = missing.difference(from_powers)
            for x1 in phiVW.PreImages(w1).AsList():
                x1rel = self.x1_relation(sigma, tau, x1)
                for x0missing, x0count in x0_counter[x1rel].iteritems():
                    if len(missing.intersection(x0missing)) == 0:
                        #if return_pairs:
                        #    if not all(self.generates(sigma, tau, x0, x1) for x0 in samples[x1rel][x0missing]):
                        #        raise RuntimeError
                        #    if len(samples[x1rel][x0missing]) != x0count:
                        #        raise RuntimeError
                        #    for x0 in samples[x1rel][x0missing]:
                        #        pairs.append((x0, x1))
                        ans += x0count
        #if return_pairs:
        #    return pairs
        if self.verbose:
            print "Finished second loop", walltime(t)
        return ans / stabilizer_count
    def _count_loops(self, sigma, tau, stabilizer_count, return_pairs = False):
        V = self.V
        ans = QQ(0)
        #pairs = []
        if self.use_prump:
            Prump = self.Prump
            for x in V.RightTransversal(Prump).AsList():
                if Prump.CanonicalRightCosetElement(x^sigma) != Prump.CanonicalRightCosetElement(self.angle_bracket(x, tau)):
                    continue
                for x0trans in Prump.List():
                    x0 = x0trans * x
                    x0rel = self.x0_relation(sigma, tau, x0)
                    for x1 in V.List():
                        if self.x1_relation(sigma, tau, x1) == x0rel and self.generates(sigma, tau, x0, x1):
                            #if return_pairs:
                            #    pairs.append((x0,x1))
                            ans += 1
        else:
            for x0 in V.List():
                for x1 in V.List():
                    if self.x0_relation(sigma, tau, x0) == self.x1_relation(sigma, tau, x1) and self.generates(sigma, tau, x0, x1):
                        #if return_pairs:
                        #    pairs.append((x0,x1))
                        ans += 1
        #if return_pairs:
        #    return pairs
        return ans/stabilizer_count

class WLooper(SageObject):
    def __init__(self, vlooper):
        self.vlooper = vlooper
        self.M = M = vlooper.meataxe_module
        self.W = W = vlooper.W
        Wgens = W.IndependentGeneratorsOfAbelianGroup()
        self.p = p = vlooper.p
        self.basis = []
        self.breaks = []
        curbreak = 0r
        zero = 0*gap.Z(p)
        changemat = []
        for i, (vecs, sub) in enumerate(M.Indecomposition()):
            for vec in vecs:
                changemat.append(vec)
                self.basis.append(prod(w^(a.Int()) for w,a in zip(Wgens, vec) if a != zero))
            self.breaks.append((curbreak, curbreak + len(vecs), i+1r))
            curbreak += len(vecs)
        self.changemat = gap.List(changemat).Inverse()
        self.dim = len(self.basis)
    def find_present(self, w):
        if w == self.W.Identity():
            return frozenset()
        return self.find_missing([int(a.Int()) for a in (self.W.IndependentGeneratorExponents(w) * self.changemat)], inverse=True)
    def find_missing(self, expvec, inverse=False):
        missing = []
        for start, end, index in self.breaks:
            if all(expvec[i] == 0 for i in xrange(start, end)):
                missing.append(index)
        if inverse:
            if self.breaks:
                return frozenset([i for i in range(1,self.breaks[-1][-1]+1) if i not in missing])
            return frozenset()
        return expvec, frozenset(missing)
    def __iter__(self):
        p = self.p
        B = self.basis
        for expvec, missing in xmrange((p for m in xrange(self.dim)), self.find_missing):
            # could be fancy to avoid this many multiplications
            w = self.W.Identity()
            for b, i in zip(B, expvec):
                if i != 0:
                    w *= b^i
            yield (w, missing)

def make_transitive_list(deg, id_start=1):
    Es = []
    for i in range(id_start,gap.NrTransitiveGroups(deg)+1):
        T = gap.TransitiveGroup(deg, i)
        for p in ZZ(T.Size()).prime_divisors():
            E = ExtensionProblem(T, p, "%sT%s (p=%s)"%(deg, i, p))
            Es.append(E)
    return Es

def make_small_list(order, p, id_start=1):
    Es = []
    for i in range(id_start,gap.NumberSmallGroups(order)+1):
        G = gap.SmallGroup(order, i).IsomorphismPermGroup().Image()
        E = ExtensionProblem(G, p, "%sG%s (p=%s)"%(order, i, p))
        Es.append(E)
    return Es

def make_field_counting_dict(filename):
    D = defaultdict(dict)
    with open(filename) as F:
        for line in F.readlines():
            t0, t1, p, count = map(ZZ, count_re.match(line).groups())
            D[t0, p][t1] = count
    return D

def count_generating_subfields(G, n, return_gps=False):
    count = ZZ(0)
    gps = []
    for C in reversed(list(G.ConjugacyClassesSubgroups())):
        H = C.Representative()
        m = G.IndexNC(H)
        if m != n:
            continue
        if C.AsList().Intersection().Size() == 1:
            if return_gps:
                gps.append(H)
            count += 1
    if return_gps:
        return gps
    else:
        return count

def count_fields_of_degree(n, p, D = None):
    nT = ZZ(gap.NrTransitiveGroups(n))
    isoclasses = {}
    if D is None or not p.divides(n):
        D = {}
        for i in range(1,nT+1):
            T = gap.TransitiveGroup(n, i)
            E = ExtensionProblem(T, p, "%sT%s (p=%s)"%(n, i, p))
            D[i] = E.count(verbose=False)
            print E.label, D[i]
    else:
        D = D[n, p]
        for i in range(1,nT+1):
            if i not in D:
                D[i] = 0
    ans = 0
    big_groups = defaultdict(list) # groups too large for IdGroup to work.
    for i in xrange(1, nT+1):
        if D[i] != 0:
            T = gap.TransitiveGroup(n, i)
            try:
                gid = T.IdGroup()
                gid = (ZZ(gid[1]), ZZ(gid[2]))
                if gid in isoclasses:
                    print "Duplicate %sT%s of %s"%(n, i, isoclasses[gid])
                    continue
                isoclasses[gid] = "%sT%s"%(n,i)
            except RuntimeError: # too big for IdGroup
                Tsize = ZZ(T.Size())
                if Tsize in big_groups:
                    found = False
                    for H, label in big_groups[Tsize]:
                        if T.IsIsomorphicGroup(H):
                            print "Duplicate %sT%s of %s"%(n, i, label)
                            found = True
                            break
                    if found:
                        continue
                big_groups[Tsize].append((T, "%sT%s"%(n, i)))
            print "Counting %sT%s "%(n, i),
            increment = D[i] * count_generating_subfields(T, n)
            ans += increment
            print increment
    return ans

class MeataxeModule(SageObject):
    def __init__(self, M, Tgens):
        self.M = M
        self.Tgens = Tgens
    def _call(self, fname, *args):
        if args:
            return gap.new('MTX.%s(%s, %s)'%(fname, self.M.name(), ', '.join(a.name() for a in args)))
        else:
            return gap.new('MTX.%s(%s)'%(fname, self.M.name()))
    def __repr__(self):
        return "Meataxe Module F_%s^%s"%(self.Field().Characteristic(), self.Dimension())
    def Generators(self):
        return self._call('Generators')
    def generators(self):
        p = ZZ(self.Field().Size())
        G = self.Generators()
        K = GF(p)
        return [matrix(K,[[K(c) for c in v] for v in gen]) for gen in G]
    def Dimension(self):
        return self._call('Dimension')
    def Field(self):
        return self._call('Field')
    def IsIrreducible(self):
        return bool(self._call('IsIrreducible'))
    def IsAbsolutelyIrreducible(self):
        return bool(self._call('IsAbsolutelyIrreducible'))
    def DegreeSplittingField(self):
        return self._call('DegreeSplittingField')
    def IsIndecomposable(self):
        return bool(self._call('IsIndecomposable'))
    @cached_method
    def Indecomposition(self):
        return [(vecs, MeataxeModule(M, self.Tgens)) for (vecs, M) in self._call('Indecomposition')]
    @cached_method
    def HomogeneousComponents(self):
        ans = []
        for rec in self._call('HomogeneousComponents'):
            comp = gap.new('%s.component'%rec.name())
            ans.append({'indices': [ZZ(a) for a in gap.new('%s.indices'%rec.name())],
                        'component': (comp[1], MeataxeModule(comp[2], self.Tgens)),
                        'images':[]})
            for other in gap.new('%s.images'%rec.name()):
                ans[-1]['images'].append((MeataxeModule(gap.new('%s.component'%other.name()), self.Tgens), gap.new('%s.isomorphism'%other.name())))
        return ans
    @cached_method
    def decomposition_type(self):
        hc = self.HomogeneousComponents()
        inds = []
        for comp in hc:
            C = comp['component'][1]
            cstr = str(C.Dimension())
            if not C.IsIrreducible():
                cstr = cstr + "*"
            if len(comp['indices']) == 1:
                inds.append(cstr)
            else:
                inds.append('%s*%s'%(len(comp['indices']), cstr))
        return " + ".join(inds)
    def is_multiplicity_free(self):
        hc = self.HomogeneousComponents()
        return all(len(comp['indices']) == 1 for comp in hc)
    def ProperSubmoduleBasis(self):
        return self._call('ProperSubmoduleBasis')
    def BasesSubmodules(self):
        return self._call('BasesSubmodules')
    def BasesMinimalSubmodules(self):
        return self._call('BasesMinimalSubmodules')
    def BasesMaximalSubmodules(self):
        return self._call('BasesMaximalSubmodules')
    def BasisRadical(self):
        return self._call('BasisRadical')
    def BasisSocle(self):
        return self._call('BasisSocle')
    def BasesCompositionSeries(self):
        return self._call('BasesCompositionSeries')
    def CompositionFactors(self):
        return self._call('CompositionFactors')
    def CollectedFactors(self):
        return self._call('CollectedFactors')
    def BasisModuleEndomorphisms(self):
        return self._call('BasisModuleEndomorphisms')
    def ModuleAutomorphisms(self):
        return self._call('ModuleAutomorphisms')
    def InvariantBilinearForm(self):
        return self._call('InvariantBilinearForm')
    def InvariantSesquilinearForm(self):
        return self._call('InvariantSesquilinearForm')
    def InvariantQuadraticForm(self):
        return self._call('InvariantQuadraticForm')
    def BasisInOrbit(self):
        return self._call('BasisInOrbit')
    def OrthogonalSign(self):
        return self._call('OrthogonalSign')

    def SubGModule(self, subspace):
        return self._call('SubGModule', subspace)
    def BasesMinimalSupermodules(self, sub):
        return self._call('BasesMinimalSupermodules', sub)
    def InducedActionSubmodule(self, sub):
        return MeataxeModule(self._call('InducedActionSubmodule', sub), self.Tgens)
    def InducedActionFactorModule(self, sub, compl=None):
        if compl is None:
            return MeataxeModule(self._call('InducedActionFactorModule', sub), self.Tgens)
        else:
            return MeataxeModule(self._call('InducedActionFactorModule', sub, compl), self.Tgens)
    def InducedAction(self, sub, typ=7):
        return self._call('InducedAction', sub, typ)
    def BasisModuleHomomorphisms(self, other):
        return self._call('BasisModuleHomomorphisms', other.M)
    def IsomorphismModules(self, other):
        return self._call('IsomorphismModules', other.M)

def stupid_exp(x, cgen, p):
    for i in range(p):
        if x == cgen^i:
            return i
    raise RuntimeError

class LabelTree(object):
    def __init__(self, label, GC, G):
        self.label = label
        self.GC = GC
        self.G = G
    def best_path(self):
        G = self.G
        Gsize = ZZ(G.Size())
        best_cost = infinity
        try:
            Norms = self.G.MinimalNormalSubgroups()
        except RuntimeError:
            if DEBUG:
                raise
            else:
                raise UnboundLocalError # to distinguish from memory errors.
        for n, N in enumerate(Norms):
            Nsize = ZZ(N.Size())
            if Nsize == 1:
                continue
            Qsize = Gsize // Nsize
            Q = self.G.FactorGroupNC(N)
            try:
                ischarsub = bool(G.IsCharacteristicSubgroup(N))
            except RuntimeError:
                if DEBUG:
                    raise
                else:
                    raise UnboundLocalError
            if Qsize < self.GC.GL.Gbound and Qsize.valuation(2) < 9:
                gid = int(Q.IdSmallGroup()[2])
                glabel = "%sG%s"%(Qsize, gid)
                if glabel in GC.missing():
                    print "Bad label %s"%glabel
                    continue
                cost = self.GC.count[glabel] * Nsize^4
                if cost == 0:
                    return None, "", [], [], []
                label = self.label
                sizes = [Qsize]
                lens = []
                genss = []
            else:
                cost, label, sizes, lens, genss = LabelTree(self.label + "_%s"%(n+1), self.GC, Q).best_path()
                if cost is None:
                    return None, "", [], [], []
                cost += Nsize^4 # We don't know the count, so we guess 1.
                sizes = [Qsize] + sizes
                lens = [len(G.GeneratorsOfGroup())] + lens
                genss = [str(N.GeneratorsOfGroup())] + genss
            if cost < best_cost or cost == best_cost and ischarsub:
                best_cost = cost
                best = label, sizes, lens, genss
        return (best_cost,) + best

class TransitiveIDs(object):
    def __init__(self, GL, Tbounds=None, idbd=None, filename=None, countfile=None):
        self.GL = GL
        p = self.GL.p
        if filename is None:
            if Tbounds is None:
                Tbounds = (GL.p, 31)
                if idbd is None:
                    filename = "tid%s"%p
                else:
                    raise ValueError
            else:
                Tbounds = (p*ceil(Tbounds[0]/p), Tbounds[1])
                filename = "tid%s_%s_%s"%(p, Tbounds[0], Tbounds[1])
                if idbd is not None:
                    filename += "_%s_%s"%(idbd[0], idbd[1])
        self.filename = filename
        if countfile is None:
            if Tbounds == (GL.p, 31):
                if idbd is None:
                    countfile = "tcount%s"%p
                else:
                    raise ValueError
            else:
                Tbounds = (p*ceil(Tbounds[0]/p), Tbounds[1])
                countfile = "tcount%s_%s_%s"%(p, Tbounds[0], Tbounds[1])
                if idbd is not None:
                    countfile += "_%s_%s"%(idbd[0], idbd[1])
        self.countfile = countfile
        self.count = {}
        self.Tbounds = Tbounds
        self.idbd = idbd
        self.id = {} # tid -> gid or None
        self.back = defaultdict(list) # gid -> tids
        self.deg = defaultdict(list)
        self.load()
    def add(self, tid, gid):
        tdeg = int(tid.split('T')[0])
        if gid:
            self.id[tid] = gid
            self.back[gid].append(tid)
            if gid not in self.deg[tdeg]:
                self.deg[tdeg].append(gid)
        else:
            self.id[tid] = None
            self.deg[tdeg].append(tid)
    def load(self, filename=None, countfile=None):
        if filename is None:
            filename = self.filename
        if countfile is None:
            countfile = self.countfile
        if not (filename is False):
            if os.path.exists(filename):
                with open(filename) as F:
                    for line in F:
                        tid, gid = line.split(':')
                        self.add(tid, gid.strip())
        if not (countfile is False):
            if os.path.exists(countfile):
                with open(countfile) as F:
                    for line in F:
                        tid, count = line.split(':')
                        tid, deg = tid.split('_')
                        self.count[tid, int(deg)] = ZZ(count)
    def merge(self, counts=True):
        p = self.GL.p
        if counts:
            self.countfile = "tcount%s"%p
            self.load(filename=False)
            for file in os.listdir('.'):
                if not file.startswith('tcount%s_'%p):
                    continue
                print "Merging %s"%file
                self.load(filename=False,countfile=file)
            self.save_count()
        else:
            self.filename = 'tid%s'%p
            self.load(countfile=False)
            for file in os.listdir('.'):
                if not file.startswith('tid%s_'%p):
                    continue
                print "Merging %s"%file
                self.load(filename=file,countfile=False)
            self.save()
    def save(self, tid=None):
        if tid is None:
            with open(self.filename, 'w') as F:
                for tid in sorted(self.id.keys(), key=_label_key):
                    gid = self.id[tid]
                    if gid is None:
                        gid = ""
                    F.write("%s: %s\n"%(tid, gid))
        else:
            with open(self.filename, 'a') as F:
                gid = self.id[tid]
                if gid is None:
                    gid = ""
                F.write("%s: %s\n"%(tid, gid))
    def save_count(self, iddeg=None):
        if iddeg is None:
            with open(self.countfile, 'w') as F:
                for label, deg in sorted(self.count.keys(), key=lambda (x,y): (y,_label_key(x))):
                    F.write("%s_%s: %s\n"%(label, deg, self.count[label,deg]))
        else:
            with open(self.countfile, 'a') as F:
                F.write("%s_%s: %s\n"%(iddeg[0], iddeg[1], self.count[iddeg]))
    def crossload(self, others):
        for other in others:
            for tid, gid in other.id.iteritems():
                if gid in self.GL.groups and tid not in self.id:
                    self.add(tid, gid)
    def compute(self):
        p = self.GL.p
        t0, t1 = self.Tbounds
        for deg in range(t0, t1, p):
            if self.idbd is None:
                a,b = 1,gap.NrTransitiveGroups(deg)+1
            else:
                a = max(1, self.idbd[0]+1)
                b = min(gap.NrTransitiveGroups(deg)+1, self.idbd[1]+1)
            for i in range(a,b):
                tlabel = "%sT%s"%(deg, i)
                if tlabel in self.id:
                    continue
                T = gap.TransitiveGroup(deg, i)
                order = ZZ(T.Size())
                if order < self.GL.Gbound and order.valuation(2) < 9:
                    gid = int(T.IdSmallGroup()[2])
                    glabel = "%sG%s"%(order, gid)
                    if glabel in self.GL.groups[order]:
                        self.add(tlabel, glabel)
                        self.save(tlabel)
                else:
                    E = ExtensionProblem(T, p, tlabel)
                    if E.is_potentially_padic():
                        self.add(tlabel, None)
                        self.save(tlabel)
                print "%s complete"%tlabel
    def write_buckets(self, deg):
        L = self.deg[deg]
        buckets = defaultdict(list)
        for label in L:
            if 'T' in label:
                T = _get_group(label)
                order = ZZ(T.Size())
                zsize = ZZ(T.Centre().Size())
                ccc = ZZ(T.NrConjugacyClasses())
                dsize = ZZ(T.DerivedSubgroup().Size())
                nc = ZZ(T.NilpotencyClass()) if order.is_prime_power() else 0
                buckets[order, zsize, dsize, ccc, nc].append(label)
        print "Bucket sizes %s"%(" ".join(str(len(L)) for L in buckets.itervalues()))
        with open('buckets', 'w') as F:
            for invs in sorted(buckets.keys(),key=lambda x: (len(buckets[x]),x)):
                if len(buckets[invs]) > 1:
                    F.write(" ".join(buckets[invs]) + '\n')
    def test_dups(self, Mlen, low=None, high=None):
        buckets = []
        with open('buckets') as F:
            for line in F:
                buckets.append(line.strip().split())
        buckets = [L for L in buckets if len(L) == Mlen]
        for i, M in enumerate(buckets):
            if (low is None or i >= low) and (high is None or i < high):
                print "testing(%s) %s"%(i, " ".join(M))
                self.test_dup_bucket(M)
    def test_dup_bucket(self, M):
        for i, x in enumerate(M):
            for j, y in enumerate(M):
                if j <= i:
                    continue
                print "%s ? %s"%(x,y)
                if _get_group(x).IsIsomorphicGroup(_get_group(y)):
                #if gap.eval('IsomorphismGroups(TransitiveGroup(' + x.replace('T',',') + '),TransitiveGroup(' + y.replace('T',',') + ')) = fail;') == 'false':
                    with open('tdup%s_tst'%(self.p), 'a') as F:
                        F.write("%s = %s"%(x, y))
    def remove(self, filename):
        with open(filename) as F:
            for line in F:
                for label in line[line.find('=')+1:].strip().split(' = '):
                    print "Removing %s"%label
                    del self.id[label]
        self.save()
    def inject(self):
        orders = []
        for tlabel, glabel in self.id.iteritems():
            if glabel is None:
                order = _get_size(tlabel)
                self.GL.groups[order].append(tlabel)
                orders.append(order)
        for order in orders:
            self.GL.groups[order] = sorted(list(set(self.GL.groups[order])), key=_label_key)
        self.GL.save()
    def count_generating_subfields(self, deg=None, label=None, lblstart=None, return_gps=False):
        if deg is None:
            t0, t1 = self.Tbounds
            for d in range(t0, t1, p):
                self.count_generating_subfields(d)
        elif label is None:
            for i, lbl in enumerate(self.deg[deg]):
                if lblstart is not None and lbl != lblstart:
                    continue
                if self.idbd is None or (i >= self.idbd[0] and i < self.idbd[1]):
                    self.count_generating_subfields(deg, lbl)
        else:
            print "Counting %s"%label
            G = _get_group(label)
            count = ZZ(0)
            gps = []
            for C in reversed(list(G.ConjugacyClassesSubgroups())):
                H = C.Representative()
                m = G.IndexNC(H)
                if m != deg:
                    continue
                if C.AsList().Intersection().Size() == 1:
                    if return_gps:
                        gps.append(H)
                    count += 1
            self.count[label,deg] = count
            if return_gps:
                return gps
        self.save_count()

def _get_gap_str(label, name):
    if 'G' in label:
        return name + ' := SmallGroup(%s,%s);\n'%(tuple(label.split('G')))
    elif 'T' in label:
        return name + ' := TransitiveGroup(%s,%s);\n'%(tuple(label.split('T')))
    elif 'Q' in label:
        deg, tid = label[:label.find('p')].split('Q')
        s = name + ' := Temp;\n'
        while '_' in label:
            with open("IGPdata/ndata_%s"%(label)) as F:
                lsplit = F.readlines()
                size, ngens, genstr = lsplit[0], lsplit[1], "\n".join(lsplit[2:])
            label = label[:label.rfind('_')]
            s = 'Temp := FactorGroupNC(Temp, NTemp);\n' + s
            s = 'NTemp := Subgroup(Temp, %s);\n'%(genstr.strip()) + s
            if '_' in label:
                s = ' '.join('f%s := tempgens[%s];'%(i,i) for i in range(1,int(ngens)+1)) + '\n' + s
                s = 'tempgens := GeneratorsOfGroup(Temp);\n' + s
        s = 'Temp := TransitiveGroup(%s,%s);\n'%(deg, tid) + s
        return s
    else:
        raise ValueError("unparsable label")
def _get_group(label):
    if 'G' in label:
        return gap.SmallGroup(*map(int, label.split('G')))
    elif 'T' in label:
        return gap.TransitiveGroup(*map(int, label.split('T')))
    elif 'Q' in label:
        gap.eval(_get_gap_str(label, label))
        return gap(label)
    else:
        raise ValueError("unparsable label")
def _get_size(label):
    if 'G' in label:
        return ZZ(label[:label.find('G')])
    else:
        return ZZ(_get_group(label).Size())
def _label_key(x):
    if 'G' in x:
        ltype = 0
        parts = map(int, x.split('G'))
    elif 'T' in x:
        ltype = 1
        parts = map(int, x.split('T'))
    else:
        ltype = 2
        parts = x.split('Q')
        parts[1:] = parts[1].split('_')
    return ltype, parts

class GeneratingSystem(SageObject):
    def __init__(self, label, p):
        self.label = label
        self.p = p
        self.load()
    def fill(self, GP, count_only=None, algorithm=None):
        label, p = self.label, self.p
        # Add short-circuiting code
        if count_only is None:
            count_only = not GP.needed[label]
        if algorithm is None:
            algorithm = 'lift' if (GP.lift_cost[label] < GP.sol_cost[label]) else 'solitaire'
        if algorithm == 'solitaire':
            if count_only:
                E = ExtensionProblem(_get_group(label), p, label)
                self.count = E.count
            else:
                raise NotImplementedError
        elif algorithm == 'lift':
            for qlabel in GP.maxquo[label]:
                QCS = GeneratingSystem(qlabel, p)
                if hasattr(QCS, 'count') and QCS.count == 0:
                    self.count = 0
                    self.genss = []
                    break
            else:
                qlabel = GP.bestquo[label]
                QGS = GeneratingSystem(qlabel, p)
                if not hasattr(QCS, 'genss'):
                    QGS.fill(GP, count_only=False)
                self._lift(QGS)
        self.save()
    def _lift(self, QGS):
        gap.eval("Read(lift_gens.g)")
        gap.eval("")
    def _filename(self):
        return os.path.join('IGPdata','%s_%s.sobj'%(self.label,self.p))
    def save(self):
        SageObject.save(self, self._filename())
    def load(self):
        old = load(self._filename())
        self.__dict__.update(old.__dict__)

class GroupCounts(object):
    def __init__(self, GP, filename=None, savename=None):
        self.GP = GP
        if filename is None:
            filename = "Gcounts.txt"
        self.filename = filename
        self.count = {}
        self.load()
    def load(self):
        p = self.GP.GL.p
        with open(self.filename) as F:
            for line in F:
                label, pstr, count = line.split(" ")
                lp = ZZ(pstr[pstr.find('=')+1:-1])
                if lp != p:
                    continue
                self.count[label] = ZZ(count.strip())
    def show_poset(self):
        for label in sorted(self.GP.maxquo, key=_label_key):
            if label not in self.count:
                continue
            print "%s(%s): %s"%(label, self.count[label], " ".join("%s(%s)^%s"%(qlabel, self.count.get(qlabel, '?'), self.GP.maxquo[label][qlabel]) for qlabel in self.GP.maxquo[label]))

def nQuotients(G, H):
    nG = ZZ(G.Size())
    nH = ZZ(H.Size())
    if not nH.divides(nG):
        return 0
    nN = nG // nH
    count = 0
    for N in G.NormalSubgroups():
        if N.Size() != nN:
            continue
        if H.IsIsomorphicGroup(G.FactorGroupNC(N)):
            count += 1
    return count

def run_transitive_test(deg_start=4,id_start=1):
    exceptional = []
    for deg in range(deg_start,31):
        print "starting degree %s (%s groups)"%(deg, gap.NrTransitiveGroups(deg))
        for E in make_transitive_list(deg,id_start if deg==deg_start else 1):
            if E.p != 2 and E.is_potentially_padic():
                print E.label,
                print E.count(verbose=False)
                #print E.group.StructureDescription(),
                #if E.pcore.Size() > 1:
                #    print VLooper(E).meataxe_module.decomposition_type()
                #if E.count(verbose=False) == 0:
                #    exceptional.append(E)
    #return exceptional

def run_small_test(ord_start=3,ord_end=75,id_start=1,p=3):
    for order in range(ord_start,ord_end,p):
        print "starting order %s (%s groups)"%(order, gap.NumberSmallGroups(order))
        for E in make_small_list(order, p, id_start if order==ord_start else 1):
            if E.is_potentially_padic():
                print E.label,
                print E.count(verbose=False)

def reduction_is_isomorphic(cid, p):
    dim, qid = cid.split("C")
    dim = ZZ(dim)
    qid = ZZ(qid)
    one = gap.Z(p)^0
    for zid in range(1, gap.CaratNrZClasses(dim, qid)+1):
        G = gap.CaratMatGroupZClass(dim, qid, zid)
        L = []
        for g in G.GeneratorsOfGroup():
            L.append(gap.List([gap.List([a * one for a in b]) for b in g]))
        Gp = gap.Group(L)
        print "%s_%s %s %s"%(cid, zid, G.Size(), Gp.Size())

def load_zero_list(filename):
    ans = []
    with open(filename) as F:
        for line in F.readlines():
            t0, t1, p = zero_re.match(line).groups()
            ans.append(ExtensionProblem(gap.TransitiveGroup(ZZ(t0), ZZ(t1)), ZZ(p), "%sT%s (p=%s)"%(t0, t1, p)))
    return ans

def process_datafile(filename):
    gap_reset_workspace()
    gap.eval('Read("caratnumber.gap")')
    gap.save_workspace()
    probs = []
    with open(filename) as F:
        for line in F.readlines():
            g = gid_re.match(line)
            if g:
                try:
                    gid = tuple(int(a) for a in g.groups())
                    G = None
                except ValueError:
                    G = False
            else:
                M = wild_re.match(line)
                if M:
                    if G is False:
                        continue
                    elif G is None:
                        G = gap.SmallGroup(*gid).IsomorphismPermGroup().Image()
                    M = M.groups()
                    p = Integer(M[0])
                    probs.append(ExtensionProblem(G, p, "%sG%s (p=%s)"%(gid[0], gid[1], p)))
    return probs

def cyc_count_check(m_bound, p_bound):
    for p in prime_range(p_bound):
        for m in srange(1, m_bound):
            if p.divides(m):
                continue
            assert cyc_count1(m, p) == cyc_count2(m, p)

def cyc_count1(m, p):
    ans = ZZ(1)
    for ell, kay in factor(m):
        if (ell^kay).divides(p-1):
            # tau/x_1 is unrestricted
            # sigma and tau/x_1 must together generate, so at least one is a generator (ell-power cyclic group)
            ans *= ell^(kay - 1) * (ell+1)
        else:
            # sigma must generate, canceling with the size of the automorphism group
            ans *= (ell^kay).gcd(p-1)
    return ans

def cyc_count2(m, p, show=False):
    ans = ZZ(0)
    e = gcd(m, p-1)
    fe = m // e
    max_b = e
    d = gcd(max_b, fe)
    while d != 1:
        max_b = max_b // d
        d = gcd(max_b, fe)
    for b in max_b.divisors():#  (a-1)*b = 0 and (a,m) = 1
        bstab = [1+(e//b)*x for x in range(b) if gcd(1+(e//b)*x,e) == 1]
        if show:
            print bstab
        for c in range(e):
            if gcd(b, c*fe) == 1 and all(c*s%e >= c for s in bstab):
                if show:
                    print b, c*fe
                ans += 1
    return ans

def setuprun(p):
    global GL, GP, GC
    gap.eval('LoadPackage("CRISP");')
    GL = GroupList(p, 2001)
    GP = GroupPoset(GL)
    GC = GroupCounter(GP)
    try:
        gap.eval('Read("lift_gens.g");')
    except RuntimeError:
        pass
    GC.fill_transitive()
    #gap.eval('LoadPackage("images");')
    #GC.run()

def setupcount(p):
    global GL, GP, GC, gap
    #sage.interfaces.gap.gap_cmd = "/home/roed/bin/gap"
    #gap = sage.interfaces.gap.Gap(use_workspace_cache=False, max_workspace_size=None)
    gap.eval('LoadPackage("CRISP");')
    gap.eval('LoadPackage("images");')
    GL = GroupList(p, 2001)
    GP = GroupPoset(GL)
    GC = GroupCounter(GP)
    try:
        gap.eval('Read("lift_gens.g");')
    except RuntimeError:
        pass
    GC.run()

def compare_counts(GL):
    p = GL.p
    #def get_count(
    for order, L in GL.groups.iteritems():
        pass
