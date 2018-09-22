# padicIGP
Code for counting the number of extensions of a p-adic field with a specified Galois group

Installation
============

You should have a recent copy of Sage, with the GAP small groups package installed (run `sage -i gap_packages`).  Clone this repository, then attach `counter.sage` (from the sage prompt in the `padicIGP` directory, type `%attach counter.sage`).  All of the commands below should be executed while in this directory.

Listing potentially p-adic groups
---------------------------------

To create a list of potentially 3-adic groups of order up to 100, do the following.
```
sage: GL = GroupList(3, 100)
2G1 potentially 3-adic
G2 complete
...
99G2 potentially 3-adic
G99 complete
```

The `GL` object is used as input for other operations; creating it will create a file `glist3` in your current directory listing the groups.  If this file is present, future calls to `GroupList` will use it instead of redoing the computation

Determining which are p-adic
----------------------------

We first create an auxilliary object to store minimal normal subgroups.  As above, the data will be loaded from a file `gposet3`; calling `clean()` is only necessary when adding data to the file.

```
sage: GP = GroupPoset(GL)
2G1 complete
...
99G2 complete
```

You can call `GP.clean()` if you want to remove the lines from the file corresponding to abelian groups.

We then create an object that does the bulk of the counting.

```
sage: GC = GroupCounter(GP)
sage: GC.run()
Abelian 2G1...  3
Abelian 3G1...  4
Abelian 4G1...  2
Abelian 4G2...  1
Abelian 5G1...  1
Prepping 6G1...  lifting 2G1 (cost 27/2)...  6
...
Prepping 96G60...  lifting 48G23 (cost 8)...  4
Abelian 97G1...  1
Abelian 98G2...  3
Abelian 99G1...  12
Abelian 99G2...  1
```

The counts are stored in a file `gcount3`, which is read from when creating the `GroupCounter` in future sessions.  They are also available in the dictionary ``GC.count``:

```
sage: GC.count['90G6']
24
sage: GC.count['72G33']
0
```

You can get a list of groups that are in the group list but have not been counted:

```
sage: GC.missing()
[]
```


Statistics
----------

Some functionality is available for computating statistics on p-adic and potentially p-adic groups.

You can determine the size of the minimal normal subgroup among groups in the list (it only includes non-abelian groups with nontrivial p-core).  This size is an important ingredient in the runtime for the algorithm determining whether the group is p-adic.

These functions are just provided for analysis; they are not used in the core implementation.

```
sage: GL.count_small_normals()
6G1
...
96G60
defaultdict(<type 'int'>, {9: 4, 2: 79, 3: 36})
```

If you're interested in the sizes of all the minimal normal subgroups, you can use the `GroupPoset` object.

```
sage: GP.extension_sizes()
55G1 5 * 11
39G1 3 * 13
2: 111
3: 36
5: 1
7: 1
9: 4
11: 1
13: 1
```
The groups with large minimal quotients are printed first, along with the factorizations of their orders.

You can summarize the counts, getting a dictionary whose keys are integers and value at `n` is the number of groups `G` in the list so that there are `n` extensions with group `G`.

```
sage: GC.summarize_counts()
```

Analysis
--------

There are some functions for attempting to explain why certain groups do not arise as p-adic Galois groups.  See the documentation in `counter.sage` for more details.  For example, after running `GC.zeros()` the file `zero3` will contain

```
24G10: abelian tame(8G3:1) V(C3) 1 tau=1
36G7: abelian tame(4G1:2) V(C3 x C3) 2*1 tau=1
54G14: abelian tame(2G1:3) V(C3 x C3 x C3) 3*1
72G33: abelian tame(8G3:1) V(C3 x C3) 2*1 tau=1
```

Using multiple cores
--------------------

The code supports parallelization, but in a somewhat manual way.  You can pass arguments to the functions that take substantial time (initialization methods on `GroupList` and `GroupPoset` and `run()` on `GroupCounter`) to break up computations into smaller pieces.