pub mod others;
pub mod sec;
pub mod simplify;
pub mod simulate;
pub mod unroll;

use aig::Aig;
use logic_form::{Clause, Cube, Lit, LitMap, Var, VarMap};
use satif::Satif;
use std::collections::{HashMap, HashSet};

#[derive(Clone, Default, Debug)]
pub struct Transys {
    pub inputs: Vec<Var>,
    pub latchs: Vec<Var>,
    pub init: Cube,
    pub bad: Cube,
    pub init_map: VarMap<Option<bool>>,
    pub constraints: Cube,
    pub trans: Vec<Clause>,
    pub max_var: Var,
    is_latch: VarMap<bool>,
    next_map: LitMap<Lit>,
    prev_map: LitMap<Lit>,
    pub dependence: VarMap<Vec<Var>>,
    pub max_latch: Var,
    restore: HashMap<Var, Var>,
}

impl Transys {
    #[inline]
    pub fn num_var(&self) -> usize {
        Into::<usize>::into(self.max_var) + 1
    }

    pub fn from_aig(aig: &Aig, rst: &HashMap<usize, usize>) -> Self {
        let false_lit: Lit = Lit::constant_lit(false);
        let mut max_var = false_lit.var();
        let mut new_var = || {
            max_var += 1;
            max_var
        };
        let mut dependence = VarMap::new();
        dependence.push(vec![]);
        for node in aig.nodes.iter().skip(1) {
            assert_eq!(Var::new(node.node_id()), new_var());
            let mut dep = Vec::new();
            if node.is_and() {
                dep.push(node.fanin0().to_lit().var());
                dep.push(node.fanin1().to_lit().var());
            }
            dependence.push(dep);
        }
        let inputs: Vec<Var> = aig.inputs.iter().map(|x| Var::new(*x)).collect();
        let latchs: Vec<Var> = aig.latchs.iter().map(|x| Var::new(x.input)).collect();
        let max_latch = *latchs.iter().max().unwrap_or(&Var::new(0));
        let primes: Vec<Lit> = aig
            .latchs
            .iter()
            .map(|l| {
                dependence.push(vec![l.next.to_lit().var()]);
                new_var().lit().not_if(!l.next.to_lit().polarity())
            })
            .collect();
        let init = aig.latch_init_cube().to_cube();
        let mut init_map = VarMap::new();
        init_map.reserve(max_latch);
        for l in init.iter() {
            init_map[l.var()] = Some(l.polarity());
        }
        let constraints: Cube = aig.constraints.iter().map(|c| c.to_lit()).collect();
        let aig_bad = if aig.bads.is_empty() {
            aig.outputs[0]
        } else {
            aig.bads[0]
        };
        let mut next_map = LitMap::new();
        let mut prev_map = LitMap::new();
        for (l, p) in latchs.iter().zip(primes.iter()) {
            next_map.reserve(*l);
            prev_map.reserve(p.var());
            let l = l.lit();
            next_map[l] = *p;
            next_map[!l] = !*p;
            prev_map[*p] = l;
            prev_map[!*p] = !l;
        }
        let test = aig.get_simplified_cnf();
        dbg!(test.len());
        let mut trans = aig.get_cnf();
        dbg!(trans.len());
        trans = test;
        for i in 0..aig.latchs.len() {
            trans.push(Clause::from([!primes[i], aig.latchs[i].next.to_lit()]));
            trans.push(Clause::from([primes[i], !aig.latchs[i].next.to_lit()]));
        }
        let bad = aig_bad.to_lit();
        let mut is_latch = VarMap::new_with(max_var);
        for l in latchs.iter() {
            is_latch[*l] = true;
        }
        let mut restore = HashMap::new();
        for (d, v) in rst.iter() {
            restore.insert(Var::new(*d), Var::new(*v));
        }
        for i in 0..aig.latchs.len() {
            let n = aig.latchs[i].next.to_lit();
            assert!(primes[i].polarity() == n.polarity());
            if let Some(r) = restore.get(&n.var()) {
                restore.insert(primes[i].var(), *r);
            }
        }
        Self {
            inputs,
            latchs,
            init,
            bad: Cube::from([bad]),
            init_map,
            constraints,
            trans,
            max_var,
            is_latch,
            next_map,
            prev_map,
            dependence,
            max_latch,
            restore,
        }
    }

    #[inline]
    pub fn new_var(&mut self) -> Var {
        self.max_var += 1;
        self.init_map.reserve(self.max_var);
        self.next_map.reserve(self.max_var);
        self.prev_map.reserve(self.max_var);
        self.is_latch.reserve(self.max_var);
        self.dependence.reserve(self.max_var);
        self.max_var
    }

    #[inline]
    pub fn add_latch(
        &mut self,
        state: Var,
        next: Lit,
        init: Option<bool>,
        trans: Vec<Clause>,
        dep: Vec<Var>,
    ) {
        assert!(dep.iter().all(|v| self.is_latch(*v)));
        self.latchs.push(state);
        let lit = state.lit();
        self.init_map[state] = init;
        self.is_latch[state] = true;
        self.next_map[lit] = next;
        self.next_map[!lit] = !next;
        self.prev_map[next] = lit;
        self.prev_map[!next] = !lit;
        if let Some(i) = init {
            self.init.push(lit.not_if(!i));
        }
        self.max_latch = self.max_latch.max(state);
        self.dependence[next.var()] = dep.iter().map(|v| self.next_map[v.lit()].var()).collect();
        self.dependence[state] = dep;
        for t in trans {
            self.trans.push(t);
        }
    }

    pub fn add_init(&mut self, v: Var, init: Option<bool>) {
        assert!(self.is_latch(v));
        self.init_map[v] = init;
        if let Some(i) = init {
            self.init.push(v.lit().not_if(!i));
        }
    }

    #[inline]
    pub fn var_next(&self, var: Var) -> Var {
        self.next_map[var.lit()].var()
    }

    #[inline]
    pub fn lit_next(&self, lit: Lit) -> Lit {
        self.next_map[lit]
    }

    #[inline]
    pub fn lit_prev(&self, lit: Lit) -> Lit {
        self.prev_map[lit]
    }

    #[inline]
    pub fn cube_next(&self, cube: &[Lit]) -> Cube {
        cube.iter().map(|l| self.lit_next(*l)).collect()
    }

    #[inline]
    pub fn cube_prev(&self, cube: &[Lit]) -> Cube {
        cube.iter().map(|l| self.lit_prev(*l)).collect()
    }

    #[inline]
    pub fn cube_subsume_init(&self, x: &[Lit]) -> bool {
        for x in x {
            if let Some(init) = self.init_map[x.var()] {
                if init != x.polarity() {
                    return false;
                }
            }
        }
        true
    }

    #[inline]
    pub fn is_latch(&self, var: Var) -> bool {
        self.is_latch[var]
    }

    #[allow(unused)]
    pub fn get_coi(&self, var: impl Iterator<Item = Var>) -> Vec<Var> {
        let mut marked = HashSet::new();
        let mut queue = vec![];
        for v in var {
            marked.insert(v);
            queue.push(v);
        }
        while let Some(v) = queue.pop() {
            for d in self.dependence[v].iter() {
                if !marked.contains(d) {
                    marked.insert(*d);
                    queue.push(*d);
                }
            }
        }
        Vec::from_iter(marked)
    }

    pub fn load_init<S: Satif + ?Sized>(&self, satif: &mut S) {
        satif.new_var_to(self.max_var);
        for i in self.init.iter() {
            satif.add_clause(&[*i]);
        }
    }

    pub fn load_trans(&self, satif: &mut impl Satif, constrain: bool) {
        satif.new_var_to(self.max_var);
        for c in self.trans.iter() {
            satif.add_clause(c);
        }
        if constrain {
            for c in self.constraints.iter() {
                satif.add_clause(&[*c]);
            }
        }
    }

    #[inline]
    pub fn restore(&self, lit: Lit) -> Lit {
        let var = self.restore[&lit.var()];
        Lit::new(var, lit.polarity())
    }

    // pub fn simplify_eq_latchs(&mut self, eqs: &[(Lit, Lit)], keep_dep: bool) {
    //     let mut marks = HashSet::new();
    //     let mut map = HashMap::new();
    //     for (x, y) in eqs.iter() {
    //         assert!(marks.insert(x.var()));
    //         assert!(marks.insert(y.var()));
    //         map.insert(*y, *x);
    //         map.insert(!*y, !*x);
    //     }
    //     for cls in self.trans.iter_mut() {
    //         for l in cls.iter_mut() {
    //             if let Some(r) = map.get(l) {
    //                 *l = *r;
    //             }
    //         }
    //     }
    //     self.simplify(&[], keep_dep, true)
    // }
}
