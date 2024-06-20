use super::IC3;
use logic_form::{Cube, Lemma, Lit};
use std::{collections::HashSet, time::Instant};

enum DownResult {
    Success(Cube),
    Fail,
    IncludeInit,
}

impl IC3 {
    fn ctg_down(
        &mut self,
        frame: usize,
        cube: &Cube,
        keep: &HashSet<Lit>,
        _level: usize,
        full: &Cube,
        cex: &mut Vec<(Lemma, Lemma)>,
    ) -> DownResult {
        let mut cube = cube.clone();
        self.statistic.num_down += 1;
        // let mut ctgs = 0;
        loop {
            if self.ts.cube_subsume_init(&cube) {
                return DownResult::IncludeInit;
            }
            let lemma = Lemma::new(cube.clone());
            for (s, t) in cex.iter() {
                if !lemma.subsume(s) && lemma.subsume(t) {
                    return DownResult::Fail;
                }
            }
            match self.blocked_with_ordered(frame, &cube, false, true, false) {
                Some(true) => {
                    return DownResult::Success(self.solvers[frame - 1].inductive_core());
                }
                Some(false) => {
                    let mut ret = false;
                    let mut cube_new = Cube::new();
                    for lit in cube {
                        if keep.contains(&lit) {
                            if let Some(true) = self.solvers[frame - 1].sat_value(lit) {
                                cube_new.push(lit);
                            } else {
                                ret = true;
                                break;
                            }
                        } else if let Some(true) = self.solvers[frame - 1].sat_value(lit) {
                            if !self.solvers[frame - 1].flip_to_none(lit.var()) {
                                cube_new.push(lit);
                            }
                        }
                    }
                    cube = cube_new;

                    let mut s = Cube::new();
                    let mut t = Cube::new();
                    for l in full.iter() {
                        if let Some(v) = self.solvers[frame - 1].sat_value(*l) {
                            if !self.solvers[frame - 1].flip_to_none(l.var()) {
                                s.push(l.not_if(!v));
                            }
                        }
                        let lt = self.ts.lit_next(*l);
                        if let Some(v) = self.solvers[frame - 1].sat_value(lt) {
                            t.push(l.not_if(!v));
                        }
                    }
                    cex.push((Lemma::new(s), Lemma::new(t)));
                    if ret {
                        return DownResult::Fail;
                    }
                }
                None => return DownResult::Fail,
            }
        }
    }

    fn handle_down_success(
        &mut self,
        _frame: usize,
        cube: Cube,
        i: usize,
        mut new_cube: Cube,
    ) -> (Cube, usize) {
        new_cube = cube
            .iter()
            .filter(|l| new_cube.contains(l))
            .cloned()
            .collect();
        let new_i = new_cube
            .iter()
            .position(|l| !(cube[0..i]).contains(l))
            .unwrap_or(new_cube.len());
        if new_i < new_cube.len() {
            assert!(!(cube[0..=i]).contains(&new_cube[new_i]))
        }
        (new_cube, new_i)
    }

    pub fn mic(&mut self, frame: usize, mut cube: Cube, level: usize) -> Cube {
        let mut cex = Vec::new();
        let start = Instant::now();
        self.solvers[frame - 1].set_domain(
            self.ts
                .cube_next(&cube)
                .iter()
                .copied()
                .chain(cube.iter().copied()),
        );
        self.statistic.avg_mic_cube_len += cube.len();
        self.statistic.num_mic += 1;
        self.activity.sort_by_activity(&mut cube, true);
        let mut keep = HashSet::new();
        let mut i = 0;
        while i < cube.len() {
            if keep.contains(&cube[i]) {
                i += 1;
                continue;
            }
            let mut removed_cube = cube.clone();
            removed_cube.remove(i);
            match self.ctg_down(frame, &removed_cube, &keep, level, &cube, &mut cex) {
                DownResult::Success(new_cube) => {
                    self.statistic.mic_drop.success();
                    (cube, i) = self.handle_down_success(frame, cube, i, new_cube);
                    self.solvers[frame - 1].unset_domain();
                    self.solvers[frame - 1].set_domain(
                        self.ts
                            .cube_next(&cube)
                            .iter()
                            .copied()
                            .chain(cube.iter().copied()),
                    );
                }
                _ => {
                    self.statistic.mic_drop.fail();
                    keep.insert(cube[i]);
                    i += 1;
                }
            }
        }
        self.solvers[frame - 1].unset_domain();
        self.activity.bump_cube_activity(&cube);
        self.statistic.overall_mic_time += start.elapsed();
        cube
    }
}
