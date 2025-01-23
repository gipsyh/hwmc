use crate::IC3;
use logic_form::Cube;

impl IC3 {
    pub fn blocked(&mut self, frame: usize, cube: &Cube, strengthen: bool) -> bool {
        assert!(!self.ts.cube_subsume_init(cube));
        let start = self.statistic.time.start();
        self.statistic.sat_num += 1;
        let res = self.solvers[frame - 1].inductive(cube, strengthen);
        self.statistic.sat_avg_time += self.statistic.time.stop(start);
        res
    }

    pub fn blocked_with_ordered(
        &mut self,
        frame: usize,
        cube: &Cube,
        ascending: bool,
        strengthen: bool,
    ) -> bool {
        let mut ordered_cube = cube.clone();
        self.activity.sort_by_activity(&mut ordered_cube, ascending);
        let start = self.statistic.time.start();
        self.statistic.sat_num += 1;
        let res = self.solvers[frame - 1].inductive(&ordered_cube, strengthen);
        self.statistic.sat_avg_time += self.statistic.time.stop(start);
        res
    }

    pub fn get_bad(&mut self) -> Option<(Cube, Cube)> {
        self.statistic.qbad_num += 1;
        let qbad_start = self.statistic.time.start();
        let solver = self.solvers.last_mut().unwrap();
        solver.assump = self.ts.bad.cube();
        solver.constrain = Default::default();
        let res = solver.solve_with_domain(&[self.ts.bad], vec![], false);
        self.statistic.qbad_avg_time += self.statistic.time.stop(qbad_start);
        res.then(|| self.get_pred(self.solvers.len()))
    }
}

impl IC3 {
    pub fn get_pred(&mut self, frame: usize) -> (Cube, Cube) {
        let solver = &mut self.solvers[frame - 1];
        let mut cls: Cube = solver.assump.clone();
        cls.extend_from_slice(&self.ts.constraints);
        if cls.is_empty() {
            return (Cube::new(), Cube::new());
        }
        let cls = !cls;
        let mut inputs = Cube::new();
        for input in self.ts.inputs.iter() {
            let lit = input.lit();
            if let Some(v) = solver.sat_value(lit) {
                inputs.push(lit.not_if(!v));
            }
        }
        self.lift.set_domain(cls.iter().cloned());
        let mut latchs = Cube::new();
        for latch in self.ts.latchs.iter() {
            let lit = latch.lit();
            if self.lift.domain.has(lit.var()) {
                if let Some(v) = solver.sat_value(lit) {
                    latchs.push(lit.not_if(!v));
                }
            }
        }

        self.activity.sort_by_activity(&mut latchs, false);
        latchs = self.lift.minimal_pred(&inputs, &latchs, &cls).unwrap();
        self.lift.unset_domain();
        (latchs, inputs)
    }
}
