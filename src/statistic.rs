use crate::IC3;
use giputils::statistic::{Average, AverageDuration, Case, RunningTime};
use std::{fmt::Debug, time::Duration};
use transys::Transys;

#[allow(unused)]
#[derive(Debug, Default)]
pub struct Statistic {
    case: Case,
    pub num_input: usize,
    pub num_latch: usize,
    pub num_nodes: usize,
    pub time: RunningTime,

    pub qgen_num: usize,
    pub qgen_avg_time: AverageDuration,
    pub qgen_avg_cube_len: Average,

    pub qblock_num: usize,
    pub qblock_avg_time: AverageDuration,
    pub qblock_avg_cube_len: Average,

    pub qpush_num: usize,
    pub qpush_avg_time: AverageDuration,
    pub qpush_avg_cube_len: Average,

    pub qbad_num: usize,
    pub qbad_avg_time: AverageDuration,

    pub overall_mic_time: Duration,
    pub overall_block_time: Duration,
    pub overall_propagate_time: Duration,

    pub bucket_sum: f64,
    pub bucket_num: usize,
}

impl Statistic {
    pub fn new(mut case: &str, model: &Transys) -> Self {
        if let Some((_, c)) = case.rsplit_once('/') {
            case = c;
        }
        Self {
            num_input: model.inputs.len(),
            num_latch: model.latchs.len(),
            num_nodes: model.max_var.into(),
            case: Case::new(case),
            ..Default::default()
        }
    }
}

impl IC3 {
    pub fn statistic(&mut self) {
        self.obligations.statistic();
        self.frame.statistic();
        for solver in self.solvers.iter() {
            self.statistic.bucket_num += solver.solver.get_bucket_num();
            self.statistic.bucket_sum += solver.solver.get_bucket_sum();
        }
        println!("{:#?}", self.statistic);
    }
}
