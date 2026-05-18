#![forbid(unsafe_code)]

use std::collections::HashMap;

use merc_lts::LTS;
use merc_lts::LabelIndex;
use merc_lts::StateIndex;
use merc_lts::Transition;
use merc_lts::TransitionLabel;

/// Represents a labelled transition system consisting of states with directed
/// labelled transitions between them.
///
/// # Details
///
/// Uses byte compressed vectors to store the states and their outgoing
/// transitions efficiently in memory.
#[derive(PartialEq, Eq, Clone)]
pub struct SimpleLabelledTransitionSystem<Label> {
    /// Encodes the states and their outgoing transitions.
    transitions: HashMap<StateIndex, Vec<Transition>>,

    /// Keeps track of the labels for every index, and which of them are hidden.
    labels: Vec<Label>,

    /// The index of the initial state.
    initial_state: StateIndex,
}

impl<Label: TransitionLabel> LTS for SimpleLabelledTransitionSystem<Label> {
    type Label = Label;

    fn outgoing_transitions(&self, state_index: StateIndex) -> Vec<Transition> {
        self.transitions
            .get(&state_index)
            .expect("State index out of bounds.")
            .clone()
    }

    fn initial_state_index(&self) -> StateIndex {
        self.initial_state
    }

    fn iter_states(&self) -> Vec<StateIndex> {
        let n = self.num_of_states();
        let mut result = Vec::with_capacity(n);
        let mut i = 0;
        while i < n {
            result.push(StateIndex::new(i));
            i += 1;
        }
        result
    }

    fn num_of_states(&self) -> usize {
        self.transitions.len()
    }

    fn num_of_labels(&self) -> usize {
        self.labels.len()
    }

    fn num_of_transitions(&self) -> usize {
        let mut total = 0usize;
        for v in self.transitions.values() {
            total += v.len();
        }
        total
    }

    fn labels(&self) -> &[Label] {
        &self.labels[0..]
    }

    fn is_hidden_label(&self, label_index: LabelIndex) -> bool {
        label_index == 0
    }
}
