#![forbid(unsafe_code)]

use std::collections::HashMap;

type StateIndex = usize;
type LabelIndex = usize;

/// Represents a transition in the LTS originating from some known state.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct Transition {
    pub label: LabelIndex,
    pub to: StateIndex,
}

impl Transition {
    /// Constructs a new transition.
    pub fn new(label: LabelIndex, to: StateIndex) -> Self {
        Self { label, to }
    }
}

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
    transitions: HashMap<LabelIndex, Vec<Transition>>,

    /// Keeps track of the labels for every index, and which of them are hidden.
    labels: Vec<Label>,

    /// The index of the initial state.
    initial_state: StateIndex,
}

impl<Label> SimpleLabelledTransitionSystem<Label> {
    pub fn outgoing_transitions(&self, state_index: StateIndex) -> Vec<Transition> {
        self.transitions
           .get(&state_index)
           .expect("State index out of bounds.")
           .clone()
    }

    pub fn initial_state_index(&self) -> StateIndex {
        self.initial_state
    }

    pub fn iter_states(&self) -> impl Iterator<Item = StateIndex> + '_ {
        0..self.num_of_states()
    }

    pub fn num_of_states(&self) -> usize {
        self.transitions.len()
    }

    pub fn num_of_labels(&self) -> usize {
        self.labels.len()
    }

    pub fn num_of_transitions(&self) -> usize {
        self.transitions.values().map(|v| v.len()).sum()
    }

    pub fn labels(&self) -> &[Label] {
        &self.labels[0..]
    }

    pub fn is_hidden_label(&self, label_index: LabelIndex) -> bool {
        label_index == 0
    }
}