#![forbid(unsafe_code)]

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
    states: Vec<usize>,
    transition_labels: Vec<LabelIndex>,
    transition_to: Vec<StateIndex>,

    /// Keeps track of the labels for every index, and which of them are hidden.
    labels: Vec<Label>,

    /// The index of the initial state.
    initial_state: StateIndex,
}

impl<Label> SimpleLabelledTransitionSystem<Label> {
    /// Creates a labelled transition system from another one, given the permutation of state indices.
    ///
    /// The permutation maps old state indices to new state indices, i.e.,
    /// `permutation(old) = new`. The transition arrays are rebuilt so that
    /// transitions are contiguous per new state index, and all transition
    /// targets are updated to reference the new state indices.
    pub fn new_from_permutation<P>(lts: Self, permutation: P) -> Self
    where
        P: Fn(StateIndex) -> StateIndex + Copy,
    {
        // Build the inverse permutation: inverse[new_index] = old_index
        let mut inverse = vec![0; lts.num_of_states()];
        for state_index in lts.iter_states() {
            inverse[permutation(state_index)] = state_index;
        }

        // Rebuild transition arrays in the order of the new state indices.
        let mut states = Vec::new();
        let mut transition_labels = Vec::new();
        let mut transition_to = Vec::new();

        for &old_index in &inverse {
            states.push(transition_labels.len());

            let start = lts.states[old_index];
            let end = lts.states[old_index + 1];

            for i in start..end {
                transition_labels.push(lts.transition_labels[i]);
                transition_to.push(permutation(lts.transition_to[i]));
            }
        }

        // Add the sentinel state.
        states.push(transition_labels.len());

        Self::from_raw_parts(
            permutation(lts.initial_state),
            states,
            transition_labels,
            transition_to,
            lts.labels,
        )
    }

    /// Constructs a [LabelledTransitionSystem] directly from its raw internal arrays.
    ///
    /// The `states` array must contain one entry per state holding the start offset of that
    /// state's transitions in the transition arrays, plus a sentinel entry at the end equal
    /// to the total number of transitions. `transition_labels` and `transition_to` must have
    /// equal length and all indices they contain must be in bounds.
    ///
    /// # Panics
    ///
    /// Panics (in debug mode) if the invariants of the internal representation are violated.
    pub fn from_raw_parts(
        initial_state: StateIndex,
        states: Vec<usize>,
        transition_labels: Vec<LabelIndex>,
        transition_to: Vec<StateIndex>,
        labels: Vec<Label>,
    ) -> Self {
        let lts = SimpleLabelledTransitionSystem {
            initial_state,
            states,
            transition_labels,
            transition_to,
            labels,
        };
        lts
    }

    pub fn initial_state_index(&self) -> StateIndex {
        self.initial_state
    }

    pub fn iter_states(&self) -> impl Iterator<Item = StateIndex> + '_ {
        0..self.num_of_states()
    }

    pub fn num_of_states(&self) -> usize {
        // Remove the sentinel state.
        self.states.len() - 1
    }

    pub fn num_of_labels(&self) -> usize {
        self.labels.len()
    }

    pub fn num_of_transitions(&self) -> usize {
        self.transition_labels.len()
    }

    pub fn labels(&self) -> &[Label] {
        &self.labels[0..]
    }

    pub fn is_hidden_label(&self, label_index: LabelIndex) -> bool {
        label_index == 0
    }
}