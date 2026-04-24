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
pub struct LabelledTransitionSystem<Label> {
    /// Encodes the states and their outgoing transitions.
    states: Vec<usize>,
    transition_labels: Vec<LabelIndex>,
    transition_to: Vec<StateIndex>,

    /// Keeps track of the labels for every index, and which of them are hidden.
    labels: Vec<Label>,

    /// The index of the initial state.
    initial_state: StateIndex,
}

impl<Label> LabelledTransitionSystem<Label> {
    /// Creates a new labelled transition system with the given transitions,
    /// labels, and hidden labels.
    ///
    /// The initial state is the state with the given index. `num_of_states` is
    /// the number of states in the LTS, if known. If it is not known, pass
    /// `None`. However, in that case the number of states will be determined
    /// based on the maximum state index in the transitions. And all states that
    /// do not have any outgoing transitions will simply be created as deadlock
    /// states.
    pub fn new<I, F>(
        initial_state: StateIndex,
        num_of_states: Option<usize>,
        mut transition_iter: F,
        labels: Vec<Label>,
    ) -> LabelledTransitionSystem<Label>
    where
        F: FnMut() -> I,
        I: Iterator<Item = (StateIndex, LabelIndex, StateIndex)>,
    {
        let mut states = Vec::new();
        if let Some(num_of_states) = num_of_states {
            states.resize_with(num_of_states, Default::default);
        }

        // Count the number of transitions for every state
        let mut num_of_transitions = 0;
        for (from, _, to) in transition_iter() {
            // Ensure that the states vector is large enough.
            if states.len() <= from.max(to) {
                states.resize_with(from.max(to) + 1, || 0);
            }

            states[from] += 1;
            num_of_transitions += 1;

            if let Some(num_of_states) = num_of_states {
                debug_assert!(
                    from < num_of_states && to < num_of_states,
                    "State index out of bounds: from {:?}, to {:?}, num_of_states {}",
                    from,
                    to,
                    num_of_states
                );
            }
        }

        if initial_state >= states.len() {
            // Ensure that the initial state is a valid state (and all states before it exist).
            states.resize_with(initial_state + 1, Default::default);
        }

        // Track the number of transitions before every state.
        let mut count = 0;
        for start in &mut states {
            let next = count + *start;
            *start = count;
            count = next;
        }

        // Place the transitions, and increment the end for every state.
        let mut transition_labels = vec![0; num_of_transitions];
        let mut transition_to = vec![0; num_of_transitions];
        for (from, label, to) in transition_iter() {
            let idx = states[from];
            transition_labels[idx] = label;
            transition_to[idx] = to;
            states[from] += 1;
        }

        // Reset the offset.
        let mut previous = 0;
        for start in &mut states {
            let result = *start;
            *start = previous;
            previous = result;
        }

        // Add the sentinel state.
        states.push(transition_labels.len());

        LabelledTransitionSystem::from_raw_parts(
            initial_state,
            states,
            transition_labels,
            transition_to,
            labels,
        )
    }

    /// Constructs a LTS by a successor function for every state.
    pub fn with_successors<F, I>(
        initial_state: StateIndex,
        num_of_states: usize,
        labels: Vec<Label>,
        mut successors: F,
    ) -> Self
    where
        F: FnMut(StateIndex) -> I,
        I: Iterator<Item = (LabelIndex, StateIndex)>,
    {
        let mut states = Vec::new();
        states.resize_with(num_of_states, Default::default);

        let mut transition_labels = Vec::with_capacity(num_of_states);
        let mut transition_to = Vec::with_capacity(num_of_states);

        for state_index in 0..num_of_states {
            states[state_index] = transition_labels.len();

            for (label, to) in successors(state_index) {
                transition_labels.push(label);
                transition_to.push(to);
            }
        }

        // Add the sentinel state.
        states.push(transition_labels.len());

        Self::from_raw_parts(
            initial_state,
            states,
            transition_labels,
            transition_to,
            labels,
        )
    }

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
        let lts = LabelledTransitionSystem {
            initial_state,
            states,
            transition_labels,
            transition_to,
            labels,
        };
        lts.assert_valid();
        lts
    }

    /// Checks that the internal representation satisfies all structural invariants.
    pub fn assert_valid(&self) {
        let num_states = self.num_of_states();
        let num_transitions = self.num_of_transitions();

        debug_assert!(
            !self.states.is_empty(),
            "states array must have at least one entry (the sentinel)"
        );

        debug_assert!(
            self.initial_state < num_states,
            "initial_state {:?} is out of bounds (num_states: {})",
            self.initial_state,
            num_states
        );

        debug_assert_eq!(
            self.states[num_states],
            num_transitions,
            "sentinel value must equal the number of transitions"
        );

        debug_assert_eq!(
            self.transition_labels.len(),
            self.transition_to.len(),
            "transition_labels and transition_to must have equal length"
        );

        for i in 0..num_states {
            debug_assert!(
                self.states[i] <= self.states[i + 1],
                "state {i} has offset {} which is greater than successor offset {}",
                self.states[i],
                self.states[i + 1]
            );
        }

        for i in 0..num_transitions {
            let label = self.transition_labels[i];
            debug_assert!(
                label < self.labels.len(),
                "transition {i} references label index {} which is out of bounds (num_labels: {})",
                label,
                self.labels.len()
            );

            let to = self.transition_to[i];
            debug_assert!(
                to < num_states,
                "transition {i} references target state {} which is out of bounds (num_states: {})",
                to,
                num_states
            );
        }
    }

    fn initial_state_index(&self) -> StateIndex {
        self.initial_state
    }

    fn outgoing_transitions(
        &self,
        state_index: StateIndex,
    ) -> impl Iterator<Item = Transition> + '_ {
        let start = self.states[state_index];
        let end = self.states[state_index + 1];

        (start..end).map(move |i| Transition {
            label: self.transition_labels[i],
            to: self.transition_to[i],
        })
    }

    fn iter_states(&self) -> impl Iterator<Item = StateIndex> + '_ {
        0..self.num_of_states()
    }

    fn num_of_states(&self) -> usize {
        // Remove the sentinel state.
        self.states.len() - 1
    }

    fn num_of_labels(&self) -> usize {
        self.labels.len()
    }

    fn num_of_transitions(&self) -> usize {
        self.transition_labels.len()
    }

    fn labels(&self) -> &[Label] {
        &self.labels[0..]
    }

    fn is_hidden_label(&self, label_index: LabelIndex) -> bool {
        label_index == 0
    }
}