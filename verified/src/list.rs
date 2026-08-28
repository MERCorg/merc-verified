
/// The actual list.
pub struct List<T> {
    head: Link<T>,
}

/// The link between nodes in the list.
enum Link<T> {
    Empty,
    More(Box<Node<T>>),
}

/// A node in the list.
struct Node<T> {
    elem: T,
    next: Link<T>,
}