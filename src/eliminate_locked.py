
def EliminateLocked(state):
    """If there is only one possibility for state.n, lock that it.

    Returns the lowest n where that possibility appears, so we can redo
    work from there knowing that.
    """

    if len(state.all_factorizations[-1]) == 1:
        state.locked[tuple(state.all_factorizations[-1][0])] = state.n
        if len(state.all_factorizations.reverse_idx[tuple(state.all_factorizations[-1][0])]) > 1:
            return state.all_factorizations.reverse_idx[tuple(state.all_factorizations[-1][0])][0]-2
    return state.n-2
