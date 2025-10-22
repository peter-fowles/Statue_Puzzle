/* 
Models the guardian puzzle from The Legend of Zelda: Twilight Princess (https://youtu.be/eAhR_9qhY1M?t=24)
Rules:
    Let G be an immutable sequence of sequences of boolean values such that all rows have equal length and all true values have at least one adjacent true value.
        (forall i, j | 0 <= i < j < |G| :: |G[i]| == |G[j]|) all rows have equal length
        (forall i | 1 <= i < |G| - 1 :: (forall j | 0 <= j < |G[i]| :: G[i][j] && (G[i - 1][j] || G[i + 1][j])) all true values have adjacent true values in the next or previous rows
        TODO: show that all true values have a valid path to each other
    Let D be a tuple-pair of tiles in G, representing the two goal tiles
    Let P be an object located at some space P.pos in G.valid(), with initial direction P.direction.
    Let S1,S1 be a set of objects such that S1.pos in G.valid(), S2.pos in G.valid(), S1.pos != S2.pos != P.pos

    - during the turn step, give each object a destination tile
*/

datatype Heading = Left | Right | Up | Down // Objects face four distinct directions
datatype TurnDirection = Clockwise | Counterclockwise // Objects can only turn 90 degrees left or right
datatype ObjType = Statue | Player // Two distinct types of objects

// grid that the puzzle takes place on, where all true tiles are real, false tiles are void
const G: seq<seq<bool>> := [
    [ true,  true, false,  true,  true],
    [ true,  true,  true,  true,  true],
    [ true,  true,  true,  true,  true],
    [false,  true,  true,  true, false],
    [false,  true,  true,  true, false],
    [false, false,  true, false, false]
]

// set of target tiles structured in coordinates of [row, col]
const T := {[1, 1], [1, 3]}

// current state of an object in the puzzle
datatype ObjState = ObjState(pos: seq<int>, heading: Heading, t: ObjType, next_pos: seq<int>)

// current state of the whole puzzle
datatype PuzzleState = PuzzleState(player:ObjState, statues:seq<ObjState>)

predicate ValidObjState(s: ObjState)
{
    InBounds(s.pos) &&
    Live(s.pos) &&
    ValidNextPos(s.pos, s.next_pos, s.heading)
}

predicate InBounds(pos: seq<int>)
{
    |pos| == 2 &&
    0 <= pos[0] < |G| &&
    0 <= pos[1] < |G[pos[0]]|
}

predicate Live(pos: seq<int>)
{
    InBounds(pos) &&
    G[pos[0]][pos[1]]
}

predicate ValidNextPos(p: seq<int>, p': seq<int>, heading: Heading)
{
    Live(p) && Live(p') && // both positions are on valid tiles
    (match(heading) { // the next space either represents a jump...
        case Up => p'[0] == p[0] - 1 && p'[1] == p[1]
        case Down => p'[0] == p[0] + 1 && p'[1] == p[1]
        case Left => p'[0] == p[0] && p'[1] == p[1] - 1
        case Right => p'[0] == p[0] && p'[1] == p[1] + 1
    } || p' == p) // or it stays the same
}

predicate InitialPuzzleState(p: PuzzleState)
{
    ValidPuzzleState(p) && !SolvedPuzzleState(p) &&
    (exists i | i in p.statues :: i.pos == [5, 2] && i.heading == Up) && 
    (exists i | i in p.statues :: i.pos == [1, 2] && i.heading == Down) &&
    p.player.pos == [3, 2] && p.player.heading == Up
}

predicate ValidPuzzleState(p: PuzzleState)
{
    |p.statues| == 2 && // there are exactly 2 objects
    ValidObjState(p.player) && // player is in a valid state
    p.player.t == Player && // player is Player type
    (forall obj | obj in p.statues :: ValidObjState(obj) && obj.t == Statue) && // all statues are in valid states
    (forall i, j | i in p.statues && j in p.statues && i != j :: i.pos != j.pos && // all statues are in unique positions
        (p.player.pos != i.pos && p.player.pos != j.pos)) // player is in a unique position
}

predicate SolvedPuzzleState(p: PuzzleState)
{
    ValidPuzzleState(p) &&
    (forall i,j | i in p.statues && j in p.statues && i != j :: i.pos in T && j.pos in T)
}

predicate TurnObject(direction: TurnDirection, o: ObjState, o': ObjState)
    requires ValidObjState(o)
{
    o'.pos == o.pos && // statue positions remain the same
    match o.heading {
        case Up => 
            (direction == Clockwise && o'.heading == Right) ||
            (direction == Counterclockwise && o'.heading == Left)
        case Down => 
            (direction == Clockwise && o'.heading == Left) ||
            (direction == Counterclockwise && o'.heading == Right)
        case Left => 
            (direction == Clockwise && o'.heading == Up) ||
            (direction == Counterclockwise && o'.heading == Down)
        case Right => 
            (direction == Clockwise && o'.heading == Down) ||
            (direction == Counterclockwise && o'.heading == Up)
    } &&
    ValidNextPos(o'.pos, o'.next_pos, o'.heading) // o' has a next position consistent with its heading
}

// shows whether two objects will bump on the next jump
// two objects bump if they attempt to jump to the same destination or they are facing each other and adjacent.
predicate Bumping(o1: ObjState, o2: ObjState)
    requires ValidObjState(o1) && ValidObjState(o2)
{
    (o1.next_pos == o2.pos && o2.next_pos == o1.pos) // both objects have the other's current position as their next destination
    || SameDestination(o1, o2) // both objects will jump to the same tile
}

predicate Facing(o1: ObjState, o2: ObjState)
    requires ValidObjState(o1) && ValidObjState(o2)
{
    exists i, j | i in [o1, o2] && j in [o1, o2] && i != j ::
        (i.pos[0] < j.pos[0] && i.pos[1] == j.pos[1] && i.heading == Down && j.heading == Up) || // same column
        (i.pos[0] == j.pos[0] && i.pos[1] < j.pos[1] && i.heading == Right && j.heading == Left) // same row
}

predicate SameDestination(o1: ObjState, o2: ObjState)
    requires ValidObjState(o1) && ValidObjState(o2)
{
    o1.next_pos == o2.next_pos
}

predicate Adjacent(o1: ObjState, o2: ObjState)
    requires ValidObjState(o1) && ValidObjState(o2)
{
    (o1.pos[1] == o2.pos[1] && ((o2.pos[0] > 0 && o1.pos[0] == o2.pos[0] - 1) || o1.pos[0] == o2.pos[0] + 1)) || // adjacent by row
    (o1.pos[0] == o2.pos[0] && ((o2.pos[1] > 0 && o1.pos[1] == o2.pos[1] - 1) || o1.pos[1] == o2.pos[1] + 1)) // adjacent by column
}

// shows that some space on the grid is open to jump
predicate Open(s: seq<nat>, p: PuzzleState)
    requires |s| == 2
{
    s[0] < |G| && s[1] < |G[s[0]]| && // space is in the grid's bounds
    G[s[0]][s[1]] && // space is a live tile
    p.player.pos != s && // space is not occupied by the player
    (forall i | i in p.statues :: i.pos != s) // space is not occupied by a statue
}

// What is true after executing one jump forward?
predicate Move(p: PuzzleState, p': PuzzleState)
    requires ValidPuzzleState(p)
{
    |p.statues| == |p'.statues| && // p' doesn't add or remove statues
    p'.player.pos == p.player.next_pos && // p.player has a valid spot to go
        Open(p'.player.pos, p) && 
        p'.player.pos != p.player.pos &&
    (forall i:nat, j:nat | i < |p.statues| && j < |p.statues| && i != j :: 
        ((Bumping(p.statues[i], p.statues[j]) && // statues are bumping, which causes them to be in the same position on the next state
            p'.statues[i] == p.statues[i] && p'.statues[j] == p.statues[j]) ||
        (!Bumping(p.statues[i], p.statues[j]) && p'.statues[i].pos == p.statues[i].next_pos && // statues are not bumping, so they move to their next positions
            p'.statues[j].pos == p.statues[j].next_pos)) && 
        (p'.player.pos != p'.statues[i].pos && p'.player.pos != p'.statues[j].pos)) // p' does not crush the player under a statue
}

predicate Turn(direction: TurnDirection, p: PuzzleState, p': PuzzleState) 
    requires ValidPuzzleState(p)
{
    |p.statues| == |p'.statues| && // number of statues matches
    TurnObject(direction, p.player, p'.player) && // p'.player shows a valid turn from p.player
    (forall i:nat | i < |p.statues| :: TurnObject(direction, p.statues[i], p'.statues[i])) // all statues in p' turn correctly from p
}

lemma Invariance (p: PuzzleState, p': PuzzleState)
    ensures InitialPuzzleState(p) ==> ValidPuzzleState(p)
    ensures ValidPuzzleState(p) && Move(p, p') ==> ValidPuzzleState(p')
    ensures ValidPuzzleState(p) && Turn(Clockwise, p, p') ==> ValidPuzzleState(p')
    ensures ValidPuzzleState(p) && Turn(Counterclockwise, p, p') ==> ValidPuzzleState(p')
    

// TODO: Prove that there is some sequence of turns and moves that lead to the solved state
// Add a condition to the IsValidPuzzleState predicate that shows the inductive steps from the initial state, and the inductive steps to a final state.
// Then, all valid states are part of some path from the initial state to a final state.
// Do I even need direction as one of the arguments?

method SanityCheck(p: PuzzleState) returns (solved: PuzzleState)
    requires InitialPuzzleState(p)
    //ensures SolvedPuzzleState(solved)
{
    solved := p;
    // TODO: Fix all errors here, and you have successfully done it!
    var p':PuzzleState;
    
    p' :| Turn(Counterclockwise, p, p');
    solved := p';
    // p' :| Move(solved, p');
    // solved := p';
    // p' :| Turn(Counterclockwise, p, p');
    // solved := p';
    // p' :| Move(solved, p');
    // solved := p';
    // p' :| Turn(Counterclockwise, p, p');
    // solved := p';
    // p' :| Move(solved, p');
    // solved := p';
    // p' :| Move(solved, p');
    // solved := p';
    // p' :| Turn(Counterclockwise, p, p');
    // solved := p';
    // p' :| Move(solved, p');
    // solved := p';
    // p' :| Turn(Counterclockwise, p, p');
    // solved := p';
    // p' :| Move(solved, p');
    // solved := p';
    // p' :| Turn(Clockwise, p, p');
    // solved := p';
    // p' :| Move(solved, p');
    // solved := p';
    // p' :| Move(solved, p');
    // solved := p';
    // p' :| Turn(Counterclockwise, p, p');
    // solved := p';
    // p' :| Move(solved, p');
    // solved := p';
    // p' :| Turn(Counterclockwise, p, p');
    // solved := p';
    // p' :| Move(solved, p');
    // solved := p';
    // p' :| Move(solved, p');
    // solved := p';
    // p' :| Turn(Counterclockwise, p, p');
    // solved := p';
    // p' :| Move(solved, p');
    // solved := p';
    // p' :| Turn(Counterclockwise, p, p');
    // solved := p';
    // p' :| Move(solved, p');
    // solved := p';
}