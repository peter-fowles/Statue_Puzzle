from moving_puzzle_objects import Movable, Player, Direction, Turn, GridObject
from enum import Enum

class Guardian(Movable):
    def __init__(self, pos, dir):
        super().__init__(pos, dir)

