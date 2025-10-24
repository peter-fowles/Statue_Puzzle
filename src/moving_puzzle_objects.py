from enum import Enum

class Direction(Enum):
    UP = (0, -1)
    DOWN = (0, 1)
    LEFT = (-1, 0)
    RIGHT = (1, 0)

class Turn(Enum):
    RIGHT = lambda dir: (-dir[1], -dir[0])
    LEFT = lambda dir: (dir[1], dir[0])

    def __init__(self, get_new_dir):
        super().__init__()
        self.get_new_dir = get_new_dir

class Movable:
    def __init__(self, pos: tuple[int, int], dir: Direction):
        '''
        Constructs a movable puzzle object

        pos: A 2-tuple containing the object's initial coordinates on a grid (x, y)
        dir: Initial direction the object is facing
        '''
        # Initial State
        self.__start_pos = pos
        self.__start_dir = dir

        # Current State
        self.__pos = pos
        self.__dir = dir

    def turn(self, turn: Turn):
        self.__dir = turn.get_new_dir(self.__dir)

    def move(self, grid: list[list['Movable']]):
        new_coords = [self.__pos[i] + self.__dir.value[i] for i in range(2)]
        if 0 <= new_coords[1] < len(grid) and 0 <= new_coords[0] < len(grid[new_coords[1]]):
            self.__pos = new_coords

    def reset(self):
        self.__pos = self.__start_pos
        self.__dir = self.__start_dir

class Player(Movable):
    def __init__(self, pos, dir):
        super().__init__(pos, dir)

class GridObject(Enum):
    PLAYER: Player
    WALL: None
