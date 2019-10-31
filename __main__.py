from argparse import ArgumentParser
from collections import deque
from dataclasses import dataclass
from io import StringIO
from itertools import accumulate
from queue import heappop, heappush
import random
from time import process_time
from typing import List, Text, Tuple

from PIL import Image

pmap = {
    0: "●",
    1: "╸",
    2: "╹",
    3: "┛",
    4: "╺",
    5: "━",
    6: "┗",
    7: "┻",
    8: "╻",
    9: "┓",
    10: "┃",
    11: "┫",
    12: "┏",
    13: "┳",
    14: "┣",
    15: "╋",
}


@dataclass
class Maze:
    maze: List[int]
    width: int
    height: int

    def __str__(self):
        dat = self.maze
        width = self.width
        height = self.height
        i = 0
        s = StringIO()
        for y in range(height):
            for x in range(width):
                print(pmap[dat[i]], end="", file=s)
                i += 1
            print(file=s)
        return s.getvalue()


INF = 2 ** 62


def gen_maze(
    width: int,
    height: int,
    branch_dist: Tuple[float, float, float, float],
    min_length: int,
    seed: int,
) -> Maze:

    random.seed(seed)

    # throughout we use a 1D list instead of a 2D list for _significant_ performance gains

    # precompute some values
    cumulative_brach_dist = list(accumulate(branch_dist))
    cell_count = width * height
    last_x = width - 1
    last_y = height - 1

    # define some ultility functions
    t = lambda x, y: width * y + x  # transform coords to index
    in_bounds = lambda x, y: 0 <= x < width and 0 <= y < height
    is_border = lambda x, y: x == 0 or y == 0 or x == last_x or y == last_y
    c_l = lambda x, y: (x - 1, y)  # cell to left
    c_r = lambda x, y: (x + 1, y)  # cell to top
    c_t = lambda x, y: (x, y - 1)  # cell to right
    c_b = lambda x, y: (x, y + 1)  # cell to bottom

    ### initialize state

    cells_visited = 0

    # for each cell, this is the number of cells adjacent to it that havent been proccessed
    cell_remaining_sides = [4] * cell_count
    for x in range(width):
        cell_remaining_sides[t(x, 0)] = 3
        cell_remaining_sides[t(x, height - 1)] = 3
    for y in range(height):
        cell_remaining_sides[t(0, y)] = 3
        cell_remaining_sides[t(width - 1, y)] = 3
    cell_remaining_sides[t(0, 0)] = 2
    cell_remaining_sides[t(width - 1, 0)] = 2
    cell_remaining_sides[t(0, height - 1)] = 2
    cell_remaining_sides[t(width - 1, height - 1)] = 2

    # distance from start to particular cell
    cell_distance = [INF] * cell_count

    # which walls around a cell are broken, its a bit mask; 0b0001: left, 0b0010: top, 0b0100: right, 0b1000: bottom
    cell_state = [0] * cell_count

    is_visited = lambda x, y: cell_distance[t(x, y)] != INF

    # contains a heap (priority queue) where the farthest cells from the start are at the front
    # used to get a cell to restart maze growth when all cells hit dead ends
    cell_by_distance = []

    def fallback_cell():
        while cell_by_distance:
            if (
                remaining_sides := cell_remaining_sides[
                    t(*(cell := cell_by_distance[0][1]))
                ]
            ) > 1:
                # cell still valid as a seed point for growth after this use
                return cell
            elif remaining_sides == 1:
                # cell not valid as a seed point for growth after this use (the one remaining side will be used)
                heappop(cell_by_distance)
                return cell
            else:
                # cell not valid as a seed point now, go to next
                heappop(cell_by_distance)

    def set_visited(x, y, d):
        nonlocal cells_visited
        cells_visited += 1
        cell_distance[t(x, y)] = d
        heappush(cell_by_distance, (-d, (x, y)))
        if in_bounds(*c_l(x, y)):
            cell_remaining_sides[t(*c_l(x, y))] -= 1
        if in_bounds(*c_r(x, y)):
            cell_remaining_sides[t(*c_r(x, y))] -= 1
        if in_bounds(*c_t(x, y)):
            cell_remaining_sides[t(*c_t(x, y))] -= 1
        if in_bounds(*c_b(x, y)):
            cell_remaining_sides[t(*c_b(x, y))] -= 1

    def open_left(x, y):
        cell_state[t(x, y)] |= 0b0001

    def open_top(x, y):
        cell_state[t(x, y)] |= 0b0010

    def open_right(x, y):
        cell_state[t(x, y)] |= 0b0100

    def open_bottom(x, y):
        cell_state[t(x, y)] |= 0b1000

    def connect(x1, y1, x2, y2):
        if x1 < x2:
            open_right(x1, y1)
            open_left(x2, y2)
        elif x2 < x1:
            open_left(x1, y1)
            open_right(x2, y2)
        elif y1 < y2:
            open_bottom(x1, y1)
            open_top(x2, y2)
        elif y2 < y1:
            open_top(x1, y1)
            open_bottom(x2, y2)

    q = deque()

    def q_up(cell: Tuple[int, int], d: int):
        q.append(cell)
        set_visited(*cell, d)

    # pick starting cell
    if random.choice([True, False]):
        x = random.randint(0, width)
        if random.choice([True, False]):
            start = (x, 0)
            open_top(*start)
        else:
            start = (x, height - 1)
            open_bottom(*start)
    else:
        y = random.randint(1, height - 1)
        if random.choice([True, False]):
            start = (0, y)
            open_left(*start)
        else:
            start = (width - 1, y)
            open_right(*start)

    q_up(start, 0)

    while cells_visited < cell_count:
        can_terminate = True
        if not q:
            # we are restarting growth here, do not allow it to fail this iteration
            can_terminate = False
            q.append(fallback_cell())

        cc = q.popleft()
        d = cell_distance[t(*cc)]
        possible_branches = []
        if in_bounds(*(n := c_l(*cc))) and not is_visited(*n):
            possible_branches.append(n)
        if in_bounds(*(n := c_r(*cc))) and not is_visited(*n):
            possible_branches.append(n)
        if in_bounds(*(n := c_t(*cc))) and not is_visited(*n):
            possible_branches.append(n)
        if in_bounds(*(n := c_b(*cc))) and not is_visited(*n):
            possible_branches.append(n)

        branch_count = random.choices(
            list(range(len(possible_branches) + 1)),
            cum_weights=cumulative_brach_dist[: len(possible_branches) + 1],
        )[0]
        if not can_terminate and branch_count == 0:
            branch_count = 1
        selection = random.sample(possible_branches, k=branch_count)
        for n in selection:
            connect(*cc, *n)
            q_up(n, d + 1)

    # punch out the exit, select a random border cell that is at lease `min_exit_distance` away from the start
    min_exit_distance = min_length if min_length > 0 else min(width, height)
    try:
        last_border_cell = random.choice(
            [
                (x, y)
                for x in range(width)
                for y in range(height)
                if is_border(x, y) and cell_distance[t(x, y)] > min_exit_distance
            ]
        )
    except IndexError:
        print("Could not find a path with min distance specified")
        exit()

    if last_border_cell[0] == 0:
        open_left(*last_border_cell)
    elif last_border_cell[1] == 0:
        open_top(*last_border_cell)
    elif last_border_cell[0] == last_x:
        open_right(*last_border_cell)
    elif last_border_cell[1] == last_y:
        open_bottom(*last_border_cell)

    return Maze(maze=cell_state, width=width, height=height)


def draw_maze(maze: Maze, filename: Text, tilesize: int = 8):
    bitmaps = {}
    for i in range(1, 16):
        bitmaps[i] = Image.open(f"{i}.png")
    out_im = Image.new("RGB", (maze.width * tilesize, maze.height * tilesize))
    i = 0
    for y in range(maze.height):
        for x in range(maze.width):
            out_im.paste(bitmaps[maze.maze[i]], (x * tilesize, y * tilesize))
            i += 1
    out_im.save(filename)


parser = ArgumentParser(
    description="Make a maze.\n\nLoads time images from [1-15].png (assumes images are tilesize x tilesize)"
)
parser.add_argument("width", type=int, help="Maze width (cell width * tile width)")
parser.add_argument("height", type=int, help="Maze height (cell height * tile width)")
parser.add_argument("filename", help="The file to write the maze to")
parser.add_argument(
    "--branch-factors",
    type=float,
    nargs=4,
    default=(0.3, 0.45, 0.2, 0.05),
    help="The relative frequency that a cell will branch 0, 1, 2, or 3 times respectively",
)
parser.add_argument(
    "--min-length",
    type=int,
    default=-1,
    help="The minimum length of the path to the end",
)
parser.add_argument(
    "--tilesize", type=int, default=8, help="The assumed width of the maze cell bitmaps"
)
parser.add_argument(
    "--seed",
    type=int,
    default=None,
    help="The seed used for maze randomness, random seed by default",
)

args = parser.parse_args()

print(f"{args.width=}")
print(f"{args.height=}")
print(f"{args.branch_factors=}")
print(f"{args.filename=}")
print(f"{args.tilesize=}")
print(f"{args.min_length=}")
print(f"{args.seed=}")


t = process_time()
# maze = gen_maze(width, height, (0.2, 0.4, 0.3, 0.1))
maze = gen_maze(
    args.width, args.height, args.branch_factors, args.min_length, args.seed
)
draw_maze(maze, args.filename, args.tilesize)
print(f"done in {process_time() - t}s")
