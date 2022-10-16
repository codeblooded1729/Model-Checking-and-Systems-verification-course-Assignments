from ply_parser import *

tree = parser.parse("G ((a ^ (X (F (X (tru U (G fls)))))) U ((F d) . (b + (! c))))")
print(str(tree.child.left.child.right.left.child))
