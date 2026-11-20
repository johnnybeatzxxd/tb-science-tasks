import json
from fractions import Fraction as F
def law_json(d): return {'%d,%d'%k:str(v) for k,v in d.items() if v!=0}
def walk_json(s,wid): return {'id':wid,'interior':law_json(s['int']),'x_axis':law_json(s['x']),'y_axis':law_json(s['y']),'origin':law_json(s['o'])}
