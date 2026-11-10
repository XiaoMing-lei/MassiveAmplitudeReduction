"""Minimal tensor overlaps retaining both embeddings before normalization.

No catalog matching is performed here. Original indexed identities are
substituted at their recorded slots. Derived physical identities are attached
by summing free-slot assignments, as required by physical symmetrization.
"""
from collections import defaultdict
from itertools import permutations, product
import construct_degree_queue as q

b,bp,p,base=q.b,q.bp,q.p,q.base


def unions_with_maps(left,right):
    al,ab,ae=left;bl,bb,be=right
    options=[[j for j,(a,z,cc) in enumerate(ab)
              if c==cc and sorted((bl[x],bl[y]))==sorted((al[a],al[z]))]
             for x,y,c in bb]
    mapping={};used=set();choices=[]
    def visit(k,shared):
        if k==len(bb):
            ll=list(al);brackets=list(ab);sub=dict(mapping);right_edges=[]
            for i,(x,y,c) in enumerate(bb):
                if choices[i] is not None:
                    right_edges.append(choices[i]);continue
                sub[x]=len(ll);ll.append(bl[x]);sub[y]=len(ll);ll.append(bl[y])
                right_edges.append(len(brackets));brackets.append((sub[x],sub[y],c))
            eps=list(ae);occupied={a:z for a,z in eps}|{z:a for a,z in eps}
            for x,y in be:
                a,z=sub[x],sub[y]
                if a==z or (a in occupied and occupied[a]!=z) or (z in occupied and occupied[z]!=a):return
                if a not in occupied:eps.append((a,z));occupied[a]=z;occupied[z]=a
            yield ((tuple(ll),tuple(brackets),tuple(eps)),shared,
                   (tuple(range(len(ab))),dict(enumerate(range(len(al))))),
                   (tuple(right_edges),sub))
            return
        x,y,c=bb[k]
        for j in options[k]:
            if j in used:continue
            a,z,_=ab[j]
            if al[a]!=bl[x]:a,z=z,a
            mapping[x],mapping[y]=a,z
            used.add(j);choices.append(j)
            yield from visit(k+1,shared+1)
            choices.pop();used.remove(j);del mapping[x];del mapping[y]
        choices.append(None);yield from visit(k+1,shared);choices.pop()
    yield from visit(0,0)


def marked_key(graph,mapping=None):
    """Exact graph-renaming key, preserving orientations and source-slot marks.

    Every vertex has one bracket and at most one epsilon edge. Components
    are paths/cycles; enumerating their two directions (and cyclic starts)
    removes dummy vertex names before any identity substitution.
    """
    ll,bb,ee=graph;roles={v:i for i,v in (mapping or {}).items()}
    edges=[(a,z,('b',c)) for a,z,c in bb]+[(a,z,('e',)) for a,z in ee]
    adj=defaultdict(list)
    for i,(a,z,kind) in enumerate(edges):adj[a].append(i);adj[z].append(i)
    remaining=set(range(len(ll)));components=[]
    while remaining:
        todo=[min(remaining)];vertices=set()
        while todo:
            v=todo.pop()
            if v in vertices:continue
            vertices.add(v)
            for ei in adj[v]:
                a,z,_=edges[ei];todo.append(z if a==v else a)
        remaining-=vertices
        starts=[v for v in vertices if len(adj[v])<=1] or sorted(vertices)
        encodings=[]
        for start in starts:
            for first in adj[start] or [None]:
                nodes=[];links=[];v=start;previous=None;chosen=first
                while True:
                    nodes.append((ll[v],roles.get(v,-1)))
                    choices=[e for e in adj[v] if e!=previous]
                    if previous is None:
                        ei=chosen
                    else:ei=choices[0] if choices else None
                    if ei is None:break
                    a,z,kind=edges[ei];w=z if v==a else a
                    links.append((kind,1 if v==a else -1))
                    if w==start:break
                    previous=ei;v=w
                encodings.append((tuple(nodes),tuple(links)))
        components.append(min(encodings))
    return tuple(sorted(components))


def overlap_frames(left,right):
    seen=set()
    for graph,shared,a,z in unions_with_maps(left,right):
        ll,bb,ee=graph
        for extra in base.matchings(ll,bb,ee):
            if not shared and not extra:continue
            whole=(ll,bb,ee+extra)
            key=(marked_key(whole,a[1]),marked_key(whole,z[1]))
            if key in seen:continue
            seen.add(key)
            yield whole,shared,a,z,extra,key


def attach_original(parent,pattern,graph,selected,mapping):
    ll,bb,ee=graph
    internal={frozenset((mapping[a],mapping[z])) for a,z in pattern[2]}
    context_eps=tuple(e for e in ee if frozenset(e) not in internal)
    rest=tuple(edge for i,edge in enumerate(bb) if i not in selected)
    result={}
    for sign,tl,tb,te in parent['raw']:
        labels=list(ll)
        for i,v in mapping.items():labels[v]=tl[i]
        brackets=rest+tuple((mapping[a],mapping[z],c) for a,z,c in tb)
        eps=context_eps+tuple((mapping[a],mapping[z]) for a,z in te)
        for mon,co in b.normalize_graph(tuple(labels),brackets,eps).items():
            b.add_term(result,mon,{e:sign*v for e,v in co.items()})
    return result


def attach_physical(row,pattern,graph,selected,mapping):
    """The reference embed_physical formula on the unnormalized common graph."""
    ll,bb,ee=graph
    internal={frozenset((mapping[a],mapping[z])) for a,z in pattern[2]}
    rest=tuple(e for i,e in enumerate(bb) if i not in selected)
    selected_ports={v for i in selected for v in bb[i][:2]}
    context_eps=tuple(e for e in ee if frozenset(e) not in internal)
    if any(a in selected_ports and z in selected_ports for a,z in context_eps):return {}
    groups=defaultdict(list)
    for v in sorted({v for e in context_eps for v in e if v in selected_ports}):groups[ll[v]].append(v)
    external=sorted({v for e in rest for v in e[:2]});ext_map={v:i for i,v in enumerate(external)}
    ext_labels=tuple(ll[v] for v in external)
    ext_brackets=tuple((ext_map[a],ext_map[z],c) for a,z,c in rest)
    off=len(external);labels=sorted(groups);result={}
    for mon,coeff in row.items():
        tl,tb,te=b.graph(mon);used={v for e in te for v in e};free=defaultdict(list)
        for v,label in enumerate(tl):
            if v not in used:free[label].append(v)
        for assignments in product(*(permutations(free[label],len(groups[label])) for label in labels)):
            sub=dict(ext_map)
            for label,assignment in zip(labels,assignments):sub.update(zip(groups[label],(off+v for v in assignment)))
            eps=tuple((off+a,off+z) for a,z in te)+tuple((sub[a],sub[z]) for a,z in context_eps)
            br=ext_brackets+tuple((off+a,off+z,c) for a,z,c in tb)
            for m,co in b.normalize_graph(ext_labels+tl,br,eps).items():b.add_term(result,m,b.pmul(coeff,co))
    return result


def attach(parent,pattern,graph,selected,mapping):
    row=(attach_original(parent,pattern,graph,selected,mapping) if parent['raw'] is not None
         else attach_physical(parent['row'],pattern,graph,selected,mapping))
    # Remove coefficient content only. The pool key retains the entire common
    # tensor monomial; disconnected factors are removed later from S's.
    return b.primitive(row)[0]
