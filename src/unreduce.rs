#![allow(unused)] // tests dont seem to count

use std::{borrow::BorrowMut, vec};

use itertools::Itertools;
use smallvec::{smallvec,SmallVec};

use crate::{adj_matrix::{GraphAdjMatrix, Permutation, Vertex, VertexVec}, planarity::{self, is_planar}};

mod perm_iter {
  use dyn_clonable::{clonable, dyn_clone::DynClone};
  use super::Permutation;
  
  pub trait DynBox {
      type Item;
      type Output: Iterator<Item=Self::Item> + Clone;
      fn dyn_box(self)-> Self::Output;
  }
  impl<T> DynBox for T where T: Iterator<Item = Permutation> + Clone + 'static {
      type Item = Permutation;
      type Output = PermIter;
      fn dyn_box(self)-> PermIter { PermIter(Box::new(self)) }
  }
  #[derive(Clone)]
  pub struct PermIter(Box<dyn PermutationIteratorClonable>);
  impl Iterator for PermIter {
      type Item = Permutation;
      fn next(&mut self) -> Option<Permutation> {
          self.0.next()
      }
  }

  #[clonable]
  trait PermutationIteratorClonable: Iterator<Item = Permutation> + Clone {}
  impl<T> PermutationIteratorClonable for T where T: Iterator<Item = Permutation> + Clone {}
  
}

#[derive(Debug, PartialEq, Eq)]
struct CanonGraph{ g: GraphAdjMatrix, autos: Vec<Permutation>}

#[derive(PartialEq, PartialOrd, Eq, Ord, Debug)]
struct SquareReduction {remove:Vertex, add: (Vertex, Vertex)}
impl SquareReduction {
  // and normalize
  fn new(remove: Vertex, add: (Vertex, Vertex)) -> Self {
    Self{remove, add: (if add.0 < add.1 { add } else {(add.1, add.0)})}
  }
  fn apply(&self,permutation: &Permutation) -> Self {
    let [rm,add0,add1] = permutation.apply_n([self.remove, self.add.0, self.add.1]);
    Self::new(rm, (add0,add1))
  }
}

//add is (x,y,z) representing edges (x,y) (y,z), normalize by x < z
#[derive(PartialEq, PartialOrd, Eq, Ord, Debug)]
struct PentaReduction {remove:Vertex, add: (Vertex, Vertex, Vertex)}
impl PentaReduction {
  // and normalize
  fn new(remove: Vertex, add: (Vertex, Vertex, Vertex)) -> Self {
    Self{remove, add: (if add.0 < add.2 { add } else {(add.2, add.1, add.0)})}
  }
  fn apply(&self,permutation: &Permutation) -> Self {
    let [rm,add0,add1,add2] = permutation.apply_n(
      [self.remove, self.add.0, self.add.1, self.add.2]);
    Self::new(rm, (add0,add1,add2))
  }
}



  
impl CanonGraph {
  pub fn slow_auto_canon(graph: &GraphAdjMatrix) -> Self {
    Self::slow_auto_cannon_with_permutation(graph).0
  }
  pub fn slow_auto_cannon_with_permutation(graph: &GraphAdjMatrix) -> (Self, Permutation) {
    use perm_iter::{DynBox};
    let vs_by_degree: Vec<Vertex> = graph.vertices().sorted_by_key(|&v|graph.degree_of(v)).collect();
    let mut degree_permutation = Permutation::default();
    
    for (u, v) in graph.vertices().zip(vs_by_degree) {
      degree_permutation.use_vertex(u);
      degree_permutation.0[v as usize] = u;
    }
    let degree_canon = graph.apply_permutation(&degree_permutation); 
    let grouped_vs = degree_canon.vertices().group_by(|&v|degree_canon.degree_of(v));
    let group_perms = grouped_vs.into_iter().map(|(_, grp)| { // -> impl Iterator<Item = Permutation> + Clone
        Permutation::iterate_set(grp.collect()).dyn_box()
    });
    let all_perms  = group_perms.reduce(
        |ps,qs| ps.cartesian_product(qs).map(|(p,q)| p.compose(&q)).dyn_box()
    ).expect("Expected at least 1 vertex");
    //dbg!(all_perms.collect::<Vec<_>>());
    
    //let min_self = all_perms.map(|p|GraphSize(self.apply_permutation(p))).min()
    let mut perms_into_min = vec![];
    let mut min_self = degree_canon.clone();
    for perm in all_perms {
      let candidate = degree_canon.apply_permutation(&perm);
      candidate.partial_cmp(&min_self).expect("Vertex list");
      if candidate < min_self {
        min_self = candidate;
        perms_into_min = vec![perm];
      }
      else if candidate == min_self { perms_into_min.push(perm)}
    }
    let into_min = degree_permutation.compose(&perms_into_min[0]);
    let min_autos = perms_into_min.iter().map(|a|perms_into_min[0].inverse().compose(a)).collect();
    (Self{g: min_self, autos:min_autos}, into_min)
}



  fn all_different_triangles(&self) -> Vec<[Vertex; 3]> {
    // find each triangle up to automorphism exactly once
    // - do not repeat a triangle 1,2,3 as 1,3,2
    // - do not repeat a triangle 1,2,3 as automorphic 1',2',3'
    // by in each case preferring the lexicographically minimum description
    let mut out = vec![];
    for v in self.g.vertices() {
      let neighbors: VertexVec = self.g.neighbors(v).collect();
      for (i,&n1) in neighbors.iter().enumerate() {
        if n1 < v {
          for &n2 in &neighbors[..i] {
            if self.g.has_edge(n1, n2) {
              let triangle = [n2,n1,v];
              if self.autos.iter().all(|a|triangle <= a.apply_n(triangle)) {
                out.push([n2,n1,v])
              }
            }
          }
        }
      }
    }
    out
  }

/*
to enumerate a class of graphs C: 
for every graph in C, define a single canonical reduction which decreases towards
a small set of generators. run the reductions in reverse, and keep only those which were
canonical

to enumerate plane triangulations, reduce a vertex of degree 3, 4, or 5; to 1,2 or 3 triangles, 
with a generator of K_4. 
canonical reduction: r3 > r4 > r5
given rn, order first by sorted neighbor degree sequence, then by canonical label

functions to write: 
1) given a graph, unreduce by adding degree 3 vertices
2) '' deg 4
3) '' deg 5
4) fn which given an iterator of size n triangulations returns an iterator of size n+1 triangulations
*/
  fn canon_3(&self) -> Option<([usize; 3], Vertex)> {
    self.g.vertices().filter_map(|v| {
      //v needs 3 neighbors
      let (a,b,c) = self.g.neighbors(v).collect_tuple()?;
      //abc need to be friends 
      if self.g.has_edges(&[(a,b), (b,c), (c,a)]) {
        let mut deg_seq = [a,b,c].map(|v|self.g.degree_of(v));
        deg_seq.sort();
        Some((deg_seq, v))
      } else {None}
    }).max()
  }

  fn expand_3(&self, [a,b,c]: [Vertex;3]) -> Option<Self> {
    let v = self.g.next_vertex();
    let expanded = self.g.with_edges(&[(a,v),(b,v),(c,v)]);
    if !is_planar(&expanded) { return None }
    //TODO canonize less
    let (canon_expanded, into_canon) = Self::slow_auto_cannon_with_permutation(&expanded); 
    let canon_v = into_canon.apply(v);
    let mut possible_vs = canon_expanded.autos.iter().map(|a|a.apply(canon_v)).dedup();
    (possible_vs.contains(&canon_expanded.canon_3()?.1)).then_some(canon_expanded)
  }

  fn expand_3s(&self) -> impl Iterator<Item = Self> + '_ {
    //always applies
    /*  if you add a vertex of degree 3, and it is the canonical reduction, either, it connected to a 
      triangle of higher priority, or it connected to the old canonical vertex of degree 3, making it
      deg 4  
    */
    match self.canon_3() {
      None => self.all_different_triangles(), 
      Some((neighbor_degrees, cur_3)) => {
        let possible_triangles = self.all_different_triangles().into_iter().filter(|&[u,v,w]| 
          [u,v,w].contains(&cur_3) || [u,v,w].map(|a|self.g.degree_of(a)+1) > neighbor_degrees
        );
        possible_triangles.collect()
      },
    }.into_iter().filter_map(|triangle|self.expand_3(triangle))
  }

  fn normalize_square([a,b,c,d]: [Vertex; 4]) -> [Vertex; 4] {
    let [aa, cc] = if a < c {[a,c]} else {[c,a]};
    let [bb, dd] = if b < d {[b,d]} else {[d, b]};
    return [aa,bb,cc,dd]
  }

  fn all_different_squares(&self) -> Vec<[Vertex; 4]> {
    //           /a\
    // a square v | b is represented uniquely as [v,a,b,c] where v<b and a<c
    //           \c/
    // as with triangles, automorphisms are resolved by picking the minimum square
    let mut out = vec![];
    for v in self.g.vertices() {
      for [a,b,c] in self.all_different_triangles() {
        // pick a vertex bb to be opposite v
        // of the remaining two, pick aa<cc, as [a b c] is in ascending order
        for [aa,bb,cc] in [[a,b,c],[a,c,b],[b,a,c]] {
          if v != bb && self.g.has_edges(&[(v, aa), (v, cc)]) {
            let [v, bb] = if v < bb {[v, bb]} else {[bb, v]};
            let square = [v,aa,bb,cc];
            out.push(Self::normalize_square(itertools::min(
              self.autos.iter().map(|a|a.apply_n(square))
            ).unwrap()));
          }
        }
      }
    }
    out.sort();
    out.dedup();
    out
  }

  fn normalize_pentagon([a,b,c,d,e]: [Vertex; 5]) -> [Vertex; 5] {
    if a < c {
      [a,b,c,d,e]
    } else {
      [c,b,a,e,d]
    }
  }

  fn all_different_pentagons(&self) -> Vec<[Vertex; 5]> {
    //            v--b--c
    // a pentagon  \/ \/ is represented uniquely as [v,b,c,d,a] where v<c
    //              a-d
    // as with triangles/squares, automorphisms are resolved by picking the minimum penta
    let mut out = vec![];
    for v in self.g.vertices() {
      for [a,b,c,d] in self.all_different_squares() {
        if  [a,b,c,d].contains(&v) {continue};
        // pick vertices aa and bb attached to v, where bb becomes the "center"
        // (aa isn't and bb is on the square's crossbar)
        for [aa,bb,cc,dd] in [[a,b,c,d],[a,d,c,b],[c,b,a,d],[c,d,a,b]] {
          if v < cc && self.g.has_edges(&[(v, aa), (v, bb)]) {
            let penta = [v,bb,cc,dd,aa];
            out.push(Self::normalize_pentagon(itertools::min(
              self.autos.iter().map(|a|a.apply_n(penta))
            ).unwrap()));
          }
        }
      }
    }
    out.sort();
    out.dedup();
    out
  }

  fn canon_4(&self) -> Option<([usize; 4], SquareReduction)> {
    // canonical 3-reduction precludes 4-reduction
    if self.g.vertices().any(|v| { self.g.degree_of(v) == 3}) { return None } 
    self.g.vertices().filter_map(|v| {
        //v needs 4 neighbors
        let (a, b, c, d) = self.g.neighbors(v).collect_tuple()?;
        //abcd need to be a cycle in some order
        let has_cycle =[[a,b,c,d],[a,c,b,d],[a,b,d,c]].into_iter().any(move |[a,b,c,d]| 
          self.g.has_edges(&[(a,b), (b,c), (c,d),(d,a)]));
        if has_cycle { 
          let mut deg_seq = [a,b,c,d].map(|v|self.g.degree_of(v));
          deg_seq.sort();
          let add_edge = [a,b,c,d].into_iter().combinations(2).map(|vs|(vs[0], vs[1]))
                            .filter(|&(u,v)|!self.g.has_edge(u, v)).max()
                            .expect("non-planar");
          Some((deg_seq, SquareReduction::new(v,add_edge)))
        } else {None}
      }).max()
  }
  
  fn expand_4(&self, [a,b,c,d]: [Vertex;4]) -> Option<Self> {
    let v = self.g.next_vertex();
    let expanded = self.g.with_edges(&[(a,v),(b,v),(c,v),(d,v)]).without_edge(b, d);
    if !is_planar(&expanded) { return None }
    //TODO canonize less
    let (canon_expanded, into_canon) = Self::slow_auto_cannon_with_permutation(&expanded);
    let base_reduction = SquareReduction::new(v,(b,d)).apply(&into_canon);
    let mut possible_reductions = canon_expanded.autos.iter().map(|a|base_reduction.apply(a));
    (possible_reductions.contains(&canon_expanded.canon_4()?.1)).then_some(canon_expanded)
  }

  fn expand_4s(&self) -> impl Iterator<Item = Self> + '_ {
    self.all_different_squares().into_iter().filter_map(|square|self.expand_4(square))
  }

  fn canon_5(&self) -> Option<([usize; 5], PentaReduction)> {
    // canonical 3/4-reduction precludes 5-reduction
    if self.g.vertices().any(|v| { [3,4].contains(&self.g.degree_of(v)) }) { return None } 
    
    self.g.vertices().filter_map(|v| {
      //v needs 5 neighbors
      let (a, b, c, d, e) = self.g.neighbors(v).collect_tuple()?;
      //abcde need to be a cycle in some order
      let mut possible_cycles = [b,c,d,e].into_iter().permutations(4).filter(|vs|vs[0]<vs[3])
        .map(|vs| [a,vs[0],vs[1],vs[2],vs[3]]);
      let has_cycle = possible_cycles.any(move |[a,b,c,d,e]| 
        self.g.has_edges(&[(a,b), (b,c), (c,d), (d,e), (e,a)]));
      if has_cycle { 
        let neighbors = [a,b,c,d,e];
        let mut deg_seq = neighbors.map(|v|self.g.degree_of(v));
        deg_seq.sort();
        let add_triple = neighbors.into_iter().filter_map(|v|{
              let (a,b) = neighbors.into_iter().filter(|&u|!self.g.has_edge(u, v)).collect_tuple()?;
              Some((a,v,b))
            }).max().expect("non-planar");
            Some((deg_seq, PentaReduction::new(v,add_triple)))
      } else {None}
    }).max()


  }
  
  fn expand_5(&self, [a,b,c,d,e]: [Vertex;5]) -> Option<Self> {
    let v = self.g.next_vertex();
    let expanded = self.g.with_edges(&[(a,v),(b,v),(c,v),(d,v),(e,v)])
      .without_edges([(b, d), (b,e)]);
    if !is_planar(&expanded) { return None }
    //TODO canonize less
    let (canon_expanded, into_canon) = Self::slow_auto_cannon_with_permutation(&expanded);
    let base_reduction = PentaReduction::new(v,(d,b,e)).apply(&into_canon);
    let mut possible_reductions = canon_expanded.autos.iter().map(|a|base_reduction.apply(a));
    (possible_reductions.contains(&canon_expanded.canon_5()?.1)).then_some(canon_expanded)
  }  
  
  fn expand_5s(&self) -> impl Iterator<Item = Self> + '_ {
    if self.g.largest_vertex() < 10 {
      // unless we have 11 distinct vertices, all expansions
      // will have a <5-order canonical reduction
      vec![]
    } else {
      unimplemented!("Too slow for practical use, pending non-slow-auto-cano");
      self.all_different_pentagons()
    }.into_iter().filter_map(|penta|self.expand_5(penta))
  }

  fn expand_triangulation(&self) -> impl Iterator<Item = Self> + '_ {
    itertools::chain!(
      self.expand_3s(),
      self.expand_4s(),
      self.expand_5s(),
    )
  }
  fn triangulations_sized(n: Vertex) -> Box<dyn Iterator<Item=Self>>{
    assert!(n >= 3, "need triangle to triangulate");
    if n == 3 {
      return Box::new(
        std::iter::once(
          Self::slow_auto_canon(
            &GraphAdjMatrix::default().with_edges(&[(0,1),(1,2),(0,2)]))
          )
      )
    }
    Box::new(
      Self::triangulations_sized(n-1).flat_map(|g|
        g.expand_triangulation().collect_vec()
      )
    )
  }
}
  
mod test {
  use std::collections::{HashSet, BTreeSet};

use literal::{set, SetLiteral};

  use crate::{adj_matrix::{test::{k_n, c_n}, Permutation}, unreduce::CanonGraph};
  use super::*;
  
  #[test] 
  fn canonize_k3_minus() {
      let k3_minus_the_first = k_n(3).without_edge(0, 1);
      let k3_m_2 = k_n(3).without_edge(0, 2);
      assert_eq!(CanonGraph::slow_auto_canon(&k3_m_2), CanonGraph::slow_auto_canon(&k3_minus_the_first))
  }

  #[test] 
  fn c4_automorphism() { 
    let c4 = k_n(4).without_edge(0, 2).without_edge(1, 3); 
    let CanonGraph{g: canon, autos} = CanonGraph::slow_auto_canon(&c4);
    assert_eq!(autos.len(),8);
    assert!(autos.iter().duplicates().next() == None);
    assert!(autos.iter().all(|a|canon.apply_permutation(a)==canon))
  }

  #[test] 
  fn p4_automorphism() { 
    let p4 = k_n(2).with_edges(&vec![(1,2), (2,3)]);
    let CanonGraph{g: canon, autos} = CanonGraph::slow_auto_canon(&p4);
    let mut id_4 = Permutation::default(); 
    id_4.1 = smallvec![0,1,2,3];
    let swapped = id_4.clone().swap(0, 1).swap(2, 3);
    assert_eq!(autos, vec![id_4, swapped]);
    assert!(autos.iter().duplicates().next() == None);
    assert!(autos.iter().all(|a|canon.apply_permutation(a)==canon))
  }

  #[test]
  fn nuclear_auto_canon() {
    //three triangles sharing a central vertex
    let nuclear_hazard = k_n(3).with_edges(
      &vec![(0,3), (0,4), (3, 4), (0, 5), (0, 6), (5, 6)]);
    let CanonGraph{g: canon, autos} = CanonGraph::slow_auto_canon(&nuclear_hazard);
    assert_eq!(autos.len(),6*4*2);
    assert!(autos.iter().duplicates().next() == None);
    assert!(autos.iter().all(|a|canon.apply_permutation(a)==canon))
  }

  #[test]
  fn k3_e3_k4() {
    assert_eq!(vec![k_n(4)], CanonGraph::slow_auto_canon(&k_n(3)).expand_3s().map(|c|c.g).collect_vec())
  }

  #[test]
  fn k4_e3_k5m() {
    let k_5_minus = CanonGraph::slow_auto_canon(&k_n(5).without_edge(0, 1));
    assert_eq!(vec![k_5_minus], CanonGraph::slow_auto_canon(&k_n(4)).expand_3s().collect_vec())
  }

  #[test]
  fn k5m_e3_bigger() {
    let k_5_minus = &k_n(5).without_edge(0, 1);
    let bigger_guy = k_5_minus.with_edges(&[(0,5), (2,5), (3,5)]);
    assert_eq!(vec![CanonGraph::slow_auto_canon(&bigger_guy)], 
      CanonGraph::slow_auto_canon(&k_5_minus).expand_3s().collect_vec());
  }

  #[test]
  fn not_all_triangles(){
    assert_eq!(vec![[0,1,2]], CanonGraph::slow_auto_canon(&k_n(4)).all_different_triangles())
  }

  
  #[test]
  fn k4_has_square(){
    assert_eq!(vec![[0,1,2,3]], CanonGraph::slow_auto_canon(&k_n(4)).all_different_squares())
  }

  #[test]
  fn k4p4_all_squares() {
    let k4p4 = k_n(4).with_edges(&[(4,2),(4,3),(4,5),(5,3)]);
    let (canon_k4p4, to_canon) = CanonGraph::slow_auto_cannon_with_permutation(&k4p4);
    let expected: BTreeSet<_> = vec![
      [0,2,1,3],[0,1,2,3],[0,1,3,2],[2,0,3,1],
      [2,3,5,4],[0,2,4,3]
    ].into_iter().map(|square|CanonGraph::normalize_square(to_canon.apply_n(square))).collect();
    assert_eq!(expected, canon_k4p4.all_different_squares()
      .into_iter().collect())
  }

  #[test] 
  fn k4p4_all_pentagons() {
    let k4p4 = k_n(4).with_edges(&[(4,2),(4,3),(4,5),(5,3)]);
    let (canon_k4p4, to_canon) = CanonGraph::slow_auto_cannon_with_permutation(&k4p4);
    let expected: BTreeSet<_> = vec![
      [0,2,4,3,1], [0,3,4,2,1], [0,3,5,4,2]
    ].into_iter().map(|penta|CanonGraph::normalize_pentagon(to_canon.apply_n(penta))).collect();
    assert_eq!(expected, canon_k4p4.all_different_pentagons()
      .into_iter().collect())
  }

  #[test]
  fn all_squares_canonical() {
    let k4m_tail = k_n(4).without_edge(0, 2).with_edges(&[(0, 4), (1,5)]);
    let glued = k4m_tail.edge_sum((1,5), (5,1), &k4m_tail).without_edge(6,9)
      .with_edges(&[(7,9), (2,6)]);
    let (canon_glue, to_canon) = CanonGraph::slow_auto_cannon_with_permutation(&glued);
    let expected = [[6,5,7,8]].into_iter().map(|penta|CanonGraph::normalize_square(to_canon.apply_n(penta))).collect_vec();
    assert_eq!(expected, canon_glue.all_different_squares())
  }

  #[test]
  fn k6m3_reduce(){
    let k6m3 = k_n(6).without_edge(0, 1).without_edge(2, 3).without_edge(4, 5);
    assert_eq!(k6m3, CanonGraph::slow_auto_canon(&k6m3).g);
    assert_eq!(48, CanonGraph::slow_auto_canon(&k6m3).autos.len());
    assert!(is_planar(&k6m3));
    let k5m = CanonGraph::slow_auto_canon(&k_n(5).without_edge(0, 1));
    assert_eq!(k5m.expand_4s().collect_vec(),vec![CanonGraph::slow_auto_canon(&k6m3)]);
  }

  #[test]
  fn k6m3_chain_reduce(){
    fn sort_autos(mut g: CanonGraph) -> CanonGraph {
      g.autos.sort();
      g
    }

    let k6m3_chain = k_n(6).without_edges([(0,1), (0,2), (1,3)]);
    assert_eq!(k6m3_chain, CanonGraph::slow_auto_canon(&k6m3_chain).g);
    assert_eq!(4, CanonGraph::slow_auto_canon(&k6m3_chain).autos.len());
    let double_pentagon = sort_autos(CanonGraph::slow_auto_canon(
      &c_n(5).with_edges_to(5).with_edges_to(6).without_edge(5,6)));
    let expanded = CanonGraph::slow_auto_canon(&k6m3_chain)
      .expand_4s().map(sort_autos).collect_vec();
    assert_eq!(expanded, vec![double_pentagon])
  }

  // #[test]
  // fn first_canon_5(){
  //   let mut expanded = GraphAdjMatrix::enumerate_all_size(7).flat_map(|g|
  //     CanonGraph::slow_auto_canon(&g).expand_5s().collect_vec()
  //   );
  //   dbg!(&expanded.next());
  // }

  // #[test]
  // fn finds_canon_5(){
  //   let k4m = k_n(4).without_edge(0, 1);
  //   let half = k4m.edge_sum((1,3), (1,3), &k4m).with_edges(&[
  //     (6,0),(6,1),(6,2),(0,4)
  //   ]);
  //   assert_eq!(2, CanonGraph::slow_auto_canon(&half).autos.len());
  //   let d12r5 = half.edge_sum((4,5), (4,5), &half).with_edges(&[
  //     (1,8),(0,7),(11,6)
  //   ]).with_contracted_edge(6, 11);
  //   println!("strict graph {{");
  //   for (i,j) in d12r5.edges() {
  //     println!("  {} -- {}",i,j);
  //   }
  //   println!("}}");
  //   // println!("json graph {{");
  //   // println!(r#"{{"nodes":["#);
  //   // for i in d12r5.vertices() {
  //   //   println!("{{\"id\": \"{}\"}},", i)
  //   // }
  //   // println!(r#"],"links": ["#);
  //   // for (i,j) in d12r5.edges() {
  //   //   println!("{{\"source\": {}, \"target\": {}, \"value\": 1}},",i,j);
  //   // }
  //   // println!("]}}");
  //   let (d12r5, canon_p) = CanonGraph::slow_auto_cannon_with_permutation(&d12r5);
  //   assert_eq!(4, d12r5.autos.len());
  //   assert!(is_planar(&d12r5.g));
  //   assert_eq!(d12r5.expand_5(canon_p.apply_n([2,6, 9, 8,1])), None);
  //   //assert_eq!(1, d12r5.expand_5s().count());
  // }

  #[should_panic(expected = "non-planar")]
  #[test]
  fn k6_canon5(){
    let k6 = CanonGraph::slow_auto_canon(&k_n(6));
    let shouldnotexist = k6.canon_5();
  }

  // #[test]
  // fn num_triangulations() {
  //   let triangle_counts = 
  //     (3..=10).map(|i|CanonGraph::triangulations_sized(i).count())
  //       .collect_vec(); 
  //       //fails at 8, gives 12 rather than 14
  //   assert_eq!(vec![1,1,1,2,5,14,50,233], triangle_counts);
  // }
}