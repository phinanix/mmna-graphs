#![allow(unused)] // tests dont seem to count

use itertools::Itertools;
use smallvec::{smallvec,SmallVec};

use crate::adj_matrix::{GraphAdjMatrix, Permutation, Vertex};

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


/*
to enumerate a class of graphs C: 
for every graph in C, define a single canonical reduction which decreases towards
a small set of generators. run the reductions in reverse, and keep only those which were
canonical

to enumerate plane triangulations, reduce a vertex of degree 3, 4, or 5; to 1,2 or 3 triangles, 
with a generator of K_4. 

functions to write: 
1) given a graph, unreduce by adding degree 3 vertices
2) '' deg 4
3) '' deg 5
4) fn which given an iterator of size n triangulations returns an iterator of size n+1 triangulations
*/

#[derive(Debug, PartialEq, Eq)]
struct CanonGraph{ g: GraphAdjMatrix, autos: Vec<Permutation>}

impl CanonGraph {
  pub fn slow_auto_canon(graph: &GraphAdjMatrix) -> Self {
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
    let mut autos = vec![];
    let mut min_self = degree_canon.clone();
    for perm in all_perms {
      let candidate = degree_canon.apply_permutation(&perm);
      candidate.partial_cmp(&min_self).expect("Vertex list");
      if candidate < min_self {
        min_self = candidate;
        autos = vec![perm];
      }
      else if candidate == min_self { autos.push(perm)}
    }
    let autos = autos.iter().map(|a|autos[0].inverse().compose(a)).collect();
    Self{g: min_self, autos}
}



  fn all_different_triangles(&self) 
    -> Vec<(Vertex, Vertex, Vertex)> {
    todo!()
  }

  fn expand_3(&self){

  }

}

mod test {
  use crate::{adj_matrix::{test::k_n, Permutation}, unreduce::CanonGraph};
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

}