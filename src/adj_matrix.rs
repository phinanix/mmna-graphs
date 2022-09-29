#![allow(unused)] // tests dont seem to count

use std::collections::binary_heap::Iter;
use std::collections::{HashSet};
use std::{error};
use std::fmt::{Debug, Display, Write};
use itertools::Itertools;
use smallvec::{smallvec,SmallVec};

pub const MAX_VS : usize = 10;

pub type Vertex = u8;
pub type VertexVec = SmallVec<[Vertex;MAX_VS]>;

// invariants: if v in vertex list is false, all adj_matrix entries are false
// adj matrix is a symmetric matrix with false on diagonal
//TODO: should this really be copy?
#[derive(Default, Clone, Copy, PartialEq, Eq, Hash)]
pub struct GraphAdjMatrix{
    vertex_list: [bool; MAX_VS],
    adj_matrix: [[bool; MAX_VS]; MAX_VS]
}

//first thing is array which sends a vertex to its place in the new permutation
//second thing is a smallvec which tells us which elements are being permuted 
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct Permutation([Vertex;MAX_VS],VertexVec);

impl Default for Permutation {
    fn default() -> Self {
        // [0..MAX_VS]
        Permutation(core::array::from_fn(|x|x as Vertex), smallvec![])
    }
}


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

impl Permutation {
    
    pub fn apply(&self, v: Vertex) -> Vertex {
        self.0[v as usize]
    }

    pub fn use_vertex(&mut self, v: Vertex) {
        if !(self.1.contains(&v)) {
            self.1.push(v);
        }
    }
    
    fn swap(mut self, u: Vertex, v: Vertex) -> Self{
        assert!(u!=v);
        self.use_vertex(u);
        self.use_vertex(v);
        
        let (new_u, new_v) = (self.0[v as usize], self.0[u as usize]);
        self.0[u as usize] = new_u;
        self.0[v as usize] = new_v;
        self
    }

    fn decode(mut num: usize, touch: &VertexVec) -> Self {
        let mut perm_to_be = core::array::from_fn(|x|
            if touch.contains(&(x as Vertex)) {u8::MAX} else {x as Vertex}
        );
        let len_factoral : usize = (1..=touch.len()).product();
        num = (len_factoral-1).checked_sub(num).expect("num can only be at most factorial");
        let mut intermediate: VertexVec = smallvec![];
        for i in (1..=touch.len()) {
            intermediate.push((num % i) as Vertex);
            num = num / i;
        }
        for (&(mut i), &t) in intermediate.iter().zip(touch).rev() {
            for &j in touch {
                if perm_to_be[j as usize] == u8::MAX {
                    if i == 0 {
                        perm_to_be[j as usize] = t;
                        break;
                    }
                    else {
                        i -= 1;
                    }
                }
            }
        }
        Permutation(perm_to_be, touch.clone())
    }

    pub fn iterate_set(touch: VertexVec) -> impl Iterator<Item = Self> + Clone {
        let len_factoral = (1..=touch.len()).product();
        (0..len_factoral).map(move |x|Self::decode(x, &touch)) 
    }

    fn compose(&self, q: &Self) -> Self {
        todo!()
    }


}

impl GraphAdjMatrix {
    pub fn add_vertex(&mut self, v: Vertex) {
        self.vertex_list[v as usize] = true
    }

    pub fn with_vertex(mut self, v: Vertex) -> Self{
        self.add_vertex(v);
        self
    }

    pub fn with_vertices(mut self, vs: VertexVec) -> Self {
        for v in vs {
            self.add_vertex(v);
        }
        self
    }

    pub fn add_edge(&mut self, u: Vertex, v: Vertex) {

        //assert!(g.vertex_list[u as usize] && g.vertex_list[v as usize]);
        assert!(u != v);
        
        self.vertex_list[u as usize] = true; 
        self.vertex_list[v as usize] = true;
        
        self.adj_matrix[u as usize][v as usize] = true;
        self.adj_matrix[v as usize][u as usize] = true;
    }

    pub fn with_edge(mut self, u: Vertex, v: Vertex) -> GraphAdjMatrix {
        self.add_edge(u, v);
        self
    }

    pub fn with_edges(mut self, edges: &Vec<(Vertex, Vertex)>) -> GraphAdjMatrix {
        for &(u, v) in edges.iter() {
            self.add_edge(u, v)
        }
        self
    }

    pub fn delete_edge(&mut self, u: Vertex, v: Vertex) {
        self.adj_matrix[u as usize][v as usize] = false;
        self.adj_matrix[v as usize][u as usize] = false;
    }

    pub fn without_edge(mut self, u: Vertex, v: Vertex) -> GraphAdjMatrix {
        self.delete_edge(u, v);
        self
    }

    pub fn delete_vertex(&mut self, u: Vertex) {
        assert!(self.vertex_list[u as usize]);

        self.vertex_list[u as usize] = false;
        self.adj_matrix[u as usize] = [false;MAX_VS];
        for row in &mut self.adj_matrix{
            row[u as usize] = false;
        }
    }

    pub fn without_vertex(&self, u: Vertex) -> Self {
        let mut new_graph = self.clone();
        new_graph.delete_vertex(u);
        new_graph
    }
    
    pub fn contract_edge(&mut self, u: Vertex, v:Vertex) {
        assert!(self.adj_matrix[u as usize][v as usize]);
        //u the new vertex 
        for t in self.neighbors(v) {
            if t != u {
                self.add_edge(u, t)
            }
        }
        self.delete_vertex(v)
    }

    pub fn with_contracted_edge(&self, u: Vertex, v: Vertex) -> Self {
        let mut new_graph = self.clone(); 
        new_graph.contract_edge(u, v);
        new_graph
    }

    pub fn vertices(&self) -> impl Iterator<Item = Vertex> {
        self.vertex_list.into_iter().positions(|x| x).map(|i| i as Vertex)
    }
    
    pub fn edges(&self) -> impl IntoIterator<Item = (Vertex, Vertex)> {
        let mut out = vec![];
        for u in 0..MAX_VS { for v in 0..u {
            if self.adj_matrix[u][v] {
                out.push((u as Vertex,v as Vertex))
            }
        }
        }
        out
    }

    pub fn largest_vertex(&self) -> Vertex {
        self.vertex_list.into_iter().rposition(|x| x).expect("no vertices") as u8
    }

    pub fn degree_of(&self, v: Vertex) -> usize {
        self.adj_matrix[v as usize].iter().filter(|&&x|x).count()
    }

    pub fn slow_auto_canon(&self) -> (Vec<Permutation>, Self) {
        use perm_iter::{DynBox};
        let degrees_of_vs = self.vertices().group_by(|&v|self.degree_of(v));
        let grouped_vs = degrees_of_vs.into_iter().sorted_by_key(|x|x.0).map(|x|x.1);
        let stuff = grouped_vs.map(|grp| { // -> impl Iterator<Item = Permutation> + Clone
            Permutation::iterate_set(grp.collect()).dyn_box()
        });
        let stuff2  = stuff.reduce(
            |ps,qs| ps.cartesian_product(qs).map(|(p,q)| p.compose(&q)).dyn_box()
        );

        todo!()
    }

    pub fn apply_permutation(&self, p: Permutation) -> Self {
        let mut out = GraphAdjMatrix::default();
        for (u, v) in self.edges().into_iter() {
            out.add_edge(p.apply(u), p.apply(v))
        }        
        out
    }

    pub fn compact_vertices(&self) -> Self {
        let mut vertex_map = [0u8; MAX_VS];
        
        for (i,v) in self.vertices().enumerate() {
            vertex_map[v as usize]= i as u8;
        }
        let mut out = GraphAdjMatrix::default();
        for (u, v) in self.edges() {
            out.add_edge(vertex_map[u as usize], vertex_map[v as usize])
        }
        out
    }

    pub fn is_connected(&self) -> bool {
        let first_v = self.largest_vertex();
        //invariant: todo intersect visited is empty 
        let mut visited = [false; MAX_VS];
        let mut todo = [false; MAX_VS];
        todo[first_v as usize] = true;
    
        while let Some(cur_v) = todo.into_iter().position(|x| x) {
            todo[cur_v] = false;
            visited[cur_v] = true; 
            for (v, adj) in self.adj_matrix[cur_v].into_iter().enumerate() {
                if adj && !visited[v] { todo[v] = true}
            }
        }
        visited == self.vertex_list
    }

    pub fn is_biconnected(&self) -> bool {
        // thingy is connected
        // for vertex delete vertex, still connected
        self.is_connected() &&
        self.vertices().all(|v| self.without_vertex(v).is_connected())
    }

    // note that this only enumerates connected graphs (but it enumerates isomorphic 
    // graphs multiple times; less times than you would think for labelled graphs)
    pub fn enumerate_all_size(num_vs: u8) -> impl Iterator<Item=Self> {
        assert!(num_vs > 0);
        let max_graph : Vec<u64> = (0.. num_vs)
            .map(|n| 2_u64.pow(n.into()) - 1)
            .collect();
        struct GraphIter{
            max_graph : Vec<u64>,
            cur_graph : Vec<u64>,
        }
        
        impl Iterator for GraphIter {
            type Item=GraphAdjMatrix;

            fn next(&mut self) -> Option<Self::Item> {
                if self.cur_graph.last().expect("no vertices") == &0 {return None}
                let out = Some(self.cur_graph.as_slice().into());
                //we increment after the return now
                for i in 0..(self.cur_graph.len() - 1) { 
                    if self.cur_graph[i] == 0 {
                        self.cur_graph[i] = self.max_graph[i];
                        self.cur_graph[i+1] -= 1;
                    } else {
                        break;
                    }
                }

                out
            }
        }
        
        return GraphIter{max_graph : max_graph.clone(), cur_graph : max_graph}
    }

    //precondition: biconnected 3+ vertice
    pub fn find_cycle(&self) -> VertexVec {
        let mut path = smallvec![self.largest_vertex()];
        path.push(self.neighbors(path[0]).next().unwrap());
        let mut prev = path[0];
        let mut seen: HashSet<Vertex> = [prev].into_iter().collect(); //TODO bitset
        while !seen.contains(path.last().unwrap()) {
            seen.insert(*path.last().unwrap());
            let next = self.neighbors(*path.last().unwrap()).filter(|&x|x!=prev).next()
                       .expect("unexpected degree 1 vertex in 'biconnected' graph");
            prev = *path.last().unwrap();
            path.push(next);
        }
        while path[0] != *path.last().unwrap() {
            path.drain(..=0);  // pop_front until we hit the cyclical part
        }
        path.drain(..=0);  // only mention loop point once
        return path
    }

    pub fn neighbors(&self, v: Vertex) -> impl Iterator<Item=Vertex> {
        self.adj_matrix[v as usize].into_iter().enumerate().filter(|(i,x)|*x).map(|(i,x)|i as Vertex)
    }

    pub fn split_on(&self, h: &GraphAdjMatrix) -> impl Iterator<Item=GraphAdjMatrix> {
        let h_vertex_list: [bool; MAX_VS] = h.vertex_list;
            //h.iter().fold([false; MAX_VS], |mut acc,i|{acc[*i as usize] = true; acc});
        let mut starts: SmallVec<[bool; MAX_VS]> =
            self.vertex_list.iter().zip(h_vertex_list).map(|(&sv,hv)|sv&!hv).collect();
        let mut bridges = vec![];
        while let Some(cur_v) = starts.iter().position(|x| *x) {
            //invariant: todo intersect visited is empty 
            let mut visited = [false; MAX_VS];
            let mut todo = [false; MAX_VS];
            todo[cur_v as usize] = true;
        
            let mut fragment = GraphAdjMatrix::default();
            while let Some(cur_v) = todo.into_iter().position(|x| x) {
                todo[cur_v] = false;
                visited[cur_v] = true;
                starts[cur_v] = false; 
                for (v, adj) in self.adj_matrix[cur_v].into_iter().enumerate() {
                    if adj {
                        fragment.add_edge(cur_v as Vertex,v as Vertex);
                        if !visited[v] && !h_vertex_list[v] { 
                            todo[v] = true
                        }
                    }
                }

            }
            bridges.push(fragment);
        }
        //above obtains all bridges with at least 1 vertex not in h. 
        //now we need to obtain all the bridges which are exactly 1 edge between 2 vertices of h.
        for v in h.vertices() { for u in h.vertices() {
            if v < u && self.adj_matrix[u as usize][v as usize] 
                && ! (h.adj_matrix[u as usize][v as usize]) {
                    bridges.push(GraphAdjMatrix::default().with_edge(u, v))
            }
        }}
        bridges.into_iter()
    }

    pub fn find_path_using(&self, face: &VertexVec) -> VertexVec {
        let first_v = self.vertices().filter(|v|face.contains(v)).next()
                      .expect("Not touching face");
        //invariant: todo intersect visited is empty 
        let mut visited_from: [Option<Vertex>; MAX_VS] = [None; MAX_VS];
        let mut todo: [Option<Vertex>; MAX_VS] = [None; MAX_VS];
        todo[first_v as usize] = Some(first_v);

        while let Some(cur_v) = todo.into_iter().position(|x|x.is_some()) {
            visited_from[cur_v] = todo[cur_v]; 
            todo[cur_v] = None;
            for (v, adj) in self.adj_matrix[cur_v].into_iter().enumerate() {
                if adj && visited_from[v].is_none() && todo[v].is_none() { 
                    todo[v] = Some(cur_v as Vertex);
                    if face.contains(&(v as Vertex)) {
                        let mut path = smallvec![v as Vertex];
                        let mut tail = cur_v as Vertex;
                        while tail != first_v {
                            path.push(tail);
                            tail = visited_from[tail as usize].unwrap();
                        }
                        path.push(first_v);
                        return path
                    }
                }
            }
        }
        panic!("No path found")
    }

    pub fn add_path_edges(&mut self, path: &VertexVec) {
        for (&u, &v) in path.iter().zip(path[1..].iter()) {
            self.add_edge(u, v)
        }
    }

}

impl From<&[u64]> for GraphAdjMatrix {
    fn from(rows: &[u64]) -> Self {
        let mut out = GraphAdjMatrix::default();
        let num_vs = rows.len();
        for x in 0..num_vs {
            for y in 0..x {
                if (rows[x] >> y) & 1 != 0 {
                    out.add_edge(x as u8, y as u8);
                }
            }
        }
        out
    }
}

impl Debug for GraphAdjMatrix {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        struct Row([bool; MAX_VS]);
        impl Debug for Row {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                for x in self.0 {
                    match x {
                        true => f.write_char('#')?,
                        false => f.write_char('.')?
                    }
                }
                Ok(())
            }
        }
        f.debug_struct("GraphAdjMatrix")
         .field("vertex_list", &Row(self.vertex_list))
         .field("adj_matrix", &self.adj_matrix.map(|x|Row(x)))
         .finish()
    }
}


pub mod test {
    use super::*;

    #[test]
    fn make_perm_zero(){
        assert_eq!(Permutation::decode(0, &smallvec![]), Permutation::default())
    }

    #[test]
    fn make_perm_one(){
        assert_eq!(Permutation::decode(1, &smallvec![0, 5]), 
            Permutation::default().swap(0, 5)
        )
    }

    #[test]
    fn six_len_3(){
        assert_eq!(Permutation::iterate_set(smallvec![0, 2, 4]).count(), 6)
    }

    #[test]
    fn we_didnt_screw_it_up(){
        let us : HashSet<Vec<_>> = Permutation::iterate_set(smallvec![0,1,2])
            .map(|p|p.0[..=2].into()).collect();
        let them : HashSet<_> = [0,1,2].into_iter().permutations(3).collect();
        assert_eq!(us, them)
    }

    #[derive(Debug, Default, Clone)]
    pub struct GraphEdgeList(pub Vec<(Vertex, Vertex)>); //edge list

    impl From<GraphEdgeList> for GraphAdjMatrix {
        fn from(list: GraphEdgeList) -> Self {
            list.0.iter().fold(Default::default(), |g, (u,v)| g.with_edge(*u, *v))
        }
    }
    
    fn vertices_el(g: GraphEdgeList) -> Vec<Vertex> {
        g.0.into_iter().flat_map(|(x, y)| [x, y]).unique().collect()
    }
    
    fn largest_vertex_el(g: GraphEdgeList) -> Vertex {
        g.0.into_iter().flat_map(|(x, y)| [x, y]).max().expect("No vertices")
    }
    fn one_e() -> GraphAdjMatrix {
        let mut one_e = GraphAdjMatrix::default();
        one_e.add_edge(0, 1);
        one_e
    }

    fn two_v() -> GraphAdjMatrix {
        let mut two_v = GraphAdjMatrix::default();
        two_v.add_vertex(0);
        two_v.add_vertex(1);
        two_v
    }

    fn one_e_el() -> GraphEdgeList {
        GraphEdgeList(vec![(0,1)])
    }

    pub fn k_n(n : Vertex) -> GraphAdjMatrix {
        let mut k_n = GraphAdjMatrix::default();
        for x in 0..n { for y in 0..x {
            k_n.add_edge(x, y);
        }}
        k_n
    }
    #[test]
    fn one_e_el_is_one_e() {
        assert_eq!(one_e(), one_e_el().into())
    }

    #[test]
    fn one_v_is_connected() {
        let mut one_v = GraphAdjMatrix::default();
        one_v.add_vertex(0);

        assert!(one_v.is_connected())
    }

    #[test]
    fn two_v_is_not_connected() {
        assert!(!two_v().is_connected())
    }

    #[test]
    fn one_edge_is_connected() {
        assert!(one_e().is_connected())
    }

    #[test]
    fn one_edge_is_biconnected() {
        assert!(one_e().is_biconnected())
    }

    #[test]
    fn two_v_is_not_biconnected() {
        assert!(!two_v().is_biconnected())
    }

    #[test]
    fn two_edges_not_biconnected() {
        let mut two_e = GraphAdjMatrix::default();
        two_e.add_edge(0, 1);
        two_e.add_edge(1,2);
        assert!(two_e.is_connected());
        assert!(!two_e.is_biconnected());
    }
    
    #[test] 
    fn canonize_k3_minus() {
        let k3_minus_the_first = k_n(3).without_edge(0, 1);
        let k3_m_2 = k_n(3).without_edge(0, 2);
        //TODO: assert_eq!(k3_m_2.slow_auto_canon().1, k3_minus_the_first.slow_auto_canon().1)
    }

    #[test]
    fn k_3_two_ways() {
        assert_eq!(k_n(3), ([0, 1, 3]).as_slice().into())
    }

    #[test]
    fn three_graphs_size_3() {
        assert_eq!(3, GraphAdjMatrix::enumerate_all_size(3).count())
    }
    #[test]    
    fn twenty_one_graphs_size_4() {
        assert_eq!(21, GraphAdjMatrix::enumerate_all_size(4).count())
    }
    #[test]    
    fn three_hundred_and_fifteen_graphs_size_5() {
        assert_eq!(1*3*7*15, GraphAdjMatrix::enumerate_all_size(5).count())
    }
    // there is K_4, five versions of K_4 without an edge (but you can't delete (0,1))
    // and 2 of the three versions of K_4 minus two parallel edges (but you can't 
    // delete (0, 1))
    #[test]
    fn biconnected_graphs_size_4() {
        assert_eq!(8, GraphAdjMatrix::enumerate_all_size(4)
            .filter(GraphAdjMatrix::is_biconnected).count())
    }
    #[test]    
    fn enumerate_size_6() {
        assert_eq!(1*3*7*15*31, GraphAdjMatrix::enumerate_all_size(6).count())
    }
    #[test]
    fn k_4_has_neighbors() {
        assert_eq!(vec![1,2,3], k_n(4).neighbors(0).collect::<Vec<_>>())
    }
    #[test]
    fn k_3_one_cycle() {
        assert_eq!(vec![0,1,2], k_n(3).find_cycle().into_vec())
    }
}
