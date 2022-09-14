
use std::char::MAX;
use std::collections::{HashSet};
use std::fmt::{Debug, Write};
use itertools::Itertools;
use smallvec::{smallvec,SmallVec};
use literal::{set, SetLiteral};

pub const MAX_VS : usize = 10;

pub type Vertex = u8;
pub type VertexVec = SmallVec<[Vertex;MAX_VS]>;

//TODO: should this really be copy?
#[derive(Default, Clone, Copy, PartialEq, Eq, Hash)]
pub struct GraphAdjMatrix{
    vertex_list: [bool; MAX_VS],
    adj_matrix: [[bool; MAX_VS]; MAX_VS]
}

// invariants: if v in vertex list is false, all adj_matrix entries are false
// adj matrix is a symmetric matrix with false on diagonal
impl GraphAdjMatrix {
    pub fn add_vertex(&mut self, v: Vertex) {
        self.vertex_list[v as usize] = true
    }

    pub fn with_vertex(mut self, v: Vertex) -> GraphAdjMatrix{
        self.add_vertex(v);
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

    pub fn vertices(&self) -> impl Iterator<Item = Vertex> {
        self.vertex_list.into_iter().positions(|x| x).map(|i| i as Vertex)
    }
    
    pub fn largest_vertex(&self) -> Vertex {
        self.vertex_list.into_iter().rposition(|x| x).expect("no vertices") as u8
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

    pub fn neighbors(&self, v: Vertex) -> impl Iterator<Item=Vertex> + '_ {
        self.adj_matrix[v as usize].iter().enumerate().filter(|(i,x)|**x).map(|(i,x)|i as Vertex)
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
    fn more() {
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