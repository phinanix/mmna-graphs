#![allow(unused)] // tests dont seem to count

use std::collections::{HashSet};
use std::fmt::{Debug, Write};
use itertools::Itertools;
use smallvec::{smallvec,SmallVec};

const MAX_VS : usize = 6;

type Vertex = u8;

#[derive(Debug, Default, Clone)]
struct GraphEdgeList(Vec<(Vertex, Vertex)>); //edge list

#[derive(Default, Clone, Copy, PartialEq, Eq, Hash)]
struct GraphAdjMatrix{
    vertex_list: [bool; MAX_VS],
    adj_matrix: [[bool; MAX_VS]; MAX_VS]
}

// invariants: if v in vertex list is false, all adj_matrix entries are false
// adj matrix is a symmetric matrix with false on diagonal
impl GraphAdjMatrix {
    fn add_vertex(&mut self, v: Vertex) {
        self.vertex_list[v as usize] = true
    }

    fn with_vertex(mut self, v: Vertex) -> GraphAdjMatrix{
        self.add_vertex(v);
        self
    }

    fn add_edge(&mut self, u: Vertex, v: Vertex) {

        //assert!(g.vertex_list[u as usize] && g.vertex_list[v as usize]);
        assert!(u != v);
        
        self.vertex_list[u as usize] = true; 
        self.vertex_list[v as usize] = true;
        
        self.adj_matrix[u as usize][v as usize] = true;
        self.adj_matrix[v as usize][u as usize] = true;
    }

    fn with_edge(mut self, u: Vertex, v: Vertex) -> GraphAdjMatrix {
        self.add_edge(u, v);
        self
    }

    fn delete_edge(&mut self, u: Vertex, v: Vertex) {
        self.adj_matrix[u as usize][v as usize] = false;
        self.adj_matrix[v as usize][u as usize] = false;
    }

    fn without_edge(mut self, u: Vertex, v: Vertex) -> GraphAdjMatrix {
        self.delete_edge(u, v);
        self
    }

    fn delete_vertex(&mut self, u: Vertex) {
        assert!(self.vertex_list[u as usize]);

        self.vertex_list[u as usize] = false;
        self.adj_matrix[u as usize] = [false;MAX_VS];
        for row in &mut self.adj_matrix{
            row[u as usize] = false;
        }
    }

    fn without_vertex(&self, u: Vertex) -> Self {
        let mut new_graph = self.clone();
        new_graph.delete_vertex(u);
        new_graph
    }

    fn vertices(&self) -> impl Iterator<Item = Vertex> {
        self.vertex_list.into_iter().positions(|x| x).map(|i| i as Vertex)
    }
    
    fn largest_vertex(&self) -> Vertex {
        self.vertex_list.into_iter().rposition(|x|x).expect("no vertices") as u8
    }
    fn is_connected(&self) -> bool {
        let first_v = self.largest_vertex();
        //todo intersect visited is empty 
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

    fn is_biconnected(&self) -> bool {
        // thingy is connected
        // for vertex delete vertex, still connected
        self.is_connected() &&
        self.vertices().all(|v| self.without_vertex(v).is_connected())
    }

    // note that this only enumerates connected graphs (but it enumerates isomorphic 
    // graphs multiple times; less times than you would think for labelled graphs)
    fn enumerate_all_size(num_vs: u8) -> impl Iterator<Item=Self> {
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
    fn find_cycle(&self) -> Face {
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
        return Face(path)
    }

    fn neighbors(&self, v: Vertex) -> impl Iterator<Item=Vertex> + '_ {
        self.adj_matrix[v as usize].iter().enumerate().filter(|(i,x)|**x).map(|(i,x)|i as Vertex)
    }

    fn split_on(&self, h: &GraphAdjMatrix) -> Vec<GraphAdjMatrix> {
        let mut starts: SmallVec<[bool; MAX_VS]> =
            self.vertex_list.iter().zip(h.vertex_list).map(|(&sv,hv)|sv&!hv).collect();
        let mut bridges = vec![];
        while let Some(cur_v) = starts.iter().position(|x| *x) {
            //todo intersect visited is empty 
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
                        if !visited[v] && !h.vertex_list[v] { 
                            todo[v] = true
                        }
                    }
                }

            }
            bridges.push(fragment);
        }
        bridges
    }

}

impl From<GraphEdgeList> for GraphAdjMatrix {
    fn from(list: GraphEdgeList) -> Self {
        list.0.iter().fold(Default::default(), |g, (u,v)| g.with_edge(*u, *v))
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

struct PlanarEmbedding {
    //clockwise_neighbors[v] is a list of v's neighbors, clockwise
    clockwise_neighbors: Vec<SmallVec<[Vertex; MAX_VS]>>,
}

#[derive(Clone,Debug)]
struct Face(SmallVec<[Vertex; MAX_VS]>);

fn vertices_el(g: GraphEdgeList) -> Vec<Vertex> {
    g.0.into_iter().flat_map(|(x, y)| [x, y]).unique().collect()
}

fn largest_vertex_el(g: GraphEdgeList) -> Vertex {
    g.0.into_iter().flat_map(|(x, y)| [x, y]).max().expect("No vertices")
}

type Bridge = GraphAdjMatrix;
fn dmp_embed(g: &GraphAdjMatrix) -> Option<PlanarEmbedding> {
    let mut starting_face: Face = g.find_cycle();
    let mut h = GraphAdjMatrix::default();
    for (&u,&v) in starting_face.0.iter().zip(
            starting_face.0[1..].iter().chain(&starting_face.0[..1])
        ) {
            h.add_edge(u, v)
    }
    let mut bridges = g.split_on(&h);
    dbg!(h,bridges);
    // let mut embed = PlanarEmbedding::from_cycle(&starting_face);
    // let mut faces = vec![starting_face.clone(), starting_face.reverse()];
    // //TODO fix this type to be indirect to canonical list of faces
    // let mut destinations: HashMap<Bridge, Vec<Face>> =
    //     bridges.iter().map(|x|(x,faces.clone())).collect();
    // while !bridges.empty() {
    //     h.embed(bridges.next())?
    // }
    // Ok(embed)
    // todo!()
    None
}

#[cfg(test)]
mod test {
    use super::*;

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

    fn k_n(n : Vertex) -> GraphAdjMatrix {
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
        //assert_eq!(1*3*7*15*31, GraphAdjMatrix::enumerate_all_size(6).count())
    }
    #[test]
    fn k_4_has_neighbors() {
        assert_eq!(vec![1,2,3], k_n(4).neighbors(0).collect::<Vec<_>>())
    }
    #[test]
    fn k_3_one_cycle() {
        assert_eq!(vec![0,1,2], k_n(3).find_cycle().0.into_vec())
    }

    #[test]
    fn split_k4_minus(){
        let k4_minus = k_n(4).without_edge(0,1);
        let shared_edge = GraphAdjMatrix::default().with_edge(2, 3);
        assert_eq!(
            k4_minus.split_on(&shared_edge),
            [vec![(0,2),(0,3)], vec![(1,2),(1,3)]].into_iter()
                .map(|v| GraphEdgeList(v).into()).collect::<Vec<GraphAdjMatrix>>()
        )
    }
    
    #[test]
    fn split_k6_minus_minus(){
        let k6mm = k_n(6).without_edge(3,4).without_edge(3,5);
        assert_eq!(
            k6mm.split_on(&k_n(3)),
            [vec![(3,0),(3,1),(3,2)], vec![(4,0),(4,1),(4,2),(5,0),(5,1),(5,2),(4,5)]].into_iter()
                .map(|v| GraphEdgeList(v).into()).collect::<Vec<GraphAdjMatrix>>()
        );
    }
}