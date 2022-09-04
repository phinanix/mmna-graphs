#![allow(unused)] // tests dont seem to count

use std::char::MAX;
use std::collections::{HashSet};
use std::fmt::{Debug, Write};
use itertools::Itertools;
use smallvec::{smallvec,SmallVec};
use literal::{set, SetLiteral};

const MAX_VS : usize = 10;

type Vertex = u8;
type VertexVec = SmallVec<[Vertex;MAX_VS]>;

#[derive(Debug, Default, Clone)]
struct GraphEdgeList(Vec<(Vertex, Vertex)>); //edge list

//TODO: should this really be copy?
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

    fn with_edges(mut self, edges: &Vec<(Vertex, Vertex)>) -> GraphAdjMatrix {
        for &(u, v) in edges.iter() {
            self.add_edge(u, v)
        }
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
        self.vertex_list.into_iter().rposition(|x| x).expect("no vertices") as u8
    }

    fn is_connected(&self) -> bool {
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

    fn split_on(&self, h: &GraphAdjMatrix) -> impl Iterator<Item=GraphAdjMatrix> {
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

    fn find_path_using(&self, face: &Face) -> VertexVec {
        let first_v = self.vertices().filter(|v|face.0.contains(v)).next()
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
                    if face.0.contains(&(v as Vertex)) {
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

    fn add_path_edges(&mut self, path: &VertexVec) {
        for (&u, &v) in path.iter().zip(path[1..].iter()) {
            self.add_edge(u, v)
        }
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


#[derive(Debug, PartialEq, Eq)]
struct PlanarEmbedding {
    //clockwise_neighbors[v] is a list of v's neighbors, clockwise
    clockwise_neighbors: Vec<VertexVec>,
}

impl PlanarEmbedding {
    fn add_path(&mut self, path: &VertexVec, face: &Face) {
        //warning: gross
        for (&u,&v) in face.0.iter().zip(face.0[1..].iter().chain(&face.0[..1])) {
            if v == path[0] {
                //add path[1] to v's clockwise neighbors just before u 
                let u_index = self.clockwise_neighbors[v as usize].iter()
                  .position(|&x| x == u).unwrap();
                self.clockwise_neighbors[v as usize].insert(u_index, path[1]);
            }
            else if v == *path.last().unwrap() {
                let u_index = self.clockwise_neighbors[v as usize].iter()
                  .position(|&x| x == u).unwrap();
                self.clockwise_neighbors[v as usize].insert(
                    u_index, path[path.len()-2]);
            }        
        }
        //we need a pair of internal vertices, ie length 4
        if path.len() >= 4 {
            for (&u,&v) in path[1..].iter().zip(path[2..(path.len()-1)].iter()) {
                self.clockwise_neighbors[v as usize].push(u);
                self.clockwise_neighbors[u as usize].push(v);
            }
        }
        //we need at least 1 internal vertex, ie length 3
        if path.len() >= 3 {
            self.clockwise_neighbors[path[1] as usize].push(path[0]);
            self.clockwise_neighbors[path[path.len()-2] as usize].push(path[path.len()-1]);
        }
    }
}


#[derive(Clone,Debug,PartialEq, Eq)]
struct Face(VertexVec);

impl Face {
    fn bisect(&self, path: &VertexVec) -> (Face, Face) {
        let path_start_index = self.0.iter().position(|&v| v == path[0]).unwrap();
        let path_end_index = self.0.iter().position(|&v| v == path[path.len() - 1]).unwrap();
        //the two faces are start->end + rev path and end->start + path
        let s_to_e_len = if path_start_index > path_end_index 
            { path_end_index + self.0.len() - path_start_index }
            else 
            { path_end_index - path_start_index};
        let mut s_e_face : VertexVec = smallvec![];
        for i in 0..(s_to_e_len) {s_e_face.push(self.0[(path_start_index+i).rem_euclid(self.0.len())])}
        let mut bw_path = path.clone();
        bw_path.reverse();
        //because otherwise the last element of the path will be duplicated
        bw_path.pop().unwrap();
        s_e_face.append(&mut bw_path);
        
        let e_to_s_len = if path_end_index > path_start_index 
            { path_start_index + self.0.len() - path_end_index }
            else 
            { path_start_index - path_end_index};
        let mut e_s_face : VertexVec = smallvec![];
        for i in 0..(e_to_s_len) {e_s_face.push(self.0[(path_end_index+i).rem_euclid(self.0.len())])}
        let mut fw_path = path.clone();
        //because otherwise the last element of the path will be duplicated
        fw_path.pop().unwrap();
        e_s_face.append(&mut fw_path);
        
        
        (Face(s_e_face), Face(e_s_face))
    }
}
    
//todo: delete ?
fn vertices_el(g: GraphEdgeList) -> Vec<Vertex> {
    g.0.into_iter().flat_map(|(x, y)| [x, y]).unique().collect()
}

fn largest_vertex_el(g: GraphEdgeList) -> Vertex {
    g.0.into_iter().flat_map(|(x, y)| [x, y]).max().expect("No vertices")
}

type Bridge = GraphAdjMatrix;
fn dmp_embed(g: &GraphAdjMatrix) -> Option<PlanarEmbedding> {
    //precondition: g has at least 3 vertices, and g is biconnected. 
    let mut starting_face: Face = g.find_cycle();
    let mut h = GraphAdjMatrix::default();
    let mut embed = PlanarEmbedding{
        clockwise_neighbors: [0; MAX_VS].map(|_|smallvec![]).into()
    };
    for (&u,&v) in starting_face.0.iter().zip(
            starting_face.0[1..].iter().chain(&starting_face.0[..1])
        ) {
            h.add_edge(u, v);
            embed.clockwise_neighbors[v as usize].push(u);
            embed.clockwise_neighbors[u as usize].push(v);
    }
    let bridges = g.split_on(&h);
    let mut faces = vec![starting_face.clone(),{
        starting_face.0.reverse();
        starting_face
    }];
    //usize idx into faces TODO bitvector
    let mut bridges: Vec<(Bridge, HashSet<usize>)> =
        bridges.into_iter().map(|x|(x,set!{0u8,1u8})).collect();
    //dbg!(&h,&bridges);
    while !bridges.is_empty() {
        dbg!(&h, &bridges);
        let (idx, (next_bridge, valid_faces)) =
            bridges.iter().enumerate().min_by_key(|(i,(b,v))|v.len()).unwrap();
        //no valid faces = no valid embedding
        let face_idx = *valid_faces.iter().next()?;
        dbg!(next_bridge, valid_faces, &faces);
        let face = faces[face_idx].clone();
        let path: VertexVec = next_bridge.find_path_using(&face);
        let next_bridge = next_bridge.clone();
        bridges.remove(idx);
        h.add_path_edges(&path);
        embed.add_path(&path, &face);
        let (face_l, face_r) = face.bisect(&path);
        faces[face_idx] = face_l.clone();
        let face_l_idx = face_idx;
        let face_r_idx = faces.len();
        faces.push(face_r.clone());
        let new_faces = [face_idx, face_r_idx];
        fn can_be_embedded(new_face: &Face, face: &Face, bridge: &Bridge) -> bool {
            //invariant: new_face was produced b y splitting face
            //(face & bridge.vertices()) - new_face == {}
            bridge.vertices()
                .filter(|v|face.0.contains(v))
                .filter(|v|!new_face.0.contains(v))
                .next().is_none()
        }
        for (bridge, valid) in /*remaining*/ &mut bridges {
            if valid.contains(&face_idx) {
                valid.remove(&face_idx);
                if can_be_embedded(&face_l, &face, bridge) {
                    valid.insert(face_l_idx);
                }
                if can_be_embedded(&face_r, &face, bridge) {
                    valid.insert(face_r_idx);
                }
            }
        }
        //todo I think this copies |bridge| multiples for some reason, 
        //this line should be writeable without clone (or Copy) I think
        let path_graph = GraphAdjMatrix::default().with_edges(
            &path.iter().zip(path[1..].iter()).map(|(&x, &y)| (x, y)).collect());
        let new_bridges = next_bridge.split_on(&path_graph).into_iter().map(
            |bridge| (bridge, new_faces.into_iter().filter(
                |&f| can_be_embedded(&faces[f], &face, &bridge)
            ).collect())
        );
        bridges.extend(new_bridges);
    }
    Some(embed)
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
        assert_eq!(1*3*7*15*31, GraphAdjMatrix::enumerate_all_size(6).count())
    }
    #[test]
    fn k_4_has_neighbors() {
        assert_eq!(vec![1,2,3], k_n(4).neighbors(0).collect::<Vec<_>>())
    }
    #[test]
    fn k_4_dmp_watdo() {
        dbg![dmp_embed(&k_n(4))];
    }

    #[test]
    fn k_5_dmp_not_embed() {
        assert_eq!(dmp_embed(&k_n(5)), None);
    }

    #[test]
    fn split_on_k_5_minus() {
        let k5_minus = k_n(5).without_edge(0, 1);
        let cycle = k_n(4).without_edge(0,1).without_edge(2,3);
        let ans: Vec<_> = k5_minus.split_on(&cycle).into_iter().collect_vec();
        let bridge1 = GraphAdjMatrix::default().with_edges(
            &vec![(0, 4),(1, 4), (2, 4), (3, 4)]);
        let bridge2 = GraphAdjMatrix::default().with_edge(2, 3);
        dbg!(&ans, &bridge1, &bridge2);
        assert_eq!(ans, vec![bridge1, bridge2])
    }

    #[test]
    fn k_5_minus_embed() {
        let k5_minus = k_n(5).without_edge(0, 1);
        let ans = Some(PlanarEmbedding { clockwise_neighbors: 
            vec![smallvec![3, 4, 2], smallvec![2, 4, 3], smallvec![4, 1, 3, 0], 
            smallvec![2, 1, 4, 0], smallvec![3, 1, 2, 0], 
            smallvec![], smallvec![], smallvec![], smallvec![], smallvec![]] });
        assert_eq!(dmp_embed(&k5_minus), ans);
    }

    #[test]
    fn k_3_dmp_embed() {
        let mut embed = PlanarEmbedding{
            clockwise_neighbors: [0; MAX_VS].map(|_|smallvec![]).into()
        };
        embed.clockwise_neighbors[0] = smallvec![1,2];
        embed.clockwise_neighbors[1] = smallvec![0,2];
        embed.clockwise_neighbors[2] = smallvec![1,0];
        assert_eq!(dmp_embed(&k_n(3)), Some(embed));
    }

    #[test]
    fn k_3_one_cycle() {
        assert_eq!(vec![0,1,2], k_n(3).find_cycle().0.into_vec())
    }

    #[test]
    fn split_k4_minus(){
        let k4_minus = k_n(4).without_edge(0,1);
        let edge23 = GraphAdjMatrix::default().with_edge(2, 3);
        assert_eq!(
            k4_minus.split_on(&edge23).collect::<Vec<GraphAdjMatrix>>(),
            [vec![(0,2),(0,3)], vec![(1,2),(1,3)]].into_iter()
                .map(|v| GraphEdgeList(v).into()).collect::<Vec<GraphAdjMatrix>>()
        )
    }
    
    #[test]
    fn split_k6_minus_minus(){
        let k6mm = k_n(6).without_edge(3,4).without_edge(3,5);
        assert_eq!(
            k6mm.split_on(&k_n(3)).collect::<Vec<GraphAdjMatrix>>(),
            [vec![(3,0),(3,1),(3,2)], vec![(4,0),(4,1),(4,2),(5,0),(5,1),(5,2),(4,5)]].into_iter()
                .map(|v| GraphEdgeList(v).into()).collect::<Vec<GraphAdjMatrix>>()
        );
    }

    #[test]
    fn k4_path_through_k3(){
        let r: VertexVec = smallvec![1,3,0];
        let asdf = k_n(4).split_on(&k_n(3)).next().unwrap();
        assert_eq!(asdf.find_path_using(&Face(smallvec![0,1,2])), r)
    }

    fn random_example() -> (Face, PlanarEmbedding, VertexVec) {
        let starting_face = smallvec![1,8,3,7,4,2];
        let mut embed = PlanarEmbedding{
            clockwise_neighbors: [0; MAX_VS].map(|_|smallvec![]).into()
        };
        for (&u,&v) in starting_face.iter().zip(
                starting_face[1..].iter().chain(&starting_face[..1])
            ) {
                embed.clockwise_neighbors[v as usize].push(u);
                embed.clockwise_neighbors[u as usize].push(v);
        }
        let path = smallvec![8,5,6,4];
        (Face(starting_face), embed, path)
    }
    // random example. the cycle is 8, 3, 7, 4, 2, 1
    // the path within the cycle is 8,5,6,4
    #[test]
    fn add_path_random_example() {
        let (face, mut embed, path) = random_example();
        embed.add_path(&path, &face);
        let ans1 : VertexVec = smallvec![5,1,3];
        let ans2 : VertexVec = smallvec![6,7,2];
        assert_eq!(embed.clockwise_neighbors[8], ans1);
        assert_eq!(embed.clockwise_neighbors[4], ans2); 
    }

    #[test]
    fn bisect_random_example() {
        let (face, embed, path) = random_example();
        let (face_l, face_r) = face.bisect(&path);
        let ans1 : VertexVec = smallvec![8,3,7,4,6,5];
        let ans2 : VertexVec = smallvec![4,2,1,8,5,6];
        assert_eq!(face_l.0, ans1);
        assert_eq!(face_r.0, ans2);
    }

    #[test]
    fn bisect_k4_wrong_example() {
        let face = Face(smallvec![0,2,1]);
        let path = smallvec![1,3,0];
        //let (face_l, face_r) = face.bisect(&path);
        let faces = face.bisect(&path);
        let goals = (Face(smallvec![1,0,3]), Face(smallvec![0,2,1,3]));
        assert_eq!(faces, goals);
        // assert_eq!(face_r, goal_r);
        // assert_eq!(face_l, goal_l);
    }

    #[test]
    fn split_on_finds_single_edges() {

    }
}