#![allow(unused)] // tests dont seem to count

use std::collections::{HashSet};
use std::fmt::{Debug};
use itertools::Itertools;
use smallvec::{smallvec};
use literal::{set, SetLiteral};

use crate::adj_matrix::{VertexVec, GraphAdjMatrix, MAX_VS};
//use adj_matrix::{};

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


type Bridge = GraphAdjMatrix;
fn dmp_embed(g: &GraphAdjMatrix) -> Option<PlanarEmbedding> {
    //precondition: g has at least 3 vertices, and g is biconnected. 
    let mut starting_face: VertexVec = g.find_cycle();
    let mut h = GraphAdjMatrix::default();
    let mut embed = PlanarEmbedding{
        clockwise_neighbors: [0; MAX_VS].map(|_|smallvec![]).into()
    };
    for (&u,&v) in starting_face.iter().zip(
            starting_face[1..].iter().chain(&starting_face[..1])
        ) {
            h.add_edge(u, v);
            embed.clockwise_neighbors[v as usize].push(u);
            embed.clockwise_neighbors[u as usize].push(v);
    }
    let bridges = g.split_on(&h);
    let mut faces = vec![
        Face(starting_face.clone()),
        { starting_face.reverse();
          Face(starting_face)
        }
    ];
    //usize idx into faces TODO bitvector
    let mut bridges: Vec<(Bridge, HashSet<usize>)> =
        bridges.into_iter().map(|x|(x,set!{0u8,1u8})).collect();
    //dbg!(&h,&bridges);
    while !bridges.is_empty() {
        //dbg!(&h, &bridges);
        let (idx, (next_bridge, valid_faces)) =
            bridges.iter().enumerate().min_by_key(|(i,(b,v))|v.len()).unwrap();
        //no valid faces = no valid embedding
        let face_idx = *valid_faces.iter().next()?;
        let face = faces[face_idx].clone();
        let path: VertexVec = next_bridge.find_path_using(&face.0);
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

fn topologize(mut g: GraphAdjMatrix) -> GraphAdjMatrix {
    // while v is a vertex of degree 1 or 2 
    while g.vertices().any(|v|
        match g.degree_of(v) {
            0|1 => {g.delete_vertex(v); true}, 
            2 => {g.contract_edge(g.neighbors(v).next().unwrap(), v); true}, 
            _ => false,
        }
    ) {}    
    g
}

fn is_planar(g: &GraphAdjMatrix) -> bool {
    let g = topologize(*g); 
    if g.vertices().next().is_none() {return true}
    let cut_vertices : VertexVec = g.vertices().filter(
        |&v|!g.without_vertex(v).is_connected()
      ).collect();
    
    if cut_vertices.len() > 0 {    
        g.split_on(&GraphAdjMatrix::default().with_vertices(cut_vertices))
         .all(|piece|is_planar(&piece))
    } else {
        dmp_embed(&g).is_some()
    }
}

fn is_apex(g: &GraphAdjMatrix) -> bool {
    g.vertices().any(|v|is_planar(&g.without_vertex(v)))
}

fn is_mimsy(g: &GraphAdjMatrix) -> bool {
    //precondition: g is biconnected, min degree 3
    !is_apex(g) && 
    g.edges().into_iter().all(|(u, v)| is_apex(&g.without_edge(u, v))
       && is_apex(&g.with_contracted_edge(u, v)))
}

#[cfg(test)]
mod test {

    use std::vec;

    use super::*;
    use crate::adj_matrix::{GraphAdjMatrix};
    use crate::adj_matrix::test::{k_n, GraphEdgeList};
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

    /*
    note that this test is nondeterministic, it sometimes finds a valid but 
    different planar embedding. the spooky thing is I don't know why - it 
    seems to me all the relevant code shoudl be deterministic

    thread 'planarity::test::k_5_minus_embed' panicked at 'assertion failed: `(left == right)`
  left: `Some(PlanarEmbedding { clockwise_neighbors: [[4, 3, 2], [4, 2, 3], [3, 1, 4, 0], [4, 1, 2, 0], [2, 1, 3, 0], [], [], [], [], []] })`,
 right: `Some(PlanarEmbedding { clockwise_neighbors: [[3, 4, 2], [2, 4, 3], [4, 1, 3, 0], [2, 1, 4, 0], [3, 1, 2, 0], [], [], [], [], []] })`', src/planarity.rs:239:9 */
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
        assert_eq!(asdf.find_path_using(&smallvec![0,1,2]), r)
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
    fn topologize_k4_with_stuff() {
        let k4_with_stuff = k_n(4).with_edge(3, 4)
                       .with_edge(4, 2) 
                       .with_edge(0, 5);
        let ans = topologize(k4_with_stuff).compact_vertices();
        assert_eq!(ans, k_n(4))
    }

    #[test]
    fn compact_one_long_edge() {
        assert_eq!(k_n(2), GraphAdjMatrix::default().with_edge(0, 3).compact_vertices())
    }

    #[test]
    fn k_3_is_planar() {
        assert!(is_planar(&k_n(3)))
    }

    #[test]
    fn k_5_is_not_planar() {
        assert!(!is_planar(&k_n(5)))
    }

    #[test]
    fn hourglass_is_planar() {
        let hourglass = k_n(3).with_edges(
            &vec![(2,3), (3,4), (2,4)]
        );
        assert!(is_planar(&hourglass))
    }

    #[test]
    fn two_k4_is_planar() {
        let two_k4 = k_n(4).with_edges(
            &vec![(3,4), (4,5), (5,6), (3,5), (4,6), (3,6)]
        );
        assert!(is_planar(&two_k4)) 
    }

    #[test]
    fn k5_and_k4_nonplanar() {
        let k5_k4 = k_n(5).with_edges(
            &vec![(7,4), (4,5), (5,6), (7,5), (4,6), (7,6)]
        );   
        assert!(!is_planar(&k5_k4))     
    }

}