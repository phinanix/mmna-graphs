use itertools::Itertools;
use smallvec::SmallVec;

const MAX_VS : usize = 5;

type Vertex = u8;

#[derive(Debug, Default, Clone)]
struct GraphEdgeList(Vec<(Vertex, Vertex)>); //edge list

#[derive(Debug, Default, Clone, Copy, PartialEq, Eq)]
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


    
    fn is_connected(&self) -> bool {
        let first_v = largest_vertex(self);
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

    fn is_biconnected(self) -> bool {
        // thingy is connected
        // for vertex delete vertex, still connected
        self.is_connected() &&
        self.vertices().all(|v| self.without_vertex(v).is_connected())
    }

    fn enumerate_all_size(num_vs: u8) -> impl Iterator<Self> {
        0..(num_vs * (num_vs - 1) / 2).map(|n|
            // for vertex 
              //for smaller vertex 
                //connect if bit is set
                // n>>=1
        )
    }

}

impl From<GraphEdgeList> for GraphAdjMatrix {
    fn from(list: GraphEdgeList) -> Self {
        list.0.iter().fold(Default::default(), |g, (u,v)| g.with_edge(*u, *v))
    }
}

struct PlanarEmbedding {
    //clockwise_neighbors[v] is a list of v's neighbors, clockwise
    clockwise_neighbors: Vec<SmallVec<[Vertex; MAX_VS]>>,
}

struct Face((Vertex, Vertex));

fn vertices_el(g: GraphEdgeList) -> Vec<Vertex> {
    g.0.into_iter().flat_map(|(x, y)| [x, y]).unique().collect()
}

fn largest_vertex_el(g: GraphEdgeList) -> Vertex {
    g.0.into_iter().flat_map(|(x, y)| [x, y]).max().expect("No vertices")
}


fn largest_vertex(g: &GraphAdjMatrix) -> Vertex {
    g.vertex_list.into_iter().rposition(|x|x).expect("no vertices") as u8
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
}