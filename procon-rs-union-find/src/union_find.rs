use std::convert::TryInto;

#[derive(Clone, Debug)]
pub struct UnionFind {
    parent_or_len: Vec<i32>,
}

impl UnionFind {
    /// 頂点数 n の UnionFind を作る。
    pub fn new(n: usize) -> Self {
        Self {
            parent_or_len: vec![-1; n],
        }
    }

    /// 全体の頂点数を返す。
    pub fn len(&self) -> usize {
        self.parent_or_len.len()
    }

    /// 全体の頂点数が 0 かどうかを返す。
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// 頂点 v が属する集合の根頂点を返す。
    pub fn root(&mut self, v: usize) -> usize {
        assert!(v < self.len());

        if self.parent_or_len[v] < 0 {
            return v;
        }

        // 経路圧縮
        let root = self.root(self.parent_or_len[v].try_into().unwrap());
        self.parent_or_len[v] = root.try_into().unwrap();
        root
    }

    /// 頂点 v が属する集合の頂点数を返す。
    pub fn group_len(&mut self, v: usize) -> usize {
        assert!(v < self.len());

        let root = self.root(v);

        (-self.parent_or_len[root]).try_into().unwrap()
    }

    /// 頂点 v, w が同じ集合に属すかどうかを返す。
    pub fn is_same(&mut self, v: usize, w: usize) -> bool {
        assert!(v < self.len());
        assert!(w < self.len());

        self.root(v) == self.root(w)
    }

    /// 頂点 v が属する集合と頂点 w が属する集合を併合する。
    pub fn unite(&mut self, v: usize, w: usize) {
        assert!(v < self.len());
        assert!(w < self.len());

        let mut root_v = self.root(v);
        let mut root_w = self.root(w);
        if root_v == root_w {
            return;
        }

        // union by size
        let len_v = -self.parent_or_len[root_v];
        let len_w = -self.parent_or_len[root_w];
        if len_v < len_w {
            std::mem::swap(&mut root_v, &mut root_w);
        }

        self.parent_or_len[root_v] = -(len_v + len_w);
        self.parent_or_len[root_w] = root_v.try_into().unwrap();
    }

    /// 全ての集合を返す。
    pub fn groups(&mut self) -> Vec<Vec<usize>> {
        let mut groups = (0..self.len())
            .map(|v| {
                let p = self.parent_or_len[v];
                if p < 0 {
                    Some(Vec::with_capacity((-p).try_into().unwrap()))
                } else {
                    None
                }
            })
            .collect::<Vec<_>>();

        for v in 0..self.len() {
            let root = self.root(v);
            groups[root].as_mut().unwrap().push(v);
        }

        groups.into_iter().flatten().collect()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_union_find() {
        let mut uf = UnionFind::new(5);

        // 初期状態

        assert_eq!(uf.len(), 5);
        assert!(!uf.is_empty());
        assert_eq!(uf.root(0), 0);
        assert_eq!(uf.group_len(0), 1);
        assert!(!uf.is_same(0, 1));
        assert_eq!(
            uf.groups(),
            vec![vec![0], vec![1], vec![2], vec![3], vec![4]]
        );

        // 併合後

        uf.unite(0, 4);
        uf.unite(1, 3);

        assert_eq!(uf.len(), 5);
        assert_eq!(uf.group_len(0), 2);
        assert_eq!(uf.group_len(1), 2);
        assert_eq!(uf.group_len(2), 1);
        assert!(uf.is_same(0, 4));
        assert!(uf.is_same(1, 3));
        assert!(!uf.is_same(0, 2));
        let mut groups = uf.groups();
        groups.sort();
        assert_eq!(groups, vec![vec![0, 4], vec![1, 3], vec![2]]);

        // 同じ集合内での unite で壊れないことを確認
        // (チェックを忘れている場合、root() が無限再帰に陥る)

        uf.unite(0, 4);

        assert!(uf.is_same(0, 4));
    }
}
