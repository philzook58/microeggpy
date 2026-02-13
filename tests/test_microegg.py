import microeggpy


def test_add_node():
    g = microeggpy.EGraph()
    id1 = g.add("a", [])
    id2 = g.add("a", [])
    assert id1 == id2
    id3 = g.add("b", [])
    assert id3 != id1
    assert not g.is_eq(id1, id3)
    g.union(id1, id3)
    assert g.is_eq(id1, id3)
