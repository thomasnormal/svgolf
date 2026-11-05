"""site/standing.py on synthetic fixtures (never shown as data).

    python3 -m unittest discover -s svgolf/tests/site      (from the lean-surfaces root)
"""

import os
import sys
import unittest

sys.path.insert(0, os.path.join(os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))), "site"))
import standing as S  # noqa: E402


def rec(i, player, area, time):
    return {"id": i, "kind": "record", "player": player, "area": area, "time": time}


def ref(i, area, time):
    return {"id": i, "kind": "reference", "player": None, "area": area, "time": time}


class AxisTest(unittest.TestCase):
    def test_empty_field(self):
        s = ref("par", 100, 100)
        st = S.standing(s, [], s, [s])
        self.assertEqual(st["field_players"], 0)
        for a in S.AXES:
            self.assertEqual(st["axes"][a]["n"], 0)
            self.assertIsNone(st["axes"][a]["beats_pct"])
            self.assertEqual(st["axes"][a]["beats_text"], "–")
        self.assertIsNone(st["position"])            # par has no board position

    def test_own_player_excluded_and_best_per_player(self):
        me = rec("me", "alice", 100, 100)
        recs = [me, rec("a2", "alice", 50, 50),       # alice's other record: not in her own field
                rec("b1", "bob", 120, 90), rec("b2", "bob", 99, 300),   # bob's best area 99, best time 90
                rec("c1", "carol", 100, 100)]
        st = S.standing(me, recs, None, recs)
        self.assertEqual(st["field_players"], 2)
        ar, tm = st["axes"]["area"], st["axes"]["time"]
        self.assertEqual((ar["beaten"], ar["matched"], ar["behind"]), (0, 1, 1))   # carol ties, bob 99 < 100
        self.assertEqual((tm["beaten"], tm["matched"], tm["behind"]), (0, 1, 1))   # carol ties, bob 90 < 100

    def test_ties_are_exact(self):
        me = rec("me", "a", 4604416, 2602)
        recs = [me, rec("x", "b", 4604417, 2602), rec("y", "c", 4604416, 2601)]
        st = S.standing(me, recs, None, recs)
        self.assertEqual(st["axes"]["area"]["beaten"], 1)     # one unit of 1e-4 um^2 is a difference
        self.assertEqual(st["axes"]["area"]["matched"], 1)
        self.assertEqual(st["axes"]["time"]["behind"], 1)     # one ps is a difference

    def test_floor_never_overclaims(self):
        me = rec("me", "p0", 1, 1)
        recs = [me] + [rec(f"r{k}", f"p{k}", 2, 2) for k in range(1, 200)] + [rec("best", "pz", 0, 0)]
        st = S.standing(me, recs, None, recs)
        a = st["axes"]["area"]
        self.assertEqual((a["beaten"], a["n"]), (199, 200))
        self.assertEqual(a["beats_text"], "99%")             # round() would print 100% with one record better

    def test_small_nonzero_is_lt1(self):
        me = rec("me", "p0", 5, 5)
        recs = [me, rec("t", "p1", 5, 5)] + [rec(f"r{k}", f"q{k}", 1, 1) for k in range(150)]
        st = S.standing(me, recs, None, recs)
        self.assertEqual(st["axes"]["area"]["matches_text"], "<1%")


class BoardTest(unittest.TestCase):
    def test_relations(self):
        me = rec("me", "a", 10, 10)
        self.assertEqual(S.board_relation(me, [rec("x", "b", 9, 10)]), "ahead")
        self.assertEqual(S.board_relation(me, [rec("x", "b", 11, 10), rec("y", "b", 10, 12)]), "beaten")
        self.assertEqual(S.board_relation(me, [rec("x", "b", 10, 10), rec("y", "b", 12, 12)]), "level")
        self.assertEqual(S.board_relation(me, [rec("x", "b", 8, 12)]), "tradeoff")
        # one record dominated, another trades off: the player is NOT beaten
        self.assertEqual(S.board_relation(me, [rec("x", "b", 11, 11), rec("y", "b", 8, 12)]), "tradeoff")
        # an identical record plus a trade-off: tradeoff, not level
        self.assertEqual(S.board_relation(me, [rec("x", "b", 10, 10), rec("y", "b", 8, 12)]), "tradeoff")
        # ahead wins over everything
        self.assertEqual(S.board_relation(me, [rec("x", "b", 10, 10), rec("y", "b", 9, 9)]), "ahead")

    def test_superscore_is_not_used_on_the_board(self):
        # bob's best area (5) and best time (5) come from two different designs; per axis he beats me on
        # both, but no single design of his dominates mine: on the board he trades off
        me = rec("me", "a", 10, 10)
        recs = [me, rec("b1", "bob", 5, 20), rec("b2", "bob", 20, 5)]
        st = S.standing(me, recs, None, recs)
        self.assertEqual(st["axes"]["area"]["behind"], 1)
        self.assertEqual(st["axes"]["time"]["behind"], 1)
        self.assertEqual(st["board"]["tradeoff"], 1)
        self.assertEqual(st["board"]["ahead"], 0)

    def test_layers_and_rank(self):
        a, b, c, d = rec("a", "p", 1, 4), rec("b", "q", 2, 2), rec("c", "r", 3, 3), rec("d", "s", 4, 1)
        pos = S.board_position(c, [a, b, c, d])
        self.assertEqual(pos["layer"], 2)                     # c is dominated by b only
        self.assertEqual(pos["rank"], 4)                      # scores 4, 4, 9, 4: three are smaller, rank 1 + 3
        pos_b = S.board_position(b, [a, b, c, d])
        self.assertEqual((pos_b["layer"], pos_b["rank"]), (1, 1))   # scores tie at 4: a shared rank
        base = {"id": "z", "kind": "baseline", "player": None, "area": 1, "time": 1}
        pz = S.board_position(base, [a, b, c, d])
        self.assertTrue(pz["hypothetical"])
        self.assertEqual((pz["layer"], pz["rank"], pz["of"]), (1, 1, 5))

    def test_field_rejects_non_records(self):
        with self.assertRaises(ValueError):
            S.field_of(rec("me", "a", 1, 1), [ref("r", 1, 1)])


class ViewTest(unittest.TestCase):
    def test_small_sets_show_everything(self):
        lo, hi = S.fit_axis([1.0, 2.0, 3.0], keep=[])
        self.assertLess(lo, 1.0)
        self.assertGreater(hi, 3.0)

    def test_fences_drop_outliers_but_keep_the_subject(self):
        vals = [10.0, 11, 12, 13, 14, 15, 16, 17, 1000]
        lo, hi = S.fit_axis(vals, keep=[])
        self.assertLess(hi, 1000)
        lo2, hi2 = S.fit_axis(vals, keep=[1000])
        self.assertGreater(hi2, 1000)

    def test_beyond_counts_corners_twice_total_once(self):
        edges, total = S.beyond([(0, 0), (5, 5), (20, 20), (20, 5)], (1, 10, 1, 10))
        self.assertEqual(edges, {"left": 1, "right": 2, "below": 1, "above": 1})
        self.assertEqual(total, 3)


if __name__ == "__main__":
    unittest.main(verbosity=1)
