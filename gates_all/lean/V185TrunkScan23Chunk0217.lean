import V185TrunkScan23Chunk0216

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_1283594 : List Nat := [3, 1, 2, 2, 2, 3, 2, 1, 3, 2, 2]
def baseStart_1283594 : Nat := 118140960795 + 1283594 * 2 ^ 59
def prefixEnd_1283594 : Nat := 4983230072969 + 3 ^ 40 * 1283594 * 2
def baseEnd_1283594 : Nat := 659100687227356166271865

theorem tailTrace_1283594 : CollatzResearch.WordTrace tailWord_1283594 prefixEnd_1283594 659100687227356166271865 := by
  unfold tailWord_1283594
  simp only [CollatzResearch.WordTrace]
  refine ⟨11704129827941408311820459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31211012874510422164854557 11704129827941408311820459)
  ·
    refine ⟨17556194741912112467730689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11704129827941408311820459 17556194741912112467730689)
    ·
      refine ⟨13167146056434084350798017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17556194741912112467730689 13167146056434084350798017)
      ·
        refine ⟨9875359542325563263098513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13167146056434084350798017 9875359542325563263098513)
        ·
          refine ⟨7406519656744172447323885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9875359542325563263098513 7406519656744172447323885)
          ·
            refine ⟨2777444871279064667746457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7406519656744172447323885 2777444871279064667746457)
            ·
              refine ⟨2083083653459298500809843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2777444871279064667746457 2083083653459298500809843)
              ·
                refine ⟨3124625480188947751214765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2083083653459298500809843 3124625480188947751214765)
                ·
                  refine ⟨1171734555070855406705537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3124625480188947751214765 1171734555070855406705537)
                  ·
                    refine ⟨878800916303141555029153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1171734555070855406705537 878800916303141555029153)
                    ·
                      refine ⟨659100687227356166271865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 878800916303141555029153 659100687227356166271865)
                      ·
                        rfl

theorem cell23_1283594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 2, 1, 3, 2, 2].length) (baseStart_1283594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1283594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1283594 prefixEnd_1283594 := by exact prefixLift 1283594
  have htrace : WordTrace (prefixWord ++ tailWord_1283594) baseStart_1283594 baseEnd_1283594 := by
    simpa [prefixWord, tailWord_1283594, baseEnd_1283594] using wordTrace_append hprefix tailTrace_1283594
  have hstable : (prefixWord ++ tailWord_1283594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1283594).length < 2 ^ (prefixWord ++ tailWord_1283594).sum := by decide
  have hdescent : baseEnd_1283594 < baseStart_1283594 := by decide
  rcases family_descends (prefixWord ++ tailWord_1283594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1283604 : List Nat := [2, 4, 3, 1, 2, 2, 1, 1, 1, 6]
def baseStart_1283604 : Nat := 118140960795 + 1283604 * 2 ^ 59
def prefixEnd_1283604 : Nat := 4983230072969 + 3 ^ 40 * 1283604 * 2
def baseEnd_1283604 : Nat := 219701940677967042382273

theorem tailTrace_1283604 : CollatzResearch.WordTrace tailWord_1283604 prefixEnd_1283604 219701940677967042382273 := by
  unfold tailWord_1283604
  simp only [CollatzResearch.WordTrace]
  refine ⟨23408442020864702477572933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31211256027819603303430577 23408442020864702477572933)
  ·
    refine ⟨4389082878912131714544925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23408442020864702477572933 4389082878912131714544925)
    ·
      refine ⟨1645906079592049392954347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4389082878912131714544925 1645906079592049392954347)
      ·
        refine ⟨2468859119388074089431521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1645906079592049392954347 2468859119388074089431521)
        ·
          refine ⟨1851644339541055567073641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2468859119388074089431521 1851644339541055567073641)
          ·
            refine ⟨1388733254655791675305231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1851644339541055567073641 1388733254655791675305231)
            ·
              refine ⟨2083099881983687512957847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1388733254655791675305231 2083099881983687512957847)
              ·
                refine ⟨3124649822975531269436771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2083099881983687512957847 3124649822975531269436771)
                ·
                  refine ⟨4686974734463296904155157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3124649822975531269436771 4686974734463296904155157)
                  ·
                    refine ⟨219701940677967042382273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4686974734463296904155157 219701940677967042382273)
                    ·
                      rfl

theorem cell23_1283604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 2, 1, 1, 1, 6].length) (baseStart_1283604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1283604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1283604 prefixEnd_1283604 := by exact prefixLift 1283604
  have htrace : WordTrace (prefixWord ++ tailWord_1283604) baseStart_1283604 baseEnd_1283604 := by
    simpa [prefixWord, tailWord_1283604, baseEnd_1283604] using wordTrace_append hprefix tailTrace_1283604
  have hstable : (prefixWord ++ tailWord_1283604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1283604).length < 2 ^ (prefixWord ++ tailWord_1283604).sum := by decide
  have hdescent : baseEnd_1283604 < baseStart_1283604 := by decide
  rcases family_descends (prefixWord ++ tailWord_1283604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1283633 : List Nat := [1, 2, 2, 3, 1, 1, 1, 2, 1, 5, 4]
def baseStart_1283633 : Nat := 118140960795 + 1283633 * 2 ^ 59
def prefixEnd_1283633 : Nat := 4983230072969 + 3 ^ 40 * 1283633 * 2
def baseEnd_1283633 : Nat := 659120712972881513684185

theorem tailTrace_1283633 : CollatzResearch.WordTrace tailWord_1283633 prefixEnd_1283633 659120712972881513684185 := by
  unfold tailWord_1283633
  simp only [CollatzResearch.WordTrace]
  refine ⟨46817941758624342907951553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31211961172416228605301035 46817941758624342907951553)
  ·
    refine ⟨35113456318968257180963665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46817941758624342907951553 35113456318968257180963665)
    ·
      refine ⟨26335092239226192885722749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35113456318968257180963665 26335092239226192885722749)
      ·
        refine ⟨9875659589709822332146031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26335092239226192885722749 9875659589709822332146031)
        ·
          refine ⟨14813489384564733498219047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9875659589709822332146031 14813489384564733498219047)
          ·
            refine ⟨22220234076847100247328571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14813489384564733498219047 22220234076847100247328571)
            ·
              refine ⟨33330351115270650370992857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22220234076847100247328571 33330351115270650370992857)
              ·
                refine ⟨24997763336452987778244643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33330351115270650370992857 24997763336452987778244643)
                ·
                  refine ⟨37496645004679481667366965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24997763336452987778244643 37496645004679481667366965)
                  ·
                    refine ⟨3515310469188701406315653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 37496645004679481667366965 3515310469188701406315653)
                    ·
                      refine ⟨659120712972881513684185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3515310469188701406315653 659120712972881513684185)
                      ·
                        rfl

theorem cell23_1283633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 2, 1, 5, 4].length) (baseStart_1283633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1283633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1283633 prefixEnd_1283633 := by exact prefixLift 1283633
  have htrace : WordTrace (prefixWord ++ tailWord_1283633) baseStart_1283633 baseEnd_1283633 := by
    simpa [prefixWord, tailWord_1283633, baseEnd_1283633] using wordTrace_append hprefix tailTrace_1283633
  have hstable : (prefixWord ++ tailWord_1283633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1283633).length < 2 ^ (prefixWord ++ tailWord_1283633).sum := by decide
  have hdescent : baseEnd_1283633 < baseStart_1283633 := by decide
  rcases family_descends (prefixWord ++ tailWord_1283633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1283653 : List Nat := [1, 3, 1, 1, 1, 4, 1, 2, 1, 3, 5]
def baseStart_1283653 : Nat := 118140960795 + 1283653 * 2 ^ 59
def prefixEnd_1283653 : Nat := 4983230072969 + 3 ^ 40 * 1283653 * 2
def baseEnd_1283653 : Nat := 659130982585971435434093

theorem tailTrace_1283653 : CollatzResearch.WordTrace tailWord_1283653 prefixEnd_1283653 659130982585971435434093 := by
  unfold tailWord_1283653
  simp only [CollatzResearch.WordTrace]
  refine ⟨46818671218551886323679613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31212447479034590882453075 46818671218551886323679613)
  ·
    refine ⟨17557001706956957371379855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46818671218551886323679613 17557001706956957371379855)
    ·
      refine ⟨26335502560435436057069783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17557001706956957371379855 26335502560435436057069783)
      ·
        refine ⟨39503253840653154085604675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26335502560435436057069783 39503253840653154085604675)
        ·
          refine ⟨59254880760979731128407013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39503253840653154085604675 59254880760979731128407013)
          ·
            refine ⟨11110290142683699586576315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 59254880760979731128407013 11110290142683699586576315)
            ·
              refine ⟨16665435214025549379864473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11110290142683699586576315 16665435214025549379864473)
              ·
                refine ⟨12499076410519162034898355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16665435214025549379864473 12499076410519162034898355)
                ·
                  refine ⟨18748614615778743052347533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12499076410519162034898355 18748614615778743052347533)
                  ·
                    refine ⟨7030730480917028644630325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18748614615778743052347533 7030730480917028644630325)
                    ·
                      refine ⟨659130982585971435434093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7030730480917028644630325 659130982585971435434093)
                      ·
                        rfl

theorem cell23_1283653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 2, 1, 3, 5].length) (baseStart_1283653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1283653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1283653 prefixEnd_1283653 := by exact prefixLift 1283653
  have htrace : WordTrace (prefixWord ++ tailWord_1283653) baseStart_1283653 baseEnd_1283653 := by
    simpa [prefixWord, tailWord_1283653, baseEnd_1283653] using wordTrace_append hprefix tailTrace_1283653
  have hstable : (prefixWord ++ tailWord_1283653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1283653).length < 2 ^ (prefixWord ++ tailWord_1283653).sum := by decide
  have hdescent : baseEnd_1283653 < baseStart_1283653 := by decide
  rcases family_descends (prefixWord ++ tailWord_1283653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1283661 : List Nat := [1, 6, 1, 1, 3, 1, 1, 3, 2, 1, 3]
def baseStart_1283661 : Nat := 118140960795 + 1283661 * 2 ^ 59
def prefixEnd_1283661 : Nat := 4983230072969 + 3 ^ 40 * 1283661 * 2
def baseEnd_1283661 : Nat := 659135090431207404134057

theorem tailTrace_1283661 : CollatzResearch.WordTrace tailWord_1283661 prefixEnd_1283661 659135090431207404134057 := by
  unfold tailWord_1283661
  simp only [CollatzResearch.WordTrace]
  refine ⟨46818963002522903689970837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31212642001681935793313891 46818963002522903689970837)
  ·
    refine ⟨2194638890743261110467383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 46818963002522903689970837 2194638890743261110467383)
    ·
      refine ⟨3291958336114891665701075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2194638890743261110467383 3291958336114891665701075)
      ·
        refine ⟨4937937504172337498551613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3291958336114891665701075 4937937504172337498551613)
        ·
          refine ⟨1851726564064626561956855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4937937504172337498551613 1851726564064626561956855)
          ·
            refine ⟨2777589846096939842935283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1851726564064626561956855 2777589846096939842935283)
            ·
              refine ⟨4166384769145409764402925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2777589846096939842935283 4166384769145409764402925)
              ·
                refine ⟨1562394288429528661651097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4166384769145409764402925 1562394288429528661651097)
                ·
                  refine ⟨1171795716322146496238323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1562394288429528661651097 1171795716322146496238323)
                  ·
                    refine ⟨1757693574483219744357485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1171795716322146496238323 1757693574483219744357485)
                    ·
                      refine ⟨659135090431207404134057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1757693574483219744357485 659135090431207404134057)
                      ·
                        rfl

theorem cell23_1283661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 1, 3, 2, 1, 3].length) (baseStart_1283661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1283661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1283661 prefixEnd_1283661 := by exact prefixLift 1283661
  have htrace : WordTrace (prefixWord ++ tailWord_1283661) baseStart_1283661 baseEnd_1283661 := by
    simpa [prefixWord, tailWord_1283661, baseEnd_1283661] using wordTrace_append hprefix tailTrace_1283661
  have hstable : (prefixWord ++ tailWord_1283661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1283661).length < 2 ^ (prefixWord ++ tailWord_1283661).sum := by decide
  have hdescent : baseEnd_1283661 < baseStart_1283661 := by decide
  rcases family_descends (prefixWord ++ tailWord_1283661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1283663 : List Nat := [1, 1, 2, 1, 1, 2, 3, 3, 1, 4, 4]
def baseStart_1283663 : Nat := 118140960795 + 1283663 * 2 ^ 59
def prefixEnd_1283663 : Nat := 4983230072969 + 3 ^ 40 * 1283663 * 2
def baseEnd_1283663 : Nat := 659136117392516396309047

theorem tailTrace_1283663 : CollatzResearch.WordTrace tailWord_1283663 prefixEnd_1283663 659136117392516396309047 := by
  unfold tailWord_1283663
  simp only [CollatzResearch.WordTrace]
  refine ⟨46819035948515658031543643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31212690632343772021029095 46819035948515658031543643)
  ·
    refine ⟨70228553922773487047315465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46819035948515658031543643 70228553922773487047315465)
    ·
      refine ⟨52671415442080115285486599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70228553922773487047315465 52671415442080115285486599)
      ·
        refine ⟨79007123163120172928229899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52671415442080115285486599 79007123163120172928229899)
        ·
          refine ⟨118510684744680259392344849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79007123163120172928229899 118510684744680259392344849)
          ·
            refine ⟨88883013558510194544258637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 118510684744680259392344849 88883013558510194544258637)
            ·
              refine ⟨33331130084441322954096989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 88883013558510194544258637 33331130084441322954096989)
              ·
                refine ⟨12499173781665496107786371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33331130084441322954096989 12499173781665496107786371)
                ·
                  refine ⟨18748760672498244161679557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12499173781665496107786371 18748760672498244161679557)
                  ·
                    refine ⟨3515392626093420780314917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18748760672498244161679557 3515392626093420780314917)
                    ·
                      refine ⟨659136117392516396309047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3515392626093420780314917 659136117392516396309047)
                      ·
                        rfl

theorem cell23_1283663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 3, 1, 4, 4].length) (baseStart_1283663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1283663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1283663 prefixEnd_1283663 := by exact prefixLift 1283663
  have htrace : WordTrace (prefixWord ++ tailWord_1283663) baseStart_1283663 baseEnd_1283663 := by
    simpa [prefixWord, tailWord_1283663, baseEnd_1283663] using wordTrace_append hprefix tailTrace_1283663
  have hstable : (prefixWord ++ tailWord_1283663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1283663).length < 2 ^ (prefixWord ++ tailWord_1283663).sum := by decide
  have hdescent : baseEnd_1283663 < baseStart_1283663 := by decide
  rcases family_descends (prefixWord ++ tailWord_1283663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1283673 : List Nat := [1, 2, 1, 2, 2, 1, 1, 6, 7]
def baseStart_1283673 : Nat := 118140960795 + 1283673 * 2 ^ 59
def prefixEnd_1283673 : Nat := 4983230072969 + 3 ^ 40 * 1283673 * 2
def baseEnd_1283673 : Nat := 73237916911006817464889

theorem tailTrace_1283673 : CollatzResearch.WordTrace tailWord_1283673 prefixEnd_1283673 73237916911006817464889 := by
  unfold tailWord_1283673
  simp only [CollatzResearch.WordTrace]
  refine ⟨46819400678479429739407673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31212933785652953159605115 46819400678479429739407673)
  ·
    refine ⟨35114550508859572304555755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46819400678479429739407673 35114550508859572304555755)
    ·
      refine ⟨52671825763289358456833633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35114550508859572304555755 52671825763289358456833633)
      ·
        refine ⟨39503869322467018842625225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52671825763289358456833633 39503869322467018842625225)
        ·
          refine ⟨29627901991850264131968919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39503869322467018842625225 29627901991850264131968919)
          ·
            refine ⟨44441852987775396197953379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29627901991850264131968919 44441852987775396197953379)
            ·
              refine ⟨66662779481663094296930069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44441852987775396197953379 66662779481663094296930069)
              ·
                refine ⟨3124817788202957545168597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 66662779481663094296930069 3124817788202957545168597)
                ·
                  refine ⟨73237916911006817464889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3124817788202957545168597 73237916911006817464889)
                  ·
                    rfl

theorem cell23_1283673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 6, 7].length) (baseStart_1283673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1283673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1283673 prefixEnd_1283673 := by exact prefixLift 1283673
  have htrace : WordTrace (prefixWord ++ tailWord_1283673) baseStart_1283673 baseEnd_1283673 := by
    simpa [prefixWord, tailWord_1283673, baseEnd_1283673] using wordTrace_append hprefix tailTrace_1283673
  have hstable : (prefixWord ++ tailWord_1283673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1283673).length < 2 ^ (prefixWord ++ tailWord_1283673).sum := by decide
  have hdescent : baseEnd_1283673 < baseStart_1283673 := by decide
  rcases family_descends (prefixWord ++ tailWord_1283673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1283701 : List Nat := [1, 3, 4, 2, 1, 1, 1, 4, 2, 2, 2]
def baseStart_1283701 : Nat := 118140960795 + 1283701 * 2 ^ 59
def prefixEnd_1283701 : Nat := 4983230072969 + 3 ^ 40 * 1283701 * 2
def baseEnd_1283701 : Nat := 659155629657387247633873

theorem tailTrace_1283701 : CollatzResearch.WordTrace tailWord_1283701 prefixEnd_1283701 659155629657387247633873 := by
  unfold tailWord_1283701
  simp only [CollatzResearch.WordTrace]
  refine ⟨46820421922377990521426957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31213614614918660347617971 46820421922377990521426957)
  ·
    refine ⟨17557658220891746445535109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46820421922377990521426957 17557658220891746445535109)
    ·
      refine ⟨3292060916417202458537833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17557658220891746445535109 3292060916417202458537833)
      ·
        refine ⟨2469045687312901843903375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3292060916417202458537833 2469045687312901843903375)
        ·
          refine ⟨3703568530969352765855063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2469045687312901843903375 3703568530969352765855063)
          ·
            refine ⟨5555352796454029148782595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3703568530969352765855063 5555352796454029148782595)
            ·
              refine ⟨8333029194681043723173893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5555352796454029148782595 8333029194681043723173893)
              ·
                refine ⟨1562442974002695698095105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8333029194681043723173893 1562442974002695698095105)
                ·
                  refine ⟨1171832230502021773571329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1562442974002695698095105 1171832230502021773571329)
                  ·
                    refine ⟨878874172876516330178497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1171832230502021773571329 878874172876516330178497)
                    ·
                      refine ⟨659155629657387247633873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 878874172876516330178497 659155629657387247633873)
                      ·
                        rfl

theorem cell23_1283701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 1, 4, 2, 2, 2].length) (baseStart_1283701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1283701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1283701 prefixEnd_1283701 := by exact prefixLift 1283701
  have htrace : WordTrace (prefixWord ++ tailWord_1283701) baseStart_1283701 baseEnd_1283701 := by
    simpa [prefixWord, tailWord_1283701, baseEnd_1283701] using wordTrace_append hprefix tailTrace_1283701
  have hstable : (prefixWord ++ tailWord_1283701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1283701).length < 2 ^ (prefixWord ++ tailWord_1283701).sum := by decide
  have hdescent : baseEnd_1283701 < baseStart_1283701 := by decide
  rcases family_descends (prefixWord ++ tailWord_1283701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1283703 : List Nat := [1, 1, 3, 1, 1, 3, 1, 2, 3, 7]
def baseStart_1283703 : Nat := 118140960795 + 1283703 * 2 ^ 59
def prefixEnd_1283703 : Nat := 4983230072969 + 3 ^ 40 * 1283703 * 2
def baseEnd_1283703 : Nat := 219718885539565413269621

theorem tailTrace_1283703 : CollatzResearch.WordTrace tailWord_1283703 prefixEnd_1283703 219718885539565413269621 := by
  unfold tailWord_1283703
  simp only [CollatzResearch.WordTrace]
  refine ⟨46820494868370744862999763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31213663245580496575333175 46820494868370744862999763)
  ·
    refine ⟨70230742302556117294499645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46820494868370744862999763 70230742302556117294499645)
    ·
      refine ⟨26336528363458543985437367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 70230742302556117294499645 26336528363458543985437367)
      ·
        refine ⟨39504792545187815978156051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26336528363458543985437367 39504792545187815978156051)
        ·
          refine ⟨59257188817781723967234077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39504792545187815978156051 59257188817781723967234077)
          ·
            refine ⟨22221445806668146487712779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 59257188817781723967234077 22221445806668146487712779)
            ·
              refine ⟨33332168710002219731569169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22221445806668146487712779 33332168710002219731569169)
              ·
                refine ⟨24999126532501664798676877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33332168710002219731569169 24999126532501664798676877)
                ·
                  refine ⟨9374672449688124299503829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24999126532501664798676877 9374672449688124299503829)
                  ·
                    refine ⟨219718885539565413269621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 9374672449688124299503829 219718885539565413269621)
                    ·
                      rfl

theorem cell23_1283703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 2, 3, 7].length) (baseStart_1283703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1283703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1283703 prefixEnd_1283703 := by exact prefixLift 1283703
  have htrace : WordTrace (prefixWord ++ tailWord_1283703) baseStart_1283703 baseEnd_1283703 := by
    simpa [prefixWord, tailWord_1283703, baseEnd_1283703] using wordTrace_append hprefix tailTrace_1283703
  have hstable : (prefixWord ++ tailWord_1283703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1283703).length < 2 ^ (prefixWord ++ tailWord_1283703).sum := by decide
  have hdescent : baseEnd_1283703 < baseStart_1283703 := by decide
  rcases family_descends (prefixWord ++ tailWord_1283703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1283752 : List Nat := [2, 1, 7, 1, 1, 2, 1, 2, 2, 2, 2]
def baseStart_1283752 : Nat := 118140960795 + 1283752 * 2 ^ 59
def prefixEnd_1283752 : Nat := 4983230072969 + 3 ^ 40 * 1283752 * 2
def baseEnd_1283752 : Nat := 659181817170766548096139

theorem tailTrace_1283752 : CollatzResearch.WordTrace tailWord_1283752 prefixEnd_1283752 659181817170766548096139 := by
  unfold tailWord_1283752
  simp only [CollatzResearch.WordTrace]
  refine ⟨23411141022596613115766755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31214854696795484154355673 23411141022596613115766755)
  ·
    refine ⟨35116711533894919673650133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23411141022596613115766755 35116711533894919673650133)
    ·
      refine ⟨823047926575662179851175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 35116711533894919673650133 823047926575662179851175)
      ·
        refine ⟨1234571889863493269776763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 823047926575662179851175 1234571889863493269776763)
        ·
          refine ⟨1851857834795239904665145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1234571889863493269776763 1851857834795239904665145)
          ·
            refine ⟨1388893376096429928498859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1851857834795239904665145 1388893376096429928498859)
            ·
              refine ⟨2083340064144644892748289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1388893376096429928498859 2083340064144644892748289)
              ·
                refine ⟨1562505048108483669561217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2083340064144644892748289 1562505048108483669561217)
                ·
                  refine ⟨1171878786081362752170913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1562505048108483669561217 1171878786081362752170913)
                  ·
                    refine ⟨878909089561022064128185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1171878786081362752170913 878909089561022064128185)
                    ·
                      refine ⟨659181817170766548096139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 878909089561022064128185 659181817170766548096139)
                      ·
                        rfl

theorem cell23_1283752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 2, 1, 2, 2, 2, 2].length) (baseStart_1283752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1283752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1283752 prefixEnd_1283752 := by exact prefixLift 1283752
  have htrace : WordTrace (prefixWord ++ tailWord_1283752) baseStart_1283752 baseEnd_1283752 := by
    simpa [prefixWord, tailWord_1283752, baseEnd_1283752] using wordTrace_append hprefix tailTrace_1283752
  have hstable : (prefixWord ++ tailWord_1283752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1283752).length < 2 ^ (prefixWord ++ tailWord_1283752).sum := by decide
  have hdescent : baseEnd_1283752 < baseStart_1283752 := by decide
  rcases family_descends (prefixWord ++ tailWord_1283752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1283757 : List Nat := [1, 5, 2, 1, 1, 1, 2, 1, 4, 1, 4]
def baseStart_1283757 : Nat := 118140960795 + 1283757 * 2 ^ 59
def prefixEnd_1283757 : Nat := 4983230072969 + 3 ^ 40 * 1283757 * 2
def baseEnd_1283757 : Nat := 659184384574039028533615

theorem tailTrace_1283757 : CollatzResearch.WordTrace tailWord_1283757 prefixEnd_1283757 659184384574039028533615 := by
  unfold tailWord_1283757
  simp only [CollatzResearch.WordTrace]
  refine ⟨46822464410175112085465525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31214976273450074723643683 46822464410175112085465525)
  ·
    refine ⟨4389606038453916758012393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 46822464410175112085465525 4389606038453916758012393)
    ·
      refine ⟨3292204528840437568509295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4389606038453916758012393 3292204528840437568509295)
      ·
        refine ⟨4938306793260656352763943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3292204528840437568509295 4938306793260656352763943)
        ·
          refine ⟨7407460189890984529145915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4938306793260656352763943 7407460189890984529145915)
          ·
            refine ⟨11111190284836476793718873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7407460189890984529145915 11111190284836476793718873)
            ·
              refine ⟨8333392713627357595289155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11111190284836476793718873 8333392713627357595289155)
              ·
                refine ⟨12500089070441036392933733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8333392713627357595289155 12500089070441036392933733)
                ·
                  refine ⟨2343766700707694323675075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12500089070441036392933733 2343766700707694323675075)
                  ·
                    refine ⟨3515650051061541485512613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2343766700707694323675075 3515650051061541485512613)
                    ·
                      refine ⟨659184384574039028533615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3515650051061541485512613 659184384574039028533615)
                      ·
                        rfl

theorem cell23_1283757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 2, 1, 4, 1, 4].length) (baseStart_1283757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1283757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1283757 prefixEnd_1283757 := by exact prefixLift 1283757
  have htrace : WordTrace (prefixWord ++ tailWord_1283757) baseStart_1283757 baseEnd_1283757 := by
    simpa [prefixWord, tailWord_1283757, baseEnd_1283757] using wordTrace_append hprefix tailTrace_1283757
  have hstable : (prefixWord ++ tailWord_1283757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1283757).length < 2 ^ (prefixWord ++ tailWord_1283757).sum := by decide
  have hdescent : baseEnd_1283757 < baseStart_1283757 := by decide
  rcases family_descends (prefixWord ++ tailWord_1283757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1283767 : List Nat := [1, 1, 3, 1, 5, 1, 1, 3, 3, 4]
def baseStart_1283767 : Nat := 118140960795 + 1283767 * 2 ^ 59
def prefixEnd_1283767 : Nat := 4983230072969 + 3 ^ 40 * 1283767 * 2
def baseEnd_1283767 : Nat := 219729839793527996469523

theorem tailTrace_1283767 : CollatzResearch.WordTrace tailWord_1283767 prefixEnd_1283767 219729839793527996469523 := by
  unfold tailWord_1283767
  simp only [CollatzResearch.WordTrace]
  refine ⟨46822829140138883793329555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31215219426759255862219703 46822829140138883793329555)
  ·
    refine ⟨70234243710208325689994333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46822829140138883793329555 70234243710208325689994333)
    ·
      refine ⟨26337841391328122133747875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 70234243710208325689994333 26337841391328122133747875)
      ·
        refine ⟨39506762086992183200621813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26337841391328122133747875 39506762086992183200621813)
        ·
          refine ⟨3703758945655517175058295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 39506762086992183200621813 3703758945655517175058295)
          ·
            refine ⟨5555638418483275762587443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3703758945655517175058295 5555638418483275762587443)
            ·
              refine ⟨8333457627724913643881165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5555638418483275762587443 8333457627724913643881165)
              ·
                refine ⟨3125046610396842616455437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8333457627724913643881165 3125046610396842616455437)
                ·
                  refine ⟨1171892478898815981170789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3125046610396842616455437 1171892478898815981170789)
                  ·
                    refine ⟨219729839793527996469523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1171892478898815981170789 219729839793527996469523)
                    ·
                      rfl

theorem cell23_1283767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 1, 3, 3, 4].length) (baseStart_1283767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1283767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1283767 prefixEnd_1283767 := by exact prefixLift 1283767
  have htrace : WordTrace (prefixWord ++ tailWord_1283767) baseStart_1283767 baseEnd_1283767 := by
    simpa [prefixWord, tailWord_1283767, baseEnd_1283767] using wordTrace_append hprefix tailTrace_1283767
  have hstable : (prefixWord ++ tailWord_1283767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1283767).length < 2 ^ (prefixWord ++ tailWord_1283767).sum := by decide
  have hdescent : baseEnd_1283767 < baseStart_1283767 := by decide
  rcases family_descends (prefixWord ++ tailWord_1283767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1283774 : List Nat := [4, 2, 1, 1, 2, 2, 2, 1, 2, 4, 2]
def baseStart_1283774 : Nat := 118140960795 + 1283774 * 2 ^ 59
def prefixEnd_1283774 : Nat := 4983230072969 + 3 ^ 40 * 1283774 * 2
def baseEnd_1283774 : Nat := 659193113745165462021037

theorem tailTrace_1283774 : CollatzResearch.WordTrace tailWord_1283774 prefixEnd_1283774 659193113745165462021037 := by
  unfold tailWord_1283774
  simp only [CollatzResearch.WordTrace]
  refine ⟨5852885556389190498604297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 31215389634075682659222917 5852885556389190498604297)
  ·
    refine ⟨4389664167291892873953223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5852885556389190498604297 4389664167291892873953223)
    ·
      refine ⟨6584496250937839310929835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4389664167291892873953223 6584496250937839310929835)
      ·
        refine ⟨9876744376406758966394753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6584496250937839310929835 9876744376406758966394753)
        ·
          refine ⟨7407558282305069224796065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9876744376406758966394753 7407558282305069224796065)
          ·
            refine ⟨5555668711728801918597049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7407558282305069224796065 5555668711728801918597049)
            ·
              refine ⟨4166751533796601438947787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5555668711728801918597049 4166751533796601438947787)
              ·
                refine ⟨6250127300694902158421681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4166751533796601438947787 6250127300694902158421681)
                ·
                  refine ⟨4687595475521176618816261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6250127300694902158421681 4687595475521176618816261)
                  ·
                    refine ⟨878924151660220616028049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4687595475521176618816261 878924151660220616028049)
                    ·
                      refine ⟨659193113745165462021037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 878924151660220616028049 659193113745165462021037)
                      ·
                        rfl

theorem cell23_1283774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 2, 1, 2, 4, 2].length) (baseStart_1283774 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1283774 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1283774 prefixEnd_1283774 := by exact prefixLift 1283774
  have htrace : WordTrace (prefixWord ++ tailWord_1283774) baseStart_1283774 baseEnd_1283774 := by
    simpa [prefixWord, tailWord_1283774, baseEnd_1283774] using wordTrace_append hprefix tailTrace_1283774
  have hstable : (prefixWord ++ tailWord_1283774).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1283774).length < 2 ^ (prefixWord ++ tailWord_1283774).sum := by decide
  have hdescent : baseEnd_1283774 < baseStart_1283774 := by decide
  rcases family_descends (prefixWord ++ tailWord_1283774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1283801 : List Nat := [1, 2, 1, 2, 3, 5, 1, 3, 1, 4]
def baseStart_1283801 : Nat := 118140960795 + 1283801 * 2 ^ 59
def prefixEnd_1283801 : Nat := 4983230072969 + 3 ^ 40 * 1283801 * 2
def baseEnd_1283801 : Nat := 219735659240945618794471

theorem tailTrace_1283801 : CollatzResearch.WordTrace tailWord_1283801 prefixEnd_1283801 219735659240945618794471 := by
  unfold tailWord_1283801
  simp only [CollatzResearch.WordTrace]
  refine ⟨46824069222015707600067257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31216046148010471733378171 46824069222015707600067257)
  ·
    refine ⟨35118051916511780700050443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46824069222015707600067257 35118051916511780700050443)
    ·
      refine ⟨52677077874767671050075665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35118051916511780700050443 52677077874767671050075665)
      ·
        refine ⟨39507808406075753287556749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52677077874767671050075665 39507808406075753287556749)
        ·
          refine ⟨14815428152278407482833781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39507808406075753287556749 14815428152278407482833781)
          ·
            refine ⟨1388946389276100701515667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 14815428152278407482833781 1388946389276100701515667)
            ·
              refine ⟨2083419583914151052273501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1388946389276100701515667 2083419583914151052273501)
              ·
                refine ⟨781282343967806644602563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2083419583914151052273501 781282343967806644602563)
                ·
                  refine ⟨1171923515951709966903845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 781282343967806644602563 1171923515951709966903845)
                  ·
                    refine ⟨219735659240945618794471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1171923515951709966903845 219735659240945618794471)
                    ·
                      rfl

theorem cell23_1283801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 5, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 5, 1, 3, 1, 4].length) (baseStart_1283801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1283801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1283801 prefixEnd_1283801 := by exact prefixLift 1283801
  have htrace : WordTrace (prefixWord ++ tailWord_1283801) baseStart_1283801 baseEnd_1283801 := by
    simpa [prefixWord, tailWord_1283801, baseEnd_1283801] using wordTrace_append hprefix tailTrace_1283801
  have hstable : (prefixWord ++ tailWord_1283801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1283801).length < 2 ^ (prefixWord ++ tailWord_1283801).sum := by decide
  have hdescent : baseEnd_1283801 < baseStart_1283801 := by decide
  rcases family_descends (prefixWord ++ tailWord_1283801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1283844 : List Nat := [2, 3, 2, 2, 1, 2, 3, 2, 1, 5]
def baseStart_1283844 : Nat := 118140960795 + 1283844 * 2 ^ 59
def prefixEnd_1283844 : Nat := 4983230072969 + 3 ^ 40 * 1283844 * 2
def baseEnd_1283844 : Nat := 219743019130326729381905

theorem tailTrace_1283844 : CollatzResearch.WordTrace tailWord_1283844 prefixEnd_1283844 219743019130326729381905 := by
  unfold tailWord_1283844
  simp only [CollatzResearch.WordTrace]
  refine ⟨23412818780429962971941293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31217091707239950629255057 23412818780429962971941293)
  ·
    refine ⟨8779807042661236114477985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23412818780429962971941293 8779807042661236114477985)
    ·
      refine ⟨6584855281995927085858489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8779807042661236114477985 6584855281995927085858489)
      ·
        refine ⟨4938641461496945314393867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6584855281995927085858489 4938641461496945314393867)
        ·
          refine ⟨7407962192245417971590801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4938641461496945314393867 7407962192245417971590801)
          ·
            refine ⟨5555971644184063478693101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7407962192245417971590801 5555971644184063478693101)
            ·
              refine ⟨2083489366569023804509913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5555971644184063478693101 2083489366569023804509913)
              ·
                refine ⟨1562617024926767853382435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2083489366569023804509913 1562617024926767853382435)
                ·
                  refine ⟨2343925537390151780073653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1562617024926767853382435 2343925537390151780073653)
                  ·
                    refine ⟨219743019130326729381905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2343925537390151780073653 219743019130326729381905)
                    ·
                      rfl

theorem cell23_1283844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 3, 2, 1, 5].length) (baseStart_1283844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1283844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1283844 prefixEnd_1283844 := by exact prefixLift 1283844
  have htrace : WordTrace (prefixWord ++ tailWord_1283844) baseStart_1283844 baseEnd_1283844 := by
    simpa [prefixWord, tailWord_1283844, baseEnd_1283844] using wordTrace_append hprefix tailTrace_1283844
  have hstable : (prefixWord ++ tailWord_1283844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1283844).length < 2 ^ (prefixWord ++ tailWord_1283844).sum := by decide
  have hdescent : baseEnd_1283844 < baseStart_1283844 := by decide
  rcases family_descends (prefixWord ++ tailWord_1283844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1283914 : List Nat := [3, 1, 2, 1, 1, 1, 4, 2, 4, 1, 3]
def baseStart_1283914 : Nat := 118140960795 + 1283914 * 2 ^ 59
def prefixEnd_1283914 : Nat := 4983230072969 + 3 ^ 40 * 1283914 * 2
def baseEnd_1283914 : Nat := 659265001036794914270393

theorem tailTrace_1283914 : CollatzResearch.WordTrace tailWord_1283914 prefixEnd_1283914 659265001036794914270393 := by
  unfold tailWord_1283914
  simp only [CollatzResearch.WordTrace]
  refine ⟨11707047667651581974732699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31218793780404218599287197 11707047667651581974732699)
  ·
    refine ⟨17560571501477372962099049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11707047667651581974732699 17560571501477372962099049)
    ·
      refine ⟨13170428626108029721574287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17560571501477372962099049 13170428626108029721574287)
      ·
        refine ⟨19755642939162044582361431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13170428626108029721574287 19755642939162044582361431)
        ·
          refine ⟨29633464408743066873542147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19755642939162044582361431 29633464408743066873542147)
          ·
            refine ⟨44450196613114600310313221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29633464408743066873542147 44450196613114600310313221)
            ·
              refine ⟨8334411864958987558183729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 44450196613114600310313221 8334411864958987558183729)
              ·
                refine ⟨6250808898719240668637797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8334411864958987558183729 6250808898719240668637797)
                ·
                  refine ⟨1172026668509857625369587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6250808898719240668637797 1172026668509857625369587)
                  ·
                    refine ⟨1758040002764786438054381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1172026668509857625369587 1758040002764786438054381)
                    ·
                      refine ⟨659265001036794914270393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1758040002764786438054381 659265001036794914270393)
                      ·
                        rfl

theorem cell23_1283914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 4, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 4, 2, 4, 1, 3].length) (baseStart_1283914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1283914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1283914 prefixEnd_1283914 := by exact prefixLift 1283914
  have htrace : WordTrace (prefixWord ++ tailWord_1283914) baseStart_1283914 baseEnd_1283914 := by
    simpa [prefixWord, tailWord_1283914, baseEnd_1283914] using wordTrace_append hprefix tailTrace_1283914
  have hstable : (prefixWord ++ tailWord_1283914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1283914).length < 2 ^ (prefixWord ++ tailWord_1283914).sum := by decide
  have hdescent : baseEnd_1283914 < baseStart_1283914 := by decide
  rcases family_descends (prefixWord ++ tailWord_1283914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1283948 : List Nat := [2, 2, 1, 1, 4, 3, 3, 1, 2, 1, 3]
def baseStart_1283948 : Nat := 118140960795 + 1283948 * 2 ^ 59
def prefixEnd_1283948 : Nat := 4983230072969 + 3 ^ 40 * 1283948 * 2
def baseEnd_1283948 : Nat := 659282459379047781245237

theorem tailTrace_1283948 : CollatzResearch.WordTrace tailWord_1283948 prefixEnd_1283948 659282459379047781245237 := by
  unfold tailWord_1283948
  simp only [CollatzResearch.WordTrace]
  refine ⟨23414715376241575852834249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31219620501655434470445665 23414715376241575852834249)
  ·
    refine ⟨17561036532181181889625687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23414715376241575852834249 17561036532181181889625687)
    ·
      refine ⟨26341554798271772834438531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17561036532181181889625687 26341554798271772834438531)
      ·
        refine ⟨39512332197407659251657797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26341554798271772834438531 39512332197407659251657797)
        ·
          refine ⟨7408562287013936109685837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 39512332197407659251657797 7408562287013936109685837)
          ·
            refine ⟨2778210857630226041132189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7408562287013936109685837 2778210857630226041132189)
            ·
              refine ⟨1041829071611334765424571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2778210857630226041132189 1041829071611334765424571)
              ·
                refine ⟨1562743607417002148136857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1041829071611334765424571 1562743607417002148136857)
                ·
                  refine ⟨1172057705562751611102643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1562743607417002148136857 1172057705562751611102643)
                  ·
                    refine ⟨1758086558344127416653965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1172057705562751611102643 1758086558344127416653965)
                    ·
                      refine ⟨659282459379047781245237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1758086558344127416653965 659282459379047781245237)
                      ·
                        rfl

theorem cell23_1283948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 2, 1, 3].length) (baseStart_1283948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1283948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1283948 prefixEnd_1283948 := by exact prefixLift 1283948
  have htrace : WordTrace (prefixWord ++ tailWord_1283948) baseStart_1283948 baseEnd_1283948 := by
    simpa [prefixWord, tailWord_1283948, baseEnd_1283948] using wordTrace_append hprefix tailTrace_1283948
  have hstable : (prefixWord ++ tailWord_1283948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1283948).length < 2 ^ (prefixWord ++ tailWord_1283948).sum := by decide
  have hdescent : baseEnd_1283948 < baseStart_1283948 := by decide
  rcases family_descends (prefixWord ++ tailWord_1283948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1283971 : List Nat := [1, 1, 1, 3, 4, 2, 1, 2, 4, 2, 2]
def baseStart_1283971 : Nat := 118140960795 + 1283971 * 2 ^ 59
def prefixEnd_1283971 : Nat := 4983230072969 + 3 ^ 40 * 1283971 * 2
def baseEnd_1283971 : Nat := 659294269434101191257631

theorem tailTrace_1283971 : CollatzResearch.WordTrace tailWord_1283971 prefixEnd_1283971 659294269434101191257631 := by
  unfold tailWord_1283971
  simp only [CollatzResearch.WordTrace]
  refine ⟨46830269631399826633755767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31220179754266551089170511 46830269631399826633755767)
  ·
    refine ⟨70245404447099739950633651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46830269631399826633755767 70245404447099739950633651)
    ·
      refine ⟨105368106670649609925950477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70245404447099739950633651 105368106670649609925950477)
      ·
        refine ⟨39513040001493603722231429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 105368106670649609925950477 39513040001493603722231429)
        ·
          refine ⟨7408695000280050697918393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 39513040001493603722231429 7408695000280050697918393)
          ·
            refine ⟨5556521250210038023438795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7408695000280050697918393 5556521250210038023438795)
            ·
              refine ⟨8334781875315057035158193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5556521250210038023438795 8334781875315057035158193)
              ·
                refine ⟨6251086406486292776368645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8334781875315057035158193 6251086406486292776368645)
                ·
                  refine ⟨1172078701216179895569121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6251086406486292776368645 1172078701216179895569121)
                  ·
                    refine ⟨879059025912134921676841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1172078701216179895569121 879059025912134921676841)
                    ·
                      refine ⟨659294269434101191257631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 879059025912134921676841 659294269434101191257631)
                      ·
                        rfl

theorem cell23_1283971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 1, 2, 4, 2, 2].length) (baseStart_1283971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1283971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1283971 prefixEnd_1283971 := by exact prefixLift 1283971
  have htrace : WordTrace (prefixWord ++ tailWord_1283971) baseStart_1283971 baseEnd_1283971 := by
    simpa [prefixWord, tailWord_1283971, baseEnd_1283971] using wordTrace_append hprefix tailTrace_1283971
  have hstable : (prefixWord ++ tailWord_1283971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1283971).length < 2 ^ (prefixWord ++ tailWord_1283971).sum := by decide
  have hdescent : baseEnd_1283971 < baseStart_1283971 := by decide
  rcases family_descends (prefixWord ++ tailWord_1283971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1283988 : List Nat := [2, 4, 2, 1, 1, 2, 2, 1, 4, 2, 2]
def baseStart_1283988 : Nat := 118140960795 + 1283988 * 2 ^ 59
def prefixEnd_1283988 : Nat := 4983230072969 + 3 ^ 40 * 1283988 * 2
def baseEnd_1283988 : Nat := 659302998605227624745053

theorem tailTrace_1283988 : CollatzResearch.WordTrace tailWord_1283988 prefixEnd_1283988 659302998605227624745053 := by
  unfold tailWord_1283988
  simp only [CollatzResearch.WordTrace]
  refine ⟨23415444836169119268562309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31220593114892159024749745 23415444836169119268562309)
  ·
    refine ⟨4390395906781709862855433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23415444836169119268562309 4390395906781709862855433)
    ·
      refine ⟨3292796930086282397141575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4390395906781709862855433 3292796930086282397141575)
      ·
        refine ⟨4939195395129423595712363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3292796930086282397141575 4939195395129423595712363)
        ·
          refine ⟨7408793092694135393568545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4939195395129423595712363 7408793092694135393568545)
          ·
            refine ⟨5556594819520601545176409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7408793092694135393568545 5556594819520601545176409)
            ·
              refine ⟨4167446114640451158882307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5556594819520601545176409 4167446114640451158882307)
              ·
                refine ⟨6251169171960676738323461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4167446114640451158882307 6251169171960676738323461)
                ·
                  refine ⟨1172094219742626888435649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6251169171960676738323461 1172094219742626888435649)
                  ·
                    refine ⟨879070664806970166326737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1172094219742626888435649 879070664806970166326737)
                    ·
                      refine ⟨659302998605227624745053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 879070664806970166326737 659302998605227624745053)
                      ·
                        rfl

theorem cell23_1283988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 2, 1, 4, 2, 2].length) (baseStart_1283988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1283988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1283988 prefixEnd_1283988 := by exact prefixLift 1283988
  have htrace : WordTrace (prefixWord ++ tailWord_1283988) baseStart_1283988 baseEnd_1283988 := by
    simpa [prefixWord, tailWord_1283988, baseEnd_1283988] using wordTrace_append hprefix tailTrace_1283988
  have hstable : (prefixWord ++ tailWord_1283988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1283988).length < 2 ^ (prefixWord ++ tailWord_1283988).sum := by decide
  have hdescent : baseEnd_1283988 < baseStart_1283988 := by decide
  rcases family_descends (prefixWord ++ tailWord_1283988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1283994 : List Nat := [3, 1, 1, 4, 2, 1, 3, 1, 7]
def baseStart_1283994 : Nat := 118140960795 + 1283994 * 2 ^ 59
def prefixEnd_1283994 : Nat := 4983230072969 + 3 ^ 40 * 1283994 * 2
def baseEnd_1283994 : Nat := 73256231054350511252225

theorem tailTrace_1283994 : CollatzResearch.WordTrace tailWord_1283994 prefixEnd_1283994 73256231054350511252225 := by
  unfold tailWord_1283994
  simp only [CollatzResearch.WordTrace]
  refine ⟨11707777127579125390460759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31220739006877667707895357 11707777127579125390460759)
  ·
    refine ⟨17561665691368688085691139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11707777127579125390460759 17561665691368688085691139)
    ·
      refine ⟨26342498537053032128536709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17561665691368688085691139 26342498537053032128536709)
      ·
        refine ⟨4939218475697443524100633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26342498537053032128536709 4939218475697443524100633)
        ·
          refine ⟨3704413856773082643075475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4939218475697443524100633 3704413856773082643075475)
          ·
            refine ⟨5556620785159623964613213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3704413856773082643075475 5556620785159623964613213)
            ·
              refine ⟨2083732794434858986729955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5556620785159623964613213 2083732794434858986729955)
              ·
                refine ⟨3125599191652288480094933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2083732794434858986729955 3125599191652288480094933)
                ·
                  refine ⟨73256231054350511252225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3125599191652288480094933 73256231054350511252225)
                  ·
                    rfl

theorem cell23_1283994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 3, 1, 7].length) (baseStart_1283994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1283994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1283994 prefixEnd_1283994 := by exact prefixLift 1283994
  have htrace : WordTrace (prefixWord ++ tailWord_1283994) baseStart_1283994 baseEnd_1283994 := by
    simpa [prefixWord, tailWord_1283994, baseEnd_1283994] using wordTrace_append hprefix tailTrace_1283994
  have hstable : (prefixWord ++ tailWord_1283994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1283994).length < 2 ^ (prefixWord ++ tailWord_1283994).sum := by decide
  have hdescent : baseEnd_1283994 < baseStart_1283994 := by decide
  rcases family_descends (prefixWord ++ tailWord_1283994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1284024 : List Nat := [2, 1, 2, 1, 2, 3, 4, 1, 2, 5]
def baseStart_1284024 : Nat := 118140960795 + 1284024 * 2 ^ 59
def prefixEnd_1284024 : Nat := 4983230072969 + 3 ^ 40 * 1284024 * 2
def baseEnd_1284024 : Nat := 219773827969596494631629

theorem tailTrace_1284024 : CollatzResearch.WordTrace tailWord_1284024 prefixEnd_1284024 219773827969596494631629 := by
  unfold tailWord_1284024
  simp only [CollatzResearch.WordTrace]
  refine ⟨23416101350103908342717563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31221468466805211123623417 23416101350103908342717563)
  ·
    refine ⟨35124152025155862514076345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23416101350103908342717563 35124152025155862514076345)
    ·
      refine ⟨26343114018866896885557259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35124152025155862514076345 26343114018866896885557259)
      ·
        refine ⟨39514671028300345328335889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26343114018866896885557259 39514671028300345328335889)
        ·
          refine ⟨29636003271225258996251917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39514671028300345328335889 29636003271225258996251917)
          ·
            refine ⟨11113501226709472123594469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29636003271225258996251917 11113501226709472123594469)
            ·
              refine ⟨2083781480008026023173963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11113501226709472123594469 2083781480008026023173963)
              ·
                refine ⟨3125672220012039034760945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2083781480008026023173963 3125672220012039034760945)
                ·
                  refine ⟨2344254165009029276070709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3125672220012039034760945 2344254165009029276070709)
                  ·
                    refine ⟨219773827969596494631629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2344254165009029276070709 219773827969596494631629)
                    ·
                      rfl

theorem cell23_1284024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 4, 1, 2, 5].length) (baseStart_1284024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1284024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1284024 prefixEnd_1284024 := by exact prefixLift 1284024
  have htrace : WordTrace (prefixWord ++ tailWord_1284024) baseStart_1284024 baseEnd_1284024 := by
    simpa [prefixWord, tailWord_1284024, baseEnd_1284024] using wordTrace_append hprefix tailTrace_1284024
  have hstable : (prefixWord ++ tailWord_1284024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1284024).length < 2 ^ (prefixWord ++ tailWord_1284024).sum := by decide
  have hdescent : baseEnd_1284024 < baseStart_1284024 := by decide
  rcases family_descends (prefixWord ++ tailWord_1284024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1284047 : List Nat := [1, 1, 2, 1, 1, 5, 1, 1, 2, 3, 5]
def baseStart_1284047 : Nat := 118140960795 + 1284047 * 2 ^ 59
def prefixEnd_1284047 : Nat := 4983230072969 + 3 ^ 40 * 1284047 * 2
def baseEnd_1284047 : Nat := 659333293963842893907281

theorem tailTrace_1284047 : CollatzResearch.WordTrace tailWord_1284047 prefixEnd_1284047 659333293963842893907281 := by
  unfold tailWord_1284047
  simp only [CollatzResearch.WordTrace]
  refine ⟨46833041579124491613522395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31222027719416327742348263 46833041579124491613522395)
  ·
    refine ⟨70249562368686737420283593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46833041579124491613522395 70249562368686737420283593)
    ·
      refine ⟨52687171776515053065212695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70249562368686737420283593 52687171776515053065212695)
      ·
        refine ⟨79030757664772579597819043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52687171776515053065212695 79030757664772579597819043)
        ·
          refine ⟨118546136497158869396728565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79030757664772579597819043 118546136497158869396728565)
          ·
            refine ⟨11113700296608644005943303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 118546136497158869396728565 11113700296608644005943303)
            ·
              refine ⟨16670550444912966008914955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11113700296608644005943303 16670550444912966008914955)
              ·
                refine ⟨25005825667369449013372433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16670550444912966008914955 25005825667369449013372433)
                ·
                  refine ⟨18754369250527086760029325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25005825667369449013372433 18754369250527086760029325)
                  ·
                    refine ⟨7032888468947657535010997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18754369250527086760029325 7032888468947657535010997)
                    ·
                      refine ⟨659333293963842893907281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7032888468947657535010997 659333293963842893907281)
                      ·
                        rfl

theorem cell23_1284047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 1, 2, 3, 5].length) (baseStart_1284047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1284047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1284047 prefixEnd_1284047 := by exact prefixLift 1284047
  have htrace : WordTrace (prefixWord ++ tailWord_1284047) baseStart_1284047 baseEnd_1284047 := by
    simpa [prefixWord, tailWord_1284047, baseEnd_1284047] using wordTrace_append hprefix tailTrace_1284047
  have hstable : (prefixWord ++ tailWord_1284047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1284047).length < 2 ^ (prefixWord ++ tailWord_1284047).sum := by decide
  have hdescent : baseEnd_1284047 < baseStart_1284047 := by decide
  rcases family_descends (prefixWord ++ tailWord_1284047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1284064 : List Nat := [2, 1, 1, 3, 1, 1, 1, 4, 4, 2, 3]
def baseStart_1284064 : Nat := 118140960795 + 1284064 * 2 ^ 59
def prefixEnd_1284064 : Nat := 4983230072969 + 3 ^ 40 * 1284064 * 2
def baseEnd_1284064 : Nat := 659342023134969327394703

theorem tailTrace_1284064 : CollatzResearch.WordTrace tailWord_1284064 prefixEnd_1284064 659342023134969327394703 := by
  unfold tailWord_1284064
  simp only [CollatzResearch.WordTrace]
  refine ⟨23416830810031451758445623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31222441080041935677927497 23416830810031451758445623)
  ·
    refine ⟨35125246215047177637668435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23416830810031451758445623 35125246215047177637668435)
    ·
      refine ⟨52687869322570766456502653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35125246215047177637668435 52687869322570766456502653)
      ·
        refine ⟨19757950995964037421188495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52687869322570766456502653 19757950995964037421188495)
        ·
          refine ⟨29636926493946056131782743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19757950995964037421188495 29636926493946056131782743)
          ·
            refine ⟨44455389740919084197674115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29636926493946056131782743 44455389740919084197674115)
            ·
              refine ⟨66683084611378626296511173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44455389740919084197674115 66683084611378626296511173)
              ·
                refine ⟨12503078364633492430595845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 66683084611378626296511173 12503078364633492430595845)
                ·
                  refine ⟨2344327193368779830736721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12503078364633492430595845 2344327193368779830736721)
                  ·
                    refine ⟨1758245395026584873052541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2344327193368779830736721 1758245395026584873052541)
                    ·
                      refine ⟨659342023134969327394703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1758245395026584873052541 659342023134969327394703)
                      ·
                        rfl

theorem cell23_1284064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 4, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 4, 4, 2, 3].length) (baseStart_1284064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1284064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1284064 prefixEnd_1284064 := by exact prefixLift 1284064
  have htrace : WordTrace (prefixWord ++ tailWord_1284064) baseStart_1284064 baseEnd_1284064 := by
    simpa [prefixWord, tailWord_1284064, baseEnd_1284064] using wordTrace_append hprefix tailTrace_1284064
  have hstable : (prefixWord ++ tailWord_1284064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1284064).length < 2 ^ (prefixWord ++ tailWord_1284064).sum := by decide
  have hdescent : baseEnd_1284064 < baseStart_1284064 := by decide
  rcases family_descends (prefixWord ++ tailWord_1284064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1284078 : List Nat := [4, 1, 2, 1, 3, 3, 1, 1, 2, 1, 4]
def baseStart_1284078 : Nat := 118140960795 + 1284078 * 2 ^ 59
def prefixEnd_1284078 : Nat := 4983230072969 + 3 ^ 40 * 1284078 * 2
def baseEnd_1284078 : Nat := 659349211864132272619639

theorem tailTrace_1284078 : CollatzResearch.WordTrace tailWord_1284078 prefixEnd_1284078 659349211864132272619639 := by
  unfold tailWord_1284078
  simp only [CollatzResearch.WordTrace]
  refine ⟨5854271530251522988487611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 31222781494674789271933925 5854271530251522988487611)
  ·
    refine ⟨8781407295377284482731417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5854271530251522988487611 8781407295377284482731417)
    ·
      refine ⟨6586055471532963362048563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8781407295377284482731417 6586055471532963362048563)
      ·
        refine ⟨9879083207299445043072845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6586055471532963362048563 9879083207299445043072845)
        ·
          refine ⟨3704656202737291891152317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9879083207299445043072845 3704656202737291891152317)
          ·
            refine ⟨1389246076026484459182119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3704656202737291891152317 1389246076026484459182119)
            ·
              refine ⟨2083869114039726688773179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1389246076026484459182119 2083869114039726688773179)
              ·
                refine ⟨3125803671059590033159769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2083869114039726688773179 3125803671059590033159769)
                ·
                  refine ⟨2344352753294692524869827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3125803671059590033159769 2344352753294692524869827)
                  ·
                    refine ⟨3516529129942038787304741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2344352753294692524869827 3516529129942038787304741)
                    ·
                      refine ⟨659349211864132272619639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3516529129942038787304741 659349211864132272619639)
                      ·
                        rfl

theorem cell23_1284078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 3, 1, 1, 2, 1, 4].length) (baseStart_1284078 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1284078 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1284078 prefixEnd_1284078 := by exact prefixLift 1284078
  have htrace : WordTrace (prefixWord ++ tailWord_1284078) baseStart_1284078 baseEnd_1284078 := by
    simpa [prefixWord, tailWord_1284078, baseEnd_1284078] using wordTrace_append hprefix tailTrace_1284078
  have hstable : (prefixWord ++ tailWord_1284078).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1284078).length < 2 ^ (prefixWord ++ tailWord_1284078).sum := by decide
  have hdescent : baseEnd_1284078 < baseStart_1284078 := by decide
  rcases family_descends (prefixWord ++ tailWord_1284078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1284081 : List Nat := [1, 2, 2, 2, 5, 1, 1, 1, 1, 4, 3]
def baseStart_1284081 : Nat := 118140960795 + 1284081 * 2 ^ 59
def prefixEnd_1284081 : Nat := 4983230072969 + 3 ^ 40 * 1284081 * 2
def baseEnd_1284081 : Nat := 659350752306095760882125

theorem tailTrace_1284081 : CollatzResearch.WordTrace tailWord_1284081 prefixEnd_1284081 659350752306095760882125 := by
  unfold tailWord_1284081
  simp only [CollatzResearch.WordTrace]
  refine ⟨46834281661001315420260097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31222854440667543613506731 46834281661001315420260097)
  ·
    refine ⟨35125711245750986565195073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46834281661001315420260097 35125711245750986565195073)
    ·
      refine ⟨26344283434313239923896305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35125711245750986565195073 26344283434313239923896305)
      ·
        refine ⟨19758212575734929942922229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26344283434313239923896305 19758212575734929942922229)
        ·
          refine ⟨1852332428975149682148959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 19758212575734929942922229 1852332428975149682148959)
          ·
            refine ⟨2778498643462724523223439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1852332428975149682148959 2778498643462724523223439)
            ·
              refine ⟨4167747965194086784835159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2778498643462724523223439 4167747965194086784835159)
              ·
                refine ⟨6251621947791130177252739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4167747965194086784835159 6251621947791130177252739)
                ·
                  refine ⟨9377432921686695265879109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6251621947791130177252739 9377432921686695265879109)
                  ·
                    refine ⟨1758268672816255362352333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9377432921686695265879109 1758268672816255362352333)
                    ·
                      refine ⟨659350752306095760882125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1758268672816255362352333 659350752306095760882125)
                      ·
                        rfl

theorem cell23_1284081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 1, 1, 1, 4, 3].length) (baseStart_1284081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1284081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1284081 prefixEnd_1284081 := by exact prefixLift 1284081
  have htrace : WordTrace (prefixWord ++ tailWord_1284081) baseStart_1284081 baseEnd_1284081 := by
    simpa [prefixWord, tailWord_1284081, baseEnd_1284081] using wordTrace_append hprefix tailTrace_1284081
  have hstable : (prefixWord ++ tailWord_1284081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1284081).length < 2 ^ (prefixWord ++ tailWord_1284081).sum := by decide
  have hdescent : baseEnd_1284081 < baseStart_1284081 := by decide
  rcases family_descends (prefixWord ++ tailWord_1284081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1284087 : List Nat := [1, 1, 3, 1, 1, 1, 1, 1, 5, 2, 6]
def baseStart_1284087 : Nat := 118140960795 + 1284087 * 2 ^ 59
def prefixEnd_1284087 : Nat := 4983230072969 + 3 ^ 40 * 1284087 * 2
def baseEnd_1284087 : Nat := 659353833190022737407097

theorem tailTrace_1284087 : CollatzResearch.WordTrace tailWord_1284087 prefixEnd_1284087 659353833190022737407097 := by
  unfold tailWord_1284087
  simp only [CollatzResearch.WordTrace]
  refine ⟨46834500498979578444978515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31223000332653052296652343 46834500498979578444978515)
  ·
    refine ⟨70251750748469367667467773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46834500498979578444978515 70251750748469367667467773)
    ·
      refine ⟨26344406530676012875300415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 70251750748469367667467773 26344406530676012875300415)
      ·
        refine ⟨39516609796014019312950623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26344406530676012875300415 39516609796014019312950623)
        ·
          refine ⟨59274914694021028969425935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39516609796014019312950623 59274914694021028969425935)
          ·
            refine ⟨88912372041031543454138903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59274914694021028969425935 88912372041031543454138903)
            ·
              refine ⟨133368558061547315181208355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 88912372041031543454138903 133368558061547315181208355)
              ·
                refine ⟨200052837092320972771812533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 133368558061547315181208355 200052837092320972771812533)
                ·
                  refine ⟨18754953477405091197357425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 200052837092320972771812533 18754953477405091197357425)
                  ·
                    refine ⟨14066215108053818398018069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18754953477405091197357425 14066215108053818398018069)
                    ·
                      refine ⟨659353833190022737407097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 14066215108053818398018069 659353833190022737407097)
                      ·
                        rfl

theorem cell23_1284087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 5, 2, 6].length) (baseStart_1284087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1284087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1284087 prefixEnd_1284087 := by exact prefixLift 1284087
  have htrace : WordTrace (prefixWord ++ tailWord_1284087) baseStart_1284087 baseEnd_1284087 := by
    simpa [prefixWord, tailWord_1284087, baseEnd_1284087] using wordTrace_append hprefix tailTrace_1284087
  have hstable : (prefixWord ++ tailWord_1284087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1284087).length < 2 ^ (prefixWord ++ tailWord_1284087).sum := by decide
  have hdescent : baseEnd_1284087 < baseStart_1284087 := by decide
  rcases family_descends (prefixWord ++ tailWord_1284087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1284101 : List Nat := [1, 3, 1, 1, 2, 6, 1, 2, 6]
def baseStart_1284101 : Nat := 118140960795 + 1284101 * 2 ^ 59
def prefixEnd_1284101 : Nat := 4983230072969 + 3 ^ 40 * 1284101 * 2
def baseEnd_1284101 : Nat := 73262335768798409181337

theorem tailTrace_1284101 : CollatzResearch.WordTrace tailWord_1284101 prefixEnd_1284101 73262335768798409181337 := by
  unfold tailWord_1284101
  simp only [CollatzResearch.WordTrace]
  refine ⟨46835011120928858835988157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31223340747285905890658771 46835011120928858835988157)
  ·
    refine ⟨17563129170348322063495559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46835011120928858835988157 17563129170348322063495559)
    ·
      refine ⟨26344693755522483095243339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17563129170348322063495559 26344693755522483095243339)
      ·
        refine ⟨39517040633283724642865009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26344693755522483095243339 39517040633283724642865009)
        ·
          refine ⟨29637780474962793482148757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39517040633283724642865009 29637780474962793482148757)
          ·
            refine ⟨1389270959763880944475723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 29637780474962793482148757 1389270959763880944475723)
            ·
              refine ⟨2083906439645821416713585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1389270959763880944475723 2083906439645821416713585)
              ·
                refine ⟨1562929829734366062535189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2083906439645821416713585 1562929829734366062535189)
                ·
                  refine ⟨73262335768798409181337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1562929829734366062535189 73262335768798409181337)
                  ·
                    rfl

theorem cell23_1284101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 6, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 6, 1, 2, 6].length) (baseStart_1284101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1284101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1284101 prefixEnd_1284101 := by exact prefixLift 1284101
  have htrace : WordTrace (prefixWord ++ tailWord_1284101) baseStart_1284101 baseEnd_1284101 := by
    simpa [prefixWord, tailWord_1284101, baseEnd_1284101] using wordTrace_append hprefix tailTrace_1284101
  have hstable : (prefixWord ++ tailWord_1284101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1284101).length < 2 ^ (prefixWord ++ tailWord_1284101).sum := by decide
  have hdescent : baseEnd_1284101 < baseStart_1284101 := by decide
  rcases family_descends (prefixWord ++ tailWord_1284101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1284131 : List Nat := [1, 1, 1, 4, 3, 1, 4, 2, 1, 5]
def baseStart_1284131 : Nat := 118140960795 + 1284131 * 2 ^ 59
def prefixEnd_1284131 : Nat := 4983230072969 + 3 ^ 40 * 1284131 * 2
def baseEnd_1284131 : Nat := 219792142112940188418965

theorem tailTrace_1284131 : CollatzResearch.WordTrace tailWord_1284131 prefixEnd_1284131 219792142112940188418965 := by
  unfold tailWord_1284131
  simp only [CollatzResearch.WordTrace]
  refine ⟨46836105310820173959580247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31224070207213449306386831 46836105310820173959580247)
  ·
    refine ⟨70254157966230260939370371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46836105310820173959580247 70254157966230260939370371)
    ·
      refine ⟨105381236949345391409055557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70254157966230260939370371 105381236949345391409055557)
      ·
        refine ⟨19758981928002260889197917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 105381236949345391409055557 19758981928002260889197917)
        ·
          refine ⟨7409618223000847833449219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19758981928002260889197917 7409618223000847833449219)
          ·
            refine ⟨11114427334501271750173829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7409618223000847833449219 11114427334501271750173829)
            ·
              refine ⟨2083955125218988453157593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11114427334501271750173829 2083955125218988453157593)
              ·
                refine ⟨1562966343914241339868195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2083955125218988453157593 1562966343914241339868195)
                ·
                  refine ⟨2344449515871362009802293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1562966343914241339868195 2344449515871362009802293)
                  ·
                    refine ⟨219792142112940188418965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2344449515871362009802293 219792142112940188418965)
                    ·
                      rfl

theorem cell23_1284131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 4, 2, 1, 5].length) (baseStart_1284131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1284131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1284131 prefixEnd_1284131 := by exact prefixLift 1284131
  have htrace : WordTrace (prefixWord ++ tailWord_1284131) baseStart_1284131 baseEnd_1284131 := by
    simpa [prefixWord, tailWord_1284131, baseEnd_1284131] using wordTrace_append hprefix tailTrace_1284131
  have hstable : (prefixWord ++ tailWord_1284131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1284131).length < 2 ^ (prefixWord ++ tailWord_1284131).sum := by decide
  have hdescent : baseEnd_1284131 < baseStart_1284131 := by decide
  rcases family_descends (prefixWord ++ tailWord_1284131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1284138 : List Nat := [3, 1, 4, 1, 2, 1, 2, 1, 1, 5, 2]
def baseStart_1284138 : Nat := 118140960795 + 1284138 * 2 ^ 59
def prefixEnd_1284138 : Nat := 4983230072969 + 3 ^ 40 * 1284138 * 2
def baseEnd_1284138 : Nat := 659380020703402037869363

theorem tailTrace_1284138 : CollatzResearch.WordTrace tailWord_1284138 prefixEnd_1284138 659380020703402037869363 := by
  unfold tailWord_1284138
  simp only [CollatzResearch.WordTrace]
  refine ⟨11709090155448703538771267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31224240414529876103390045 11709090155448703538771267)
  ·
    refine ⟨17563635233173055308156901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11709090155448703538771267 17563635233173055308156901)
    ·
      refine ⟨3293181606219947870279419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17563635233173055308156901 3293181606219947870279419)
      ·
        refine ⟨4939772409329921805419129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3293181606219947870279419 4939772409329921805419129)
        ·
          refine ⟨3704829306997441354064347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4939772409329921805419129 3704829306997441354064347)
          ·
            refine ⟨5557243960496162031096521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3704829306997441354064347 5557243960496162031096521)
            ·
              refine ⟨4167932970372121523322391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5557243960496162031096521 4167932970372121523322391)
              ·
                refine ⟨6251899455558182284983587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4167932970372121523322391 6251899455558182284983587)
                ·
                  refine ⟨9377849183337273427475381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6251899455558182284983587 9377849183337273427475381)
                  ·
                    refine ⟨879173360937869383825817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9377849183337273427475381 879173360937869383825817)
                    ·
                      refine ⟨659380020703402037869363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 879173360937869383825817 659380020703402037869363)
                      ·
                        rfl

theorem cell23_1284138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 2, 1, 1, 5, 2].length) (baseStart_1284138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1284138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1284138 prefixEnd_1284138 := by exact prefixLift 1284138
  have htrace : WordTrace (prefixWord ++ tailWord_1284138) baseStart_1284138 baseEnd_1284138 := by
    simpa [prefixWord, tailWord_1284138, baseEnd_1284138] using wordTrace_append hprefix tailTrace_1284138
  have hstable : (prefixWord ++ tailWord_1284138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1284138).length < 2 ^ (prefixWord ++ tailWord_1284138).sum := by decide
  have hdescent : baseEnd_1284138 < baseStart_1284138 := by decide
  rcases family_descends (prefixWord ++ tailWord_1284138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1284145 : List Nat := [1, 2, 2, 3, 1, 3, 3, 3, 1, 1, 3]
def baseStart_1284145 : Nat := 118140960795 + 1284145 * 2 ^ 59
def prefixEnd_1284145 : Nat := 4983230072969 + 3 ^ 40 * 1284145 * 2
def baseEnd_1284145 : Nat := 659383615067983510481831

theorem tailTrace_1284145 : CollatzResearch.WordTrace tailWord_1284145 prefixEnd_1284145 659383615067983510481831 := by
  unfold tailWord_1284145
  simp only [CollatzResearch.WordTrace]
  refine ⟨46836615932769454350589889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31224410621846302900393259 46836615932769454350589889)
  ·
    refine ⟨35127461949577090762942417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46836615932769454350589889 35127461949577090762942417)
    ·
      refine ⟨26345596462182818072206813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35127461949577090762942417 26345596462182818072206813)
      ·
        refine ⟨9879598673318556777077555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26345596462182818072206813 9879598673318556777077555)
        ·
          refine ⟨14819398009977835165616333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9879598673318556777077555 14819398009977835165616333)
          ·
            refine ⟨5557274253741688187106125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14819398009977835165616333 5557274253741688187106125)
            ·
              refine ⟨2083977845153133070164797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5557274253741688187106125 2083977845153133070164797)
              ·
                refine ⟨781491691932424901311799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2083977845153133070164797 781491691932424901311799)
                ·
                  refine ⟨1172237537898637351967699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 781491691932424901311799 1172237537898637351967699)
                  ·
                    refine ⟨1758356306847956027951549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1172237537898637351967699 1758356306847956027951549)
                    ·
                      refine ⟨659383615067983510481831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1758356306847956027951549 659383615067983510481831)
                      ·
                        rfl

theorem cell23_1284145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 3, 3, 1, 1, 3].length) (baseStart_1284145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1284145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1284145 prefixEnd_1284145 := by exact prefixLift 1284145
  have htrace : WordTrace (prefixWord ++ tailWord_1284145) baseStart_1284145 baseEnd_1284145 := by
    simpa [prefixWord, tailWord_1284145, baseEnd_1284145] using wordTrace_append hprefix tailTrace_1284145
  have hstable : (prefixWord ++ tailWord_1284145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1284145).length < 2 ^ (prefixWord ++ tailWord_1284145).sum := by decide
  have hdescent : baseEnd_1284145 < baseStart_1284145 := by decide
  rcases family_descends (prefixWord ++ tailWord_1284145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1284151 : List Nat := [1, 1, 3, 1, 2, 2, 4, 3, 1, 1, 4]
def baseStart_1284151 : Nat := 118140960795 + 1284151 * 2 ^ 59
def prefixEnd_1284151 : Nat := 4983230072969 + 3 ^ 40 * 1284151 * 2
def baseEnd_1284151 : Nat := 659386695951910487006803

theorem tailTrace_1284151 : CollatzResearch.WordTrace tailWord_1284151 prefixEnd_1284151 659386695951910487006803 := by
  unfold tailWord_1284151
  simp only [CollatzResearch.WordTrace]
  refine ⟨46836834770747717375308307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31224556513831811583538871 46836834770747717375308307)
  ·
    refine ⟨70255252156121576062962461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46836834770747717375308307 70255252156121576062962461)
    ·
      refine ⟨26345719558545591023610923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 70255252156121576062962461 26345719558545591023610923)
      ·
        refine ⟨39518579337818386535416385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26345719558545591023610923 39518579337818386535416385)
        ·
          refine ⟨29638934503363789901562289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39518579337818386535416385 29638934503363789901562289)
          ·
            refine ⟨22229200877522842426171717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29638934503363789901562289 22229200877522842426171717)
            ·
              refine ⟨4167975164535532954907197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22229200877522842426171717 4167975164535532954907197)
              ·
                refine ⟨1562990686700824858090199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4167975164535532954907197 1562990686700824858090199)
                ·
                  refine ⟨2344486030051237287135299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1562990686700824858090199 2344486030051237287135299)
                  ·
                    refine ⟨3516729045076855930702949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2344486030051237287135299 3516729045076855930702949)
                    ·
                      refine ⟨659386695951910487006803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3516729045076855930702949 659386695951910487006803)
                      ·
                        rfl

theorem cell23_1284151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 4, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 4, 3, 1, 1, 4].length) (baseStart_1284151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1284151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1284151 prefixEnd_1284151 := by exact prefixLift 1284151
  have htrace : WordTrace (prefixWord ++ tailWord_1284151) baseStart_1284151 baseEnd_1284151 := by
    simpa [prefixWord, tailWord_1284151, baseEnd_1284151] using wordTrace_append hprefix tailTrace_1284151
  have hstable : (prefixWord ++ tailWord_1284151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1284151).length < 2 ^ (prefixWord ++ tailWord_1284151).sum := by decide
  have hdescent : baseEnd_1284151 < baseStart_1284151 := by decide
  rcases family_descends (prefixWord ++ tailWord_1284151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1284168 : List Nat := [2, 1, 3, 1, 1, 1, 2, 5, 3, 2, 2]
def baseStart_1284168 : Nat := 118140960795 + 1284168 * 2 ^ 59
def prefixEnd_1284168 : Nat := 4983230072969 + 3 ^ 40 * 1284168 * 2
def baseEnd_1284168 : Nat := 659395425123036920494225

theorem tailTrace_1284168 : CollatzResearch.WordTrace tailWord_1284168 prefixEnd_1284168 659395425123036920494225 := by
  unfold tailWord_1284168
  simp only [CollatzResearch.WordTrace]
  refine ⟨23418727405843064639338579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31224969874457419519118105 23418727405843064639338579)
  ·
    refine ⟨35128091108764596959007869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23418727405843064639338579 35128091108764596959007869)
    ·
      refine ⟨13173034165786723859627951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35128091108764596959007869 13173034165786723859627951)
      ·
        refine ⟨19759551248680085789441927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13173034165786723859627951 19759551248680085789441927)
        ·
          refine ⟨29639326873020128684162891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19759551248680085789441927 29639326873020128684162891)
          ·
            refine ⟨44458990309530193026244337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29639326873020128684162891 44458990309530193026244337)
            ·
              refine ⟨33344242732147644769683253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44458990309530193026244337 33344242732147644769683253)
              ·
                refine ⟨3126022756138841697157805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 33344242732147644769683253 3126022756138841697157805)
                ·
                  refine ⟨1172258533552065636434177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3126022756138841697157805 1172258533552065636434177)
                  ·
                    refine ⟨879193900164049227325633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1172258533552065636434177 879193900164049227325633)
                    ·
                      refine ⟨659395425123036920494225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 879193900164049227325633 659395425123036920494225)
                      ·
                        rfl

theorem cell23_1284168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 5, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 5, 3, 2, 2].length) (baseStart_1284168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1284168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1284168 prefixEnd_1284168 := by exact prefixLift 1284168
  have htrace : WordTrace (prefixWord ++ tailWord_1284168) baseStart_1284168 baseEnd_1284168 := by
    simpa [prefixWord, tailWord_1284168, baseEnd_1284168] using wordTrace_append hprefix tailTrace_1284168
  have hstable : (prefixWord ++ tailWord_1284168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1284168).length < 2 ^ (prefixWord ++ tailWord_1284168).sum := by decide
  have hdescent : baseEnd_1284168 < baseStart_1284168 := by decide
  rcases family_descends (prefixWord ++ tailWord_1284168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1284174 : List Nat := [4, 1, 1, 1, 1, 4, 1, 10]
def baseStart_1284174 : Nat := 118140960795 + 1284174 * 2 ^ 59
def prefixEnd_1284174 : Nat := 4983230072969 + 3 ^ 40 * 1284174 * 2
def baseEnd_1284174 : Nat := 24422166889146811000711

theorem tailTrace_1284174 : CollatzResearch.WordTrace tailWord_1284174 prefixEnd_1284174 24422166889146811000711 := by
  unfold tailWord_1284174
  simp only [CollatzResearch.WordTrace]
  refine ⟨5854709206208049037924447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 31225115766442928202263717 5854709206208049037924447)
  ·
    refine ⟨8782063809312073556886671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5854709206208049037924447 8782063809312073556886671)
    ·
      refine ⟨13173095713968110335330007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8782063809312073556886671 13173095713968110335330007)
      ·
        refine ⟨19759643570952165502995011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13173095713968110335330007 19759643570952165502995011)
        ·
          refine ⟨29639465356428248254492517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19759643570952165502995011 29639465356428248254492517)
          ·
            refine ⟨5557399754330296547717347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 29639465356428248254492517 5557399754330296547717347)
            ·
              refine ⟨8336099631495444821576021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5557399754330296547717347 8336099631495444821576021)
              ·
                refine ⟨24422166889146811000711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 8336099631495444821576021 24422166889146811000711)
                ·
                  rfl

theorem cell23_1284174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 1, 10].length) (baseStart_1284174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1284174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1284174 prefixEnd_1284174 := by exact prefixLift 1284174
  have htrace : WordTrace (prefixWord ++ tailWord_1284174) baseStart_1284174 baseEnd_1284174 := by
    simpa [prefixWord, tailWord_1284174, baseEnd_1284174] using wordTrace_append hprefix tailTrace_1284174
  have hstable : (prefixWord ++ tailWord_1284174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1284174).length < 2 ^ (prefixWord ++ tailWord_1284174).sum := by decide
  have hdescent : baseEnd_1284174 < baseStart_1284174 := by decide
  rcases family_descends (prefixWord ++ tailWord_1284174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1284182 : List Nat := [5, 2, 2, 1, 1, 3, 1, 2, 1, 5]
def baseStart_1284182 : Nat := 118140960795 + 1284182 * 2 ^ 59
def prefixEnd_1284182 : Nat := 4983230072969 + 3 ^ 40 * 1284182 * 2
def baseEnd_1284182 : Nat := 219800871284066621906387

theorem tailTrace_1284182 : CollatzResearch.WordTrace tailWord_1284182 prefixEnd_1284182 219800871284066621906387 := by
  unfold tailWord_1284182
  simp only [CollatzResearch.WordTrace]
  refine ⟨2927372839602213104355425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 31225310289090273113124533 2927372839602213104355425)
  ·
    refine ⟨2195529629701659828266569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2927372839602213104355425 2195529629701659828266569)
    ·
      refine ⟨1646647222276244871199927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2195529629701659828266569 1646647222276244871199927)
      ·
        refine ⟨2469970833414367306799891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1646647222276244871199927 2469970833414367306799891)
        ·
          refine ⟨3704956250121550960199837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2469970833414367306799891 3704956250121550960199837)
          ·
            refine ⟨1389358593795581610074939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3704956250121550960199837 1389358593795581610074939)
            ·
              refine ⟨2084037890693372415112409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1389358593795581610074939 2084037890693372415112409)
              ·
                refine ⟨1563028418020029311334307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2084037890693372415112409 1563028418020029311334307)
                ·
                  refine ⟨2344542627030043967001461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1563028418020029311334307 2344542627030043967001461)
                  ·
                    refine ⟨219800871284066621906387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2344542627030043967001461 219800871284066621906387)
                    ·
                      rfl

theorem cell23_1284182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 3, 1, 2, 1, 5].length) (baseStart_1284182 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1284182 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1284182 prefixEnd_1284182 := by exact prefixLift 1284182
  have htrace : WordTrace (prefixWord ++ tailWord_1284182) baseStart_1284182 baseEnd_1284182 := by
    simpa [prefixWord, tailWord_1284182, baseEnd_1284182] using wordTrace_append hprefix tailTrace_1284182
  have hstable : (prefixWord ++ tailWord_1284182).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1284182).length < 2 ^ (prefixWord ++ tailWord_1284182).sum := by decide
  have hdescent : baseEnd_1284182 < baseStart_1284182 := by decide
  rcases family_descends (prefixWord ++ tailWord_1284182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1284188 : List Nat := [2, 2, 4, 1, 1, 3, 1, 1, 3, 2, 3]
def baseStart_1284188 : Nat := 118140960795 + 1284188 * 2 ^ 59
def prefixEnd_1284188 : Nat := 4983230072969 + 3 ^ 40 * 1284188 * 2
def baseEnd_1284188 : Nat := 659405694736126842244133

theorem tailTrace_1284188 : CollatzResearch.WordTrace tailWord_1284188 prefixEnd_1284188 659405694736126842244133 := by
  unfold tailWord_1284188
  simp only [CollatzResearch.WordTrace]
  refine ⟨23419092135806836347202609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31225456181075781796270145 23419092135806836347202609)
  ·
    refine ⟨17564319101855127260401957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23419092135806836347202609 17564319101855127260401957)
    ·
      refine ⟨3293309831597836361325367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17564319101855127260401957 3293309831597836361325367)
      ·
        refine ⟨4939964747396754541988051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3293309831597836361325367 4939964747396754541988051)
        ·
          refine ⟨7409947121095131812982077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4939964747396754541988051 7409947121095131812982077)
          ·
            refine ⟨2778730170410674429868279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7409947121095131812982077 2778730170410674429868279)
            ·
              refine ⟨4168095255616011644802419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2778730170410674429868279 4168095255616011644802419)
              ·
                refine ⟨6252142883424017467203629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4168095255616011644802419 6252142883424017467203629)
                ·
                  refine ⟨2344553581284006550201361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6252142883424017467203629 2344553581284006550201361)
                  ·
                    refine ⟨1758415185963004912651021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2344553581284006550201361 1758415185963004912651021)
                    ·
                      refine ⟨659405694736126842244133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1758415185963004912651021 659405694736126842244133)
                      ·
                        rfl

theorem cell23_1284188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 1, 1, 3, 2, 3].length) (baseStart_1284188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1284188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1284188 prefixEnd_1284188 := by exact prefixLift 1284188
  have htrace : WordTrace (prefixWord ++ tailWord_1284188) baseStart_1284188 baseEnd_1284188 := by
    simpa [prefixWord, tailWord_1284188, baseEnd_1284188] using wordTrace_append hprefix tailTrace_1284188
  have hstable : (prefixWord ++ tailWord_1284188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1284188).length < 2 ^ (prefixWord ++ tailWord_1284188).sum := by decide
  have hdescent : baseEnd_1284188 < baseStart_1284188 := by decide
  rcases family_descends (prefixWord ++ tailWord_1284188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1284201 : List Nat := [1, 2, 1, 1, 1, 5, 3, 2, 1, 3, 3]
def baseStart_1284201 : Nat := 118140960795 + 1284201 * 2 ^ 59
def prefixEnd_1284201 : Nat := 4983230072969 + 3 ^ 40 * 1284201 * 2
def baseEnd_1284201 : Nat := 659412369984635291381573

theorem tailTrace_1284201 : CollatzResearch.WordTrace tailWord_1284201 prefixEnd_1284201 659412369984635291381573 := by
  unfold tailWord_1284201
  simp only [CollatzResearch.WordTrace]
  refine ⟨46838658420566575914628457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31225772280377717276418971 46838658420566575914628457)
  ·
    refine ⟨35128993815424931935971343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46838658420566575914628457 35128993815424931935971343)
    ·
      refine ⟨52693490723137397903957015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35128993815424931935971343 52693490723137397903957015)
      ·
        refine ⟨79040236084706096855935523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52693490723137397903957015 79040236084706096855935523)
        ·
          refine ⟨118560354127059145283903285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79040236084706096855935523 118560354127059145283903285)
          ·
            refine ⟨11115033199411794870365933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 118560354127059145283903285 11115033199411794870365933)
            ·
              refine ⟨4168137449779423076387225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11115033199411794870365933 4168137449779423076387225)
              ·
                refine ⟨3126103087334567307290419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4168137449779423076387225 3126103087334567307290419)
                ·
                  refine ⟨4689154631001850960935629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3126103087334567307290419 4689154631001850960935629)
                  ·
                    refine ⟨1758432986625694110350861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4689154631001850960935629 1758432986625694110350861)
                    ·
                      refine ⟨659412369984635291381573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1758432986625694110350861 659412369984635291381573)
                      ·
                        rfl

theorem cell23_1284201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 3, 2, 1, 3, 3].length) (baseStart_1284201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1284201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1284201 prefixEnd_1284201 := by exact prefixLift 1284201
  have htrace : WordTrace (prefixWord ++ tailWord_1284201) baseStart_1284201 baseEnd_1284201 := by
    simpa [prefixWord, tailWord_1284201, baseEnd_1284201] using wordTrace_append hprefix tailTrace_1284201
  have hstable : (prefixWord ++ tailWord_1284201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1284201).length < 2 ^ (prefixWord ++ tailWord_1284201).sum := by decide
  have hdescent : baseEnd_1284201 < baseStart_1284201 := by decide
  rcases family_descends (prefixWord ++ tailWord_1284201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1284205 : List Nat := [1, 5, 1, 1, 2, 1, 5, 1, 1, 2, 3]
def baseStart_1284205 : Nat := 118140960795 + 1284205 * 2 ^ 59
def prefixEnd_1284205 : Nat := 4983230072969 + 3 ^ 40 * 1284205 * 2
def baseEnd_1284205 : Nat := 659414423907253275731555

theorem tailTrace_1284205 : CollatzResearch.WordTrace tailWord_1284205 prefixEnd_1284205 659414423907253275731555 := by
  unfold tailWord_1284205
  simp only [CollatzResearch.WordTrace]
  refine ⟨46838804312552084597774069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31225869541701389731849379 46838804312552084597774069)
  ·
    refine ⟨4391137904301757931041319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 46838804312552084597774069 4391137904301757931041319)
    ·
      refine ⟨6586706856452636896561979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4391137904301757931041319 6586706856452636896561979)
      ·
        refine ⟨9880060284678955344842969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6586706856452636896561979 9880060284678955344842969)
        ·
          refine ⟨7410045213509216508632227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9880060284678955344842969 7410045213509216508632227)
          ·
            refine ⟨11115067820263824762948341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7410045213509216508632227 11115067820263824762948341)
            ·
              refine ⟨1042037608149733571526407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 11115067820263824762948341 1042037608149733571526407)
              ·
                refine ⟨1563056412224600357289611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1042037608149733571526407 1563056412224600357289611)
                ·
                  refine ⟨2344584618336900535934417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1563056412224600357289611 2344584618336900535934417)
                  ·
                    refine ⟨1758438463752675401950813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2344584618336900535934417 1758438463752675401950813)
                    ·
                      refine ⟨659414423907253275731555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1758438463752675401950813 659414423907253275731555)
                      ·
                        rfl

theorem cell23_1284205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 5, 1, 1, 2, 3].length) (baseStart_1284205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1284205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1284205 prefixEnd_1284205 := by exact prefixLift 1284205
  have htrace : WordTrace (prefixWord ++ tailWord_1284205) baseStart_1284205 baseEnd_1284205 := by
    simpa [prefixWord, tailWord_1284205, baseEnd_1284205] using wordTrace_append hprefix tailTrace_1284205
  have hstable : (prefixWord ++ tailWord_1284205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1284205).length < 2 ^ (prefixWord ++ tailWord_1284205).sum := by decide
  have hdescent : baseEnd_1284205 < baseStart_1284205 := by decide
  rcases family_descends (prefixWord ++ tailWord_1284205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1284228 : List Nat := [2, 3, 2, 1, 2, 1, 1, 1, 5, 3, 2]
def baseStart_1284228 : Nat := 118140960795 + 1284228 * 2 ^ 59
def prefixEnd_1284228 : Nat := 4983230072969 + 3 ^ 40 * 1284228 * 2
def baseEnd_1284228 : Nat := 659426233962306685743949

theorem tailTrace_1284228 : CollatzResearch.WordTrace tailWord_1284228 prefixEnd_1284228 659426233962306685743949 := by
  unfold tailWord_1284228
  simp only [CollatzResearch.WordTrace]
  refine ⟨23419821595734379762930669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31226428794312506350574225 23419821595734379762930669)
  ·
    refine ⟨8782433098400392411099001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23419821595734379762930669 8782433098400392411099001)
    ·
      refine ⟨6586824823800294308324251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8782433098400392411099001 6586824823800294308324251)
      ·
        refine ⟨9880237235700441462486377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6586824823800294308324251 9880237235700441462486377)
        ·
          refine ⟨7410177926775331096864783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9880237235700441462486377 7410177926775331096864783)
          ·
            refine ⟨11115266890162996645297175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7410177926775331096864783 11115266890162996645297175)
            ·
              refine ⟨16672900335244494967945763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11115266890162996645297175 16672900335244494967945763)
              ·
                refine ⟨25009350502866742451918645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16672900335244494967945763 25009350502866742451918645)
                ·
                  refine ⟨2344626609643757104867373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 25009350502866742451918645 2344626609643757104867373)
                  ·
                    refine ⟨879234978616408914325265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2344626609643757104867373 879234978616408914325265)
                    ·
                      refine ⟨659426233962306685743949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 879234978616408914325265 659426233962306685743949)
                      ·
                        rfl

theorem cell23_1284228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 1, 5, 3, 2].length) (baseStart_1284228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1284228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1284228 prefixEnd_1284228 := by exact prefixLift 1284228
  have htrace : WordTrace (prefixWord ++ tailWord_1284228) baseStart_1284228 baseEnd_1284228 := by
    simpa [prefixWord, tailWord_1284228, baseEnd_1284228] using wordTrace_append hprefix tailTrace_1284228
  have hstable : (prefixWord ++ tailWord_1284228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1284228).length < 2 ^ (prefixWord ++ tailWord_1284228).sum := by decide
  have hdescent : baseEnd_1284228 < baseStart_1284228 := by decide
  rcases family_descends (prefixWord ++ tailWord_1284228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1284281 : List Nat := [1, 2, 1, 4, 1, 2, 4, 1, 7]
def baseStart_1284281 : Nat := 118140960795 + 1284281 * 2 ^ 59
def prefixEnd_1284281 : Nat := 4983230072969 + 3 ^ 40 * 1284281 * 2
def baseEnd_1284281 : Nat := 73272605381888330931245

theorem tailTrace_1284281 : CollatzResearch.WordTrace tailWord_1284281 prefixEnd_1284281 73272605381888330931245 := by
  unfold tailWord_1284281
  simp only [CollatzResearch.WordTrace]
  refine ⟨46841576260276749577540697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31227717506851166385027131 46841576260276749577540697)
  ·
    refine ⟨35131182195207562183155523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46841576260276749577540697 35131182195207562183155523)
    ·
      refine ⟨52696773292811343274733285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35131182195207562183155523 52696773292811343274733285)
      ·
        refine ⟨9880644992402126864012491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 52696773292811343274733285 9880644992402126864012491)
        ·
          refine ⟨14820967488603190296018737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9880644992402126864012491 14820967488603190296018737)
          ·
            refine ⟨11115725616452392722014053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14820967488603190296018737 11115725616452392722014053)
            ·
              refine ⟨2084198553084823635377635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11115725616452392722014053 2084198553084823635377635)
              ·
                refine ⟨3126297829627235453066453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2084198553084823635377635 3126297829627235453066453)
                ·
                  refine ⟨73272605381888330931245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3126297829627235453066453 73272605381888330931245)
                  ·
                    rfl

theorem cell23_1284281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 4, 1, 7].length) (baseStart_1284281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1284281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1284281 prefixEnd_1284281 := by exact prefixLift 1284281
  have htrace : WordTrace (prefixWord ++ tailWord_1284281) baseStart_1284281 baseEnd_1284281 := by
    simpa [prefixWord, tailWord_1284281, baseEnd_1284281] using wordTrace_append hprefix tailTrace_1284281
  have hstable : (prefixWord ++ tailWord_1284281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1284281).length < 2 ^ (prefixWord ++ tailWord_1284281).sum := by decide
  have hdescent : baseEnd_1284281 < baseStart_1284281 := by decide
  rcases family_descends (prefixWord ++ tailWord_1284281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1284292 : List Nat := [2, 3, 3, 1, 2, 3, 1, 1, 1, 4, 2]
def baseStart_1284292 : Nat := 118140960795 + 1284292 * 2 ^ 59
def prefixEnd_1284292 : Nat := 4983230072969 + 3 ^ 40 * 1284292 * 2
def baseEnd_1284292 : Nat := 659459096724194435343655

theorem tailTrace_1284292 : CollatzResearch.WordTrace tailWord_1284292 prefixEnd_1284292 659459096724194435343655 := by
  unfold tailWord_1284292
  simp only [CollatzResearch.WordTrace]
  refine ⟨23420988731618449228095565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31227984975491265637460753 23420988731618449228095565)
  ·
    refine ⟨8782870774356918460535837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23420988731618449228095565 8782870774356918460535837)
    ·
      refine ⟨3293576540383844422700939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8782870774356918460535837 3293576540383844422700939)
      ·
        refine ⟨4940364810575766634051409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3293576540383844422700939 4940364810575766634051409)
        ·
          refine ⟨3705273607931824975538557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4940364810575766634051409 3705273607931824975538557)
          ·
            refine ⟨1389477602974434365826959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3705273607931824975538557 1389477602974434365826959)
            ·
              refine ⟨2084216404461651548740439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1389477602974434365826959 2084216404461651548740439)
              ·
                refine ⟨3126324606692477323110659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2084216404461651548740439 3126324606692477323110659)
                ·
                  refine ⟨4689486910038715984665989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3126324606692477323110659 4689486910038715984665989)
                  ·
                    refine ⟨879278795632259247124873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4689486910038715984665989 879278795632259247124873)
                    ·
                      refine ⟨659459096724194435343655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 879278795632259247124873 659459096724194435343655)
                      ·
                        rfl

theorem cell23_1284292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 3, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 3, 1, 1, 1, 4, 2].length) (baseStart_1284292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1284292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1284292 prefixEnd_1284292 := by exact prefixLift 1284292
  have htrace : WordTrace (prefixWord ++ tailWord_1284292) baseStart_1284292 baseEnd_1284292 := by
    simpa [prefixWord, tailWord_1284292, baseEnd_1284292] using wordTrace_append hprefix tailTrace_1284292
  have hstable : (prefixWord ++ tailWord_1284292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1284292).length < 2 ^ (prefixWord ++ tailWord_1284292).sum := by decide
  have hdescent : baseEnd_1284292 < baseStart_1284292 := by decide
  rcases family_descends (prefixWord ++ tailWord_1284292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1284311 : List Nat := [1, 1, 3, 2, 1, 2, 1, 5, 2, 5]
def baseStart_1284311 : Nat := 118140960795 + 1284311 * 2 ^ 59
def prefixEnd_1284311 : Nat := 4983230072969 + 3 ^ 40 * 1284311 * 2
def baseEnd_1284311 : Nat := 219822950952209953668689

theorem tailTrace_1284311 : CollatzResearch.WordTrace tailWord_1284311 prefixEnd_1284311 219822950952209953668689 := by
  unfold tailWord_1284311
  simp only [CollatzResearch.WordTrace]
  refine ⟨46842670450168064701132787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31228446966778709800755191 46842670450168064701132787)
  ·
    refine ⟨70264005675252097051699181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46842670450168064701132787 70264005675252097051699181)
    ·
      refine ⟨26349002128219536394387193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 70264005675252097051699181 26349002128219536394387193)
      ·
        refine ⟨19761751596164652295790395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26349002128219536394387193 19761751596164652295790395)
        ·
          refine ⟨29642627394246978443685593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19761751596164652295790395 29642627394246978443685593)
          ·
            refine ⟨22231970545685233832764195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29642627394246978443685593 22231970545685233832764195)
            ·
              refine ⟨33347955818527850749146293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22231970545685233832764195 33347955818527850749146293)
              ·
                refine ⟨3126370857986986007732465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 33347955818527850749146293 3126370857986986007732465)
                ·
                  refine ⟨2344778143490239505799349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3126370857986986007732465 2344778143490239505799349)
                  ·
                    refine ⟨219822950952209953668689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2344778143490239505799349 219822950952209953668689)
                    ·
                      rfl

theorem cell23_1284311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 5, 2, 5].length) (baseStart_1284311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1284311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1284311 prefixEnd_1284311 := by exact prefixLift 1284311
  have htrace : WordTrace (prefixWord ++ tailWord_1284311) baseStart_1284311 baseEnd_1284311 := by
    simpa [prefixWord, tailWord_1284311, baseEnd_1284311] using wordTrace_append hprefix tailTrace_1284311
  have hstable : (prefixWord ++ tailWord_1284311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1284311).length < 2 ^ (prefixWord ++ tailWord_1284311).sum := by decide
  have hdescent : baseEnd_1284311 < baseStart_1284311 := by decide
  rcases family_descends (prefixWord ++ tailWord_1284311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1284321 : List Nat := [1, 2, 3, 1, 3, 1, 2, 2, 1, 2, 5]
def baseStart_1284321 : Nat := 118140960795 + 1284321 * 2 ^ 59
def prefixEnd_1284321 : Nat := 4983230072969 + 3 ^ 40 * 1284321 * 2
def baseEnd_1284321 : Nat := 659473987663174821881021

theorem tailTrace_1284321 : CollatzResearch.WordTrace tailWord_1284321 prefixEnd_1284321 659473987663174821881021 := by
  unfold tailWord_1284321
  simp only [CollatzResearch.WordTrace]
  refine ⟨46843035180131836408996817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31228690120087890939331211 46843035180131836408996817)
  ·
    refine ⟨35132276385098877306747613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46843035180131836408996817 35132276385098877306747613)
    ·
      refine ⟨13174603644412078990030355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35132276385098877306747613 13174603644412078990030355)
      ·
        refine ⟨19761905466618118485045533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13174603644412078990030355 19761905466618118485045533)
        ·
          refine ⟨7410714549981794431892075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19761905466618118485045533 7410714549981794431892075)
          ·
            refine ⟨11116071824972691647838113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7410714549981794431892075 11116071824972691647838113)
            ·
              refine ⟨8337053868729518735878585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11116071824972691647838113 8337053868729518735878585)
              ·
                refine ⟨6252790401547139051908939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8337053868729518735878585 6252790401547139051908939)
                ·
                  refine ⟨9379185602320708577863409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6252790401547139051908939 9379185602320708577863409)
                  ·
                    refine ⟨7034389201740531433397557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9379185602320708577863409 7034389201740531433397557)
                    ·
                      refine ⟨659473987663174821881021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7034389201740531433397557 659473987663174821881021)
                      ·
                        rfl

theorem cell23_1284321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 2, 2, 1, 2, 5].length) (baseStart_1284321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1284321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1284321 prefixEnd_1284321 := by exact prefixLift 1284321
  have htrace : WordTrace (prefixWord ++ tailWord_1284321) baseStart_1284321 baseEnd_1284321 := by
    simpa [prefixWord, tailWord_1284321, baseEnd_1284321] using wordTrace_append hprefix tailTrace_1284321
  have hstable : (prefixWord ++ tailWord_1284321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1284321).length < 2 ^ (prefixWord ++ tailWord_1284321).sum := by decide
  have hdescent : baseEnd_1284321 < baseStart_1284321 := by decide
  rcases family_descends (prefixWord ++ tailWord_1284321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1284328 : List Nat := [2, 1, 4, 1, 2, 3, 1, 2, 2, 5]
def baseStart_1284328 : Nat := 118140960795 + 1284328 * 2 ^ 59
def prefixEnd_1284328 : Nat := 4983230072969 + 3 ^ 40 * 1284328 * 2
def baseEnd_1284328 : Nat := 219825860675918764831163

theorem tailTrace_1284328 : CollatzResearch.WordTrace tailWord_1284328 prefixEnd_1284328 219825860675918764831163 := by
  unfold tailWord_1284328
  simp only [CollatzResearch.WordTrace]
  refine ⟨23421645245553238302250819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31228860327404317736334425 23421645245553238302250819)
  ·
    refine ⟨35132467868329857453376229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23421645245553238302250819 35132467868329857453376229)
    ·
      refine ⟨6587337725311848272508043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 35132467868329857453376229 6587337725311848272508043)
      ·
        refine ⟨9881006587967772408762065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6587337725311848272508043 9881006587967772408762065)
        ·
          refine ⟨7410754940975829306571549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9881006587967772408762065 7410754940975829306571549)
          ·
            refine ⟨2779033102865935989964331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7410754940975829306571549 2779033102865935989964331)
            ·
              refine ⟨4168549654298903984946497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2779033102865935989964331 4168549654298903984946497)
              ·
                refine ⟨3126412240724177988709873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4168549654298903984946497 3126412240724177988709873)
                ·
                  refine ⟨2344809180543133491532405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3126412240724177988709873 2344809180543133491532405)
                  ·
                    refine ⟨219825860675918764831163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2344809180543133491532405 219825860675918764831163)
                    ·
                      rfl

theorem cell23_1284328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 1, 2, 2, 5].length) (baseStart_1284328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1284328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1284328 prefixEnd_1284328 := by exact prefixLift 1284328
  have htrace : WordTrace (prefixWord ++ tailWord_1284328) baseStart_1284328 baseEnd_1284328 := by
    simpa [prefixWord, tailWord_1284328, baseEnd_1284328] using wordTrace_append hprefix tailTrace_1284328
  have hstable : (prefixWord ++ tailWord_1284328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1284328).length < 2 ^ (prefixWord ++ tailWord_1284328).sum := by decide
  have hdescent : baseEnd_1284328 < baseStart_1284328 := by decide
  rcases family_descends (prefixWord ++ tailWord_1284328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1284338 : List Nat := [3, 2, 1, 3, 2, 2, 1, 1, 1, 2, 5]
def baseStart_1284338 : Nat := 118140960795 + 1284338 * 2 ^ 59
def prefixEnd_1284338 : Nat := 4983230072969 + 3 ^ 40 * 1284338 * 2
def baseEnd_1284338 : Nat := 659482716834301255368443

theorem tailTrace_1284338 : CollatzResearch.WordTrace tailWord_1284338 prefixEnd_1284338 659482716834301255368443 := by
  unfold tailWord_1284338
  simp only [CollatzResearch.WordTrace]
  refine ⟨11710913805267562078091417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31229103480713498874910445 11710913805267562078091417)
  ·
    refine ⟨8783185353950671558568563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11710913805267562078091417 8783185353950671558568563)
    ·
      refine ⟨13174778030926007337852845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8783185353950671558568563 13174778030926007337852845)
      ·
        refine ⟨4940541761597252751694817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13174778030926007337852845 4940541761597252751694817)
        ·
          refine ⟨3705406321197939563771113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4940541761597252751694817 3705406321197939563771113)
          ·
            refine ⟨2779054740898454672828335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3705406321197939563771113 2779054740898454672828335)
            ·
              refine ⟨4168582111347682009242503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2779054740898454672828335 4168582111347682009242503)
              ·
                refine ⟨6252873167021523013863755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4168582111347682009242503 6252873167021523013863755)
                ·
                  refine ⟨9379309750532284520795633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6252873167021523013863755 9379309750532284520795633)
                  ·
                    refine ⟨7034482312899213390596725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9379309750532284520795633 7034482312899213390596725)
                    ·
                      refine ⟨659482716834301255368443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7034482312899213390596725 659482716834301255368443)
                      ·
                        rfl

theorem cell23_1284338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 1, 1, 1, 2, 5].length) (baseStart_1284338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1284338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1284338 prefixEnd_1284338 := by exact prefixLift 1284338
  have htrace : WordTrace (prefixWord ++ tailWord_1284338) baseStart_1284338 baseEnd_1284338 := by
    simpa [prefixWord, tailWord_1284338, baseEnd_1284338] using wordTrace_append hprefix tailTrace_1284338
  have hstable : (prefixWord ++ tailWord_1284338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1284338).length < 2 ^ (prefixWord ++ tailWord_1284338).sum := by decide
  have hdescent : baseEnd_1284338 < baseStart_1284338 := by decide
  rcases family_descends (prefixWord ++ tailWord_1284338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1284382 : List Nat := [4, 3, 2, 1, 1, 1, 2, 2, 2, 1, 4]
def baseStart_1284382 : Nat := 118140960795 + 1284382 * 2 ^ 59
def prefixEnd_1284382 : Nat := 4983230072969 + 3 ^ 40 * 1284382 * 2
def baseEnd_1284382 : Nat := 659505309983099083218241

theorem tailTrace_1284382 : CollatzResearch.WordTrace tailWord_1284382 prefixEnd_1284382 659505309983099083218241 := by
  unfold tailWord_1284382
  simp only [CollatzResearch.WordTrace]
  refine ⟨5855657504113855478370925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 31230173355273895884644933 5855657504113855478370925)
  ·
    refine ⟨2195871564042695804389097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5855657504113855478370925 2195871564042695804389097)
    ·
      refine ⟨1646903673032021853291823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2195871564042695804389097 1646903673032021853291823)
      ·
        refine ⟨2470355509548032779937735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1646903673032021853291823 2470355509548032779937735)
        ·
          refine ⟨3705533264322049169906603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2470355509548032779937735 3705533264322049169906603)
          ·
            refine ⟨5558299896483073754859905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3705533264322049169906603 5558299896483073754859905)
            ·
              refine ⟨4168724922362305316144929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5558299896483073754859905 4168724922362305316144929)
              ·
                refine ⟨3126543691771728987108697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4168724922362305316144929 3126543691771728987108697)
                ·
                  refine ⟨2344907768828796740331523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3126543691771728987108697 2344907768828796740331523)
                  ·
                    refine ⟨3517361653243195110497285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2344907768828796740331523 3517361653243195110497285)
                    ·
                      refine ⟨659505309983099083218241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3517361653243195110497285 659505309983099083218241)
                      ·
                        rfl

theorem cell23_1284382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 2, 2, 2, 1, 4].length) (baseStart_1284382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1284382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1284382 prefixEnd_1284382 := by exact prefixLift 1284382
  have htrace : WordTrace (prefixWord ++ tailWord_1284382) baseStart_1284382 baseEnd_1284382 := by
    simpa [prefixWord, tailWord_1284382, baseEnd_1284382] using wordTrace_append hprefix tailTrace_1284382
  have hstable : (prefixWord ++ tailWord_1284382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1284382).length < 2 ^ (prefixWord ++ tailWord_1284382).sum := by decide
  have hdescent : baseEnd_1284382 < baseStart_1284382 := by decide
  rcases family_descends (prefixWord ++ tailWord_1284382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1284388 : List Nat := [2, 3, 1, 3, 1, 2, 1, 4, 6]
def baseStart_1284388 : Nat := 118140960795 + 1284388 * 2 ^ 59
def prefixEnd_1284388 : Nat := 4983230072969 + 3 ^ 40 * 1284388 * 2
def baseEnd_1284388 : Nat := 73278710096336228860357

theorem tailTrace_1284388 : CollatzResearch.WordTrace tailWord_1284388 prefixEnd_1284388 73278710096336228860357 := by
  unfold tailWord_1284388
  simp only [CollatzResearch.WordTrace]
  refine ⟨23422739435444553425842909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31230319247259404567790545 23422739435444553425842909)
  ·
    refine ⟨8783527288291707534691091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23422739435444553425842909 8783527288291707534691091)
    ·
      refine ⟨13175290932437561302036637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8783527288291707534691091 13175290932437561302036637)
      ·
        refine ⟨4940734099664085488263739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13175290932437561302036637 4940734099664085488263739)
        ·
          refine ⟨7411101149496128232395609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4940734099664085488263739 7411101149496128232395609)
          ·
            refine ⟨5558325862122096174296707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7411101149496128232395609 5558325862122096174296707)
            ·
              refine ⟨8337488793183144261445061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5558325862122096174296707 8337488793183144261445061)
              ·
                refine ⟨1563279148721839549020949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8337488793183144261445061 1563279148721839549020949)
                ·
                  refine ⟨73278710096336228860357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1563279148721839549020949 73278710096336228860357)
                  ·
                    rfl

theorem cell23_1284388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 1, 4, 6].length) (baseStart_1284388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1284388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1284388 prefixEnd_1284388 := by exact prefixLift 1284388
  have htrace : WordTrace (prefixWord ++ tailWord_1284388) baseStart_1284388 baseEnd_1284388 := by
    simpa [prefixWord, tailWord_1284388, baseEnd_1284388] using wordTrace_append hprefix tailTrace_1284388
  have hstable : (prefixWord ++ tailWord_1284388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1284388).length < 2 ^ (prefixWord ++ tailWord_1284388).sum := by decide
  have hdescent : baseEnd_1284388 < baseStart_1284388 := by decide
  rcases family_descends (prefixWord ++ tailWord_1284388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1284415 : List Nat := [1, 1, 2, 2, 4, 1, 3, 2, 3, 1, 3]
def baseStart_1284415 : Nat := 118140960795 + 1284415 * 2 ^ 59
def prefixEnd_1284415 : Nat := 4983230072969 + 3 ^ 40 * 1284415 * 2
def baseEnd_1284415 : Nat := 659522254844697454105589

theorem tailTrace_1284415 : CollatzResearch.WordTrace tailWord_1284415 prefixEnd_1284415 659522254844697454105589 := by
  unfold tailWord_1284415
  simp only [CollatzResearch.WordTrace]
  refine ⟨46846463641791290462918699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31230975761194193641945799 46846463641791290462918699)
  ·
    refine ⟨70269695462686935694378049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46846463641791290462918699 70269695462686935694378049)
    ·
      refine ⟨52702271597015201770783537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70269695462686935694378049 52702271597015201770783537)
      ·
        refine ⟨39526703697761401328087653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52702271597015201770783537 39526703697761401328087653)
        ·
          refine ⟨7411256943330262749016435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 39526703697761401328087653 7411256943330262749016435)
          ·
            refine ⟨11116885414995394123524653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7411256943330262749016435 11116885414995394123524653)
            ·
              refine ⟨4168832030623272796321745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11116885414995394123524653 4168832030623272796321745)
              ·
                refine ⟨3126624022967454597241309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4168832030623272796321745 3126624022967454597241309)
                ·
                  refine ⟨1172484008612795473965491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3126624022967454597241309 1172484008612795473965491)
                  ·
                    refine ⟨1758726012919193210948237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1172484008612795473965491 1758726012919193210948237)
                    ·
                      refine ⟨659522254844697454105589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1758726012919193210948237 659522254844697454105589)
                      ·
                        rfl

theorem cell23_1284415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 3, 2, 3, 1, 3].length) (baseStart_1284415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1284415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1284415 prefixEnd_1284415 := by exact prefixLift 1284415
  have htrace : WordTrace (prefixWord ++ tailWord_1284415) baseStart_1284415 baseEnd_1284415 := by
    simpa [prefixWord, tailWord_1284415, baseEnd_1284415] using wordTrace_append hprefix tailTrace_1284415
  have hstable : (prefixWord ++ tailWord_1284415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1284415).length < 2 ^ (prefixWord ++ tailWord_1284415).sum := by decide
  have hdescent : baseEnd_1284415 < baseStart_1284415 := by decide
  rcases family_descends (prefixWord ++ tailWord_1284415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1284431 : List Nat := [1, 1, 2, 1, 1, 2, 1, 5, 3, 6]
def baseStart_1284431 : Nat := 118140960795 + 1284431 * 2 ^ 59
def prefixEnd_1284431 : Nat := 4983230072969 + 3 ^ 40 * 1284431 * 2
def baseEnd_1284431 : Nat := 219843490178389797168505

theorem tailTrace_1284431 : CollatzResearch.WordTrace tailWord_1284431 prefixEnd_1284431 219843490178389797168505 := by
  unfold tailWord_1284431
  simp only [CollatzResearch.WordTrace]
  refine ⟨46847047209733325195501147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31231364806488883463667431 46847047209733325195501147)
  ·
    refine ⟨70270570814599987793251721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46847047209733325195501147 70270570814599987793251721)
    ·
      refine ⟨52702928110949990844938791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70270570814599987793251721 52702928110949990844938791)
      ·
        refine ⟨79054392166424986267408187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52702928110949990844938791 79054392166424986267408187)
        ·
          refine ⟨118581588249637479401112281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79054392166424986267408187 118581588249637479401112281)
          ·
            refine ⟨88936191187228109550834211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 118581588249637479401112281 88936191187228109550834211)
            ·
              refine ⟨133404286780842164326251317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 88936191187228109550834211 133404286780842164326251317)
              ·
                refine ⟨12506651885703952905586061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 133404286780842164326251317 12506651885703952905586061)
                ·
                  refine ⟨4689994457138982339594773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12506651885703952905586061 4689994457138982339594773)
                  ·
                    refine ⟨219843490178389797168505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4689994457138982339594773 219843490178389797168505)
                    ·
                      rfl

theorem cell23_1284431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 5, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 5, 3, 6].length) (baseStart_1284431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1284431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1284431 prefixEnd_1284431 := by exact prefixLift 1284431
  have htrace : WordTrace (prefixWord ++ tailWord_1284431) baseStart_1284431 baseEnd_1284431 := by
    simpa [prefixWord, tailWord_1284431, baseEnd_1284431] using wordTrace_append hprefix tailTrace_1284431
  have hstable : (prefixWord ++ tailWord_1284431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1284431).length < 2 ^ (prefixWord ++ tailWord_1284431).sum := by decide
  have hdescent : baseEnd_1284431 < baseStart_1284431 := by decide
  rcases family_descends (prefixWord ++ tailWord_1284431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1284432 : List Nat := [2, 1, 1, 1, 1, 6, 1, 5, 1, 1, 3]
def baseStart_1284432 : Nat := 118140960795 + 1284432 * 2 ^ 59
def prefixEnd_1284432 : Nat := 4983230072969 + 3 ^ 40 * 1284432 * 2
def baseEnd_1284432 : Nat := 659530984015823887593011

theorem tailTrace_1284432 : CollatzResearch.WordTrace tailWord_1284432 prefixEnd_1284432 659530984015823887593011 := by
  unfold tailWord_1284432
  simp only [CollatzResearch.WordTrace]
  refine ⟨23423541841364851183143775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31231389121819801577525033 23423541841364851183143775)
  ·
    refine ⟨35135312762047276774715663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23423541841364851183143775 35135312762047276774715663)
    ·
      refine ⟨52702969143070915162073495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35135312762047276774715663 52702969143070915162073495)
      ·
        refine ⟨79054453714606372743110243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52702969143070915162073495 79054453714606372743110243)
        ·
          refine ⟨118581680571909559114665365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79054453714606372743110243 118581680571909559114665365)
          ·
            refine ⟨5558516276808260583499939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 118581680571909559114665365 5558516276808260583499939)
            ·
              refine ⟨8337774415212390875249909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5558516276808260583499939 8337774415212390875249909)
              ·
                refine ⟨781666351426161644554679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8337774415212390875249909 781666351426161644554679)
                ·
                  refine ⟨1172499527139242466832019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 781666351426161644554679 1172499527139242466832019)
                  ·
                    refine ⟨1758749290708863700248029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1172499527139242466832019 1758749290708863700248029)
                    ·
                      refine ⟨659530984015823887593011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1758749290708863700248029 659530984015823887593011)
                      ·
                        rfl

theorem cell23_1284432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 1, 5, 1, 1, 3].length) (baseStart_1284432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1284432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1284432 prefixEnd_1284432 := by exact prefixLift 1284432
  have htrace : WordTrace (prefixWord ++ tailWord_1284432) baseStart_1284432 baseEnd_1284432 := by
    simpa [prefixWord, tailWord_1284432, baseEnd_1284432] using wordTrace_append hprefix tailTrace_1284432
  have hstable : (prefixWord ++ tailWord_1284432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1284432).length < 2 ^ (prefixWord ++ tailWord_1284432).sum := by decide
  have hdescent : baseEnd_1284432 < baseStart_1284432 := by decide
  rcases family_descends (prefixWord ++ tailWord_1284432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1284475 : List Nat := [1, 1, 1, 1, 1, 7, 1, 4, 1, 2, 3]
def baseStart_1284475 : Nat := 118140960795 + 1284475 * 2 ^ 59
def prefixEnd_1284475 : Nat := 4983230072969 + 3 ^ 40 * 1284475 * 2
def baseEnd_1284475 : Nat := 659553063683967219355313

theorem tailTrace_1284475 : CollatzResearch.WordTrace tailWord_1284475 prefixEnd_1284475 659553063683967219355313 := by
  unfold tailWord_1284475
  simp only [CollatzResearch.WordTrace]
  refine ⟨46848652021573920710102879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31232434681049280473401919 46848652021573920710102879)
  ·
    refine ⟨70272978032360881065154319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46848652021573920710102879 70272978032360881065154319)
    ·
      refine ⟨105409467048541321597731479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70272978032360881065154319 105409467048541321597731479)
      ·
        refine ⟨158114200572811982396597219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105409467048541321597731479 158114200572811982396597219)
        ·
          refine ⟨237171300859217973594895829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 158114200572811982396597219 237171300859217973594895829)
          ·
            refine ⟨5558702363887921256130371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 237171300859217973594895829 5558702363887921256130371)
            ·
              refine ⟨8338053545831881884195557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5558702363887921256130371 8338053545831881884195557)
              ·
                refine ⟨1563385039843477853286667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8338053545831881884195557 1563385039843477853286667)
                ·
                  refine ⟨2345077559765216779930001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1563385039843477853286667 2345077559765216779930001)
                  ·
                    refine ⟨1758808169823912584947501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2345077559765216779930001 1758808169823912584947501)
                    ·
                      refine ⟨659553063683967219355313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1758808169823912584947501 659553063683967219355313)
                      ·
                        rfl

theorem cell23_1284475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 1, 4, 1, 2, 3].length) (baseStart_1284475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1284475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1284475 prefixEnd_1284475 := by exact prefixLift 1284475
  have htrace : WordTrace (prefixWord ++ tailWord_1284475) baseStart_1284475 baseEnd_1284475 := by
    simpa [prefixWord, tailWord_1284475, baseEnd_1284475] using wordTrace_append hprefix tailTrace_1284475
  have hstable : (prefixWord ++ tailWord_1284475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1284475).length < 2 ^ (prefixWord ++ tailWord_1284475).sum := by decide
  have hdescent : baseEnd_1284475 < baseStart_1284475 := by decide
  rcases family_descends (prefixWord ++ tailWord_1284475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1284505 : List Nat := [1, 2, 1, 2, 1, 4, 1, 3, 4, 1, 3]
def baseStart_1284505 : Nat := 118140960795 + 1284505 * 2 ^ 59
def prefixEnd_1284505 : Nat := 4983230072969 + 3 ^ 40 * 1284505 * 2
def baseEnd_1284505 : Nat := 659568468103602101980175

theorem tailTrace_1284505 : CollatzResearch.WordTrace tailWord_1284505 prefixEnd_1284505 659568468103602101980175 := by
  unfold tailWord_1284505
  simp only [CollatzResearch.WordTrace]
  refine ⟨46849746211465235833694969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31233164140976823889129979 46849746211465235833694969)
  ·
    refine ⟨35137309658598926875271227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46849746211465235833694969 35137309658598926875271227)
    ·
      refine ⟨52705964487898390312906841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35137309658598926875271227 52705964487898390312906841)
      ·
        refine ⟨39529473365923792734680131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52705964487898390312906841 39529473365923792734680131)
        ·
          refine ⟨59294210048885689102020197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39529473365923792734680131 59294210048885689102020197)
          ·
            refine ⟨11117664384166066706628787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 59294210048885689102020197 11117664384166066706628787)
            ·
              refine ⟨16676496576249100059943181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11117664384166066706628787 16676496576249100059943181)
              ·
                refine ⟨6253686216093412522478693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16676496576249100059943181 6253686216093412522478693)
                ·
                  refine ⟨1172566165517514847964755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6253686216093412522478693 1172566165517514847964755)
                  ·
                    refine ⟨1758849248276272271947133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1172566165517514847964755 1758849248276272271947133)
                    ·
                      refine ⟨659568468103602101980175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1758849248276272271947133 659568468103602101980175)
                      ·
                        rfl

theorem cell23_1284505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 3, 4, 1, 3].length) (baseStart_1284505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1284505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1284505 prefixEnd_1284505 := by exact prefixLift 1284505
  have htrace : WordTrace (prefixWord ++ tailWord_1284505) baseStart_1284505 baseEnd_1284505 := by
    simpa [prefixWord, tailWord_1284505, baseEnd_1284505] using wordTrace_append hprefix tailTrace_1284505
  have hstable : (prefixWord ++ tailWord_1284505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1284505).length < 2 ^ (prefixWord ++ tailWord_1284505).sum := by decide
  have hdescent : baseEnd_1284505 < baseStart_1284505 := by decide
  rcases family_descends (prefixWord ++ tailWord_1284505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1284558 : List Nat := [4, 1, 1, 1, 2, 1, 1, 1, 2, 3, 6]
def baseStart_1284558 : Nat := 118140960795 + 1284558 * 2 ^ 59
def prefixEnd_1284558 : Nat := 4983230072969 + 3 ^ 40 * 1284558 * 2
def baseEnd_1284558 : Nat := 659595682578290394617431

theorem tailTrace_1284558 : CollatzResearch.WordTrace tailWord_1284558 prefixEnd_1284558 659595682578290394617431 := by
  unfold tailWord_1284558
  simp only [CollatzResearch.WordTrace]
  refine ⟨5856459910034153235671791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 31234452853515483923582885 5856459910034153235671791)
  ·
    refine ⟨8784689865051229853507687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5856459910034153235671791 8784689865051229853507687)
    ·
      refine ⟨13177034797576844780261531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8784689865051229853507687 13177034797576844780261531)
      ·
        refine ⟨19765552196365267170392297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13177034797576844780261531 19765552196365267170392297)
        ·
          refine ⟨14824164147273950377794223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19765552196365267170392297 14824164147273950377794223)
          ·
            refine ⟨22236246220910925566691335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14824164147273950377794223 22236246220910925566691335)
            ·
              refine ⟨33354369331366388350037003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22236246220910925566691335 33354369331366388350037003)
              ·
                refine ⟨50031553997049582525055505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33354369331366388350037003 50031553997049582525055505)
                ·
                  refine ⟨37523665497787186893791629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 50031553997049582525055505 37523665497787186893791629)
                  ·
                    refine ⟨14071374561670195085171861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 37523665497787186893791629 14071374561670195085171861)
                    ·
                      refine ⟨659595682578290394617431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 14071374561670195085171861 659595682578290394617431)
                      ·
                        rfl

theorem cell23_1284558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 1, 2, 3, 6].length) (baseStart_1284558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1284558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1284558 prefixEnd_1284558 := by exact prefixLift 1284558
  have htrace : WordTrace (prefixWord ++ tailWord_1284558) baseStart_1284558 baseEnd_1284558 := by
    simpa [prefixWord, tailWord_1284558, baseEnd_1284558] using wordTrace_append hprefix tailTrace_1284558
  have hstable : (prefixWord ++ tailWord_1284558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1284558).length < 2 ^ (prefixWord ++ tailWord_1284558).sum := by decide
  have hdescent : baseEnd_1284558 < baseStart_1284558 := by decide
  rcases family_descends (prefixWord ++ tailWord_1284558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1284565 : List Nat := [1, 3, 2, 3, 1, 2, 1, 1, 2, 4, 3]
def baseStart_1284565 : Nat := 118140960795 + 1284565 * 2 ^ 59
def prefixEnd_1284565 : Nat := 4983230072969 + 3 ^ 40 * 1284565 * 2
def baseEnd_1284565 : Nat := 659599276942871867229899

theorem tailTrace_1284565 : CollatzResearch.WordTrace tailWord_1284565 prefixEnd_1284565 659599276942871867229899 := by
  unfold tailWord_1284565
  simp only [CollatzResearch.WordTrace]
  refine ⟨46851934591247866080879149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31234623060831910720586099 46851934591247866080879149)
  ·
    refine ⟨17569475471717949780329681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46851934591247866080879149 17569475471717949780329681)
    ·
      refine ⟨13177106603788462335247261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17569475471717949780329681 13177106603788462335247261)
      ·
        refine ⟨4941414976420673375717723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13177106603788462335247261 4941414976420673375717723)
        ·
          refine ⟨7412122464631010063576585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4941414976420673375717723 7412122464631010063576585)
          ·
            refine ⟨5559091848473257547682439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7412122464631010063576585 5559091848473257547682439)
            ·
              refine ⟨8338637772709886321523659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5559091848473257547682439 8338637772709886321523659)
              ·
                refine ⟨12507956659064829482285489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8338637772709886321523659 12507956659064829482285489)
                ·
                  refine ⟨9380967494298622111714117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12507956659064829482285489 9380967494298622111714117)
                  ·
                    refine ⟨1758931405180991645946397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9380967494298622111714117 1758931405180991645946397)
                    ·
                      refine ⟨659599276942871867229899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1758931405180991645946397 659599276942871867229899)
                      ·
                        rfl

theorem cell23_1284565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 1, 1, 2, 4, 3].length) (baseStart_1284565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1284565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1284565 prefixEnd_1284565 := by exact prefixLift 1284565
  have htrace : WordTrace (prefixWord ++ tailWord_1284565) baseStart_1284565 baseEnd_1284565 := by
    simpa [prefixWord, tailWord_1284565, baseEnd_1284565] using wordTrace_append hprefix tailTrace_1284565
  have hstable : (prefixWord ++ tailWord_1284565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1284565).length < 2 ^ (prefixWord ++ tailWord_1284565).sum := by decide
  have hdescent : baseEnd_1284565 < baseStart_1284565 := by decide
  rcases family_descends (prefixWord ++ tailWord_1284565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1284568 : List Nat := [2, 1, 2, 2, 2, 1, 1, 5, 7]
def baseStart_1284568 : Nat := 118140960795 + 1284568 * 2 ^ 59
def prefixEnd_1284568 : Nat := 4983230072969 + 3 ^ 40 * 1284568 * 2
def baseEnd_1284568 : Nat := 73288979709426150610265

theorem tailTrace_1284568 : CollatzResearch.WordTrace tailWord_1284568 prefixEnd_1284568 73288979709426150610265 := by
  unfold tailWord_1284568
  simp only [CollatzResearch.WordTrace]
  refine ⟨23426022005118498796619179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31234696006824665062158905 23426022005118498796619179)
  ·
    refine ⟨35139033007677748194928769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23426022005118498796619179 35139033007677748194928769)
    ·
      refine ⟨26354274755758311146196577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35139033007677748194928769 26354274755758311146196577)
      ·
        refine ⟨19765706066818733359647433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26354274755758311146196577 19765706066818733359647433)
        ·
          refine ⟨14824279550114050019735575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19765706066818733359647433 14824279550114050019735575)
          ·
            refine ⟨22236419325171075029603363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14824279550114050019735575 22236419325171075029603363)
            ·
              refine ⟨33354628987756612544405045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22236419325171075029603363 33354628987756612544405045)
              ·
                refine ⟨3126996467602182426037973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 33354628987756612544405045 3126996467602182426037973)
                ·
                  refine ⟨73288979709426150610265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3126996467602182426037973 73288979709426150610265)
                  ·
                    rfl

theorem cell23_1284568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 5, 7].length) (baseStart_1284568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1284568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1284568 prefixEnd_1284568 := by exact prefixLift 1284568
  have htrace : WordTrace (prefixWord ++ tailWord_1284568) baseStart_1284568 baseEnd_1284568 := by
    simpa [prefixWord, tailWord_1284568, baseEnd_1284568] using wordTrace_append hprefix tailTrace_1284568
  have hstable : (prefixWord ++ tailWord_1284568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1284568).length < 2 ^ (prefixWord ++ tailWord_1284568).sum := by decide
  have hdescent : baseEnd_1284568 < baseStart_1284568 := by decide
  rcases family_descends (prefixWord ++ tailWord_1284568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1284575 : List Nat := [1, 1, 2, 3, 3, 3, 1, 1, 2, 2, 4]
def baseStart_1284575 : Nat := 118140960795 + 1284575 * 2 ^ 59
def prefixEnd_1284575 : Nat := 4983230072969 + 3 ^ 40 * 1284575 * 2
def baseEnd_1284575 : Nat := 659604411749416828104853

theorem tailTrace_1284575 : CollatzResearch.WordTrace tailWord_1284575 prefixEnd_1284575 659604411749416828104853 := by
  unfold tailWord_1284575
  simp only [CollatzResearch.WordTrace]
  refine ⟨46852299321211637788743179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31234866214141091859162119 46852299321211637788743179)
  ·
    refine ⟨70278448981817456683114769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46852299321211637788743179 70278448981817456683114769)
    ·
      refine ⟨52708836736363092512336077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70278448981817456683114769 52708836736363092512336077)
      ·
        refine ⟨19765813776136159692126029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52708836736363092512336077 19765813776136159692126029)
        ·
          refine ⟨7412180166051059884547261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19765813776136159692126029 7412180166051059884547261)
          ·
            refine ⟨2779567562269147456705223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7412180166051059884547261 2779567562269147456705223)
            ·
              refine ⟨4169351343403721185057835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2779567562269147456705223 4169351343403721185057835)
              ·
                refine ⟨6254027015105581777586753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4169351343403721185057835 6254027015105581777586753)
                ·
                  refine ⟨4690520261329186333190065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6254027015105581777586753 4690520261329186333190065)
                  ·
                    refine ⟨3517890195996889749892549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4690520261329186333190065 3517890195996889749892549)
                    ·
                      refine ⟨659604411749416828104853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3517890195996889749892549 659604411749416828104853)
                      ·
                        rfl

theorem cell23_1284575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 1, 1, 2, 2, 4].length) (baseStart_1284575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1284575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1284575 prefixEnd_1284575 := by exact prefixLift 1284575
  have htrace : WordTrace (prefixWord ++ tailWord_1284575) baseStart_1284575 baseEnd_1284575 := by
    simpa [prefixWord, tailWord_1284575, baseEnd_1284575] using wordTrace_append hprefix tailTrace_1284575
  have hstable : (prefixWord ++ tailWord_1284575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1284575).length < 2 ^ (prefixWord ++ tailWord_1284575).sum := by decide
  have hdescent : baseEnd_1284575 < baseStart_1284575 := by decide
  rcases family_descends (prefixWord ++ tailWord_1284575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1284579 : List Nat := [1, 1, 1, 6, 3, 1, 2, 1, 1, 4, 2]
def baseStart_1284579 : Nat := 118140960795 + 1284579 * 2 ^ 59
def prefixEnd_1284579 : Nat := 4983230072969 + 3 ^ 40 * 1284579 * 2
def baseEnd_1284579 : Nat := 659606465672034812454835

theorem tailTrace_1284579 : CollatzResearch.WordTrace tailWord_1284579 prefixEnd_1284579 659606465672034812454835 := by
  unfold tailWord_1284579
  simp only [CollatzResearch.WordTrace]
  refine ⟨46852445213197146471888791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31234963475464764314592527 46852445213197146471888791)
  ·
    refine ⟨70278667819795719707833187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46852445213197146471888791 70278667819795719707833187)
    ·
      refine ⟨105418001729693579561749781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70278667819795719707833187 105418001729693579561749781)
      ·
        refine ⟨4941468831079386541957021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 105418001729693579561749781 4941468831079386541957021)
        ·
          refine ⟨1853050811654769953233883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4941468831079386541957021 1853050811654769953233883)
          ·
            refine ⟨2779576217482154929850825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1853050811654769953233883 2779576217482154929850825)
            ·
              refine ⟨2084682163111616197388119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2779576217482154929850825 2084682163111616197388119)
              ·
                refine ⟨3127023244667424296082179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2084682163111616197388119 3127023244667424296082179)
                ·
                  refine ⟨4690534867001136444123269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3127023244667424296082179 4690534867001136444123269)
                  ·
                    refine ⟨879475287562713083273113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4690534867001136444123269 879475287562713083273113)
                    ·
                      refine ⟨659606465672034812454835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 879475287562713083273113 659606465672034812454835)
                      ·
                        rfl

theorem cell23_1284579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 2, 1, 1, 4, 2].length) (baseStart_1284579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1284579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1284579 prefixEnd_1284579 := by exact prefixLift 1284579
  have htrace : WordTrace (prefixWord ++ tailWord_1284579) baseStart_1284579 baseEnd_1284579 := by
    simpa [prefixWord, tailWord_1284579, baseEnd_1284579] using wordTrace_append hprefix tailTrace_1284579
  have hstable : (prefixWord ++ tailWord_1284579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1284579).length < 2 ^ (prefixWord ++ tailWord_1284579).sum := by decide
  have hdescent : baseEnd_1284579 < baseStart_1284579 := by decide
  rcases family_descends (prefixWord ++ tailWord_1284579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1284612 : List Nat := [2, 3, 2, 3, 1, 1, 1, 2, 2, 3, 3]
def baseStart_1284612 : Nat := 118140960795 + 1284612 * 2 ^ 59
def prefixEnd_1284612 : Nat := 4983230072969 + 3 ^ 40 * 1284612 * 2
def baseEnd_1284612 : Nat := 659623410533633183342183

theorem tailTrace_1284612 : CollatzResearch.WordTrace tailWord_1284612 prefixEnd_1284612 659623410533633183342183 := by
  unfold tailWord_1284612
  simp only [CollatzResearch.WordTrace]
  refine ⟨23426824411038796553920045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31235765881385062071893393 23426824411038796553920045)
  ·
    refine ⟨8785059154139548707720017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23426824411038796553920045 8785059154139548707720017)
    ·
      refine ⟨6588794365604661530790013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8785059154139548707720017 6588794365604661530790013)
      ·
        refine ⟨2470797887101748074046255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6588794365604661530790013 2470797887101748074046255)
        ·
          refine ⟨3706196830652622111069383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2470797887101748074046255 3706196830652622111069383)
          ·
            refine ⟨5559295245978933166604075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3706196830652622111069383 5559295245978933166604075)
            ·
              refine ⟨8338942868968399749906113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5559295245978933166604075 8338942868968399749906113)
              ·
                refine ⟨6254207151726299812429585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8338942868968399749906113 6254207151726299812429585)
                ·
                  refine ⟨4690655363794724859322189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6254207151726299812429585 4690655363794724859322189)
                  ·
                    refine ⟨1758995761423021822245821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4690655363794724859322189 1758995761423021822245821)
                    ·
                      refine ⟨659623410533633183342183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1758995761423021822245821 659623410533633183342183)
                      ·
                        rfl

theorem cell23_1284612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 1, 2, 2, 3, 3].length) (baseStart_1284612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1284612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1284612 prefixEnd_1284612 := by exact prefixLift 1284612
  have htrace : WordTrace (prefixWord ++ tailWord_1284612) baseStart_1284612 baseEnd_1284612 := by
    simpa [prefixWord, tailWord_1284612, baseEnd_1284612] using wordTrace_append hprefix tailTrace_1284612
  have hstable : (prefixWord ++ tailWord_1284612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1284612).length < 2 ^ (prefixWord ++ tailWord_1284612).sum := by decide
  have hdescent : baseEnd_1284612 < baseStart_1284612 := by decide
  rcases family_descends (prefixWord ++ tailWord_1284612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1284655 : List Nat := [1, 1, 2, 1, 2, 1, 1, 1, 8, 2, 3]
def baseStart_1284655 : Nat := 118140960795 + 1284655 * 2 ^ 59
def prefixEnd_1284655 : Nat := 4983230072969 + 3 ^ 40 * 1284655 * 2
def baseEnd_1284655 : Nat := 659645490201776515104485

theorem tailTrace_1284655 : CollatzResearch.WordTrace tailWord_1284655 prefixEnd_1284655 659645490201776515104485 := by
  unfold tailWord_1284655
  simp only [CollatzResearch.WordTrace]
  refine ⟨46855217160921811451655419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31236811440614540967770279 46855217160921811451655419)
  ·
    refine ⟨70282825741382717177483129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46855217160921811451655419 70282825741382717177483129)
    ·
      refine ⟨52712119306037037883112347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70282825741382717177483129 52712119306037037883112347)
      ·
        refine ⟨79068178959055556824668521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52712119306037037883112347 79068178959055556824668521)
        ·
          refine ⟨59301134219291667618501391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79068178959055556824668521 59301134219291667618501391)
          ·
            refine ⟨88951701328937501427752087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59301134219291667618501391 88951701328937501427752087)
            ·
              refine ⟨133427551993406252141628131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 88951701328937501427752087 133427551993406252141628131)
              ·
                refine ⟨200141327990109378212442197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 133427551993406252141628131 200141327990109378212442197)
                ·
                  refine ⟨2345406187384094275927057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 200141327990109378212442197 2345406187384094275927057)
                  ·
                    refine ⟨1759054640538070706945293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2345406187384094275927057 1759054640538070706945293)
                    ·
                      refine ⟨659645490201776515104485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1759054640538070706945293 659645490201776515104485)
                      ·
                        rfl

theorem cell23_1284655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 1, 8, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 1, 8, 2, 3].length) (baseStart_1284655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1284655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1284655 prefixEnd_1284655 := by exact prefixLift 1284655
  have htrace : WordTrace (prefixWord ++ tailWord_1284655) baseStart_1284655 baseEnd_1284655 := by
    simpa [prefixWord, tailWord_1284655, baseEnd_1284655] using wordTrace_append hprefix tailTrace_1284655
  have hstable : (prefixWord ++ tailWord_1284655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1284655).length < 2 ^ (prefixWord ++ tailWord_1284655).sum := by decide
  have hdescent : baseEnd_1284655 < baseStart_1284655 := by decide
  rcases family_descends (prefixWord ++ tailWord_1284655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1284676 : List Nat := [2, 3, 5, 1, 1, 1, 1, 1, 1, 2, 5]
def baseStart_1284676 : Nat := 118140960795 + 1284676 * 2 ^ 59
def prefixEnd_1284676 : Nat := 4983230072969 + 3 ^ 40 * 1284676 * 2
def baseEnd_1284676 : Nat := 659656273295520932941889

theorem tailTrace_1284676 : CollatzResearch.WordTrace tailWord_1284676 prefixEnd_1284676 659656273295520932941889 := by
  unfold tailWord_1284676
  simp only [CollatzResearch.WordTrace]
  refine ⟨23427991546922866019084941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31237322062563821358779921 23427991546922866019084941)
  ·
    refine ⟨8785496830096074757156853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23427991546922866019084941 8785496830096074757156853)
    ·
      refine ⟨823640327821507008483455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 8785496830096074757156853 823640327821507008483455)
      ·
        refine ⟨1235460491732260512725183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 823640327821507008483455 1235460491732260512725183)
        ·
          refine ⟨1853190737598390769087775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1235460491732260512725183 1853190737598390769087775)
          ·
            refine ⟨2779786106397586153631663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1853190737598390769087775 2779786106397586153631663)
            ·
              refine ⟨4169679159596379230447495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2779786106397586153631663 4169679159596379230447495)
              ·
                refine ⟨6254518739394568845671243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4169679159596379230447495 6254518739394568845671243)
                ·
                  refine ⟨9381778109091853268506865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6254518739394568845671243 9381778109091853268506865)
                  ·
                    refine ⟨7036333581818889951380149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9381778109091853268506865 7036333581818889951380149)
                    ·
                      refine ⟨659656273295520932941889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7036333581818889951380149 659656273295520932941889)
                      ·
                        rfl

theorem cell23_1284676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 1, 1, 1, 2, 5].length) (baseStart_1284676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1284676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1284676 prefixEnd_1284676 := by exact prefixLift 1284676
  have htrace : WordTrace (prefixWord ++ tailWord_1284676) baseStart_1284676 baseEnd_1284676 := by
    simpa [prefixWord, tailWord_1284676, baseEnd_1284676] using wordTrace_append hprefix tailTrace_1284676
  have hstable : (prefixWord ++ tailWord_1284676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1284676).length < 2 ^ (prefixWord ++ tailWord_1284676).sum := by decide
  have hdescent : baseEnd_1284676 < baseStart_1284676 := by decide
  rcases family_descends (prefixWord ++ tailWord_1284676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1284679 : List Nat := [1, 1, 4, 1, 4, 3, 1, 1, 3, 4]
def baseStart_1284679 : Nat := 118140960795 + 1284679 * 2 ^ 59
def prefixEnd_1284679 : Nat := 4983230072969 + 3 ^ 40 * 1284679 * 2
def baseEnd_1284679 : Nat := 219885937912494807068125

theorem tailTrace_1284679 : CollatzResearch.WordTrace tailWord_1284679 prefixEnd_1284679 219885937912494807068125 := by
  unfold tailWord_1284679
  simp only [CollatzResearch.WordTrace]
  refine ⟨46856092512834863550529091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31237395008556575700352727 46856092512834863550529091)
  ·
    refine ⟨70284138769252295325793637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46856092512834863550529091 70284138769252295325793637)
    ·
      refine ⟨13178276019234805373586307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 70284138769252295325793637 13178276019234805373586307)
      ·
        refine ⟨19767414028852208060379461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13178276019234805373586307 19767414028852208060379461)
        ·
          refine ⟨3706390130409789011321149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19767414028852208060379461 3706390130409789011321149)
          ·
            refine ⟨1389896298903670879245431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3706390130409789011321149 1389896298903670879245431)
            ·
              refine ⟨2084844448355506318868147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1389896298903670879245431 2084844448355506318868147)
              ·
                refine ⟨3127266672533259478302221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2084844448355506318868147 3127266672533259478302221)
                ·
                  refine ⟨1172725002199972304363333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3127266672533259478302221 1172725002199972304363333)
                  ·
                    refine ⟨219885937912494807068125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1172725002199972304363333 219885937912494807068125)
                    ·
                      rfl

theorem cell23_1284679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 3, 1, 1, 3, 4].length) (baseStart_1284679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1284679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1284679 prefixEnd_1284679 := by exact prefixLift 1284679
  have htrace : WordTrace (prefixWord ++ tailWord_1284679) baseStart_1284679 baseEnd_1284679 := by
    simpa [prefixWord, tailWord_1284679, baseEnd_1284679] using wordTrace_append hprefix tailTrace_1284679
  have hstable : (prefixWord ++ tailWord_1284679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1284679).length < 2 ^ (prefixWord ++ tailWord_1284679).sum := by decide
  have hdescent : baseEnd_1284679 < baseStart_1284679 := by decide
  rcases family_descends (prefixWord ++ tailWord_1284679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1284692 : List Nat := [2, 4, 1, 1, 1, 4, 1, 3, 6]
def baseStart_1284692 : Nat := 118140960795 + 1284692 * 2 ^ 59
def prefixEnd_1284692 : Nat := 4983230072969 + 3 ^ 40 * 1284692 * 2
def baseEnd_1284692 : Nat := 73296054331776985593535

theorem tailTrace_1284692 : CollatzResearch.WordTrace tailWord_1284692 prefixEnd_1284692 73296054331776985593535 := by
  unfold tailWord_1284692
  simp only [CollatzResearch.WordTrace]
  refine ⟨23428283330893883385376165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31237711107858511180501553 23428283330893883385376165)
  ·
    refine ⟨4392803124542603134758031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23428283330893883385376165 4392803124542603134758031)
    ·
      refine ⟨6589204686813904702137047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4392803124542603134758031 6589204686813904702137047)
      ·
        refine ⟨9883807030220857053205571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6589204686813904702137047 9883807030220857053205571)
        ·
          refine ⟨14825710545331285579808357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9883807030220857053205571 14825710545331285579808357)
          ·
            refine ⟨2779820727249616046214067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14825710545331285579808357 2779820727249616046214067)
            ·
              refine ⟨4169731090874424069321101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2779820727249616046214067 4169731090874424069321101)
              ·
                refine ⟨1563649159077909025995413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4169731090874424069321101 1563649159077909025995413)
                ·
                  refine ⟨73296054331776985593535, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1563649159077909025995413 73296054331776985593535)
                  ·
                    rfl

theorem cell23_1284692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 1, 3, 6].length) (baseStart_1284692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1284692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1284692 prefixEnd_1284692 := by exact prefixLift 1284692
  have htrace : WordTrace (prefixWord ++ tailWord_1284692) baseStart_1284692 baseEnd_1284692 := by
    simpa [prefixWord, tailWord_1284692, baseEnd_1284692] using wordTrace_append hprefix tailTrace_1284692
  have hstable : (prefixWord ++ tailWord_1284692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1284692).length < 2 ^ (prefixWord ++ tailWord_1284692).sum := by decide
  have hdescent : baseEnd_1284692 < baseStart_1284692 := by decide
  rcases family_descends (prefixWord ++ tailWord_1284692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1284729 : List Nat := [1, 2, 1, 3, 3, 2, 2, 2, 2, 3, 2]
def baseStart_1284729 : Nat := 118140960795 + 1284729 * 2 ^ 59
def prefixEnd_1284729 : Nat := 4983230072969 + 3 ^ 40 * 1284729 * 2
def baseEnd_1284729 : Nat := 659683487770209225579145

theorem tailTrace_1284729 : CollatzResearch.WordTrace tailWord_1284729 prefixEnd_1284729 659683487770209225579145 := by
  unfold tailWord_1284729
  simp only [CollatzResearch.WordTrace]
  refine ⟨46857916162653722089849241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31238610775102481393232827 46857916162653722089849241)
  ·
    refine ⟨35143437121990291567386931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46857916162653722089849241 35143437121990291567386931)
    ·
      refine ⟨52715155682985437351080397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35143437121990291567386931 52715155682985437351080397)
      ·
        refine ⟨19768183381119539006655149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52715155682985437351080397 19768183381119539006655149)
        ·
          refine ⟨7413068767919827127495681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19768183381119539006655149 7413068767919827127495681)
          ·
            refine ⟨5559801575939870345621761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7413068767919827127495681 5559801575939870345621761)
            ·
              refine ⟨4169851181954902759216321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5559801575939870345621761 4169851181954902759216321)
              ·
                refine ⟨3127388386466177069412241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4169851181954902759216321 3127388386466177069412241)
                ·
                  refine ⟨2345541289849632802059181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3127388386466177069412241 2345541289849632802059181)
                  ·
                    refine ⟨879577983693612300772193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2345541289849632802059181 879577983693612300772193)
                    ·
                      refine ⟨659683487770209225579145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 879577983693612300772193 659683487770209225579145)
                      ·
                        rfl

theorem cell23_1284729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 2, 2, 2, 3, 2].length) (baseStart_1284729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1284729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1284729 prefixEnd_1284729 := by exact prefixLift 1284729
  have htrace : WordTrace (prefixWord ++ tailWord_1284729) baseStart_1284729 baseEnd_1284729 := by
    simpa [prefixWord, tailWord_1284729, baseEnd_1284729] using wordTrace_append hprefix tailTrace_1284729
  have hstable : (prefixWord ++ tailWord_1284729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1284729).length < 2 ^ (prefixWord ++ tailWord_1284729).sum := by decide
  have hdescent : baseEnd_1284729 < baseStart_1284729 := by decide
  rcases family_descends (prefixWord ++ tailWord_1284729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1284736 : List Nat := [2, 1, 1, 2, 1, 6, 1, 4, 1, 1, 3]
def baseStart_1284736 : Nat := 118140960795 + 1284736 * 2 ^ 59
def prefixEnd_1284736 : Nat := 4983230072969 + 3 ^ 40 * 1284736 * 2
def baseEnd_1284736 : Nat := 659687082134790698191613

theorem tailTrace_1284736 : CollatzResearch.WordTrace tailWord_1284736 prefixEnd_1284736 659687082134790698191613 := by
  unfold tailWord_1284736
  simp only [CollatzResearch.WordTrace]
  refine ⟨23429085736814181142677031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31238780982418908190236041 23429085736814181142677031)
  ·
    refine ⟨35143628605221271714015547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23429085736814181142677031 35143628605221271714015547)
    ·
      refine ⟨52715442907831907571023321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35143628605221271714015547 52715442907831907571023321)
      ·
        refine ⟨39536582180873930678267491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52715442907831907571023321 39536582180873930678267491)
        ·
          refine ⟨59304873271310896017401237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39536582180873930678267491 59304873271310896017401237)
          ·
            refine ⟨2779915934592698250815683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 59304873271310896017401237 2779915934592698250815683)
            ·
              refine ⟨4169873901889047376223525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2779915934592698250815683 4169873901889047376223525)
              ·
                refine ⟨781851356604196383041911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4169873901889047376223525 781851356604196383041911)
                ·
                  refine ⟨1172777034906294574562867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 781851356604196383041911 1172777034906294574562867)
                  ·
                    refine ⟨1759165552359441861844301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1172777034906294574562867 1759165552359441861844301)
                    ·
                      refine ⟨659687082134790698191613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1759165552359441861844301 659687082134790698191613)
                      ·
                        rfl

theorem cell23_1284736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 1, 4, 1, 1, 3].length) (baseStart_1284736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1284736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1284736 prefixEnd_1284736 := by exact prefixLift 1284736
  have htrace : WordTrace (prefixWord ++ tailWord_1284736) baseStart_1284736 baseEnd_1284736 := by
    simpa [prefixWord, tailWord_1284736, baseEnd_1284736] using wordTrace_append hprefix tailTrace_1284736
  have hstable : (prefixWord ++ tailWord_1284736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1284736).length < 2 ^ (prefixWord ++ tailWord_1284736).sum := by decide
  have hdescent : baseEnd_1284736 < baseStart_1284736 := by decide
  rcases family_descends (prefixWord ++ tailWord_1284736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1284745 : List Nat := [1, 2, 1, 1, 4, 1, 1, 3, 3, 1, 5]
def baseStart_1284745 : Nat := 118140960795 + 1284745 * 2 ^ 59
def prefixEnd_1284745 : Nat := 4983230072969 + 3 ^ 40 * 1284745 * 2
def baseEnd_1284745 : Nat := 659691703460681162979071

theorem tailTrace_1284745 : CollatzResearch.WordTrace tailWord_1284745 prefixEnd_1284745 659691703460681162979071 := by
  unfold tailWord_1284745
  simp only [CollatzResearch.WordTrace]
  refine ⟨46858499730595756822431689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31238999820397171214954459 46858499730595756822431689)
  ·
    refine ⟨35143874797946817616823767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46858499730595756822431689 35143874797946817616823767)
    ·
      refine ⟨52715812196920226425235651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35143874797946817616823767 52715812196920226425235651)
      ·
        refine ⟨79073718295380339637853477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52715812196920226425235651 79073718295380339637853477)
        ·
          refine ⟨14826322180383813682097527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 79073718295380339637853477 14826322180383813682097527)
          ·
            refine ⟨22239483270575720523146291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14826322180383813682097527 22239483270575720523146291)
            ·
              refine ⟨33359224905863580784719437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22239483270575720523146291 33359224905863580784719437)
              ·
                refine ⟨12509709339698842794269789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33359224905863580784719437 12509709339698842794269789)
                ·
                  refine ⟨4691141002387066047851171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12509709339698842794269789 4691141002387066047851171)
                  ·
                    refine ⟨7036711503580599071776757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4691141002387066047851171 7036711503580599071776757)
                    ·
                      refine ⟨659691703460681162979071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7036711503580599071776757 659691703460681162979071)
                      ·
                        rfl

theorem cell23_1284745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 3, 3, 1, 5].length) (baseStart_1284745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1284745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1284745 prefixEnd_1284745 := by exact prefixLift 1284745
  have htrace : WordTrace (prefixWord ++ tailWord_1284745) baseStart_1284745 baseEnd_1284745 := by
    simpa [prefixWord, tailWord_1284745, baseEnd_1284745] using wordTrace_append hprefix tailTrace_1284745
  have hstable : (prefixWord ++ tailWord_1284745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1284745).length < 2 ^ (prefixWord ++ tailWord_1284745).sum := by decide
  have hdescent : baseEnd_1284745 < baseStart_1284745 := by decide
  rcases family_descends (prefixWord ++ tailWord_1284745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1284755 : List Nat := [1, 1, 1, 2, 1, 2, 2, 2, 5, 2, 4]
def baseStart_1284755 : Nat := 118140960795 + 1284755 * 2 ^ 59
def prefixEnd_1284755 : Nat := 4983230072969 + 3 ^ 40 * 1284755 * 2
def baseEnd_1284755 : Nat := 659696838267226123854025

theorem tailTrace_1284755 : CollatzResearch.WordTrace tailWord_1284755 prefixEnd_1284755 659696838267226123854025 := by
  unfold tailWord_1284755
  simp only [CollatzResearch.WordTrace]
  refine ⟨46858864460559528530295719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31239242973706352353530479 46858864460559528530295719)
  ·
    refine ⟨70288296690839292795443579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46858864460559528530295719 70288296690839292795443579)
    ·
      refine ⟨105432445036258939193165369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70288296690839292795443579 105432445036258939193165369)
      ·
        refine ⟨79074333777194204394874027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 105432445036258939193165369 79074333777194204394874027)
        ·
          refine ⟨118611500665791306592311041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79074333777194204394874027 118611500665791306592311041)
          ·
            refine ⟨88958625499343479944233281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 118611500665791306592311041 88958625499343479944233281)
            ·
              refine ⟨66718969124507609958174961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 88958625499343479944233281 66718969124507609958174961)
              ·
                refine ⟨50039226843380707468631221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 66718969124507609958174961 50039226843380707468631221)
                ·
                  refine ⟨4691177516566941325184177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 50039226843380707468631221 4691177516566941325184177)
                  ·
                    refine ⟨3518383137425205993888133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4691177516566941325184177 3518383137425205993888133)
                    ·
                      refine ⟨659696838267226123854025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3518383137425205993888133 659696838267226123854025)
                      ·
                        rfl

theorem cell23_1284755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 2, 5, 2, 4].length) (baseStart_1284755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1284755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1284755 prefixEnd_1284755 := by exact prefixLift 1284755
  have htrace : WordTrace (prefixWord ++ tailWord_1284755) baseStart_1284755 baseEnd_1284755 := by
    simpa [prefixWord, tailWord_1284755, baseEnd_1284755] using wordTrace_append hprefix tailTrace_1284755
  have hstable : (prefixWord ++ tailWord_1284755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1284755).length < 2 ^ (prefixWord ++ tailWord_1284755).sum := by decide
  have hdescent : baseEnd_1284755 < baseStart_1284755 := by decide
  rcases family_descends (prefixWord ++ tailWord_1284755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1284765 : List Nat := [1, 4, 2, 1, 1, 1, 2, 11]
def baseStart_1284765 : Nat := 118140960795 + 1284765 * 2 ^ 59
def prefixEnd_1284765 : Nat := 4983230072969 + 3 ^ 40 * 1284765 * 2
def baseEnd_1284765 : Nat := 24433406410139669804777

theorem tailTrace_1284765 : CollatzResearch.WordTrace tailWord_1284765 prefixEnd_1284765 24433406410139669804777 := by
  unfold tailWord_1284765
  simp only [CollatzResearch.WordTrace]
  refine ⟨46859229190523300238159749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31239486127015533492106499 46859229190523300238159749)
  ·
    refine ⟨8786105473223118794654953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 46859229190523300238159749 8786105473223118794654953)
    ·
      refine ⟨6589579104917339095991215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8786105473223118794654953 6589579104917339095991215)
      ·
        refine ⟨9884368657376008643986823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6589579104917339095991215 9884368657376008643986823)
        ·
          refine ⟨14826552986064012965980235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9884368657376008643986823 14826552986064012965980235)
          ·
            refine ⟨22239829479096019448970353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14826552986064012965980235 22239829479096019448970353)
            ·
              refine ⟨16679872109322014586727765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22239829479096019448970353 16679872109322014586727765)
              ·
                refine ⟨24433406410139669804777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 16679872109322014586727765 24433406410139669804777)
                ·
                  rfl

theorem cell23_1284765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 11].length) (baseStart_1284765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1284765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1284765 prefixEnd_1284765 := by exact prefixLift 1284765
  have htrace : WordTrace (prefixWord ++ tailWord_1284765) baseStart_1284765 baseEnd_1284765 := by
    simpa [prefixWord, tailWord_1284765, baseEnd_1284765] using wordTrace_append hprefix tailTrace_1284765
  have hstable : (prefixWord ++ tailWord_1284765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1284765).length < 2 ^ (prefixWord ++ tailWord_1284765).sum := by decide
  have hdescent : baseEnd_1284765 < baseStart_1284765 := by decide
  rcases family_descends (prefixWord ++ tailWord_1284765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1284772 : List Nat := [2, 3, 1, 2, 2, 1, 1, 4, 1, 2, 4]
def baseStart_1284772 : Nat := 118140960795 + 1284772 * 2 ^ 59
def prefixEnd_1284772 : Nat := 4983230072969 + 3 ^ 40 * 1284772 * 2
def baseEnd_1284772 : Nat := 659705567438352557341447

theorem tailTrace_1284772 : CollatzResearch.WordTrace tailWord_1284772 prefixEnd_1284772 659705567438352557341447 := by
  unfold tailWord_1284772
  simp only [CollatzResearch.WordTrace]
  refine ⟨23429742250748970216832285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31239656334331960289109713 23429742250748970216832285)
  ·
    refine ⟨8786153344030863831312107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23429742250748970216832285 8786153344030863831312107)
    ·
      refine ⟨13179230016046295746968161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8786153344030863831312107 13179230016046295746968161)
      ·
        refine ⟨9884422512034721810226121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13179230016046295746968161 9884422512034721810226121)
        ·
          refine ⟨7413316884026041357669591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9884422512034721810226121 7413316884026041357669591)
          ·
            refine ⟨11119975326039062036504387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7413316884026041357669591 11119975326039062036504387)
            ·
              refine ⟨16679962989058593054756581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11119975326039062036504387 16679962989058593054756581)
              ·
                refine ⟨3127493060448486197766859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16679962989058593054756581 3127493060448486197766859)
                ·
                  refine ⟨4691239590672729296650289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3127493060448486197766859 4691239590672729296650289)
                  ·
                    refine ⟨3518429693004546972487717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4691239590672729296650289 3518429693004546972487717)
                    ·
                      refine ⟨659705567438352557341447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3518429693004546972487717 659705567438352557341447)
                      ·
                        rfl

theorem cell23_1284772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 4, 1, 2, 4].length) (baseStart_1284772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1284772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1284772 prefixEnd_1284772 := by exact prefixLift 1284772
  have htrace : WordTrace (prefixWord ++ tailWord_1284772) baseStart_1284772 baseEnd_1284772 := by
    simpa [prefixWord, tailWord_1284772, baseEnd_1284772] using wordTrace_append hprefix tailTrace_1284772
  have hstable : (prefixWord ++ tailWord_1284772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1284772).length < 2 ^ (prefixWord ++ tailWord_1284772).sum := by decide
  have hdescent : baseEnd_1284772 < baseStart_1284772 := by decide
  rcases family_descends (prefixWord ++ tailWord_1284772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1284805 : List Nat := [1, 3, 1, 1, 1, 1, 2, 1, 3, 4, 5]
def baseStart_1284805 : Nat := 118140960795 + 1284805 * 2 ^ 59
def prefixEnd_1284805 : Nat := 4983230072969 + 3 ^ 40 * 1284805 * 2
def baseEnd_1284805 : Nat := 659722512299950928228795

theorem tailTrace_1284805 : CollatzResearch.WordTrace tailWord_1284805 prefixEnd_1284805 659722512299950928228795 := by
  unfold tailWord_1284805
  simp only [CollatzResearch.WordTrace]
  refine ⟨46860688110378387069615869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31240458740252258046410579 46860688110378387069615869)
  ·
    refine ⟨17572758041391895151105951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46860688110378387069615869 17572758041391895151105951)
    ·
      refine ⟨26359137062087842726658927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17572758041391895151105951 26359137062087842726658927)
      ·
        refine ⟨39538705593131764089988391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26359137062087842726658927 39538705593131764089988391)
        ·
          refine ⟨59308058389697646134982587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39538705593131764089988391 59308058389697646134982587)
          ·
            refine ⟨88962087584546469202473881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59308058389697646134982587 88962087584546469202473881)
            ·
              refine ⟨66721565688409851901855411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 88962087584546469202473881 66721565688409851901855411)
              ·
                refine ⟨100082348532614777852783117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 66721565688409851901855411 100082348532614777852783117)
                ·
                  refine ⟨37530880699730541694793669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 100082348532614777852783117 37530880699730541694793669)
                  ·
                    refine ⟨7037040131199476567773813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 37530880699730541694793669 7037040131199476567773813)
                    ·
                      refine ⟨659722512299950928228795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7037040131199476567773813 659722512299950928228795)
                      ·
                        rfl

theorem cell23_1284805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 1, 3, 4, 5].length) (baseStart_1284805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1284805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1284805 prefixEnd_1284805 := by exact prefixLift 1284805
  have htrace : WordTrace (prefixWord ++ tailWord_1284805) baseStart_1284805 baseEnd_1284805 := by
    simpa [prefixWord, tailWord_1284805, baseEnd_1284805] using wordTrace_append hprefix tailTrace_1284805
  have hstable : (prefixWord ++ tailWord_1284805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1284805).length < 2 ^ (prefixWord ++ tailWord_1284805).sum := by decide
  have hdescent : baseEnd_1284805 < baseStart_1284805 := by decide
  rcases family_descends (prefixWord ++ tailWord_1284805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1284836 : List Nat := [2, 3, 1, 1, 1, 4, 2, 3, 1, 3, 2]
def baseStart_1284836 : Nat := 118140960795 + 1284836 * 2 ^ 59
def prefixEnd_1284836 : Nat := 4983230072969 + 3 ^ 40 * 1284836 * 2
def baseEnd_1284836 : Nat := 659738430200240306941153

theorem tailTrace_1284836 : CollatzResearch.WordTrace tailWord_1284836 prefixEnd_1284836 659738430200240306941153 := by
  unfold tailWord_1284836
  simp only [CollatzResearch.WordTrace]
  refine ⟨23430909386633039681997181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31241212515510719575996241 23430909386633039681997181)
  ·
    refine ⟨8786591019987389880748943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23430909386633039681997181 8786591019987389880748943)
    ·
      refine ⟨13179886529981084821123415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8786591019987389880748943 13179886529981084821123415)
      ·
        refine ⟨19769829794971627231685123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13179886529981084821123415 19769829794971627231685123)
        ·
          refine ⟨29654744692457440847527685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19769829794971627231685123 29654744692457440847527685)
          ·
            refine ⟨5560264629835770158911441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 29654744692457440847527685 5560264629835770158911441)
            ·
              refine ⟨4170198472376827619183581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5560264629835770158911441 4170198472376827619183581)
              ·
                refine ⟨1563824427141310357193843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4170198472376827619183581 1563824427141310357193843)
                ·
                  refine ⟨2345736640711965535790765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1563824427141310357193843 2345736640711965535790765)
                  ·
                    refine ⟨879651240266987075921537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2345736640711965535790765 879651240266987075921537)
                    ·
                      refine ⟨659738430200240306941153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 879651240266987075921537 659738430200240306941153)
                      ·
                        rfl

theorem cell23_1284836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 2, 3, 1, 3, 2].length) (baseStart_1284836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1284836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1284836 prefixEnd_1284836 := by exact prefixLift 1284836
  have htrace : WordTrace (prefixWord ++ tailWord_1284836) baseStart_1284836 baseEnd_1284836 := by
    simpa [prefixWord, tailWord_1284836, baseEnd_1284836] using wordTrace_append hprefix tailTrace_1284836
  have hstable : (prefixWord ++ tailWord_1284836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1284836).length < 2 ^ (prefixWord ++ tailWord_1284836).sum := by decide
  have hdescent : baseEnd_1284836 < baseStart_1284836 := by decide
  rcases family_descends (prefixWord ++ tailWord_1284836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1284900 : List Nat := [2, 3, 1, 3, 3, 1, 2, 2, 2, 2, 2]
def baseStart_1284900 : Nat := 118140960795 + 1284900 * 2 ^ 59
def prefixEnd_1284900 : Nat := 4983230072969 + 3 ^ 40 * 1284900 * 2
def baseEnd_1284900 : Nat := 659771292962128056540859

theorem tailTrace_1284900 : CollatzResearch.WordTrace tailWord_1284900 prefixEnd_1284900 659771292962128056540859 := by
  unfold tailWord_1284900
  simp only [CollatzResearch.WordTrace]
  refine ⟨23432076522517109147162077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31242768696689478862882769 23432076522517109147162077)
  ·
    refine ⟨8787028695943915930185779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23432076522517109147162077 8787028695943915930185779)
    ·
      refine ⟨13180543043915873895278669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8787028695943915930185779 13180543043915873895278669)
      ·
        refine ⟨4942703641468452710729501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13180543043915873895278669 4942703641468452710729501)
        ·
          refine ⟨1853513865550669766523563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4942703641468452710729501 1853513865550669766523563)
          ·
            refine ⟨2780270798326004649785345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1853513865550669766523563 2780270798326004649785345)
            ·
              refine ⟨2085203098744503487339009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2780270798326004649785345 2085203098744503487339009)
              ·
                refine ⟨1563902324058377615504257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2085203098744503487339009 1563902324058377615504257)
                ·
                  refine ⟨1172926743043783211628193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1563902324058377615504257 1172926743043783211628193)
                  ·
                    refine ⟨879695057282837408721145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1172926743043783211628193 879695057282837408721145)
                    ·
                      refine ⟨659771292962128056540859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 879695057282837408721145 659771292962128056540859)
                      ·
                        rfl

theorem cell23_1284900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 2, 2, 2, 2, 2].length) (baseStart_1284900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1284900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1284900 prefixEnd_1284900 := by exact prefixLift 1284900
  have htrace : WordTrace (prefixWord ++ tailWord_1284900) baseStart_1284900 baseEnd_1284900 := by
    simpa [prefixWord, tailWord_1284900, baseEnd_1284900] using wordTrace_append hprefix tailTrace_1284900
  have hstable : (prefixWord ++ tailWord_1284900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1284900).length < 2 ^ (prefixWord ++ tailWord_1284900).sum := by decide
  have hdescent : baseEnd_1284900 < baseStart_1284900 := by decide
  rcases family_descends (prefixWord ++ tailWord_1284900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1284949 : List Nat := [1, 3, 2, 2, 2, 1, 1, 2, 5, 4]
def baseStart_1284949 : Nat := 118140960795 + 1284949 * 2 ^ 59
def prefixEnd_1284949 : Nat := 4983230072969 + 3 ^ 40 * 1284949 * 2
def baseEnd_1284949 : Nat := 219932151171399454942711

theorem tailTrace_1284949 : CollatzResearch.WordTrace tailWord_1284949 prefixEnd_1284949 219932151171399454942711 := by
  unfold tailWord_1284949
  simp only [CollatzResearch.WordTrace]
  refine ⟨46865940221856699662857901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31243960147904466441905267 46865940221856699662857901)
  ·
    refine ⟨17574727583196262373571713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46865940221856699662857901 17574727583196262373571713)
    ·
      refine ⟨13181045687397196780178785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17574727583196262373571713 13181045687397196780178785)
      ·
        refine ⟨9885784265547897585134089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13181045687397196780178785 9885784265547897585134089)
        ·
          refine ⟨7414338199160923188850567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9885784265547897585134089 7414338199160923188850567)
          ·
            refine ⟨11121507298741384783275851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7414338199160923188850567 11121507298741384783275851)
            ·
              refine ⟨16682260948112077174913777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11121507298741384783275851 16682260948112077174913777)
              ·
                refine ⟨12511695711084057881185333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16682260948112077174913777 12511695711084057881185333)
                ·
                  refine ⟨1172971472914130426361125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 12511695711084057881185333 1172971472914130426361125)
                  ·
                    refine ⟨219932151171399454942711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1172971472914130426361125 219932151171399454942711)
                    ·
                      rfl

theorem cell23_1284949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 2, 5, 4].length) (baseStart_1284949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1284949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1284949 prefixEnd_1284949 := by exact prefixLift 1284949
  have htrace : WordTrace (prefixWord ++ tailWord_1284949) baseStart_1284949 baseEnd_1284949 := by
    simpa [prefixWord, tailWord_1284949, baseEnd_1284949] using wordTrace_append hprefix tailTrace_1284949
  have hstable : (prefixWord ++ tailWord_1284949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1284949).length < 2 ^ (prefixWord ++ tailWord_1284949).sum := by decide
  have hdescent : baseEnd_1284949 < baseStart_1284949 := by decide
  rcases family_descends (prefixWord ++ tailWord_1284949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1284952 : List Nat := [2, 1, 2, 2, 1, 1, 1, 2, 1, 6, 4]
def baseStart_1284952 : Nat := 118140960795 + 1284952 * 2 ^ 59
def prefixEnd_1284952 : Nat := 4983230072969 + 3 ^ 40 * 1284952 * 2
def baseEnd_1284952 : Nat := 659797993956161853090619

theorem tailTrace_1284952 : CollatzResearch.WordTrace tailWord_1284952 prefixEnd_1284952 659797993956161853090619 := by
  unfold tailWord_1284952
  simp only [CollatzResearch.WordTrace]
  refine ⟨23433024820422915587608555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31244033093897220783478073 23433024820422915587608555)
  ·
    refine ⟨35149537230634373381412833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23433024820422915587608555 35149537230634373381412833)
    ·
      refine ⟨26362152922975780036059625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35149537230634373381412833 26362152922975780036059625)
      ·
        refine ⟨19771614692231835027044719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26362152922975780036059625 19771614692231835027044719)
        ·
          refine ⟨29657422038347752540567079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19771614692231835027044719 29657422038347752540567079)
          ·
            refine ⟨44486133057521628810850619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29657422038347752540567079 44486133057521628810850619)
            ·
              refine ⟨66729199586282443216275929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44486133057521628810850619 66729199586282443216275929)
              ·
                refine ⟨50046899689711832412206947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 66729199586282443216275929 50046899689711832412206947)
                ·
                  refine ⟨75070349534567748618310421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 50046899689711832412206947 75070349534567748618310421)
                  ·
                    refine ⟨3518922634432863216483301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 75070349534567748618310421 3518922634432863216483301)
                    ·
                      refine ⟨659797993956161853090619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3518922634432863216483301 659797993956161853090619)
                      ·
                        rfl

theorem cell23_1284952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 2, 1, 6, 4].length) (baseStart_1284952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1284952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1284952 prefixEnd_1284952 := by exact prefixLift 1284952
  have htrace : WordTrace (prefixWord ++ tailWord_1284952) baseStart_1284952 baseEnd_1284952 := by
    simpa [prefixWord, tailWord_1284952, baseEnd_1284952] using wordTrace_append hprefix tailTrace_1284952
  have hstable : (prefixWord ++ tailWord_1284952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1284952).length < 2 ^ (prefixWord ++ tailWord_1284952).sum := by decide
  have hdescent : baseEnd_1284952 < baseStart_1284952 := by decide
  rcases family_descends (prefixWord ++ tailWord_1284952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1284959 : List Nat := [1, 1, 2, 3, 1, 3, 2, 1, 4, 2, 3]
def baseStart_1284959 : Nat := 118140960795 + 1284959 * 2 ^ 59
def prefixEnd_1284959 : Nat := 4983230072969 + 3 ^ 40 * 1284959 * 2
def baseEnd_1284959 : Nat := 659801588320743325703087

theorem tailTrace_1284959 : CollatzResearch.WordTrace tailWord_1284959 prefixEnd_1284959 659801588320743325703087 := by
  unfold tailWord_1284959
  simp only [CollatzResearch.WordTrace]
  refine ⟨46866304951820471370721931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31244203301213647580481287 46866304951820471370721931)
  ·
    refine ⟨70299457427730707056082897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46866304951820471370721931 70299457427730707056082897)
    ·
      refine ⟨52724593070798030292062173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70299457427730707056082897 52724593070798030292062173)
      ·
        refine ⟨19771722401549261359523315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52724593070798030292062173 19771722401549261359523315)
        ·
          refine ⟨29657583602323892039284973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19771722401549261359523315 29657583602323892039284973)
          ·
            refine ⟨11121593850871459514731865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29657583602323892039284973 11121593850871459514731865)
            ·
              refine ⟨8341195388153594636048899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11121593850871459514731865 8341195388153594636048899)
              ·
                refine ⟨12511793082230391954073349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8341195388153594636048899 12511793082230391954073349)
                ·
                  refine ⟨2345961202918198491388753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12511793082230391954073349 2345961202918198491388753)
                  ·
                    refine ⟨1759470902188648868541565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2345961202918198491388753 1759470902188648868541565)
                    ·
                      refine ⟨659801588320743325703087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1759470902188648868541565 659801588320743325703087)
                      ·
                        rfl

theorem cell23_1284959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 2, 1, 4, 2, 3].length) (baseStart_1284959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1284959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1284959 prefixEnd_1284959 := by exact prefixLift 1284959
  have htrace : WordTrace (prefixWord ++ tailWord_1284959) baseStart_1284959 baseEnd_1284959 := by
    simpa [prefixWord, tailWord_1284959, baseEnd_1284959] using wordTrace_append hprefix tailTrace_1284959
  have hstable : (prefixWord ++ tailWord_1284959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1284959).length < 2 ^ (prefixWord ++ tailWord_1284959).sum := by decide
  have hdescent : baseEnd_1284959 < baseStart_1284959 := by decide
  rcases family_descends (prefixWord ++ tailWord_1284959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1285000 : List Nat := [2, 1, 3, 3, 2, 3, 1, 3, 1, 4]
def baseStart_1285000 : Nat := 118140960795 + 1285000 * 2 ^ 59
def prefixEnd_1285000 : Nat := 4983230072969 + 3 ^ 40 * 1285000 * 2
def baseEnd_1285000 : Nat := 219940880342525888430133

theorem tailTrace_1285000 : CollatzResearch.WordTrace tailWord_1285000 prefixEnd_1285000 219940880342525888430133 := by
  unfold tailWord_1285000
  simp only [CollatzResearch.WordTrace]
  refine ⟨23433900172335967686482227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31245200229781290248642969 23433900172335967686482227)
  ·
    refine ⟨35150850258503951529723341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23433900172335967686482227 35150850258503951529723341)
    ·
      refine ⟨13181568846938981823646253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35150850258503951529723341 13181568846938981823646253)
      ·
        refine ⟨4943088317602118183867345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13181568846938981823646253 4943088317602118183867345)
        ·
          refine ⟨3707316238201588637900509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4943088317602118183867345 3707316238201588637900509)
          ·
            refine ⟨1390243589325595739212691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3707316238201588637900509 1390243589325595739212691)
            ·
              refine ⟨2085365383988393608819037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1390243589325595739212691 2085365383988393608819037)
              ·
                refine ⟨782012018995647603307139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2085365383988393608819037 782012018995647603307139)
                ·
                  refine ⟨1173018028493471404960709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 782012018995647603307139 1173018028493471404960709)
                  ·
                    refine ⟨219940880342525888430133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1173018028493471404960709 219940880342525888430133)
                    ·
                      rfl

theorem cell23_1285000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 3, 1, 3, 1, 4].length) (baseStart_1285000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1285000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1285000 prefixEnd_1285000 := by exact prefixLift 1285000
  have htrace : WordTrace (prefixWord ++ tailWord_1285000) baseStart_1285000 baseEnd_1285000 := by
    simpa [prefixWord, tailWord_1285000, baseEnd_1285000] using wordTrace_append hprefix tailTrace_1285000
  have hstable : (prefixWord ++ tailWord_1285000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1285000).length < 2 ^ (prefixWord ++ tailWord_1285000).sum := by decide
  have hdescent : baseEnd_1285000 < baseStart_1285000 := by decide
  rcases family_descends (prefixWord ++ tailWord_1285000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1285023 : List Nat := [1, 1, 2, 5, 2, 1, 3, 1, 3, 1, 3]
def baseStart_1285023 : Nat := 118140960795 + 1285023 * 2 ^ 59
def prefixEnd_1285023 : Nat := 4983230072969 + 3 ^ 40 * 1285023 * 2
def baseEnd_1285023 : Nat := 659834451082631075302793

theorem tailTrace_1285023 : CollatzResearch.WordTrace tailWord_1285023 prefixEnd_1285023 659834451082631075302793 := by
  unfold tailWord_1285023
  simp only [CollatzResearch.WordTrace]
  refine ⟨46868639223588610301051723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31245759482392406867367815 46868639223588610301051723)
  ·
    refine ⟨70302958835382915451577585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46868639223588610301051723 70302958835382915451577585)
    ·
      refine ⟨52727219126537186588683189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70302958835382915451577585 52727219126537186588683189)
      ·
        refine ⟨4943176793112861242689049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 52727219126537186588683189 4943176793112861242689049)
        ·
          refine ⟨3707382594834645932016787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4943176793112861242689049 3707382594834645932016787)
          ·
            refine ⟨5561073892251968898025181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3707382594834645932016787 5561073892251968898025181)
            ·
              refine ⟨2085402709594488336759443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5561073892251968898025181 2085402709594488336759443)
              ·
                refine ⟨3128104064391732505139165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2085402709594488336759443 3128104064391732505139165)
                ·
                  refine ⟨1173039024146899689427187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3128104064391732505139165 1173039024146899689427187)
                  ·
                    refine ⟨1759558536220349534140781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1173039024146899689427187 1759558536220349534140781)
                    ·
                      refine ⟨659834451082631075302793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1759558536220349534140781 659834451082631075302793)
                      ·
                        rfl

theorem cell23_1285023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 3, 1, 3, 1, 3].length) (baseStart_1285023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1285023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1285023 prefixEnd_1285023 := by exact prefixLift 1285023
  have htrace : WordTrace (prefixWord ++ tailWord_1285023) baseStart_1285023 baseEnd_1285023 := by
    simpa [prefixWord, tailWord_1285023, baseEnd_1285023] using wordTrace_append hprefix tailTrace_1285023
  have hstable : (prefixWord ++ tailWord_1285023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1285023).length < 2 ^ (prefixWord ++ tailWord_1285023).sum := by decide
  have hdescent : baseEnd_1285023 < baseStart_1285023 := by decide
  rcases family_descends (prefixWord ++ tailWord_1285023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1285039 : List Nat := [1, 1, 2, 1, 2, 2, 2, 2, 6, 4]
def baseStart_1285039 : Nat := 118140960795 + 1285039 * 2 ^ 59
def prefixEnd_1285039 : Nat := 4983230072969 + 3 ^ 40 * 1285039 * 2
def baseEnd_1285039 : Nat := 219947555591034337567573

theorem tailTrace_1285039 : CollatzResearch.WordTrace tailWord_1285039 prefixEnd_1285039 219947555591034337567573 := by
  unfold tailWord_1285039
  simp only [CollatzResearch.WordTrace]
  refine ⟨46869222791530645033634171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31246148527687096689089447 46869222791530645033634171)
  ·
    refine ⟨70303834187295967550451257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46869222791530645033634171 70303834187295967550451257)
    ·
      refine ⟨52727875640471975662838443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70303834187295967550451257 52727875640471975662838443)
      ·
        refine ⟨79091813460707963494257665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52727875640471975662838443 79091813460707963494257665)
        ·
          refine ⟨59318860095530972620693249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79091813460707963494257665 59318860095530972620693249)
          ·
            refine ⟨44489145071648229465519937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59318860095530972620693249 44489145071648229465519937)
            ·
              refine ⟨33366858803736172099139953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44489145071648229465519937 33366858803736172099139953)
              ·
                refine ⟨25025144102802129074354965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33366858803736172099139953 25025144102802129074354965)
                ·
                  refine ⟨1173053629818849800360389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 25025144102802129074354965 1173053629818849800360389)
                  ·
                    refine ⟨219947555591034337567573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1173053629818849800360389 219947555591034337567573)
                    ·
                      rfl

theorem cell23_1285039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 2, 6, 4].length) (baseStart_1285039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1285039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1285039 prefixEnd_1285039 := by exact prefixLift 1285039
  have htrace : WordTrace (prefixWord ++ tailWord_1285039) baseStart_1285039 baseEnd_1285039 := by
    simpa [prefixWord, tailWord_1285039, baseEnd_1285039] using wordTrace_append hprefix tailTrace_1285039
  have hstable : (prefixWord ++ tailWord_1285039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1285039).length < 2 ^ (prefixWord ++ tailWord_1285039).sum := by decide
  have hdescent : baseEnd_1285039 < baseStart_1285039 := by decide
  rcases family_descends (prefixWord ++ tailWord_1285039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1285059 : List Nat := [1, 1, 1, 3, 1, 1, 2, 6, 1, 2, 4]
def baseStart_1285059 : Nat := 118140960795 + 1285059 * 2 ^ 59
def prefixEnd_1285059 : Nat := 4983230072969 + 3 ^ 40 * 1285059 * 2
def baseEnd_1285059 : Nat := 659852936386192934452627

theorem tailTrace_1285059 : CollatzResearch.WordTrace tailWord_1285059 prefixEnd_1285059 659852936386192934452627 := by
  unfold tailWord_1285059
  simp only [CollatzResearch.WordTrace]
  refine ⟨46869952251458188449362231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31246634834305458966241487 46869952251458188449362231)
  ·
    refine ⟨70304928377187282674043347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46869952251458188449362231 70304928377187282674043347)
    ·
      refine ⟨105457392565780924011065021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70304928377187282674043347 105457392565780924011065021)
      ·
        refine ⟨39546522212167846504149383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 105457392565780924011065021 39546522212167846504149383)
        ·
          refine ⟨59319783318251769756224075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39546522212167846504149383 59319783318251769756224075)
          ·
            refine ⟨88979674977377654634336113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59319783318251769756224075 88979674977377654634336113)
            ·
              refine ⟨66734756233033240975752085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 88979674977377654634336113 66734756233033240975752085)
              ·
                refine ⟨3128191698423433170738379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 66734756233033240975752085 3128191698423433170738379)
                ·
                  refine ⟨4692287547635149756107569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3128191698423433170738379 4692287547635149756107569)
                  ·
                    refine ⟨3519215660726362317080677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4692287547635149756107569 3519215660726362317080677)
                    ·
                      refine ⟨659852936386192934452627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3519215660726362317080677 659852936386192934452627)
                      ·
                        rfl

theorem cell23_1285059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 6, 1, 2, 4].length) (baseStart_1285059 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1285059 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1285059 prefixEnd_1285059 := by exact prefixLift 1285059
  have htrace : WordTrace (prefixWord ++ tailWord_1285059) baseStart_1285059 baseEnd_1285059 := by
    simpa [prefixWord, tailWord_1285059, baseEnd_1285059] using wordTrace_append hprefix tailTrace_1285059
  have hstable : (prefixWord ++ tailWord_1285059).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1285059).length < 2 ^ (prefixWord ++ tailWord_1285059).sum := by decide
  have hdescent : baseEnd_1285059 < baseStart_1285059 := by decide
  rcases family_descends (prefixWord ++ tailWord_1285059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1285074 : List Nat := [3, 2, 2, 3, 1, 3, 2, 2, 1, 1, 3]
def baseStart_1285074 : Nat := 118140960795 + 1285074 * 2 ^ 59
def prefixEnd_1285074 : Nat := 4983230072969 + 3 ^ 40 * 1285074 * 2
def baseEnd_1285074 : Nat := 659860638596010375765059

theorem tailTrace_1285074 : CollatzResearch.WordTrace tailWord_1285074 prefixEnd_1285074 659860638596010375765059 := by
  unfold tailWord_1285074
  simp only [CollatzResearch.WordTrace]
  refine ⟨11717624836600961502789569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31246999564269230674105517 11717624836600961502789569)
  ·
    refine ⟨8788218627450721127092177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11717624836600961502789569 8788218627450721127092177)
    ·
      refine ⟨6591163970588040845319133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8788218627450721127092177 6591163970588040845319133)
      ·
        refine ⟨2471686488970515316994675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6591163970588040845319133 2471686488970515316994675)
        ·
          refine ⟨3707529733455772975492013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2471686488970515316994675 3707529733455772975492013)
          ·
            refine ⟨1390323650045914865809505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3707529733455772975492013 1390323650045914865809505)
            ·
              refine ⟨1042742737534436149357129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1390323650045914865809505 1042742737534436149357129)
              ·
                refine ⟨782057053150827112017847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1042742737534436149357129 782057053150827112017847)
                ·
                  refine ⟨1173085579726240668026771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 782057053150827112017847 1173085579726240668026771)
                  ·
                    refine ⟨1759628369589361002040157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1173085579726240668026771 1759628369589361002040157)
                    ·
                      refine ⟨659860638596010375765059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1759628369589361002040157 659860638596010375765059)
                      ·
                        rfl

theorem cell23_1285074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 3, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 3, 2, 2, 1, 1, 3].length) (baseStart_1285074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1285074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1285074 prefixEnd_1285074 := by exact prefixLift 1285074
  have htrace : WordTrace (prefixWord ++ tailWord_1285074) baseStart_1285074 baseEnd_1285074 := by
    simpa [prefixWord, tailWord_1285074, baseEnd_1285074] using wordTrace_append hprefix tailTrace_1285074
  have hstable : (prefixWord ++ tailWord_1285074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1285074).length < 2 ^ (prefixWord ++ tailWord_1285074).sum := by decide
  have hdescent : baseEnd_1285074 < baseStart_1285074 := by decide
  rcases family_descends (prefixWord ++ tailWord_1285074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1285090 : List Nat := [3, 3, 3, 1, 1, 1, 2, 3, 2, 4]
def baseStart_1285090 : Nat := 118140960795 + 1285090 * 2 ^ 59
def prefixEnd_1285090 : Nat := 4983230072969 + 3 ^ 40 * 1285090 * 2
def baseEnd_1285090 : Nat := 219956284762160771054995

theorem tailTrace_1285090 : CollatzResearch.WordTrace tailWord_1285090 prefixEnd_1285090 219956284762160771054995 := by
  unfold tailWord_1285090
  simp only [CollatzResearch.WordTrace]
  refine ⟨11717770728586470185935181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31247388609563920495827149 11717770728586470185935181)
  ·
    refine ⟨4394164023219926319725693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11717770728586470185935181 4394164023219926319725693)
    ·
      refine ⟨1647811508707472369897135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4394164023219926319725693 1647811508707472369897135)
      ·
        refine ⟨2471717263061208554845703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1647811508707472369897135 2471717263061208554845703)
        ·
          refine ⟨3707575894591812832268555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2471717263061208554845703 3707575894591812832268555)
          ·
            refine ⟨5561363841887719248402833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3707575894591812832268555 5561363841887719248402833)
            ·
              refine ⟨4171022881415789436302125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5561363841887719248402833 4171022881415789436302125)
              ·
                refine ⟨1564133580530921038613297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4171022881415789436302125 1564133580530921038613297)
                ·
                  refine ⟨1173100185398190778959973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1564133580530921038613297 1173100185398190778959973)
                  ·
                    refine ⟨219956284762160771054995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1173100185398190778959973 219956284762160771054995)
                    ·
                      rfl

theorem cell23_1285090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 2, 3, 2, 4].length) (baseStart_1285090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1285090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1285090 prefixEnd_1285090 := by exact prefixLift 1285090
  have htrace : WordTrace (prefixWord ++ tailWord_1285090) baseStart_1285090 baseEnd_1285090 := by
    simpa [prefixWord, tailWord_1285090, baseEnd_1285090] using wordTrace_append hprefix tailTrace_1285090
  have hstable : (prefixWord ++ tailWord_1285090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1285090).length < 2 ^ (prefixWord ++ tailWord_1285090).sum := by decide
  have hdescent : baseEnd_1285090 < baseStart_1285090 := by decide
  rcases family_descends (prefixWord ++ tailWord_1285090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1285096 : List Nat := [2, 1, 4, 1, 1, 1, 3, 3, 1, 3, 3]
def baseStart_1285096 : Nat := 118140960795 + 1285096 * 2 ^ 59
def prefixEnd_1285096 : Nat := 4983230072969 + 3 ^ 40 * 1285096 * 2
def baseEnd_1285096 : Nat := 659871935170409289689957

theorem tailTrace_1285096 : CollatzResearch.WordTrace tailWord_1285096 prefixEnd_1285096 659871935170409289689957 := by
  unfold tailWord_1285096
  simp only [CollatzResearch.WordTrace]
  refine ⟨23435650876162071884229571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31247534501549429178972761 23435650876162071884229571)
  ·
    refine ⟨35153476314243107826344357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23435650876162071884229571 35153476314243107826344357)
    ·
      refine ⟨6591276808920582717439567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 35153476314243107826344357 6591276808920582717439567)
      ·
        refine ⟨9886915213380874076159351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6591276808920582717439567 9886915213380874076159351)
        ·
          refine ⟨14830372820071311114239027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9886915213380874076159351 14830372820071311114239027)
          ·
            refine ⟨22245559230106966671358541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14830372820071311114239027 22245559230106966671358541)
            ·
              refine ⟨8342084711290112501759453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22245559230106966671358541 8342084711290112501759453)
              ·
                refine ⟨3128281766733792188159795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8342084711290112501759453 3128281766733792188159795)
                ·
                  refine ⟨4692422650100688282239693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3128281766733792188159795 4692422650100688282239693)
                  ·
                    refine ⟨1759658493787758105839885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4692422650100688282239693 1759658493787758105839885)
                    ·
                      refine ⟨659871935170409289689957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1759658493787758105839885 659871935170409289689957)
                      ·
                        rfl

theorem cell23_1285096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 3, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 3, 3, 1, 3, 3].length) (baseStart_1285096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1285096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1285096 prefixEnd_1285096 := by exact prefixLift 1285096
  have htrace : WordTrace (prefixWord ++ tailWord_1285096) baseStart_1285096 baseEnd_1285096 := by
    simpa [prefixWord, tailWord_1285096, baseEnd_1285096] using wordTrace_append hprefix tailTrace_1285096
  have hstable : (prefixWord ++ tailWord_1285096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1285096).length < 2 ^ (prefixWord ++ tailWord_1285096).sum := by decide
  have hdescent : baseEnd_1285096 < baseStart_1285096 := by decide
  rcases family_descends (prefixWord ++ tailWord_1285096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1285108 : List Nat := [2, 6, 2, 1, 1, 1, 2, 3, 1, 1, 3]
def baseStart_1285108 : Nat := 118140960795 + 1285108 * 2 ^ 59
def prefixEnd_1285108 : Nat := 4983230072969 + 3 ^ 40 * 1285108 * 2
def baseEnd_1285108 : Nat := 659878096938263242739903

theorem tailTrace_1285108 : CollatzResearch.WordTrace tailWord_1285108 prefixEnd_1285108 659878096938263242739903 := by
  unfold tailWord_1285108
  simp only [CollatzResearch.WordTrace]
  refine ⟨23435869714140334908947989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31247826285520446545263985 23435869714140334908947989)
  ·
    refine ⟨1098556392850328198856937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 23435869714140334908947989 1098556392850328198856937)
    ·
      refine ⟨823917294637746149142703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1098556392850328198856937 823917294637746149142703)
      ·
        refine ⟨1235875941956619223714055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 823917294637746149142703 1235875941956619223714055)
        ·
          refine ⟨1853813912934928835571083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1235875941956619223714055 1853813912934928835571083)
          ·
            refine ⟨2780720869402393253356625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1853813912934928835571083 2780720869402393253356625)
            ·
              refine ⟨2085540652051794940017469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2780720869402393253356625 2085540652051794940017469)
              ·
                refine ⟨782077744519423102506551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2085540652051794940017469 782077744519423102506551)
                ·
                  refine ⟨1173116616779134653759827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 782077744519423102506551 1173116616779134653759827)
                  ·
                    refine ⟨1759674925168701980639741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1173116616779134653759827 1759674925168701980639741)
                    ·
                      refine ⟨659878096938263242739903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1759674925168701980639741 659878096938263242739903)
                      ·
                        rfl

theorem cell23_1285108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 2, 3, 1, 1, 3].length) (baseStart_1285108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1285108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1285108 prefixEnd_1285108 := by exact prefixLift 1285108
  have htrace : WordTrace (prefixWord ++ tailWord_1285108) baseStart_1285108 baseEnd_1285108 := by
    simpa [prefixWord, tailWord_1285108, baseEnd_1285108] using wordTrace_append hprefix tailTrace_1285108
  have hstable : (prefixWord ++ tailWord_1285108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1285108).length < 2 ^ (prefixWord ++ tailWord_1285108).sum := by decide
  have hdescent : baseEnd_1285108 < baseStart_1285108 := by decide
  rcases family_descends (prefixWord ++ tailWord_1285108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1285130 : List Nat := [3, 1, 2, 2, 3, 1, 3, 2, 2, 1, 3]
def baseStart_1285130 : Nat := 118140960795 + 1285130 * 2 ^ 59
def prefixEnd_1285130 : Nat := 4983230072969 + 3 ^ 40 * 1285130 * 2
def baseEnd_1285130 : Nat := 659889393512662156664801

theorem tailTrace_1285130 : CollatzResearch.WordTrace tailWord_1285130 prefixEnd_1285130 659889393512662156664801 := by
  unfold tailWord_1285130
  simp only [CollatzResearch.WordTrace]
  refine ⟨11718135458550241893799211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31248361222800645050131229 11718135458550241893799211)
  ·
    refine ⟨17577203187825362840698817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11718135458550241893799211 17577203187825362840698817)
    ·
      refine ⟨13182902390869022130524113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17577203187825362840698817 13182902390869022130524113)
      ·
        refine ⟨9887176793151766597893085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13182902390869022130524113 9887176793151766597893085)
        ·
          refine ⟨3707691297431912474209907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9887176793151766597893085 3707691297431912474209907)
          ·
            refine ⟨5561536946147868711314861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3707691297431912474209907 5561536946147868711314861)
            ·
              refine ⟨2085576354805450766743073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5561536946147868711314861 2085576354805450766743073)
              ·
                refine ⟨1564182266104088075057305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2085576354805450766743073 1564182266104088075057305)
                ·
                  refine ⟨1173136699578066056292979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1564182266104088075057305 1173136699578066056292979)
                  ·
                    refine ⟨1759705049367099084439469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1173136699578066056292979 1759705049367099084439469)
                    ·
                      refine ⟨659889393512662156664801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1759705049367099084439469 659889393512662156664801)
                      ·
                        rfl

theorem cell23_1285130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 3, 2, 2, 1, 3].length) (baseStart_1285130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1285130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1285130 prefixEnd_1285130 := by exact prefixLift 1285130
  have htrace : WordTrace (prefixWord ++ tailWord_1285130) baseStart_1285130 baseEnd_1285130 := by
    simpa [prefixWord, tailWord_1285130, baseEnd_1285130] using wordTrace_append hprefix tailTrace_1285130
  have hstable : (prefixWord ++ tailWord_1285130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1285130).length < 2 ^ (prefixWord ++ tailWord_1285130).sum := by decide
  have hdescent : baseEnd_1285130 < baseStart_1285130 := by decide
  rcases family_descends (prefixWord ++ tailWord_1285130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1285139 : List Nat := [1, 1, 1, 2, 1, 4, 1, 2, 4, 1, 5]
def baseStart_1285139 : Nat := 118140960795 + 1285139 * 2 ^ 59
def prefixEnd_1285139 : Nat := 4983230072969 + 3 ^ 40 * 1285139 * 2
def baseEnd_1285139 : Nat := 659894014838552621452259

theorem tailTrace_1285139 : CollatzResearch.WordTrace tailWord_1285139 prefixEnd_1285139 659894014838552621452259 := by
  unfold tailWord_1285139
  simp only [CollatzResearch.WordTrace]
  refine ⟨46872870091168362112274471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31248580060778908074849647 46872870091168362112274471)
  ·
    refine ⟨70309305136752543168411707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46872870091168362112274471 70309305136752543168411707)
    ·
      refine ⟨105463957705128814752617561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70309305136752543168411707 105463957705128814752617561)
      ·
        refine ⟨79097968278846611064463171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 105463957705128814752617561 79097968278846611064463171)
        ·
          refine ⟨118646952418269916596694757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79097968278846611064463171 118646952418269916596694757)
          ·
            refine ⟨22246303578425609361880267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 118646952418269916596694757 22246303578425609361880267)
            ·
              refine ⟨33369455367638414042820401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22246303578425609361880267 33369455367638414042820401)
              ·
                refine ⟨25027091525728810532115301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33369455367638414042820401 25027091525728810532115301)
                ·
                  refine ⟨4692579661074151974771619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25027091525728810532115301 4692579661074151974771619)
                  ·
                    refine ⟨7038869491611227962157429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4692579661074151974771619 7038869491611227962157429)
                    ·
                      refine ⟨659894014838552621452259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7038869491611227962157429 659894014838552621452259)
                      ·
                        rfl

theorem cell23_1285139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 2, 4, 1, 5].length) (baseStart_1285139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1285139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1285139 prefixEnd_1285139 := by exact prefixLift 1285139
  have htrace : WordTrace (prefixWord ++ tailWord_1285139) baseStart_1285139 baseEnd_1285139 := by
    simpa [prefixWord, tailWord_1285139, baseEnd_1285139] using wordTrace_append hprefix tailTrace_1285139
  have hstable : (prefixWord ++ tailWord_1285139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1285139).length < 2 ^ (prefixWord ++ tailWord_1285139).sum := by decide
  have hdescent : baseEnd_1285139 < baseStart_1285139 := by decide
  rcases family_descends (prefixWord ++ tailWord_1285139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1285223 : List Nat := [1, 1, 5, 1, 1, 4, 2, 1, 2, 5]
def baseStart_1285223 : Nat := 118140960795 + 1285223 * 2 ^ 59
def prefixEnd_1285223 : Nat := 4983230072969 + 3 ^ 40 * 1285223 * 2
def baseEnd_1285223 : Nat := 219979049071176764267291

theorem tailTrace_1285223 : CollatzResearch.WordTrace tailWord_1285223 prefixEnd_1285223 219979049071176764267291 := by
  unfold tailWord_1285223
  simp only [CollatzResearch.WordTrace]
  refine ⟨46875933822864044458332323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31250622548576029638888215 46875933822864044458332323)
  ·
    refine ⟨70313900734296066687498485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46875933822864044458332323 70313900734296066687498485)
    ·
      refine ⟨6591928193840256251952983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 70313900734296066687498485 6591928193840256251952983)
      ·
        refine ⟨9887892290760384377929475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6591928193840256251952983 9887892290760384377929475)
        ·
          refine ⟨14831838436140576566894213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9887892290760384377929475 14831838436140576566894213)
          ·
            refine ⟨2780969706776358106292665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14831838436140576566894213 2780969706776358106292665)
            ·
              refine ⟨2085727280082268579719499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2780969706776358106292665 2085727280082268579719499)
              ·
                refine ⟨3128590920123402869579249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2085727280082268579719499 3128590920123402869579249)
                ·
                  refine ⟨2346443190092552152184437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3128590920123402869579249 2346443190092552152184437)
                  ·
                    refine ⟨219979049071176764267291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2346443190092552152184437 219979049071176764267291)
                    ·
                      rfl

theorem cell23_1285223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 2, 1, 2, 5].length) (baseStart_1285223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1285223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1285223 prefixEnd_1285223 := by exact prefixLift 1285223
  have htrace : WordTrace (prefixWord ++ tailWord_1285223) baseStart_1285223 baseEnd_1285223 := by
    simpa [prefixWord, tailWord_1285223, baseEnd_1285223] using wordTrace_append hprefix tailTrace_1285223
  have hstable : (prefixWord ++ tailWord_1285223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1285223).length < 2 ^ (prefixWord ++ tailWord_1285223).sum := by decide
  have hdescent : baseEnd_1285223 < baseStart_1285223 := by decide
  rcases family_descends (prefixWord ++ tailWord_1285223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1285287 : List Nat := [1, 1, 6, 2, 1, 1, 1, 5, 1, 4]
def baseStart_1285287 : Nat := 118140960795 + 1285287 * 2 ^ 59
def prefixEnd_1285287 : Nat := 4983230072969 + 3 ^ 40 * 1285287 * 2
def baseEnd_1285287 : Nat := 219990003325139347467193

theorem tailTrace_1285287 : CollatzResearch.WordTrace tailWord_1285287 prefixEnd_1285287 219990003325139347467193 := by
  unfold tailWord_1285287
  simp only [CollatzResearch.WordTrace]
  refine ⟨46878268094632183388662115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31252178729754788925774743 46878268094632183388662115)
  ·
    refine ⟨70317402141948275082993173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46878268094632183388662115 70317402141948275082993173)
    ·
      refine ⟨3296128225403825394515305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 70317402141948275082993173 3296128225403825394515305)
      ·
        refine ⟨2472096169052869045886479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3296128225403825394515305 2472096169052869045886479)
        ·
          refine ⟨3708144253579303568829719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2472096169052869045886479 3708144253579303568829719)
          ·
            refine ⟨5562216380368955353244579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3708144253579303568829719 5562216380368955353244579)
            ·
              refine ⟨8343324570553433029866869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5562216380368955353244579 8343324570553433029866869)
              ·
                refine ⟨782186678489384346550019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8343324570553433029866869 782186678489384346550019)
                ·
                  refine ⟨1173280017734076519825029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 782186678489384346550019 1173280017734076519825029)
                  ·
                    refine ⟨219990003325139347467193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1173280017734076519825029 219990003325139347467193)
                    ·
                      rfl

theorem cell23_1285287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 1, 5, 1, 4].length) (baseStart_1285287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1285287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1285287 prefixEnd_1285287 := by exact prefixLift 1285287
  have htrace : WordTrace (prefixWord ++ tailWord_1285287) baseStart_1285287 baseEnd_1285287 := by
    simpa [prefixWord, tailWord_1285287, baseEnd_1285287] using wordTrace_append hprefix tailTrace_1285287
  have hstable : (prefixWord ++ tailWord_1285287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1285287).length < 2 ^ (prefixWord ++ tailWord_1285287).sum := by decide
  have hdescent : baseEnd_1285287 < baseStart_1285287 := by decide
  rcases family_descends (prefixWord ++ tailWord_1285287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1285330 : List Nat := [3, 2, 2, 2, 1, 1, 4, 2, 1, 5]
def baseStart_1285330 : Nat := 118140960795 + 1285330 * 2 ^ 59
def prefixEnd_1285330 : Nat := 4983230072969 + 3 ^ 40 * 1285330 * 2
def baseEnd_1285330 : Nat := 219997363214520458054627

theorem tailTrace_1285330 : CollatzResearch.WordTrace tailWord_1285330 prefixEnd_1285330 219997363214520458054627 := by
  unfold tailWord_1285330
  simp only [CollatzResearch.WordTrace]
  refine ⟨11719959108369100433119361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31253224288984267821651629 11719959108369100433119361)
  ·
    refine ⟨8789969331276825324839521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11719959108369100433119361 8789969331276825324839521)
    ·
      refine ⟨6592476998457618993629641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8789969331276825324839521 6592476998457618993629641)
      ·
        refine ⟨4944357748843214245222231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6592476998457618993629641 4944357748843214245222231)
        ·
          refine ⟨7416536623264821367833347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4944357748843214245222231 7416536623264821367833347)
          ·
            refine ⟨11124804934897232051750021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7416536623264821367833347 11124804934897232051750021)
            ·
              refine ⟨2085900925293231009703129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11124804934897232051750021 2085900925293231009703129)
              ·
                refine ⟨1564425693969923257277347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2085900925293231009703129 1564425693969923257277347)
                ·
                  refine ⟨2346638540954884885916021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1564425693969923257277347 2346638540954884885916021)
                  ·
                    refine ⟨219997363214520458054627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2346638540954884885916021 219997363214520458054627)
                    ·
                      rfl

theorem cell23_1285330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 4, 2, 1, 5].length) (baseStart_1285330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1285330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1285330 prefixEnd_1285330 := by exact prefixLift 1285330
  have htrace : WordTrace (prefixWord ++ tailWord_1285330) baseStart_1285330 baseEnd_1285330 := by
    simpa [prefixWord, tailWord_1285330, baseEnd_1285330] using wordTrace_append hprefix tailTrace_1285330
  have hstable : (prefixWord ++ tailWord_1285330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1285330).length < 2 ^ (prefixWord ++ tailWord_1285330).sum := by decide
  have hdescent : baseEnd_1285330 < baseStart_1285330 := by decide
  rcases family_descends (prefixWord ++ tailWord_1285330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1285343 : List Nat := [1, 1, 2, 3, 2, 1, 3, 2, 4, 4]
def baseStart_1285343 : Nat := 118140960795 + 1285343 * 2 ^ 59
def prefixEnd_1285343 : Nat := 4983230072969 + 3 ^ 40 * 1285343 * 2
def baseEnd_1285343 : Nat := 219999588297356607767107

theorem tailTrace_1285343 : CollatzResearch.WordTrace tailWord_1285343 prefixEnd_1285343 219999588297356607767107 := by
  unfold tailWord_1285343
  simp only [CollatzResearch.WordTrace]
  refine ⟨46880310582429304952700683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31253540388286203301800455 46880310582429304952700683)
  ·
    refine ⟨70320465873643957429051025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46880310582429304952700683 70320465873643957429051025)
    ·
      refine ⟨52740349405232968071788269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70320465873643957429051025 52740349405232968071788269)
      ·
        refine ⟨19777631026962363026920601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52740349405232968071788269 19777631026962363026920601)
        ·
          refine ⟨14833223270221772270190451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19777631026962363026920601 14833223270221772270190451)
          ·
            refine ⟨22249834905332658405285677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14833223270221772270190451 22249834905332658405285677)
            ·
              refine ⟨8343688089499746901982129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22249834905332658405285677 8343688089499746901982129)
              ·
                refine ⟨6257766067124810176486597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8343688089499746901982129 6257766067124810176486597)
                ·
                  refine ⟨1173331137585901908091237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6257766067124810176486597 1173331137585901908091237)
                  ·
                    refine ⟨219999588297356607767107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1173331137585901908091237 219999588297356607767107)
                    ·
                      rfl

theorem cell23_1285343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 3, 2, 4, 4].length) (baseStart_1285343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1285343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1285343 prefixEnd_1285343 := by exact prefixLift 1285343
  have htrace : WordTrace (prefixWord ++ tailWord_1285343) baseStart_1285343 baseEnd_1285343 := by
    simpa [prefixWord, tailWord_1285343, baseEnd_1285343] using wordTrace_append hprefix tailTrace_1285343
  have hstable : (prefixWord ++ tailWord_1285343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1285343).length < 2 ^ (prefixWord ++ tailWord_1285343).sum := by decide
  have hdescent : baseEnd_1285343 < baseStart_1285343 := by decide
  rcases family_descends (prefixWord ++ tailWord_1285343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1285344 : List Nat := [2, 1, 1, 3, 1, 6, 1, 3, 1, 1, 3]
def baseStart_1285344 : Nat := 118140960795 + 1285344 * 2 ^ 59
def prefixEnd_1285344 : Nat := 4983230072969 + 3 ^ 40 * 1285344 * 2
def baseEnd_1285344 : Nat := 659999278372724319388817

theorem tailTrace_1285344 : CollatzResearch.WordTrace tailWord_1285344 prefixEnd_1285344 659999278372724319388817 := by
  unfold tailWord_1285344
  simp only [CollatzResearch.WordTrace]
  refine ⟨23440173527712841061743543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31253564703617121415658057 23440173527712841061743543)
  ·
    refine ⟨35160260291569261592615315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23440173527712841061743543 35160260291569261592615315)
    ·
      refine ⟨52740390437353892388922973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35160260291569261592615315 52740390437353892388922973)
      ·
        refine ⟨19777646414007709645846115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52740390437353892388922973 19777646414007709645846115)
        ·
          refine ⟨29666469621011564468769173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19777646414007709645846115 29666469621011564468769173)
          ·
            refine ⟨1390615763484917084473555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 29666469621011564468769173 1390615763484917084473555)
            ·
              refine ⟨2085923645227375626710333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1390615763484917084473555 2085923645227375626710333)
              ·
                refine ⟨782221366960265860016375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2085923645227375626710333 782221366960265860016375)
                ·
                  refine ⟨1173332050440398790024563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 782221366960265860016375 1173332050440398790024563)
                  ·
                    refine ⟨1759998075660598185036845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1173332050440398790024563 1759998075660598185036845)
                    ·
                      refine ⟨659999278372724319388817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1759998075660598185036845 659999278372724319388817)
                      ·
                        rfl

theorem cell23_1285344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 6, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 6, 1, 3, 1, 1, 3].length) (baseStart_1285344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1285344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1285344 prefixEnd_1285344 := by exact prefixLift 1285344
  have htrace : WordTrace (prefixWord ++ tailWord_1285344) baseStart_1285344 baseEnd_1285344 := by
    simpa [prefixWord, tailWord_1285344, baseEnd_1285344] using wordTrace_append hprefix tailTrace_1285344
  have hstable : (prefixWord ++ tailWord_1285344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1285344).length < 2 ^ (prefixWord ++ tailWord_1285344).sum := by decide
  have hdescent : baseEnd_1285344 < baseStart_1285344 := by decide
  rcases family_descends (prefixWord ++ tailWord_1285344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1285356 : List Nat := [2, 2, 1, 1, 2, 4, 11]
def baseStart_1285356 : Nat := 118140960795 + 1285356 * 2 ^ 59
def prefixEnd_1285356 : Nat := 4983230072969 + 3 ^ 40 * 1285356 * 2
def baseEnd_1285356 : Nat := 8148215310377509536281

theorem tailTrace_1285356 : CollatzResearch.WordTrace tailWord_1285356 prefixEnd_1285356 8148215310377509536281 := by
  unfold tailWord_1285356
  simp only [CollatzResearch.WordTrace]
  refine ⟨23440392365691104086461961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31253856487588138781949281 23440392365691104086461961)
  ·
    refine ⟨17580294274268328064846471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23440392365691104086461961 17580294274268328064846471)
    ·
      refine ⟨26370441411402492097269707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17580294274268328064846471 26370441411402492097269707)
      ·
        refine ⟨39555662117103738145904561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26370441411402492097269707 39555662117103738145904561)
        ·
          refine ⟨29666746587827803609428421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39555662117103738145904561 29666746587827803609428421)
          ·
            refine ⟨5562514985217713176767829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 29666746587827803609428421 5562514985217713176767829)
            ·
              refine ⟨8148215310377509536281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 5562514985217713176767829 8148215310377509536281)
              ·
                rfl

theorem cell23_1285356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 11].length) (baseStart_1285356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1285356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1285356 prefixEnd_1285356 := by exact prefixLift 1285356
  have htrace : WordTrace (prefixWord ++ tailWord_1285356) baseStart_1285356 baseEnd_1285356 := by
    simpa [prefixWord, tailWord_1285356, baseEnd_1285356] using wordTrace_append hprefix tailTrace_1285356
  have hstable : (prefixWord ++ tailWord_1285356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1285356).length < 2 ^ (prefixWord ++ tailWord_1285356).sum := by decide
  have hdescent : baseEnd_1285356 < baseStart_1285356 := by decide
  rcases family_descends (prefixWord ++ tailWord_1285356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1285376 : List Nat := [2, 1, 1, 2, 1, 1, 3, 1, 1, 4, 6]
def baseStart_1285376 : Nat := 118140960795 + 1285376 * 2 ^ 59
def prefixEnd_1285376 : Nat := 4983230072969 + 3 ^ 40 * 1285376 * 2
def baseEnd_1285376 : Nat := 660015709753668194188669

theorem tailTrace_1285376 : CollatzResearch.WordTrace tailWord_1285376 prefixEnd_1285376 660015709753668194188669 := by
  unfold tailWord_1285376
  simp only [CollatzResearch.WordTrace]
  refine ⟨23440757095654875794325991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31254342794206501059101321 23440757095654875794325991)
  ·
    refine ⟨35161135643482313691488987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23440757095654875794325991 35161135643482313691488987)
    ·
      refine ⟨52741703465223470537233481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35161135643482313691488987 52741703465223470537233481)
      ·
        refine ⟨39556277598917602902925111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52741703465223470537233481 39556277598917602902925111)
        ·
          refine ⟨59334416398376404354387667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39556277598917602902925111 59334416398376404354387667)
          ·
            refine ⟨89001624597564606531581501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59334416398376404354387667 89001624597564606531581501)
            ·
              refine ⟨33375609224086727449343063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 89001624597564606531581501 33375609224086727449343063)
              ·
                refine ⟨50063413836130091174014595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33375609224086727449343063 50063413836130091174014595)
                ·
                  refine ⟨75095120754195136761021893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 50063413836130091174014595 75095120754195136761021893)
                  ·
                    refine ⟨14080335141411588142691605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 75095120754195136761021893 14080335141411588142691605)
                    ·
                      refine ⟨660015709753668194188669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 14080335141411588142691605 660015709753668194188669)
                      ·
                        rfl

theorem cell23_1285376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 1, 1, 4, 6].length) (baseStart_1285376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1285376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1285376 prefixEnd_1285376 := by exact prefixLift 1285376
  have htrace : WordTrace (prefixWord ++ tailWord_1285376) baseStart_1285376 baseEnd_1285376 := by
    simpa [prefixWord, tailWord_1285376, baseEnd_1285376] using wordTrace_append hprefix tailTrace_1285376
  have hstable : (prefixWord ++ tailWord_1285376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1285376).length < 2 ^ (prefixWord ++ tailWord_1285376).sum := by decide
  have hdescent : baseEnd_1285376 < baseStart_1285376 := by decide
  rcases family_descends (prefixWord ++ tailWord_1285376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1285377 : List Nat := [1, 2, 4, 1, 1, 3, 4, 1, 2, 4]
def baseStart_1285377 : Nat := 118140960795 + 1285377 * 2 ^ 59
def prefixEnd_1285377 : Nat := 4983230072969 + 3 ^ 40 * 1285377 * 2
def baseEnd_1285377 : Nat := 220005407744774230092055

theorem tailTrace_1285377 : CollatzResearch.WordTrace tailWord_1285377 prefixEnd_1285377 220005407744774230092055 := by
  unfold tailWord_1285377
  simp only [CollatzResearch.WordTrace]
  refine ⟨46881550664306128759438385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31254367109537419172958923 46881550664306128759438385)
  ·
    refine ⟨35161162998229596569578789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46881550664306128759438385 35161162998229596569578789)
    ·
      refine ⟨6592718062168049356796023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 35161162998229596569578789 6592718062168049356796023)
      ·
        refine ⟨9889077093252074035194035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6592718062168049356796023 9889077093252074035194035)
        ·
          refine ⟨14833615639878111052791053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9889077093252074035194035 14833615639878111052791053)
          ·
            refine ⟨5562605864954291644796645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14833615639878111052791053 5562605864954291644796645)
            ·
              refine ⟨1042988599678929683399371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5562605864954291644796645 1042988599678929683399371)
              ·
                refine ⟨1564482899518394525099057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1042988599678929683399371 1564482899518394525099057)
                ·
                  refine ⟨1173362174638795893824293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1564482899518394525099057 1173362174638795893824293)
                  ·
                    refine ⟨220005407744774230092055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1173362174638795893824293 220005407744774230092055)
                    ·
                      rfl

theorem cell23_1285377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 4, 1, 2, 4].length) (baseStart_1285377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1285377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1285377 prefixEnd_1285377 := by exact prefixLift 1285377
  have htrace : WordTrace (prefixWord ++ tailWord_1285377) baseStart_1285377 baseEnd_1285377 := by
    simpa [prefixWord, tailWord_1285377, baseEnd_1285377] using wordTrace_append hprefix tailTrace_1285377
  have hstable : (prefixWord ++ tailWord_1285377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1285377).length < 2 ^ (prefixWord ++ tailWord_1285377).sum := by decide
  have hdescent : baseEnd_1285377 < baseStart_1285377 := by decide
  rcases family_descends (prefixWord ++ tailWord_1285377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1285384 : List Nat := [2, 1, 3, 2, 5, 1, 1, 2, 1, 1, 4]
def baseStart_1285384 : Nat := 118140960795 + 1285384 * 2 ^ 59
def prefixEnd_1285384 : Nat := 4983230072969 + 3 ^ 40 * 1285384 * 2
def baseEnd_1285384 : Nat := 660019817598904162888633

theorem tailTrace_1285384 : CollatzResearch.WordTrace tailWord_1285384 prefixEnd_1285384 660019817598904162888633 := by
  unfold tailWord_1285384
  simp only [CollatzResearch.WordTrace]
  refine ⟨23440902987640384477471603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31254537316853845969962137 23440902987640384477471603)
  ·
    refine ⟨35161354481460576716207405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23440902987640384477471603 35161354481460576716207405)
    ·
      refine ⟨13185507930547716268577777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35161354481460576716207405 13185507930547716268577777)
      ·
        refine ⟨9889130947910787201433333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13185507930547716268577777 9889130947910787201433333)
        ·
          refine ⟨927106026366636300134375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 9889130947910787201433333 927106026366636300134375)
          ·
            refine ⟨1390659039549954450201563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 927106026366636300134375 1390659039549954450201563)
            ·
              refine ⟨2085988559324931675302345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1390659039549954450201563 2085988559324931675302345)
              ·
                refine ⟨1564491419493698756476759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2085988559324931675302345 1564491419493698756476759)
                ·
                  refine ⟨2346737129240548134715139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1564491419493698756476759 2346737129240548134715139)
                  ·
                    refine ⟨3520105693860822202072709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2346737129240548134715139 3520105693860822202072709)
                    ·
                      refine ⟨660019817598904162888633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3520105693860822202072709 660019817598904162888633)
                      ·
                        rfl

theorem cell23_1285384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 5, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 5, 1, 1, 2, 1, 1, 4].length) (baseStart_1285384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1285384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1285384 prefixEnd_1285384 := by exact prefixLift 1285384
  have htrace : WordTrace (prefixWord ++ tailWord_1285384) baseStart_1285384 baseEnd_1285384 := by
    simpa [prefixWord, tailWord_1285384, baseEnd_1285384] using wordTrace_append hprefix tailTrace_1285384
  have hstable : (prefixWord ++ tailWord_1285384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1285384).length < 2 ^ (prefixWord ++ tailWord_1285384).sum := by decide
  have hdescent : baseEnd_1285384 < baseStart_1285384 := by decide
  rcases family_descends (prefixWord ++ tailWord_1285384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1285387 : List Nat := [1, 1, 1, 1, 5, 5, 1, 2, 1, 2, 3]
def baseStart_1285387 : Nat := 118140960795 + 1285387 * 2 ^ 59
def prefixEnd_1285387 : Nat := 4983230072969 + 3 ^ 40 * 1285387 * 2
def baseEnd_1285387 : Nat := 660021358040867651151119

theorem tailTrace_1285387 : CollatzResearch.WordTrace tailWord_1285387 prefixEnd_1285387 660021358040867651151119 := by
  unfold tailWord_1285387
  simp only [CollatzResearch.WordTrace]
  refine ⟨46881915394269900467302415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31254610262846600311534943 46881915394269900467302415)
  ·
    refine ⟨70322873091404850700953623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46881915394269900467302415 70322873091404850700953623)
    ·
      refine ⟨105484309637107276051430435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70322873091404850700953623 105484309637107276051430435)
      ·
        refine ⟨158226464455660914077145653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105484309637107276051430435 158226464455660914077145653)
        ·
          refine ⟨14833731042718210694732405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 158226464455660914077145653 14833731042718210694732405)
          ·
            refine ⟨1390662285254832252631163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 14833731042718210694732405 1390662285254832252631163)
            ·
              refine ⟨2085993427882248378946745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1390662285254832252631163 2085993427882248378946745)
              ·
                refine ⟨1564495070911686284210059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2085993427882248378946745 1564495070911686284210059)
                ·
                  refine ⟨2346742606367529426315089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1564495070911686284210059 2346742606367529426315089)
                  ·
                    refine ⟨1760056954775647069736317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2346742606367529426315089 1760056954775647069736317)
                    ·
                      refine ⟨660021358040867651151119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1760056954775647069736317 660021358040867651151119)
                      ·
                        rfl

theorem cell23_1285387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 5, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 5, 1, 2, 1, 2, 3].length) (baseStart_1285387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1285387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1285387 prefixEnd_1285387 := by exact prefixLift 1285387
  have htrace : WordTrace (prefixWord ++ tailWord_1285387) baseStart_1285387 baseEnd_1285387 := by
    simpa [prefixWord, tailWord_1285387, baseEnd_1285387] using wordTrace_append hprefix tailTrace_1285387
  have hstable : (prefixWord ++ tailWord_1285387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1285387).length < 2 ^ (prefixWord ++ tailWord_1285387).sum := by decide
  have hdescent : baseEnd_1285387 < baseStart_1285387 := by decide
  rcases family_descends (prefixWord ++ tailWord_1285387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1285400 : List Nat := [2, 1, 2, 3, 1, 4, 1, 2, 1, 3, 3]
def baseStart_1285400 : Nat := 118140960795 + 1285400 * 2 ^ 59
def prefixEnd_1285400 : Nat := 4983230072969 + 3 ^ 40 * 1285400 * 2
def baseEnd_1285400 : Nat := 660028033289376100288559

theorem tailTrace_1285400 : CollatzResearch.WordTrace tailWord_1285400 prefixEnd_1285400 660028033289376100288559 := by
  unfold tailWord_1285400
  simp only [CollatzResearch.WordTrace]
  refine ⟨23441194771611401843762827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31254926362148535791683769 23441194771611401843762827)
  ·
    refine ⟨35161792157417102765644241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23441194771611401843762827 35161792157417102765644241)
    ·
      refine ⟨26371344118062827074233181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35161792157417102765644241 26371344118062827074233181)
      ·
        refine ⟨9889254044273560152837443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26371344118062827074233181 9889254044273560152837443)
        ·
          refine ⟨14833881066410340229256165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9889254044273560152837443 14833881066410340229256165)
          ·
            refine ⟨2781352699951938792985531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14833881066410340229256165 2781352699951938792985531)
            ·
              refine ⟨4172029049927908189478297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2781352699951938792985531 4172029049927908189478297)
              ·
                refine ⟨3129021787445931142108723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4172029049927908189478297 3129021787445931142108723)
                ·
                  refine ⟨4693532681168896713163085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3129021787445931142108723 4693532681168896713163085)
                  ·
                    refine ⟨1760074755438336267436157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4693532681168896713163085 1760074755438336267436157)
                    ·
                      refine ⟨660028033289376100288559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1760074755438336267436157 660028033289376100288559)
                      ·
                        rfl

theorem cell23_1285400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 1, 2, 1, 3, 3].length) (baseStart_1285400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1285400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1285400 prefixEnd_1285400 := by exact prefixLift 1285400
  have htrace : WordTrace (prefixWord ++ tailWord_1285400) baseStart_1285400 baseEnd_1285400 := by
    simpa [prefixWord, tailWord_1285400, baseEnd_1285400] using wordTrace_append hprefix tailTrace_1285400
  have hstable : (prefixWord ++ tailWord_1285400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1285400).length < 2 ^ (prefixWord ++ tailWord_1285400).sum := by decide
  have hdescent : baseEnd_1285400 < baseStart_1285400 := by decide
  rcases family_descends (prefixWord ++ tailWord_1285400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1285418 : List Nat := [3, 1, 4, 2, 1, 1, 4, 2, 1, 2, 2]
def baseStart_1285418 : Nat := 118140960795 + 1285418 * 2 ^ 59
def prefixEnd_1285418 : Nat := 4983230072969 + 3 ^ 40 * 1285418 * 2
def baseEnd_1285418 : Nat := 660037275941157029863477

theorem tailTrace_1285418 : CollatzResearch.WordTrace tailWord_1285418 prefixEnd_1285418 660037275941157029863477 := by
  unfold tailWord_1285418
  simp only [CollatzResearch.WordTrace]
  refine ⟨11720761514289398190420227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31255364038105061841120605 11720761514289398190420227)
  ·
    refine ⟨17581142271434097285630341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11720761514289398190420227 17581142271434097285630341)
    ·
      refine ⟨3296464175893893241055689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17581142271434097285630341 3296464175893893241055689)
      ·
        refine ⟨2472348131920419930791767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3296464175893893241055689 2472348131920419930791767)
        ·
          refine ⟨3708522197880629896187651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2472348131920419930791767 3708522197880629896187651)
          ·
            refine ⟨5562783296820944844281477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3708522197880629896187651 5562783296820944844281477)
            ·
              refine ⟨1043021868153927158302777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5562783296820944844281477 1043021868153927158302777)
              ·
                refine ⟨782266401115445368727083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1043021868153927158302777 782266401115445368727083)
                ·
                  refine ⟨1173399601673168053090625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 782266401115445368727083 1173399601673168053090625)
                  ·
                    refine ⟨880049701254876039817969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1173399601673168053090625 880049701254876039817969)
                    ·
                      refine ⟨660037275941157029863477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 880049701254876039817969 660037275941157029863477)
                      ·
                        rfl

theorem cell23_1285418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 4, 2, 1, 2, 2].length) (baseStart_1285418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1285418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1285418 prefixEnd_1285418 := by exact prefixLift 1285418
  have htrace : WordTrace (prefixWord ++ tailWord_1285418) baseStart_1285418 baseEnd_1285418 := by
    simpa [prefixWord, tailWord_1285418, baseEnd_1285418] using wordTrace_append hprefix tailTrace_1285418
  have hstable : (prefixWord ++ tailWord_1285418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1285418).length < 2 ^ (prefixWord ++ tailWord_1285418).sum := by decide
  have hdescent : baseEnd_1285418 < baseStart_1285418 := by decide
  rcases family_descends (prefixWord ++ tailWord_1285418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1285443 : List Nat := [1, 1, 1, 3, 1, 3, 1, 1, 4, 4, 3]
def baseStart_1285443 : Nat := 118140960795 + 1285443 * 2 ^ 59
def prefixEnd_1285443 : Nat := 4983230072969 + 3 ^ 40 * 1285443 * 2
def baseEnd_1285443 : Nat := 660050112957519432050861

theorem tailTrace_1285443 : CollatzResearch.WordTrace tailWord_1285443 prefixEnd_1285443 660050112957519432050861 := by
  unfold tailWord_1285443
  simp only [CollatzResearch.WordTrace]
  refine ⟨46883957882067022031340983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31255971921378014687560655 46883957882067022031340983)
  ·
    refine ⟨70325936823100533047011475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46883957882067022031340983 70325936823100533047011475)
    ·
      refine ⟨105488905234650799570517213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70325936823100533047011475 105488905234650799570517213)
      ·
        refine ⟨39558339462994049838943955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 105488905234650799570517213 39558339462994049838943955)
        ·
          refine ⟨59337509194491074758415933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39558339462994049838943955 59337509194491074758415933)
          ·
            refine ⟨22251565947934153034405975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 59337509194491074758415933 22251565947934153034405975)
            ·
              refine ⟨33377348921901229551608963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22251565947934153034405975 33377348921901229551608963)
              ·
                refine ⟨50066023382851844327413445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33377348921901229551608963 50066023382851844327413445)
                ·
                  refine ⟨9387379384284720811390021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 50066023382851844327413445 9387379384284720811390021)
                  ·
                    refine ⟨1760133634553385152135629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9387379384284720811390021 1760133634553385152135629)
                    ·
                      refine ⟨660050112957519432050861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1760133634553385152135629 660050112957519432050861)
                      ·
                        rfl

theorem cell23_1285443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 1, 4, 4, 3].length) (baseStart_1285443 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1285443 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1285443 prefixEnd_1285443 := by exact prefixLift 1285443
  have htrace : WordTrace (prefixWord ++ tailWord_1285443) baseStart_1285443 baseEnd_1285443 := by
    simpa [prefixWord, tailWord_1285443, baseEnd_1285443] using wordTrace_append hprefix tailTrace_1285443
  have hstable : (prefixWord ++ tailWord_1285443).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1285443).length < 2 ^ (prefixWord ++ tailWord_1285443).sum := by decide
  have hdescent : baseEnd_1285443 < baseStart_1285443 := by decide
  rcases family_descends (prefixWord ++ tailWord_1285443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1285444 : List Nat := [2, 3, 4, 1, 1, 1, 2, 1, 3, 3, 2]
def baseStart_1285444 : Nat := 118140960795 + 1285444 * 2 ^ 59
def prefixEnd_1285444 : Nat := 4983230072969 + 3 ^ 40 * 1285444 * 2
def baseEnd_1285444 : Nat := 660050626438173928138357

theorem tailTrace_1285444 : CollatzResearch.WordTrace tailWord_1285444 prefixEnd_1285444 660050626438173928138357 := by
  unfold tailWord_1285444
  simp only [CollatzResearch.WordTrace]
  refine ⟨23441997177531699601063693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31255996236708932801418257 23441997177531699601063693)
  ·
    refine ⟨8790748941574387350398885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23441997177531699601063693 8790748941574387350398885)
    ·
      refine ⟨1648265426545197628199791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8790748941574387350398885 1648265426545197628199791)
      ·
        refine ⟨2472398139817796442299687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1648265426545197628199791 2472398139817796442299687)
        ·
          refine ⟨3708597209726694663449531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2472398139817796442299687 3708597209726694663449531)
          ·
            refine ⟨5562895814590041995174297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3708597209726694663449531 5562895814590041995174297)
            ·
              refine ⟨4172171860942531496380723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5562895814590041995174297 4172171860942531496380723)
              ·
                refine ⟨6258257791413797244571085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4172171860942531496380723 6258257791413797244571085)
                ·
                  refine ⟨2346846671780173966714157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6258257791413797244571085 2346846671780173966714157)
                  ·
                    refine ⟨880067501917565237517809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2346846671780173966714157 880067501917565237517809)
                    ·
                      refine ⟨660050626438173928138357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 880067501917565237517809 660050626438173928138357)
                      ·
                        rfl

theorem cell23_1285444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 2, 1, 3, 3, 2].length) (baseStart_1285444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1285444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1285444 prefixEnd_1285444 := by exact prefixLift 1285444
  have htrace : WordTrace (prefixWord ++ tailWord_1285444) baseStart_1285444 baseEnd_1285444 := by
    simpa [prefixWord, tailWord_1285444, baseEnd_1285444] using wordTrace_append hprefix tailTrace_1285444
  have hstable : (prefixWord ++ tailWord_1285444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1285444).length < 2 ^ (prefixWord ++ tailWord_1285444).sum := by decide
  have hdescent : baseEnd_1285444 < baseStart_1285444 := by decide
  rcases family_descends (prefixWord ++ tailWord_1285444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1285457 : List Nat := [1, 2, 2, 1, 4, 1, 2, 2, 4, 2, 2]
def baseStart_1285457 : Nat := 118140960795 + 1285457 * 2 ^ 59
def prefixEnd_1285457 : Nat := 4983230072969 + 3 ^ 40 * 1285457 * 2
def baseEnd_1285457 : Nat := 660057301686682377275797

theorem tailTrace_1285457 : CollatzResearch.WordTrace tailWord_1285457 prefixEnd_1285457 660057301686682377275797 := by
  unfold tailWord_1285457
  simp only [CollatzResearch.WordTrace]
  refine ⟨46884468504016302422350625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31256312336010868281567083 46884468504016302422350625)
  ·
    refine ⟨35163351378012226816762969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46884468504016302422350625 35163351378012226816762969)
    ·
      refine ⟨26372513533509170112572227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35163351378012226816762969 26372513533509170112572227)
      ·
        refine ⟨39558770300263755168858341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26372513533509170112572227 39558770300263755168858341)
        ·
          refine ⟨7417269431299454094160939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 39558770300263755168858341 7417269431299454094160939)
          ·
            refine ⟨11125904146949181141241409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7417269431299454094160939 11125904146949181141241409)
            ·
              refine ⟨8344428110211885855931057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11125904146949181141241409 8344428110211885855931057)
              ·
                refine ⟨6258321082658914391948293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8344428110211885855931057 6258321082658914391948293)
                ·
                  refine ⟨1173435202998546448490305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6258321082658914391948293 1173435202998546448490305)
                  ·
                    refine ⟨880076402248909836367729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1173435202998546448490305 880076402248909836367729)
                    ·
                      refine ⟨660057301686682377275797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 880076402248909836367729 660057301686682377275797)
                      ·
                        rfl

theorem cell23_1285457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 2, 2, 4, 2, 2].length) (baseStart_1285457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1285457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1285457 prefixEnd_1285457 := by exact prefixLift 1285457
  have htrace : WordTrace (prefixWord ++ tailWord_1285457) baseStart_1285457 baseEnd_1285457 := by
    simpa [prefixWord, tailWord_1285457, baseEnd_1285457] using wordTrace_append hprefix tailTrace_1285457
  have hstable : (prefixWord ++ tailWord_1285457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1285457).length < 2 ^ (prefixWord ++ tailWord_1285457).sum := by decide
  have hdescent : baseEnd_1285457 < baseStart_1285457 := by decide
  rcases family_descends (prefixWord ++ tailWord_1285457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1285461 : List Nat := [1, 3, 2, 2, 3, 3, 2, 1, 1, 3, 2]
def baseStart_1285461 : Nat := 118140960795 + 1285461 * 2 ^ 59
def prefixEnd_1285461 : Nat := 4983230072969 + 3 ^ 40 * 1285461 * 2
def baseEnd_1285461 : Nat := 660059355609300361625779

theorem tailTrace_1285461 : CollatzResearch.WordTrace tailWord_1285461 prefixEnd_1285461 660059355609300361625779 := by
  unfold tailWord_1285461
  simp only [CollatzResearch.WordTrace]
  refine ⟨46884614396001811105496237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31256409597334540736997491 46884614396001811105496237)
  ·
    refine ⟨17581730398500679164561089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46884614396001811105496237 17581730398500679164561089)
    ·
      refine ⟨13186297798875509373420817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17581730398500679164561089 13186297798875509373420817)
      ·
        refine ⟨9889723349156632030065613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13186297798875509373420817 9889723349156632030065613)
        ·
          refine ⟨3708646255933737011274605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9889723349156632030065613 3708646255933737011274605)
          ·
            refine ⟨1390742345975151379227977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3708646255933737011274605 1390742345975151379227977)
            ·
              refine ⟨1043056759481363534420983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1390742345975151379227977 1043056759481363534420983)
              ·
                refine ⟨1564585139222045301631475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1043056759481363534420983 1564585139222045301631475)
                ·
                  refine ⟨2346877708833067952447213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1564585139222045301631475 2346877708833067952447213)
                  ·
                    refine ⟨880079140812400482167705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2346877708833067952447213 880079140812400482167705)
                    ·
                      refine ⟨660059355609300361625779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 880079140812400482167705 660059355609300361625779)
                      ·
                        rfl

theorem cell23_1285461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 3, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 3, 2, 1, 1, 3, 2].length) (baseStart_1285461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1285461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1285461 prefixEnd_1285461 := by exact prefixLift 1285461
  have htrace : WordTrace (prefixWord ++ tailWord_1285461) baseStart_1285461 baseEnd_1285461 := by
    simpa [prefixWord, tailWord_1285461, baseEnd_1285461] using wordTrace_append hprefix tailTrace_1285461
  have hstable : (prefixWord ++ tailWord_1285461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1285461).length < 2 ^ (prefixWord ++ tailWord_1285461).sum := by decide
  have hdescent : baseEnd_1285461 < baseStart_1285461 := by decide
  rcases family_descends (prefixWord ++ tailWord_1285461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1285474 : List Nat := [3, 3, 2, 1, 1, 1, 3, 1, 4, 2, 2]
def baseStart_1285474 : Nat := 118140960795 + 1285474 * 2 ^ 59
def prefixEnd_1285474 : Nat := 4983230072969 + 3 ^ 40 * 1285474 * 2
def baseEnd_1285474 : Nat := 660066030857808810763219

theorem tailTrace_1285474 : CollatzResearch.WordTrace tailWord_1285474 prefixEnd_1285474 660066030857808810763219 := by
  unfold tailWord_1285474
  simp only [CollatzResearch.WordTrace]
  refine ⟨11721272136238678581429869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31256725696636476217146317 11721272136238678581429869)
  ·
    refine ⟨4395477051089504468036201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11721272136238678581429869 4395477051089504468036201)
    ·
      refine ⟨3296607788317128351027151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4395477051089504468036201 3296607788317128351027151)
      ·
        refine ⟨4944911682475692526540727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3296607788317128351027151 4944911682475692526540727)
        ·
          refine ⟨7417367523713538789811091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4944911682475692526540727 7417367523713538789811091)
          ·
            refine ⟨11126051285570308184716637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7417367523713538789811091 11126051285570308184716637)
            ·
              refine ⟨4172269232088865569268739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11126051285570308184716637 4172269232088865569268739)
              ·
                refine ⟨6258403848133298353903109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4172269232088865569268739 6258403848133298353903109)
                ·
                  refine ⟨1173450721524993441356833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6258403848133298353903109 1173450721524993441356833)
                  ·
                    refine ⟨880088041143745081017625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1173450721524993441356833 880088041143745081017625)
                    ·
                      refine ⟨660066030857808810763219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 880088041143745081017625 660066030857808810763219)
                      ·
                        rfl

theorem cell23_1285474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 3, 1, 4, 2, 2].length) (baseStart_1285474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1285474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1285474 prefixEnd_1285474 := by exact prefixLift 1285474
  have htrace : WordTrace (prefixWord ++ tailWord_1285474) baseStart_1285474 baseEnd_1285474 := by
    simpa [prefixWord, tailWord_1285474, baseEnd_1285474] using wordTrace_append hprefix tailTrace_1285474
  have hstable : (prefixWord ++ tailWord_1285474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1285474).length < 2 ^ (prefixWord ++ tailWord_1285474).sum := by decide
  have hdescent : baseEnd_1285474 < baseStart_1285474 := by decide
  rcases family_descends (prefixWord ++ tailWord_1285474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1285490 : List Nat := [3, 2, 1, 2, 1, 2, 1, 3, 2, 3, 3]
def baseStart_1285490 : Nat := 118140960795 + 1285490 * 2 ^ 59
def prefixEnd_1285490 : Nat := 4983230072969 + 3 ^ 40 * 1285490 * 2
def baseEnd_1285490 : Nat := 660074246548280748163145

theorem tailTrace_1285490 : CollatzResearch.WordTrace tailWord_1285490 prefixEnd_1285490 660074246548280748163145 := by
  unfold tailWord_1285490
  simp only [CollatzResearch.WordTrace]
  refine ⟨11721418028224187264575481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31257114741931166038867949 11721418028224187264575481)
  ·
    refine ⟨8791063521168140448431611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11721418028224187264575481 8791063521168140448431611)
    ·
      refine ⟨13186595281752210672647417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8791063521168140448431611 13186595281752210672647417)
      ·
        refine ⟨9889946461314158004485563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13186595281752210672647417 9889946461314158004485563)
        ·
          refine ⟨14834919691971237006728345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9889946461314158004485563 14834919691971237006728345)
          ·
            refine ⟨11126189768978427755046259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14834919691971237006728345 11126189768978427755046259)
            ·
              refine ⟨16689284653467641632569389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11126189768978427755046259 16689284653467641632569389)
              ·
                refine ⟨6258481745050365612213521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16689284653467641632569389 6258481745050365612213521)
                ·
                  refine ⟨4693861308787774209160141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6258481745050365612213521 4693861308787774209160141)
                  ·
                    refine ⟨1760197990795415328435053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4693861308787774209160141 1760197990795415328435053)
                    ·
                      refine ⟨660074246548280748163145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1760197990795415328435053 660074246548280748163145)
                      ·
                        rfl

theorem cell23_1285490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 3, 2, 3, 3].length) (baseStart_1285490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1285490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1285490 prefixEnd_1285490 := by exact prefixLift 1285490
  have htrace : WordTrace (prefixWord ++ tailWord_1285490) baseStart_1285490 baseEnd_1285490 := by
    simpa [prefixWord, tailWord_1285490, baseEnd_1285490] using wordTrace_append hprefix tailTrace_1285490
  have hstable : (prefixWord ++ tailWord_1285490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1285490).length < 2 ^ (prefixWord ++ tailWord_1285490).sum := by decide
  have hdescent : baseEnd_1285490 < baseStart_1285490 := by decide
  rcases family_descends (prefixWord ++ tailWord_1285490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1285564 : List Nat := [2, 2, 2, 4, 2, 1, 2, 1, 2, 1, 4]
def baseStart_1285564 : Nat := 118140960795 + 1285564 * 2 ^ 59
def prefixEnd_1285564 : Nat := 4983230072969 + 3 ^ 40 * 1285564 * 2
def baseEnd_1285564 : Nat := 660112244116713458637805

theorem tailTrace_1285564 : CollatzResearch.WordTrace tailWord_1285564 prefixEnd_1285564 660112244116713458637805 := by
  unfold tailWord_1285564
  simp only [CollatzResearch.WordTrace]
  refine ⟨23444185557314329848247873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31258914076419106464330497 23444185557314329848247873)
  ·
    refine ⟨17583139167985747386185905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23444185557314329848247873 17583139167985747386185905)
    ·
      refine ⟨13187354375989310539639429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17583139167985747386185905 13187354375989310539639429)
      ·
        refine ⟨2472628945497995726182393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13187354375989310539639429 2472628945497995726182393)
        ·
          refine ⟨1854471709123496794636795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2472628945497995726182393 1854471709123496794636795)
          ·
            refine ⟨2781707563685245191955193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1854471709123496794636795 2781707563685245191955193)
            ·
              refine ⟨2086280672763933893966395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2781707563685245191955193 2086280672763933893966395)
              ·
                refine ⟨3129421009145900840949593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2086280672763933893966395 3129421009145900840949593)
                ·
                  refine ⟨2347065756859425630712195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3129421009145900840949593 2347065756859425630712195)
                  ·
                    refine ⟨3520598635289138446068293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2347065756859425630712195 3520598635289138446068293)
                    ·
                      refine ⟨660112244116713458637805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3520598635289138446068293 660112244116713458637805)
                      ·
                        rfl

theorem cell23_1285564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 2, 1, 2, 1, 4].length) (baseStart_1285564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1285564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1285564 prefixEnd_1285564 := by exact prefixLift 1285564
  have htrace : WordTrace (prefixWord ++ tailWord_1285564) baseStart_1285564 baseEnd_1285564 := by
    simpa [prefixWord, tailWord_1285564, baseEnd_1285564] using wordTrace_append hprefix tailTrace_1285564
  have hstable : (prefixWord ++ tailWord_1285564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1285564).length < 2 ^ (prefixWord ++ tailWord_1285564).sum := by decide
  have hdescent : baseEnd_1285564 < baseStart_1285564 := by decide
  rcases family_descends (prefixWord ++ tailWord_1285564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1285614 : List Nat := [4, 1, 2, 1, 2, 1, 3, 2, 3, 1, 3]
def baseStart_1285614 : Nat := 118140960795 + 1285614 * 2 ^ 59
def prefixEnd_1285614 : Nat := 4983230072969 + 3 ^ 40 * 1285614 * 2
def baseEnd_1285614 : Nat := 660137918149438263012575

theorem tailTrace_1285614 : CollatzResearch.WordTrace tailWord_1285614 prefixEnd_1285614 660137918149438263012575 := by
  unfold tailWord_1285614
  simp only [CollatzResearch.WordTrace]
  refine ⟨5861274345555939779476987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 31260129842965012157210597 5861274345555939779476987)
  ·
    refine ⟨8791911518333909669215481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5861274345555939779476987 8791911518333909669215481)
    ·
      refine ⟨6593933638750432251911611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8791911518333909669215481 6593933638750432251911611)
      ·
        refine ⟨9890900458125648377867417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6593933638750432251911611 9890900458125648377867417)
        ·
          refine ⟨7418175343594236283400563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9890900458125648377867417 7418175343594236283400563)
          ·
            refine ⟨11127263015391354425100845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7418175343594236283400563 11127263015391354425100845)
            ·
              refine ⟨4172723630771757909412817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11127263015391354425100845 4172723630771757909412817)
              ·
                refine ⟨3129542723078818432059613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4172723630771757909412817 3129542723078818432059613)
                ·
                  refine ⟨1173578521154556912022355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3129542723078818432059613 1173578521154556912022355)
                  ·
                    refine ⟨1760367781731835368033533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1173578521154556912022355 1760367781731835368033533)
                    ·
                      refine ⟨660137918149438263012575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1760367781731835368033533 660137918149438263012575)
                      ·
                        rfl

theorem cell23_1285614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 3, 2, 3, 1, 3].length) (baseStart_1285614 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1285614 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1285614 prefixEnd_1285614 := by exact prefixLift 1285614
  have htrace : WordTrace (prefixWord ++ tailWord_1285614) baseStart_1285614 baseEnd_1285614 := by
    simpa [prefixWord, tailWord_1285614, baseEnd_1285614] using wordTrace_append hprefix tailTrace_1285614
  have hstable : (prefixWord ++ tailWord_1285614).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1285614).length < 2 ^ (prefixWord ++ tailWord_1285614).sum := by decide
  have hdescent : baseEnd_1285614 < baseStart_1285614 := by decide
  rcases family_descends (prefixWord ++ tailWord_1285614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1285624 : List Nat := [2, 1, 2, 1, 1, 5, 3, 1, 2, 3, 2]
def baseStart_1285624 : Nat := 118140960795 + 1285624 * 2 ^ 59
def prefixEnd_1285624 : Nat := 4983230072969 + 3 ^ 40 * 1285624 * 2
def baseEnd_1285624 : Nat := 660143052955983223887529

theorem tailTrace_1285624 : CollatzResearch.WordTrace tailWord_1285624 prefixEnd_1285624 660143052955983223887529 := by
  unfold tailWord_1285624
  simp only [CollatzResearch.WordTrace]
  refine ⟨23445279747205644971839963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31260372996274193295786617 23445279747205644971839963)
  ·
    refine ⟨35167919620808467457759945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23445279747205644971839963 35167919620808467457759945)
    ·
      refine ⟨26375939715606350593319959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35167919620808467457759945 26375939715606350593319959)
      ·
        refine ⟨39563909573409525889979939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26375939715606350593319959 39563909573409525889979939)
        ·
          refine ⟨59345864360114288834969909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39563909573409525889979939 59345864360114288834969909)
          ·
            refine ⟨5563674783760714578278429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 59345864360114288834969909 5563674783760714578278429)
            ·
              refine ⟨2086378043910267966854411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5563674783760714578278429 2086378043910267966854411)
              ·
                refine ⟨3129567065865401950281617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2086378043910267966854411 3129567065865401950281617)
                ·
                  refine ⟨2347175299399051462711213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3129567065865401950281617 2347175299399051462711213)
                  ·
                    refine ⟨880190737274644298516705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2347175299399051462711213 880190737274644298516705)
                    ·
                      refine ⟨660143052955983223887529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 880190737274644298516705 660143052955983223887529)
                      ·
                        rfl

theorem cell23_1285624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 3, 1, 2, 3, 2].length) (baseStart_1285624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1285624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1285624 prefixEnd_1285624 := by exact prefixLift 1285624
  have htrace : WordTrace (prefixWord ++ tailWord_1285624) baseStart_1285624 baseEnd_1285624 := by
    simpa [prefixWord, tailWord_1285624, baseEnd_1285624] using wordTrace_append hprefix tailTrace_1285624
  have hstable : (prefixWord ++ tailWord_1285624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1285624).length < 2 ^ (prefixWord ++ tailWord_1285624).sum := by decide
  have hdescent : baseEnd_1285624 < baseStart_1285624 := by decide
  rcases family_descends (prefixWord ++ tailWord_1285624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1285660 : List Nat := [2, 2, 3, 1, 2, 1, 2, 10]
def baseStart_1285660 : Nat := 118140960795 + 1285660 * 2 ^ 59
def prefixEnd_1285660 : Nat := 4983230072969 + 3 ^ 40 * 1285660 * 2
def baseEnd_1285660 : Nat := 24450427342946114186569

theorem tailTrace_1285660 : CollatzResearch.WordTrace tailWord_1285660 prefixEnd_1285660 24450427342946114186569 := by
  unfold tailWord_1285660
  simp only [CollatzResearch.WordTrace]
  refine ⟨23445936261140434045995217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31261248348187245394660289 23445936261140434045995217)
  ·
    refine ⟨17584452195855325534496413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23445936261140434045995217 17584452195855325534496413)
    ·
      refine ⟨6594169573445747075436155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17584452195855325534496413 6594169573445747075436155)
      ·
        refine ⟨9891254360168620613154233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6594169573445747075436155 9891254360168620613154233)
        ·
          refine ⟨7418440770126465459865675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9891254360168620613154233 7418440770126465459865675)
          ·
            refine ⟨11127661155189698189798513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7418440770126465459865675 11127661155189698189798513)
            ·
              refine ⟨8345745866392273642348885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11127661155189698189798513 8345745866392273642348885)
              ·
                refine ⟨24450427342946114186569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 8345745866392273642348885 24450427342946114186569)
                ·
                  rfl

theorem cell23_1285660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 2, 10].length) (baseStart_1285660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1285660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1285660 prefixEnd_1285660 := by exact prefixLift 1285660
  have htrace : WordTrace (prefixWord ++ tailWord_1285660) baseStart_1285660 baseEnd_1285660 := by
    simpa [prefixWord, tailWord_1285660, baseEnd_1285660] using wordTrace_append hprefix tailTrace_1285660
  have hstable : (prefixWord ++ tailWord_1285660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1285660).length < 2 ^ (prefixWord ++ tailWord_1285660).sum := by decide
  have hdescent : baseEnd_1285660 < baseStart_1285660 := by decide
  rcases family_descends (prefixWord ++ tailWord_1285660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1285664 : List Nat := [2, 1, 1, 6, 1, 3, 1, 1, 1, 6]
def baseStart_1285664 : Nat := 118140960795 + 1285664 * 2 ^ 59
def prefixEnd_1285664 : Nat := 4983230072969 + 3 ^ 40 * 1285664 * 2
def baseEnd_1285664 : Nat := 220054530727387689129115

theorem tailTrace_1285664 : CollatzResearch.WordTrace tailWord_1285664 prefixEnd_1285664 220054530727387689129115 := by
  unfold tailWord_1285664
  simp only [CollatzResearch.WordTrace]
  refine ⟨23446009207133188387568023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31261345609510917850090697 23446009207133188387568023)
  ·
    refine ⟨35169013810699782581352035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23446009207133188387568023 35169013810699782581352035)
    ·
      refine ⟨52753520716049673872028053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35169013810699782581352035 52753520716049673872028053)
      ·
        refine ⟨2472821283564828462751315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 52753520716049673872028053 2472821283564828462751315)
        ·
          refine ⟨3709231925347242694126973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2472821283564828462751315 3709231925347242694126973)
          ·
            refine ⟨1390961972005216010297615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3709231925347242694126973 1390961972005216010297615)
            ·
              refine ⟨2086442958007824015446423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1390961972005216010297615 2086442958007824015446423)
              ·
                refine ⟨3129664437011736023169635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2086442958007824015446423 3129664437011736023169635)
                ·
                  refine ⟨4694496655517604034754453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3129664437011736023169635 4694496655517604034754453)
                  ·
                    refine ⟨220054530727387689129115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4694496655517604034754453 220054530727387689129115)
                    ·
                      rfl

theorem cell23_1285664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 3, 1, 1, 1, 6].length) (baseStart_1285664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1285664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1285664 prefixEnd_1285664 := by exact prefixLift 1285664
  have htrace : WordTrace (prefixWord ++ tailWord_1285664) baseStart_1285664 baseEnd_1285664 := by
    simpa [prefixWord, tailWord_1285664, baseEnd_1285664] using wordTrace_append hprefix tailTrace_1285664
  have hstable : (prefixWord ++ tailWord_1285664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1285664).length < 2 ^ (prefixWord ++ tailWord_1285664).sum := by decide
  have hdescent : baseEnd_1285664 < baseStart_1285664 := by decide
  rcases family_descends (prefixWord ++ tailWord_1285664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1285667 : List Nat := [1, 1, 1, 4, 5, 1, 1, 1, 1, 1, 6]
def baseStart_1285667 : Nat := 118140960795 + 1285667 * 2 ^ 59
def prefixEnd_1285667 : Nat := 4983230072969 + 3 ^ 40 * 1285667 * 2
def baseEnd_1285667 : Nat := 660165132624126555649831

theorem tailTrace_1285667 : CollatzResearch.WordTrace tailWord_1285667 prefixEnd_1285667 660165132624126555649831 := by
  unfold tailWord_1285667
  simp only [CollatzResearch.WordTrace]
  refine ⟨46892127833255508287495255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31261418555503672191663503 46892127833255508287495255)
  ·
    refine ⟨70338191749883262431242883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46892127833255508287495255 70338191749883262431242883)
    ·
      refine ⟨105507287624824893646864325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70338191749883262431242883 105507287624824893646864325)
      ·
        refine ⟨19782616429654667558787061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 105507287624824893646864325 19782616429654667558787061)
        ·
          refine ⟨1854620290280125083636287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 19782616429654667558787061 1854620290280125083636287)
          ·
            refine ⟨2781930435420187625454431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1854620290280125083636287 2781930435420187625454431)
            ·
              refine ⟨4172895653130281438181647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2781930435420187625454431 4172895653130281438181647)
              ·
                refine ⟨6259343479695422157272471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4172895653130281438181647 6259343479695422157272471)
                ·
                  refine ⟨9389015219543133235908707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6259343479695422157272471 9389015219543133235908707)
                  ·
                    refine ⟨14083522829314699853863061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9389015219543133235908707 14083522829314699853863061)
                    ·
                      refine ⟨660165132624126555649831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 14083522829314699853863061 660165132624126555649831)
                      ·
                        rfl

theorem cell23_1285667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 1, 1, 1, 1, 6].length) (baseStart_1285667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1285667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1285667 prefixEnd_1285667 := by exact prefixLift 1285667
  have htrace : WordTrace (prefixWord ++ tailWord_1285667) baseStart_1285667 baseEnd_1285667 := by
    simpa [prefixWord, tailWord_1285667, baseEnd_1285667] using wordTrace_append hprefix tailTrace_1285667
  have hstable : (prefixWord ++ tailWord_1285667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1285667).length < 2 ^ (prefixWord ++ tailWord_1285667).sum := by decide
  have hdescent : baseEnd_1285667 < baseStart_1285667 := by decide
  rcases family_descends (prefixWord ++ tailWord_1285667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1285688 : List Nat := [2, 1, 2, 1, 4, 2, 3, 3, 1, 2, 2]
def baseStart_1285688 : Nat := 118140960795 + 1285688 * 2 ^ 59
def prefixEnd_1285688 : Nat := 4983230072969 + 3 ^ 40 * 1285688 * 2
def baseEnd_1285688 : Nat := 660175915717870973487235

theorem tailTrace_1285688 : CollatzResearch.WordTrace tailWord_1285688 prefixEnd_1285688 660175915717870973487235 := by
  unfold tailWord_1285688
  simp only [CollatzResearch.WordTrace]
  refine ⟨23446446883089714437004859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31261929177452952582673145 23446446883089714437004859)
  ·
    refine ⟨35169670324634571655507289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23446446883089714437004859 35169670324634571655507289)
    ·
      refine ⟨26377252743475928741630467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35169670324634571655507289 26377252743475928741630467)
      ·
        refine ⟨39565879115213893112445701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26377252743475928741630467 39565879115213893112445701)
        ·
          refine ⟨7418602334102604958583569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 39565879115213893112445701 7418602334102604958583569)
          ·
            refine ⟨5563951750576953718937677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7418602334102604958583569 5563951750576953718937677)
            ·
              refine ⟨2086481906466357644601629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5563951750576953718937677 2086481906466357644601629)
              ·
                refine ⟨782430714924884116725611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2086481906466357644601629 782430714924884116725611)
                ·
                  refine ⟨1173646072387326175088417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 782430714924884116725611 1173646072387326175088417)
                  ·
                    refine ⟨880234554290494631316313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1173646072387326175088417 880234554290494631316313)
                    ·
                      refine ⟨660175915717870973487235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 880234554290494631316313 660175915717870973487235)
                      ·
                        rfl

theorem cell23_1285688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 3, 3, 1, 2, 2].length) (baseStart_1285688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1285688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1285688 prefixEnd_1285688 := by exact prefixLift 1285688
  have htrace : WordTrace (prefixWord ++ tailWord_1285688) baseStart_1285688 baseEnd_1285688 := by
    simpa [prefixWord, tailWord_1285688, baseEnd_1285688] using wordTrace_append hprefix tailTrace_1285688
  have hstable : (prefixWord ++ tailWord_1285688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1285688).length < 2 ^ (prefixWord ++ tailWord_1285688).sum := by decide
  have hdescent : baseEnd_1285688 < baseStart_1285688 := by decide
  rcases family_descends (prefixWord ++ tailWord_1285688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1285720 : List Nat := [2, 1, 2, 2, 1, 2, 1, 3, 1, 8]
def baseStart_1285720 : Nat := 118140960795 + 1285720 * 2 ^ 59
def prefixEnd_1285720 : Nat := 4983230072969 + 3 ^ 40 * 1285720 * 2
def baseEnd_1285720 : Nat := 220064115699604949429029

theorem tailTrace_1285720 : CollatzResearch.WordTrace tailWord_1285720 prefixEnd_1285720 220064115699604949429029 := by
  unfold tailWord_1285720
  simp only [CollatzResearch.WordTrace]
  refine ⟨23447030451031749169587307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31262707268042332226116409 23447030451031749169587307)
  ·
    refine ⟨35170545676547623754380961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23447030451031749169587307 35170545676547623754380961)
    ·
      refine ⟨26377909257410717815785721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35170545676547623754380961 26377909257410717815785721)
      ·
        refine ⟨19783431943058038361839291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26377909257410717815785721 19783431943058038361839291)
        ·
          refine ⟨29675147914587057542758937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19783431943058038361839291 29675147914587057542758937)
          ·
            refine ⟨22256360935940293157069203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29675147914587057542758937 22256360935940293157069203)
            ·
              refine ⟨33384541403910439735603805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22256360935940293157069203 33384541403910439735603805)
              ·
                refine ⟨12519203026466414900851427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33384541403910439735603805 12519203026466414900851427)
                ·
                  refine ⟨18778804539699622351277141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12519203026466414900851427 18778804539699622351277141)
                  ·
                    refine ⟨220064115699604949429029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 18778804539699622351277141 220064115699604949429029)
                    ·
                      rfl

theorem cell23_1285720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 3, 1, 8].length) (baseStart_1285720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1285720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1285720 prefixEnd_1285720 := by exact prefixLift 1285720
  have htrace : WordTrace (prefixWord ++ tailWord_1285720) baseStart_1285720 baseEnd_1285720 := by
    simpa [prefixWord, tailWord_1285720, baseEnd_1285720] using wordTrace_append hprefix tailTrace_1285720
  have hstable : (prefixWord ++ tailWord_1285720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1285720).length < 2 ^ (prefixWord ++ tailWord_1285720).sum := by decide
  have hdescent : baseEnd_1285720 < baseStart_1285720 := by decide
  rcases family_descends (prefixWord ++ tailWord_1285720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1285725 : List Nat := [1, 4, 4, 2, 1, 2, 1, 2, 1, 2, 3]
def baseStart_1285725 : Nat := 118140960795 + 1285725 * 2 ^ 59
def prefixEnd_1285725 : Nat := 4983230072969 + 3 ^ 40 * 1285725 * 2
def baseEnd_1285725 : Nat := 660194914502087328724565

theorem tailTrace_1285725 : CollatzResearch.WordTrace tailWord_1285725 prefixEnd_1285725 660194914502087328724565 := by
  unfold tailWord_1285725
  simp only [CollatzResearch.WordTrace]
  refine ⟨46894243267045384193106629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31262828844696922795404419 46894243267045384193106629)
  ·
    refine ⟨8792670612571009536207493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 46894243267045384193106629 8792670612571009536207493)
    ·
      refine ⟨1648625739857064288038905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8792670612571009536207493 1648625739857064288038905)
      ·
        refine ⟨1236469304892798216029179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1648625739857064288038905 1236469304892798216029179)
        ·
          refine ⟨1854703957339197324043769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1236469304892798216029179 1854703957339197324043769)
          ·
            refine ⟨1391027968004397993032827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1854703957339197324043769 1391027968004397993032827)
            ·
              refine ⟨2086541952006596989549241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1391027968004397993032827 2086541952006596989549241)
              ·
                refine ⟨1564906464004947742161931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2086541952006596989549241 1564906464004947742161931)
                ·
                  refine ⟨2347359696007421613242897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1564906464004947742161931 2347359696007421613242897)
                  ·
                    refine ⟨1760519772005566209932173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2347359696007421613242897 1760519772005566209932173)
                    ·
                      refine ⟨660194914502087328724565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1760519772005566209932173 660194914502087328724565)
                      ·
                        rfl

theorem cell23_1285725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 2, 1, 2, 1, 2, 3].length) (baseStart_1285725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1285725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1285725 prefixEnd_1285725 := by exact prefixLift 1285725
  have htrace : WordTrace (prefixWord ++ tailWord_1285725) baseStart_1285725 baseEnd_1285725 := by
    simpa [prefixWord, tailWord_1285725, baseEnd_1285725] using wordTrace_append hprefix tailTrace_1285725
  have hstable : (prefixWord ++ tailWord_1285725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1285725).length < 2 ^ (prefixWord ++ tailWord_1285725).sum := by decide
  have hdescent : baseEnd_1285725 < baseStart_1285725 := by decide
  rcases family_descends (prefixWord ++ tailWord_1285725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1285731 : List Nat := [1, 1, 1, 5, 1, 3, 3, 2, 1, 3, 2]
def baseStart_1285731 : Nat := 118140960795 + 1285731 * 2 ^ 59
def prefixEnd_1285731 : Nat := 4983230072969 + 3 ^ 40 * 1285731 * 2
def baseEnd_1285731 : Nat := 660197995386014305249537

theorem tailTrace_1285731 : CollatzResearch.WordTrace tailWord_1285731 prefixEnd_1285731 660197995386014305249537 := by
  unfold tailWord_1285731
  simp only [CollatzResearch.WordTrace]
  refine ⟨46894462105023647217825047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31262974736682431478550031 46894462105023647217825047)
  ·
    refine ⟨70341693157535470826737571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46894462105023647217825047 70341693157535470826737571)
    ·
      refine ⟨105512539736303206240106357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70341693157535470826737571 105512539736303206240106357)
      ·
        refine ⟨9891800600278425585009971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 105512539736303206240106357 9891800600278425585009971)
        ·
          refine ⟨14837700900417638377514957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9891800600278425585009971 14837700900417638377514957)
          ·
            refine ⟨5564137837656614391568109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14837700900417638377514957 5564137837656614391568109)
            ·
              refine ⟨2086551689121230396838041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5564137837656614391568109 2086551689121230396838041)
              ·
                refine ⟨1564913766840922797628531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2086551689121230396838041 1564913766840922797628531)
                ·
                  refine ⟨2347370650261384196442797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1564913766840922797628531 2347370650261384196442797)
                  ·
                    refine ⟨880263993848019073666049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2347370650261384196442797 880263993848019073666049)
                    ·
                      refine ⟨660197995386014305249537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 880263993848019073666049 660197995386014305249537)
                      ·
                        rfl

theorem cell23_1285731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 3, 2, 1, 3, 2].length) (baseStart_1285731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1285731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1285731 prefixEnd_1285731 := by exact prefixLift 1285731
  have htrace : WordTrace (prefixWord ++ tailWord_1285731) baseStart_1285731 baseEnd_1285731 := by
    simpa [prefixWord, tailWord_1285731, baseEnd_1285731] using wordTrace_append hprefix tailTrace_1285731
  have hstable : (prefixWord ++ tailWord_1285731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1285731).length < 2 ^ (prefixWord ++ tailWord_1285731).sum := by decide
  have hdescent : baseEnd_1285731 < baseStart_1285731 := by decide
  rcases family_descends (prefixWord ++ tailWord_1285731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1285744 : List Nat := [2, 1, 1, 1, 6, 1, 1, 1, 3, 4, 2]
def baseStart_1285744 : Nat := 118140960795 + 1285744 * 2 ^ 59
def prefixEnd_1285744 : Nat := 4983230072969 + 3 ^ 40 * 1285744 * 2
def baseEnd_1285744 : Nat := 660204670634522754386977

theorem tailTrace_1285744 : CollatzResearch.WordTrace tailWord_1285744 prefixEnd_1285744 660204670634522754386977 := by
  unfold tailWord_1285744
  simp only [CollatzResearch.WordTrace]
  refine ⟨23447468126988275219024143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31263290835984366958698857 23447468126988275219024143)
  ·
    refine ⟨35171202190482412828536215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23447468126988275219024143 35171202190482412828536215)
    ·
      refine ⟨52756803285723619242804323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35171202190482412828536215 52756803285723619242804323)
      ·
        refine ⟨79135204928585428864206485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52756803285723619242804323 79135204928585428864206485)
        ·
          refine ⟨3709462731027441978009679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 79135204928585428864206485 3709462731027441978009679)
          ·
            refine ⟨5564194096541162967014519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3709462731027441978009679 5564194096541162967014519)
            ·
              refine ⟨8346291144811744450521779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5564194096541162967014519 8346291144811744450521779)
              ·
                refine ⟨12519436717217616675782669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8346291144811744450521779 12519436717217616675782669)
                ·
                  refine ⟨4694788768956606253418501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12519436717217616675782669 4694788768956606253418501)
                  ·
                    refine ⟨880272894179363672515969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4694788768956606253418501 880272894179363672515969)
                    ·
                      refine ⟨660204670634522754386977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 880272894179363672515969 660204670634522754386977)
                      ·
                        rfl

theorem cell23_1285744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 1, 1, 3, 4, 2].length) (baseStart_1285744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1285744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1285744 prefixEnd_1285744 := by exact prefixLift 1285744
  have htrace : WordTrace (prefixWord ++ tailWord_1285744) baseStart_1285744 baseEnd_1285744 := by
    simpa [prefixWord, tailWord_1285744, baseEnd_1285744] using wordTrace_append hprefix tailTrace_1285744
  have hstable : (prefixWord ++ tailWord_1285744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1285744).length < 2 ^ (prefixWord ++ tailWord_1285744).sum := by decide
  have hdescent : baseEnd_1285744 < baseStart_1285744 := by decide
  rcases family_descends (prefixWord ++ tailWord_1285744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1285774 : List Nat := [4, 1, 1, 3, 1, 3, 1, 1, 2, 2, 4]
def baseStart_1285774 : Nat := 118140960795 + 1285774 * 2 ^ 59
def prefixEnd_1285774 : Nat := 4983230072969 + 3 ^ 40 * 1285774 * 2
def baseEnd_1285774 : Nat := 660220075054157637011839

theorem tailTrace_1285774 : CollatzResearch.WordTrace tailWord_1285774 prefixEnd_1285774 660220075054157637011839 := by
  unfold tailWord_1285774
  simp only [CollatzResearch.WordTrace]
  refine ⟨5862003805483483195205047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 31264020295911910374426917 5862003805483483195205047)
  ·
    refine ⟨8793005708225224792807571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5862003805483483195205047 8793005708225224792807571)
    ·
      refine ⟨13189508562337837189211357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8793005708225224792807571 13189508562337837189211357)
      ·
        refine ⟨4946065710876688945954259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13189508562337837189211357 4946065710876688945954259)
        ·
          refine ⟨7419098566315033418931389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4946065710876688945954259 7419098566315033418931389)
          ·
            refine ⟨2782161962368137532099271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7419098566315033418931389 2782161962368137532099271)
            ·
              refine ⟨4173242943552206298148907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2782161962368137532099271 4173242943552206298148907)
              ·
                refine ⟨6259864415328309447223361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4173242943552206298148907 6259864415328309447223361)
                ·
                  refine ⟨4694898311496232085417521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6259864415328309447223361 4694898311496232085417521)
                  ·
                    refine ⟨3521173733622174064063141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4694898311496232085417521 3521173733622174064063141)
                    ·
                      refine ⟨660220075054157637011839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3521173733622174064063141 660220075054157637011839)
                      ·
                        rfl

theorem cell23_1285774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 1, 1, 2, 2, 4].length) (baseStart_1285774 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1285774 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1285774 prefixEnd_1285774 := by exact prefixLift 1285774
  have htrace : WordTrace (prefixWord ++ tailWord_1285774) baseStart_1285774 baseEnd_1285774 := by
    simpa [prefixWord, tailWord_1285774, baseEnd_1285774] using wordTrace_append hprefix tailTrace_1285774
  have hstable : (prefixWord ++ tailWord_1285774).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1285774).length < 2 ^ (prefixWord ++ tailWord_1285774).sum := by decide
  have hdescent : baseEnd_1285774 < baseStart_1285774 := by decide
  rcases family_descends (prefixWord ++ tailWord_1285774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1285778 : List Nat := [3, 2, 3, 1, 3, 1, 2, 1, 1, 4, 2]
def baseStart_1285778 : Nat := 118140960795 + 1285778 * 2 ^ 59
def prefixEnd_1285778 : Nat := 4983230072969 + 3 ^ 40 * 1285778 * 2
def baseEnd_1285778 : Nat := 660222128976775621361821

theorem tailTrace_1285778 : CollatzResearch.WordTrace tailWord_1285778 prefixEnd_1285778 660222128976775621361821 := by
  unfold tailWord_1285778
  simp only [CollatzResearch.WordTrace]
  refine ⟨11724044083963343561196497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31264117557235582829857325 11724044083963343561196497)
  ·
    refine ⟨8793033062972507670897373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11724044083963343561196497 8793033062972507670897373)
    ·
      refine ⟨3297387398614690376586515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8793033062972507670897373 3297387398614690376586515)
      ·
        refine ⟨4946081097922035564879773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3297387398614690376586515 4946081097922035564879773)
        ·
          refine ⟨1854780411720763336829915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4946081097922035564879773 1854780411720763336829915)
          ·
            refine ⟨2782170617581145005244873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1854780411720763336829915 2782170617581145005244873)
            ·
              refine ⟨2086627963185858753933655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2782170617581145005244873 2086627963185858753933655)
              ·
                refine ⟨3129941944778788130900483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2086627963185858753933655 3129941944778788130900483)
                ·
                  refine ⟨4694912917168182196350725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3129941944778788130900483 4694912917168182196350725)
                  ·
                    refine ⟨880296171969034161815761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4694912917168182196350725 880296171969034161815761)
                    ·
                      refine ⟨660222128976775621361821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 880296171969034161815761 660222128976775621361821)
                      ·
                        rfl

theorem cell23_1285778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 2, 1, 1, 4, 2].length) (baseStart_1285778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1285778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1285778 prefixEnd_1285778 := by exact prefixLift 1285778
  have htrace : WordTrace (prefixWord ++ tailWord_1285778) baseStart_1285778 baseEnd_1285778 := by
    simpa [prefixWord, tailWord_1285778, baseEnd_1285778] using wordTrace_append hprefix tailTrace_1285778
  have hstable : (prefixWord ++ tailWord_1285778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1285778).length < 2 ^ (prefixWord ++ tailWord_1285778).sum := by decide
  have hdescent : baseEnd_1285778 < baseStart_1285778 := by decide
  rcases family_descends (prefixWord ++ tailWord_1285778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1285847 : List Nat := [1, 1, 3, 2, 1, 3, 1, 1, 2, 4, 4]
def baseStart_1285847 : Nat := 118140960795 + 1285847 * 2 ^ 59
def prefixEnd_1285847 : Nat := 4983230072969 + 3 ^ 40 * 1285847 * 2
def baseEnd_1285847 : Nat := 660257559141935851399003

theorem tailTrace_1285847 : CollatzResearch.WordTrace tailWord_1285847 prefixEnd_1285847 660257559141935851399003 := by
  unfold tailWord_1285847
  simp only [CollatzResearch.WordTrace]
  refine ⟨46898692972603399029047795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31265795315068932686031863 46898692972603399029047795)
  ·
    refine ⟨70348039458905098543571693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46898692972603399029047795 70348039458905098543571693)
    ·
      refine ⟨26380514797089411953839385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 70348039458905098543571693 26380514797089411953839385)
      ·
        refine ⟨19785386097817058965379539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26380514797089411953839385 19785386097817058965379539)
        ·
          refine ⟨29678079146725588448069309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19785386097817058965379539 29678079146725588448069309)
          ·
            refine ⟨11129279680022095668025991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29678079146725588448069309 11129279680022095668025991)
            ·
              refine ⟨16693919520033143502038987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11129279680022095668025991 16693919520033143502038987)
              ·
                refine ⟨25040879280049715253058481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16693919520033143502038987 25040879280049715253058481)
                ·
                  refine ⟨18780659460037286439793861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25040879280049715253058481 18780659460037286439793861)
                  ·
                    refine ⟨3521373648756991207461349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18780659460037286439793861 3521373648756991207461349)
                    ·
                      refine ⟨660257559141935851399003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3521373648756991207461349 660257559141935851399003)
                      ·
                        rfl

theorem cell23_1285847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 1, 2, 4, 4].length) (baseStart_1285847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1285847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1285847 prefixEnd_1285847 := by exact prefixLift 1285847
  have htrace : WordTrace (prefixWord ++ tailWord_1285847) baseStart_1285847 baseEnd_1285847 := by
    simpa [prefixWord, tailWord_1285847, baseEnd_1285847] using wordTrace_append hprefix tailTrace_1285847
  have hstable : (prefixWord ++ tailWord_1285847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1285847).length < 2 ^ (prefixWord ++ tailWord_1285847).sum := by decide
  have hdescent : baseEnd_1285847 < baseStart_1285847 := by decide
  rcases family_descends (prefixWord ++ tailWord_1285847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1285874 : List Nat := [3, 2, 1, 3, 1, 1, 2, 4, 6]
def baseStart_1285874 : Nat := 118140960795 + 1285874 * 2 ^ 59
def prefixEnd_1285874 : Nat := 4983230072969 + 3 ^ 40 * 1285874 * 2
def baseEnd_1285874 : Nat := 73363491457734138417931

theorem tailTrace_1285874 : CollatzResearch.WordTrace tailWord_1285874 prefixEnd_1285874 73363491457734138417931 := by
  unfold tailWord_1285874
  simp only [CollatzResearch.WordTrace]
  refine ⟨11724919435876395660070169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31266451829003721760187117 11724919435876395660070169)
  ·
    refine ⟨8793689576907296745052627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11724919435876395660070169 8793689576907296745052627)
    ·
      refine ⟨13190534365360945117578941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8793689576907296745052627 13190534365360945117578941)
      ·
        refine ⟨4946450387010354419092103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13190534365360945117578941 4946450387010354419092103)
        ·
          refine ⟨7419675580515531628638155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4946450387010354419092103 7419675580515531628638155)
          ·
            refine ⟨11129513370773297442957233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7419675580515531628638155 11129513370773297442957233)
            ·
              refine ⟨8347135028079973082217925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11129513370773297442957233 8347135028079973082217925)
              ·
                refine ⟨1565087817764994952915861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8347135028079973082217925 1565087817764994952915861)
                ·
                  refine ⟨73363491457734138417931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1565087817764994952915861 73363491457734138417931)
                  ·
                    rfl

theorem cell23_1285874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 2, 4, 6].length) (baseStart_1285874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1285874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1285874 prefixEnd_1285874 := by exact prefixLift 1285874
  have htrace : WordTrace (prefixWord ++ tailWord_1285874) baseStart_1285874 baseEnd_1285874 := by
    simpa [prefixWord, tailWord_1285874, baseEnd_1285874] using wordTrace_append hprefix tailTrace_1285874
  have hstable : (prefixWord ++ tailWord_1285874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1285874).length < 2 ^ (prefixWord ++ tailWord_1285874).sum := by decide
  have hdescent : baseEnd_1285874 < baseStart_1285874 := by decide
  rcases family_descends (prefixWord ++ tailWord_1285874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1285878 : List Nat := [5, 1, 1, 1, 1, 5, 1, 1, 3, 4]
def baseStart_1285878 : Nat := 118140960795 + 1285878 * 2 ^ 59
def prefixEnd_1285878 : Nat := 4983230072969 + 3 ^ 40 * 1285878 * 2
def baseEnd_1285878 : Nat := 220091159014075076703787

theorem tailTrace_1285878 : CollatzResearch.WordTrace tailWord_1285878 prefixEnd_1285878 220091159014075076703787 := by
  unfold tailWord_1285878
  simp only [CollatzResearch.WordTrace]
  refine ⟨2931238977218193207714143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 31266549090327394215617525 2931238977218193207714143)
  ·
    refine ⟨4396858465827289811571215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2931238977218193207714143 4396858465827289811571215)
    ·
      refine ⟨6595287698740934717356823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4396858465827289811571215 6595287698740934717356823)
      ·
        refine ⟨9892931548111402076035235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6595287698740934717356823 9892931548111402076035235)
        ·
          refine ⟨14839397322167103114052853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9892931548111402076035235 14839397322167103114052853)
          ·
            refine ⟨1391193498953165916942455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 14839397322167103114052853 1391193498953165916942455)
            ·
              refine ⟨2086790248429748875413683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1391193498953165916942455 2086790248429748875413683)
              ·
                refine ⟨3130185372644623313120525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2086790248429748875413683 3130185372644623313120525)
                ·
                  refine ⟨1173819514741733742420197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3130185372644623313120525 1173819514741733742420197)
                  ·
                    refine ⟨220091159014075076703787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1173819514741733742420197 220091159014075076703787)
                    ·
                      rfl

theorem cell23_1285878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 5, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 5, 1, 1, 3, 4].length) (baseStart_1285878 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1285878 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1285878 prefixEnd_1285878 := by exact prefixLift 1285878
  have htrace : WordTrace (prefixWord ++ tailWord_1285878) baseStart_1285878 baseEnd_1285878 := by
    simpa [prefixWord, tailWord_1285878, baseEnd_1285878] using wordTrace_append hprefix tailTrace_1285878
  have hstable : (prefixWord ++ tailWord_1285878).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1285878).length < 2 ^ (prefixWord ++ tailWord_1285878).sum := by decide
  have hdescent : baseEnd_1285878 < baseStart_1285878 := by decide
  rcases family_descends (prefixWord ++ tailWord_1285878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1285928 : List Nat := [2, 1, 5, 1, 1, 2, 2, 2, 2, 3, 2]
def baseStart_1285928 : Nat := 118140960795 + 1285928 * 2 ^ 59
def prefixEnd_1285928 : Nat := 4983230072969 + 3 ^ 40 * 1285928 * 2
def baseEnd_1285928 : Nat := 660299151074950034486131

theorem tailTrace_1285928 : CollatzResearch.WordTrace tailWord_1285928 prefixEnd_1285928 660299151074950034486131 := by
  unfold tailWord_1285928
  simp only [CollatzResearch.WordTrace]
  refine ⟨23450823642654974931373219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31267764856873299908497625 23450823642654974931373219)
  ·
    refine ⟨35176235463982462397059829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23450823642654974931373219 35176235463982462397059829)
    ·
      refine ⟨3297772074748355849724359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 35176235463982462397059829 3297772074748355849724359)
      ·
        refine ⟨4946658112122533774586539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3297772074748355849724359 4946658112122533774586539)
        ·
          refine ⟨7419987168183800661879809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4946658112122533774586539 7419987168183800661879809)
          ·
            refine ⟨5564990376137850496409857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7419987168183800661879809 5564990376137850496409857)
            ·
              refine ⟨4173742782103387872307393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5564990376137850496409857 4173742782103387872307393)
              ·
                refine ⟨3130307086577540904230545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4173742782103387872307393 3130307086577540904230545)
                ·
                  refine ⟨2347730314933155678172909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3130307086577540904230545 2347730314933155678172909)
                  ·
                    refine ⟨880398868099933379314841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2347730314933155678172909 880398868099933379314841)
                    ·
                      refine ⟨660299151074950034486131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 880398868099933379314841 660299151074950034486131)
                      ·
                        rfl

theorem cell23_1285928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 2, 2, 2, 3, 2].length) (baseStart_1285928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1285928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1285928 prefixEnd_1285928 := by exact prefixLift 1285928
  have htrace : WordTrace (prefixWord ++ tailWord_1285928) baseStart_1285928 baseEnd_1285928 := by
    simpa [prefixWord, tailWord_1285928, baseEnd_1285928] using wordTrace_append hprefix tailTrace_1285928
  have hstable : (prefixWord ++ tailWord_1285928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1285928).length < 2 ^ (prefixWord ++ tailWord_1285928).sum := by decide
  have hdescent : baseEnd_1285928 < baseStart_1285928 := by decide
  rcases family_descends (prefixWord ++ tailWord_1285928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1285951 : List Nat := [1, 1, 2, 2, 6, 1, 2, 1, 1, 6]
def baseStart_1285951 : Nat := 118140960795 + 1285951 * 2 ^ 59
def prefixEnd_1285951 : Nat := 4983230072969 + 3 ^ 40 * 1285951 * 2
def baseEnd_1285951 : Nat := 220103653710001148166175

theorem tailTrace_1285951 : CollatzResearch.WordTrace tailWord_1285951 prefixEnd_1285951 220103653710001148166175 := by
  unfold tailWord_1285951
  simp only [CollatzResearch.WordTrace]
  refine ⟨46902486164226624790833707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31268324109484416527222471 46902486164226624790833707)
  ·
    refine ⟨70353729246339937186250561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46902486164226624790833707 70353729246339937186250561)
    ·
      refine ⟨52765296934754952889687921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70353729246339937186250561 52765296934754952889687921)
      ·
        refine ⟨39573972701066214667265941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52765296934754952889687921 39573972701066214667265941)
        ·
          refine ⟨1855029970362478812528091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 39573972701066214667265941 1855029970362478812528091)
          ·
            refine ⟨2782544955543718218792137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1855029970362478812528091 2782544955543718218792137)
            ·
              refine ⟨2086908716657788664094103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2782544955543718218792137 2086908716657788664094103)
              ·
                refine ⟨3130363074986682996141155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2086908716657788664094103 3130363074986682996141155)
                ·
                  refine ⟨4695544612480024494211733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3130363074986682996141155 4695544612480024494211733)
                  ·
                    refine ⟨220103653710001148166175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4695544612480024494211733 220103653710001148166175)
                    ·
                      rfl

theorem cell23_1285951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 2, 1, 1, 6].length) (baseStart_1285951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1285951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1285951 prefixEnd_1285951 := by exact prefixLift 1285951
  have htrace : WordTrace (prefixWord ++ tailWord_1285951) baseStart_1285951 baseEnd_1285951 := by
    simpa [prefixWord, tailWord_1285951, baseEnd_1285951] using wordTrace_append hprefix tailTrace_1285951
  have hstable : (prefixWord ++ tailWord_1285951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1285951).length < 2 ^ (prefixWord ++ tailWord_1285951).sum := by decide
  have hdescent : baseEnd_1285951 < baseStart_1285951 := by decide
  rcases family_descends (prefixWord ++ tailWord_1285951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1285961 : List Nat := [1, 2, 1, 1, 2, 4, 2, 4, 1, 2, 3]
def baseStart_1285961 : Nat := 118140960795 + 1285961 * 2 ^ 59
def prefixEnd_1285961 : Nat := 4983230072969 + 3 ^ 40 * 1285961 * 2
def baseEnd_1285961 : Nat := 660316095936548405373479

theorem tailTrace_1285961 : CollatzResearch.WordTrace tailWord_1285961 prefixEnd_1285961 660316095936548405373479 := by
  unfold tailWord_1285961
  simp only [CollatzResearch.WordTrace]
  refine ⟨46902850894190396498697737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31268567262793597665798491 46902850894190396498697737)
  ·
    refine ⟨35177138170642797374023303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46902850894190396498697737 35177138170642797374023303)
    ·
      refine ⟨52765707255964196061034955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35177138170642797374023303 52765707255964196061034955)
      ·
        refine ⟨79148560883946294091552433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52765707255964196061034955 79148560883946294091552433)
        ·
          refine ⟨59361420662959720568664325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79148560883946294091552433 59361420662959720568664325)
          ·
            refine ⟨11130266374304947606624561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 59361420662959720568664325 11130266374304947606624561)
            ·
              refine ⟨8347699780728710704968421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11130266374304947606624561 8347699780728710704968421)
              ·
                refine ⟨1565193708886633257181579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8347699780728710704968421 1565193708886633257181579)
                ·
                  refine ⟨2347790563329949885772369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1565193708886633257181579 2347790563329949885772369)
                  ·
                    refine ⟨1760842922497462414329277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2347790563329949885772369 1760842922497462414329277)
                    ·
                      refine ⟨660316095936548405373479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1760842922497462414329277 660316095936548405373479)
                      ·
                        rfl

theorem cell23_1285961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 2, 4, 1, 2, 3].length) (baseStart_1285961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1285961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1285961 prefixEnd_1285961 := by exact prefixLift 1285961
  have htrace : WordTrace (prefixWord ++ tailWord_1285961) baseStart_1285961 baseEnd_1285961 := by
    simpa [prefixWord, tailWord_1285961, baseEnd_1285961] using wordTrace_append hprefix tailTrace_1285961
  have hstable : (prefixWord ++ tailWord_1285961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1285961).length < 2 ^ (prefixWord ++ tailWord_1285961).sum := by decide
  have hdescent : baseEnd_1285961 < baseStart_1285961 := by decide
  rcases family_descends (prefixWord ++ tailWord_1285961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1285975 : List Nat := [1, 1, 3, 2, 5, 2, 2, 1, 1, 1, 4]
def baseStart_1285975 : Nat := 118140960795 + 1285975 * 2 ^ 59
def prefixEnd_1285975 : Nat := 4983230072969 + 3 ^ 40 * 1285975 * 2
def baseEnd_1285975 : Nat := 660323284665711350598415

theorem tailTrace_1285975 : CollatzResearch.WordTrace tailWord_1285975 prefixEnd_1285975 660323284665711350598415 := by
  unfold tailWord_1285975
  simp only [CollatzResearch.WordTrace]
  refine ⟨46903361516139676889707379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31268907677426451259804919 46903361516139676889707379)
  ·
    refine ⟨70355042274209515334561069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46903361516139676889707379 70355042274209515334561069)
    ·
      refine ⟨26383140852828568250460401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 70355042274209515334561069 26383140852828568250460401)
      ·
        refine ⟨19787355639621426187845301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26383140852828568250460401 19787355639621426187845301)
        ·
          refine ⟨1855064591214508705110497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 19787355639621426187845301 1855064591214508705110497)
          ·
            refine ⟨1391298443410881528832873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1855064591214508705110497 1391298443410881528832873)
            ·
              refine ⟨1043473832558161146624655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1391298443410881528832873 1043473832558161146624655)
              ·
                refine ⟨1565210748837241719936983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1043473832558161146624655 1565210748837241719936983)
                ·
                  refine ⟨2347816123255862579905475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1565210748837241719936983 2347816123255862579905475)
                  ·
                    refine ⟨3521724184883793869858213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2347816123255862579905475 3521724184883793869858213)
                    ·
                      refine ⟨660323284665711350598415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3521724184883793869858213 660323284665711350598415)
                      ·
                        rfl

theorem cell23_1285975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 2, 2, 1, 1, 1, 4].length) (baseStart_1285975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1285975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1285975 prefixEnd_1285975 := by exact prefixLift 1285975
  have htrace : WordTrace (prefixWord ++ tailWord_1285975) baseStart_1285975 baseEnd_1285975 := by
    simpa [prefixWord, tailWord_1285975, baseEnd_1285975] using wordTrace_append hprefix tailTrace_1285975
  have hstable : (prefixWord ++ tailWord_1285975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1285975).length < 2 ^ (prefixWord ++ tailWord_1285975).sum := by decide
  have hdescent : baseEnd_1285975 < baseStart_1285975 := by decide
  rcases family_descends (prefixWord ++ tailWord_1285975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1286026 : List Nat := [3, 1, 2, 4, 3, 1, 1, 3, 1, 2, 2]
def baseStart_1286026 : Nat := 118140960795 + 1286026 * 2 ^ 59
def prefixEnd_1286026 : Nat := 4983230072969 + 3 ^ 40 * 1286026 * 2
def baseEnd_1286026 : Nat := 660349472179090651060681

theorem tailTrace_1286026 : CollatzResearch.WordTrace tailWord_1286026 prefixEnd_1286026 660349472179090651060681 := by
  unfold tailWord_1286026
  simp only [CollatzResearch.WordTrace]
  refine ⟨11726305409738728149953483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31270147759303275066542621 11726305409738728149953483)
  ·
    refine ⟨17589458114608092224930225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11726305409738728149953483 17589458114608092224930225)
    ·
      refine ⟨13192093585956069168697669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17589458114608092224930225 13192093585956069168697669)
      ·
        refine ⟨2473517547366762969130813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13192093585956069168697669 2473517547366762969130813)
        ·
          refine ⟨927569080262536113424055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2473517547366762969130813 927569080262536113424055)
          ·
            refine ⟨1391353620393804170136083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 927569080262536113424055 1391353620393804170136083)
            ·
              refine ⟨2087030430590706255204125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1391353620393804170136083 2087030430590706255204125)
              ·
                refine ⟨782636411471514845701547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2087030430590706255204125 782636411471514845701547)
                ·
                  refine ⟨1173954617207272268552321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 782636411471514845701547 1173954617207272268552321)
                  ·
                    refine ⟨880465962905454201414241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1173954617207272268552321 880465962905454201414241)
                    ·
                      refine ⟨660349472179090651060681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 880465962905454201414241 660349472179090651060681)
                      ·
                        rfl

theorem cell23_1286026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 3, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 3, 1, 1, 3, 1, 2, 2].length) (baseStart_1286026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1286026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1286026 prefixEnd_1286026 := by exact prefixLift 1286026
  have htrace : WordTrace (prefixWord ++ tailWord_1286026) baseStart_1286026 baseEnd_1286026 := by
    simpa [prefixWord, tailWord_1286026, baseEnd_1286026] using wordTrace_append hprefix tailTrace_1286026
  have hstable : (prefixWord ++ tailWord_1286026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1286026).length < 2 ^ (prefixWord ++ tailWord_1286026).sum := by decide
  have hdescent : baseEnd_1286026 < baseStart_1286026 := by decide
  rcases family_descends (prefixWord ++ tailWord_1286026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1286111 : List Nat := [1, 1, 2, 3, 4, 1, 2, 1, 1, 2, 5]
def baseStart_1286111 : Nat := 118140960795 + 1286111 * 2 ^ 59
def prefixEnd_1286111 : Nat := 4983230072969 + 3 ^ 40 * 1286111 * 2
def baseEnd_1286111 : Nat := 660393118034722818497789

theorem tailTrace_1286111 : CollatzResearch.WordTrace tailWord_1286111 prefixEnd_1286111 660393118034722818497789 := by
  unfold tailWord_1286111
  simp only [CollatzResearch.WordTrace]
  refine ⟨46908321843646972116658187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31272214562431314744438791 46908321843646972116658187)
  ·
    refine ⟨70362482765470458174987281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46908321843646972116658187 70362482765470458174987281)
    ·
      refine ⟨52771862074102843631240461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70362482765470458174987281 52771862074102843631240461)
      ·
        refine ⟨19789448277788566361715173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52771862074102843631240461 19789448277788566361715173)
        ·
          refine ⟨3710521552085356192821595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19789448277788566361715173 3710521552085356192821595)
          ·
            refine ⟨5565782328128034289232393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3710521552085356192821595 5565782328128034289232393)
            ·
              refine ⟨4174336746096025716924295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5565782328128034289232393 4174336746096025716924295)
              ·
                refine ⟨6261505119144038575386443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4174336746096025716924295 6261505119144038575386443)
                ·
                  refine ⟨9392257678716057863079665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6261505119144038575386443 9392257678716057863079665)
                  ·
                    refine ⟨7044193259037043397309749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9392257678716057863079665 7044193259037043397309749)
                    ·
                      refine ⟨660393118034722818497789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7044193259037043397309749 660393118034722818497789)
                      ·
                        rfl

theorem cell23_1286111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 2, 1, 1, 2, 5].length) (baseStart_1286111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1286111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1286111 prefixEnd_1286111 := by exact prefixLift 1286111
  have htrace : WordTrace (prefixWord ++ tailWord_1286111) baseStart_1286111 baseEnd_1286111 := by
    simpa [prefixWord, tailWord_1286111, baseEnd_1286111] using wordTrace_append hprefix tailTrace_1286111
  have hstable : (prefixWord ++ tailWord_1286111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1286111).length < 2 ^ (prefixWord ++ tailWord_1286111).sum := by decide
  have hdescent : baseEnd_1286111 < baseStart_1286111 := by decide
  rcases family_descends (prefixWord ++ tailWord_1286111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1286150 : List Nat := [6, 2, 1, 2, 1, 2, 1, 2, 2, 2, 2]
def baseStart_1286150 : Nat := 118140960795 + 1286150 * 2 ^ 59
def prefixEnd_1286150 : Nat := 4983230072969 + 3 ^ 40 * 1286150 * 2
def baseEnd_1286150 : Nat := 660413143780248165910111

theorem tailTrace_1286150 : CollatzResearch.WordTrace tailWord_1286150 prefixEnd_1286150 660413143780248165910111 := by
  unfold tailWord_1286150
  simp only [CollatzResearch.WordTrace]
  refine ⟨1465929509078302555541497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 31273162860337121184885269 1465929509078302555541497)
  ·
    refine ⟨1099447131808726916656123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1465929509078302555541497 1099447131808726916656123)
    ·
      refine ⟨1649170697713090374984185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1099447131808726916656123 1649170697713090374984185)
      ·
        refine ⟨1236878023284817781238139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1649170697713090374984185 1236878023284817781238139)
        ·
          refine ⟨1855317034927226671857209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1236878023284817781238139 1855317034927226671857209)
          ·
            refine ⟨1391487776195420003892907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1855317034927226671857209 1391487776195420003892907)
            ·
              refine ⟨2087231664293130005839361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1391487776195420003892907 2087231664293130005839361)
              ·
                refine ⟨1565423748219847504379521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2087231664293130005839361 1565423748219847504379521)
                ·
                  refine ⟨1174067811164885628284641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1565423748219847504379521 1174067811164885628284641)
                  ·
                    refine ⟨880550858373664221213481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1174067811164885628284641 880550858373664221213481)
                    ·
                      refine ⟨660413143780248165910111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 880550858373664221213481 660413143780248165910111)
                      ·
                        rfl

theorem cell23_1286150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 2, 1, 2, 2, 2, 2].length) (baseStart_1286150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1286150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1286150 prefixEnd_1286150 := by exact prefixLift 1286150
  have htrace : WordTrace (prefixWord ++ tailWord_1286150) baseStart_1286150 baseEnd_1286150 := by
    simpa [prefixWord, tailWord_1286150, baseEnd_1286150] using wordTrace_append hprefix tailTrace_1286150
  have hstable : (prefixWord ++ tailWord_1286150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1286150).length < 2 ^ (prefixWord ++ tailWord_1286150).sum := by decide
  have hdescent : baseEnd_1286150 < baseStart_1286150 := by decide
  rcases family_descends (prefixWord ++ tailWord_1286150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1286151 : List Nat := [1, 1, 4, 3, 1, 2, 1, 1, 2, 1, 6]
def baseStart_1286151 : Nat := 118140960795 + 1286151 * 2 ^ 59
def prefixEnd_1286151 : Nat := 4983230072969 + 3 ^ 40 * 1286151 * 2
def baseEnd_1286151 : Nat := 660413657260902661997605

theorem tailTrace_1286151 : CollatzResearch.WordTrace tailWord_1286151 prefixEnd_1286151 660413657260902661997605 := by
  unfold tailWord_1286151
  simp only [CollatzResearch.WordTrace]
  refine ⟨46909780763502058948114307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31273187175668039298742871 46909780763502058948114307)
  ·
    refine ⟨70364671145253088422171461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46909780763502058948114307 70364671145253088422171461)
    ·
      refine ⟨13193375839734954079157149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 70364671145253088422171461 13193375839734954079157149)
      ·
        refine ⟨4947515939900607779683931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13193375839734954079157149 4947515939900607779683931)
        ·
          refine ⟨7421273909850911669525897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4947515939900607779683931 7421273909850911669525897)
          ·
            refine ⟨5565955432388183752144423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7421273909850911669525897 5565955432388183752144423)
            ·
              refine ⟨8348933148582275628216635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5565955432388183752144423 8348933148582275628216635)
              ·
                refine ⟨12523399722873413442324953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8348933148582275628216635 12523399722873413442324953)
                ·
                  refine ⟨9392549792155060081743715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12523399722873413442324953 9392549792155060081743715)
                  ·
                    refine ⟨14088824688232590122615573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9392549792155060081743715 14088824688232590122615573)
                    ·
                      refine ⟨660413657260902661997605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 14088824688232590122615573 660413657260902661997605)
                      ·
                        rfl

theorem cell23_1286151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 1, 1, 2, 1, 6].length) (baseStart_1286151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1286151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1286151 prefixEnd_1286151 := by exact prefixLift 1286151
  have htrace : WordTrace (prefixWord ++ tailWord_1286151) baseStart_1286151 baseEnd_1286151 := by
    simpa [prefixWord, tailWord_1286151, baseEnd_1286151] using wordTrace_append hprefix tailTrace_1286151
  have hstable : (prefixWord ++ tailWord_1286151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1286151).length < 2 ^ (prefixWord ++ tailWord_1286151).sum := by decide
  have hdescent : baseEnd_1286151 < baseStart_1286151 := by decide
  rcases family_descends (prefixWord ++ tailWord_1286151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1286158 : List Nat := [4, 1, 1, 2, 2, 1, 2, 1, 4, 2, 3]
def baseStart_1286158 : Nat := 118140960795 + 1286158 * 2 ^ 59
def prefixEnd_1286158 : Nat := 4983230072969 + 3 ^ 40 * 1286158 * 2
def baseEnd_1286158 : Nat := 660417251625484134610073

theorem tailTrace_1286158 : CollatzResearch.WordTrace tailWord_1286158 prefixEnd_1286158 660417251625484134610073 := by
  unfold tailWord_1286158
  simp only [CollatzResearch.WordTrace]
  refine ⟨5863754509309587392952391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 31273357382984466095746085 5863754509309587392952391)
  ·
    refine ⟨8795631763964381089428587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5863754509309587392952391 8795631763964381089428587)
    ·
      refine ⟨13193447645946571634142881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8795631763964381089428587 13193447645946571634142881)
      ·
        refine ⟨9895085734459928725607161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13193447645946571634142881 9895085734459928725607161)
        ·
          refine ⟨7421314300844946544205371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9895085734459928725607161 7421314300844946544205371)
          ·
            refine ⟨11131971451267419816308057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7421314300844946544205371 11131971451267419816308057)
            ·
              refine ⟨8348978588450564862231043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11131971451267419816308057 8348978588450564862231043)
              ·
                refine ⟨12523467882675847293346565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8348978588450564862231043 12523467882675847293346565)
                ·
                  refine ⟨2348150228001721367502481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12523467882675847293346565 2348150228001721367502481)
                  ·
                    refine ⟨1761112671001291025626861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2348150228001721367502481 1761112671001291025626861)
                    ·
                      refine ⟨660417251625484134610073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1761112671001291025626861 660417251625484134610073)
                      ·
                        rfl

theorem cell23_1286158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 2, 1, 4, 2, 3].length) (baseStart_1286158 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1286158 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1286158 prefixEnd_1286158 := by exact prefixLift 1286158
  have htrace : WordTrace (prefixWord ++ tailWord_1286158) baseStart_1286158 baseEnd_1286158 := by
    simpa [prefixWord, tailWord_1286158, baseEnd_1286158] using wordTrace_append hprefix tailTrace_1286158
  have hstable : (prefixWord ++ tailWord_1286158).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1286158).length < 2 ^ (prefixWord ++ tailWord_1286158).sum := by decide
  have hdescent : baseEnd_1286158 < baseStart_1286158 := by decide
  rcases family_descends (prefixWord ++ tailWord_1286158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1286165 : List Nat := [1, 3, 2, 1, 5, 1, 2, 1, 3, 4]
def baseStart_1286165 : Nat := 118140960795 + 1286165 * 2 ^ 59
def prefixEnd_1286165 : Nat := 4983230072969 + 3 ^ 40 * 1286165 * 2
def baseEnd_1286165 : Nat := 220140281996688535740847

theorem tailTrace_1286165 : CollatzResearch.WordTrace tailWord_1286165 prefixEnd_1286165 220140281996688535740847 := by
  unfold tailWord_1286165
  simp only [CollatzResearch.WordTrace]
  refine ⟨46910291385451339339123949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31273527590300892892749299 46910291385451339339123949)
  ·
    refine ⟨17591359269544252252171481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46910291385451339339123949 17591359269544252252171481)
    ·
      refine ⟨13193519452158189189128611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17591359269544252252171481 13193519452158189189128611)
      ·
        refine ⟨19790279178237283783692917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13193519452158189189128611 19790279178237283783692917)
        ·
          refine ⟨1855338672959745354721211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 19790279178237283783692917 1855338672959745354721211)
          ·
            refine ⟨2783008009439618032081817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1855338672959745354721211 2783008009439618032081817)
            ·
              refine ⟨2087256007079713524061363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2783008009439618032081817 2087256007079713524061363)
              ·
                refine ⟨3130884010619570286092045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2087256007079713524061363 3130884010619570286092045)
                ·
                  refine ⟨1174081503982338857284517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3130884010619570286092045 1174081503982338857284517)
                  ·
                    refine ⟨220140281996688535740847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1174081503982338857284517 220140281996688535740847)
                    ·
                      rfl

theorem cell23_1286165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 2, 1, 3, 4].length) (baseStart_1286165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1286165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1286165 prefixEnd_1286165 := by exact prefixLift 1286165
  have htrace : WordTrace (prefixWord ++ tailWord_1286165) baseStart_1286165 baseEnd_1286165 := by
    simpa [prefixWord, tailWord_1286165, baseEnd_1286165] using wordTrace_append hprefix tailTrace_1286165
  have hstable : (prefixWord ++ tailWord_1286165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1286165).length < 2 ^ (prefixWord ++ tailWord_1286165).sum := by decide
  have hdescent : baseEnd_1286165 < baseStart_1286165 := by decide
  rcases family_descends (prefixWord ++ tailWord_1286165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1286188 : List Nat := [2, 2, 1, 1, 1, 2, 2, 3, 5, 1, 3]
def baseStart_1286188 : Nat := 118140960795 + 1286188 * 2 ^ 59
def prefixEnd_1286188 : Nat := 4983230072969 + 3 ^ 40 * 1286188 * 2
def baseEnd_1286188 : Nat := 660432656045119017234935

theorem tailTrace_1286188 : CollatzResearch.WordTrace tailWord_1286188 prefixEnd_1286188 660432656045119017234935 := by
  unfold tailWord_1286188
  simp only [CollatzResearch.WordTrace]
  refine ⟨23455565132184007133605609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31274086842912009511474145 23455565132184007133605609)
  ·
    refine ⟨17591673849138005350204207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23455565132184007133605609 17591673849138005350204207)
    ·
      refine ⟨26387510773707008025306311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17591673849138005350204207 26387510773707008025306311)
      ·
        refine ⟨39581266160560512037959467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26387510773707008025306311 39581266160560512037959467)
        ·
          refine ⟨59371899240840768056939201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39581266160560512037959467 59371899240840768056939201)
          ·
            refine ⟨44528924430630576042704401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59371899240840768056939201 44528924430630576042704401)
            ·
              refine ⟨33396693322972932032028301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44528924430630576042704401 33396693322972932032028301)
              ·
                refine ⟨12523759996114849512010613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33396693322972932032028301 12523759996114849512010613)
                ·
                  refine ⟨1174102499635767141750995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 12523759996114849512010613 1174102499635767141750995)
                  ·
                    refine ⟨1761153749453650712626493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1174102499635767141750995 1761153749453650712626493)
                    ·
                      refine ⟨660432656045119017234935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1761153749453650712626493 660432656045119017234935)
                      ·
                        rfl

theorem cell23_1286188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 5, 1, 3].length) (baseStart_1286188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1286188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1286188 prefixEnd_1286188 := by exact prefixLift 1286188
  have htrace : WordTrace (prefixWord ++ tailWord_1286188) baseStart_1286188 baseEnd_1286188 := by
    simpa [prefixWord, tailWord_1286188, baseEnd_1286188] using wordTrace_append hprefix tailTrace_1286188
  have hstable : (prefixWord ++ tailWord_1286188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1286188).length < 2 ^ (prefixWord ++ tailWord_1286188).sum := by decide
  have hdescent : baseEnd_1286188 < baseStart_1286188 := by decide
  rcases family_descends (prefixWord ++ tailWord_1286188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1286208 : List Nat := [2, 1, 1, 2, 2, 4, 2, 3, 1, 5]
def baseStart_1286208 : Nat := 118140960795 + 1286208 * 2 ^ 59
def prefixEnd_1286208 : Nat := 4983230072969 + 3 ^ 40 * 1286208 * 2
def baseEnd_1286208 : Nat := 220147641886069646328281

theorem tailTrace_1286208 : CollatzResearch.WordTrace tailWord_1286208 prefixEnd_1286208 220147641886069646328281 := by
  unfold tailWord_1286208
  simp only [CollatzResearch.WordTrace]
  refine ⟨23455929862147778841469639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31274573149530371788626185 23455929862147778841469639)
  ·
    refine ⟨35183894793221668262204459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23455929862147778841469639 35183894793221668262204459)
    ·
      refine ⟨52775842189832502393306689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35183894793221668262204459 52775842189832502393306689)
      ·
        refine ⟨39581881642374376794980017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52775842189832502393306689 39581881642374376794980017)
        ·
          refine ⟨29686411231780782596235013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39581881642374376794980017 29686411231780782596235013)
          ·
            refine ⟨5566202105958896736794065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 29686411231780782596235013 5566202105958896736794065)
            ·
              refine ⟨4174651579469172552595549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5566202105958896736794065 4174651579469172552595549)
              ·
                refine ⟨1565494342300939707223331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4174651579469172552595549 1565494342300939707223331)
                ·
                  refine ⟨2348241513451409560834997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1565494342300939707223331 2348241513451409560834997)
                  ·
                    refine ⟨220147641886069646328281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2348241513451409560834997 220147641886069646328281)
                    ·
                      rfl

theorem cell23_1286208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 2, 3, 1, 5].length) (baseStart_1286208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1286208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1286208 prefixEnd_1286208 := by exact prefixLift 1286208
  have htrace : WordTrace (prefixWord ++ tailWord_1286208) baseStart_1286208 baseEnd_1286208 := by
    simpa [prefixWord, tailWord_1286208, baseEnd_1286208] using wordTrace_append hprefix tailTrace_1286208
  have hstable : (prefixWord ++ tailWord_1286208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1286208).length < 2 ^ (prefixWord ++ tailWord_1286208).sum := by decide
  have hdescent : baseEnd_1286208 < baseStart_1286208 := by decide
  rcases family_descends (prefixWord ++ tailWord_1286208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1286215 : List Nat := [1, 1, 4, 1, 3, 1, 3, 2, 2, 3, 2]
def baseStart_1286215 : Nat := 118140960795 + 1286215 * 2 ^ 59
def prefixEnd_1286215 : Nat := 4983230072969 + 3 ^ 40 * 1286215 * 2
def baseEnd_1286215 : Nat := 660446520022790411597311

theorem tailTrace_1286215 : CollatzResearch.WordTrace tailWord_1286215 prefixEnd_1286215 660446520022790411597311 := by
  unfold tailWord_1286215
  simp only [CollatzResearch.WordTrace]
  refine ⟨46912115035270197878444099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31274743356846798585629399 46912115035270197878444099)
  ·
    refine ⟨70368172552905296817666149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46912115035270197878444099 70368172552905296817666149)
    ·
      refine ⟨13194032353669743153312403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 70368172552905296817666149 13194032353669743153312403)
      ·
        refine ⟨19791048530504614729968605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13194032353669743153312403 19791048530504614729968605)
        ·
          refine ⟨7421643198939230523738227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19791048530504614729968605 7421643198939230523738227)
          ·
            refine ⟨11132464798408845785607341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7421643198939230523738227 11132464798408845785607341)
            ·
              refine ⟨4174674299403317169602753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11132464798408845785607341 4174674299403317169602753)
              ·
                refine ⟨3131005724552487877202065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4174674299403317169602753 3131005724552487877202065)
                ·
                  refine ⟨2348254293414365907901549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3131005724552487877202065 2348254293414365907901549)
                  ·
                    refine ⟨880595360030387215463081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2348254293414365907901549 880595360030387215463081)
                    ·
                      refine ⟨660446520022790411597311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 880595360030387215463081 660446520022790411597311)
                      ·
                        rfl

theorem cell23_1286215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 3, 2, 2, 3, 2].length) (baseStart_1286215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1286215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1286215 prefixEnd_1286215 := by exact prefixLift 1286215
  have htrace : WordTrace (prefixWord ++ tailWord_1286215) baseStart_1286215 baseEnd_1286215 := by
    simpa [prefixWord, tailWord_1286215, baseEnd_1286215] using wordTrace_append hprefix tailTrace_1286215
  have hstable : (prefixWord ++ tailWord_1286215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1286215).length < 2 ^ (prefixWord ++ tailWord_1286215).sum := by decide
  have hdescent : baseEnd_1286215 < baseStart_1286215 := by decide
  rcases family_descends (prefixWord ++ tailWord_1286215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1286222 : List Nat := [4, 1, 1, 1, 1, 6, 1, 1, 3, 1, 3]
def baseStart_1286222 : Nat := 118140960795 + 1286222 * 2 ^ 59
def prefixEnd_1286222 : Nat := 4983230072969 + 3 ^ 40 * 1286222 * 2
def baseEnd_1286222 : Nat := 660450114387371884209779

theorem tailTrace_1286222 : CollatzResearch.WordTrace tailWord_1286222 prefixEnd_1286222 660450114387371884209779 := by
  unfold tailWord_1286222
  simp only [CollatzResearch.WordTrace]
  refine ⟨5864046293280604759243615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 31274913564163225382632613 5864046293280604759243615)
  ·
    refine ⟨8796069439920907138865423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5864046293280604759243615 8796069439920907138865423)
    ·
      refine ⟨13194104159881360708298135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8796069439920907138865423 13194104159881360708298135)
      ·
        refine ⟨19791156239822041062447203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13194104159881360708298135 19791156239822041062447203)
        ·
          refine ⟨29686734359733061593670805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19791156239822041062447203 29686734359733061593670805)
          ·
            refine ⟨1391565673112487262203319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 29686734359733061593670805 1391565673112487262203319)
            ·
              refine ⟨2087348509668730893304979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1391565673112487262203319 2087348509668730893304979)
              ·
                refine ⟨3131022764503096339957469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2087348509668730893304979 3131022764503096339957469)
                ·
                  refine ⟨1174133536688661127484051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3131022764503096339957469 1174133536688661127484051)
                  ·
                    refine ⟨1761200305032991691226077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1174133536688661127484051 1761200305032991691226077)
                    ·
                      refine ⟨660450114387371884209779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1761200305032991691226077 660450114387371884209779)
                      ·
                        rfl

theorem cell23_1286222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 6, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 6, 1, 1, 3, 1, 3].length) (baseStart_1286222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1286222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1286222 prefixEnd_1286222 := by exact prefixLift 1286222
  have htrace : WordTrace (prefixWord ++ tailWord_1286222) baseStart_1286222 baseEnd_1286222 := by
    simpa [prefixWord, tailWord_1286222, baseEnd_1286222] using wordTrace_append hprefix tailTrace_1286222
  have hstable : (prefixWord ++ tailWord_1286222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1286222).length < 2 ^ (prefixWord ++ tailWord_1286222).sum := by decide
  have hdescent : baseEnd_1286222 < baseStart_1286222 := by decide
  rcases family_descends (prefixWord ++ tailWord_1286222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1286228 : List Nat := [2, 4, 1, 1, 1, 1, 1, 4, 3, 1, 4]
def baseStart_1286228 : Nat := 118140960795 + 1286228 * 2 ^ 59
def prefixEnd_1286228 : Nat := 4983230072969 + 3 ^ 40 * 1286228 * 2
def baseEnd_1286228 : Nat := 660453195271298860734751

theorem tailTrace_1286228 : CollatzResearch.WordTrace tailWord_1286228 prefixEnd_1286228 660453195271298860734751 := by
  unfold tailWord_1286228
  simp only [CollatzResearch.WordTrace]
  refine ⟨23456294592111550549333669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31275059456148734065778225 23456294592111550549333669)
  ·
    refine ⟨4398055236020915728000063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23456294592111550549333669 4398055236020915728000063)
    ·
      refine ⟨6597082854031373592000095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4398055236020915728000063 6597082854031373592000095)
      ·
        refine ⟨9895624281047060388000143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6597082854031373592000095 9895624281047060388000143)
        ·
          refine ⟨14843436421570590582000215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9895624281047060388000143 14843436421570590582000215)
          ·
            refine ⟨22265154632355885873000323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14843436421570590582000215 22265154632355885873000323)
            ·
              refine ⟨33397731948533828809500485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22265154632355885873000323 33397731948533828809500485)
              ·
                refine ⟨6262074740350092901781341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 33397731948533828809500485 6262074740350092901781341)
                ·
                  refine ⟨2348278027631284838168003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6262074740350092901781341 2348278027631284838168003)
                  ·
                    refine ⟨3522417041446927257252005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2348278027631284838168003 3522417041446927257252005)
                    ·
                      refine ⟨660453195271298860734751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3522417041446927257252005 660453195271298860734751)
                      ·
                        rfl

theorem cell23_1286228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 4, 3, 1, 4].length) (baseStart_1286228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1286228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1286228 prefixEnd_1286228 := by exact prefixLift 1286228
  have htrace : WordTrace (prefixWord ++ tailWord_1286228) baseStart_1286228 baseEnd_1286228 := by
    simpa [prefixWord, tailWord_1286228, baseEnd_1286228] using wordTrace_append hprefix tailTrace_1286228
  have hstable : (prefixWord ++ tailWord_1286228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1286228).length < 2 ^ (prefixWord ++ tailWord_1286228).sum := by decide
  have hdescent : baseEnd_1286228 < baseStart_1286228 := by decide
  rcases family_descends (prefixWord ++ tailWord_1286228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1286245 : List Nat := [1, 3, 1, 3, 2, 2, 3, 2, 1, 1, 4]
def baseStart_1286245 : Nat := 118140960795 + 1286245 * 2 ^ 59
def prefixEnd_1286245 : Nat := 4983230072969 + 3 ^ 40 * 1286245 * 2
def baseEnd_1286245 : Nat := 660461924442425294222173

theorem tailTrace_1286245 : CollatzResearch.WordTrace tailWord_1286245 prefixEnd_1286245 660461924442425294222173 := by
  unfold tailWord_1286245
  simp only [CollatzResearch.WordTrace]
  refine ⟨46913209225161513002036189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31275472816774342001357459 46913209225161513002036189)
  ·
    refine ⟨17592453459435567375763571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46913209225161513002036189 17592453459435567375763571)
    ·
      refine ⟨26388680189153351063645357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17592453459435567375763571 26388680189153351063645357)
      ·
        refine ⟨9895755070932506648867009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26388680189153351063645357 9895755070932506648867009)
        ·
          refine ⟨7421816303199379986650257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9895755070932506648867009 7421816303199379986650257)
          ·
            refine ⟨5566362227399534989987693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7421816303199379986650257 5566362227399534989987693)
            ·
              refine ⟨2087385835274825621245385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5566362227399534989987693 2087385835274825621245385)
              ·
                refine ⟨1565539376456119215934039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2087385835274825621245385 1565539376456119215934039)
                ·
                  refine ⟨2348309064684178823901059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1565539376456119215934039 2348309064684178823901059)
                  ·
                    refine ⟨3522463597026268235851589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2348309064684178823901059 3522463597026268235851589)
                    ·
                      refine ⟨660461924442425294222173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3522463597026268235851589 660461924442425294222173)
                      ·
                        rfl

theorem cell23_1286245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 3, 2, 1, 1, 4].length) (baseStart_1286245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1286245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1286245 prefixEnd_1286245 := by exact prefixLift 1286245
  have htrace : WordTrace (prefixWord ++ tailWord_1286245) baseStart_1286245 baseEnd_1286245 := by
    simpa [prefixWord, tailWord_1286245, baseEnd_1286245] using wordTrace_append hprefix tailTrace_1286245
  have hstable : (prefixWord ++ tailWord_1286245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1286245).length < 2 ^ (prefixWord ++ tailWord_1286245).sum := by decide
  have hdescent : baseEnd_1286245 < baseStart_1286245 := by decide
  rcases family_descends (prefixWord ++ tailWord_1286245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1286258 : List Nat := [3, 2, 1, 2, 2, 2, 1, 1, 3, 2, 4]
def baseStart_1286258 : Nat := 118140960795 + 1286258 * 2 ^ 59
def prefixEnd_1286258 : Nat := 4983230072969 + 3 ^ 40 * 1286258 * 2
def baseEnd_1286258 : Nat := 660468599690933743359613

theorem tailTrace_1286258 : CollatzResearch.WordTrace tailWord_1286258 prefixEnd_1286258 660468599690933743359613 := by
  unfold tailWord_1286258
  simp only [CollatzResearch.WordTrace]
  refine ⟨11728420843528604055564857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31275788916076277481506285 11728420843528604055564857)
  ·
    refine ⟨8796315632646453041673643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11728420843528604055564857 8796315632646453041673643)
    ·
      refine ⟨13194473448969679562510465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8796315632646453041673643 13194473448969679562510465)
      ·
        refine ⟨9895855086727259671882849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13194473448969679562510465 9895855086727259671882849)
        ·
          refine ⟨7421891315045444753912137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9895855086727259671882849 7421891315045444753912137)
          ·
            refine ⟨5566418486284083565434103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7421891315045444753912137 5566418486284083565434103)
            ·
              refine ⟨8349627729426125348151155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5566418486284083565434103 8349627729426125348151155)
              ·
                refine ⟨12524441594139188022226733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8349627729426125348151155 12524441594139188022226733)
                ·
                  refine ⟨4696665597802195508335025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12524441594139188022226733 4696665597802195508335025)
                  ·
                    refine ⟨3522499198351646631251269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4696665597802195508335025 3522499198351646631251269)
                    ·
                      refine ⟨660468599690933743359613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3522499198351646631251269 660468599690933743359613)
                      ·
                        rfl

theorem cell23_1286258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 1, 1, 3, 2, 4].length) (baseStart_1286258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1286258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1286258 prefixEnd_1286258 := by exact prefixLift 1286258
  have htrace : WordTrace (prefixWord ++ tailWord_1286258) baseStart_1286258 baseEnd_1286258 := by
    simpa [prefixWord, tailWord_1286258, baseEnd_1286258] using wordTrace_append hprefix tailTrace_1286258
  have hstable : (prefixWord ++ tailWord_1286258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1286258).length < 2 ^ (prefixWord ++ tailWord_1286258).sum := by decide
  have hdescent : baseEnd_1286258 < baseStart_1286258 := by decide
  rcases family_descends (prefixWord ++ tailWord_1286258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1286265 : List Nat := [1, 2, 1, 3, 4, 3, 1, 1, 1, 1, 5]
def baseStart_1286265 : Nat := 118140960795 + 1286265 * 2 ^ 59
def prefixEnd_1286265 : Nat := 4983230072969 + 3 ^ 40 * 1286265 * 2
def baseEnd_1286265 : Nat := 660472194055515215972081

theorem tailTrace_1286265 : CollatzResearch.WordTrace tailWord_1286265 prefixEnd_1286265 660472194055515215972081 := by
  unfold tailWord_1286265
  simp only [CollatzResearch.WordTrace]
  refine ⟨46913938685089056417764249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31275959123392704278509499 46913938685089056417764249)
  ·
    refine ⟨35185454013816792313323187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46913938685089056417764249 35185454013816792313323187)
    ·
      refine ⟨52778181020725188469984781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35185454013816792313323187 52778181020725188469984781)
      ·
        refine ⟨19791817882771945676244293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52778181020725188469984781 19791817882771945676244293)
        ·
          refine ⟨3710965853019739814295805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19791817882771945676244293 3710965853019739814295805)
          ·
            refine ⟨1391612194882402430360927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3710965853019739814295805 1391612194882402430360927)
            ·
              refine ⟨2087418292323603645541391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1391612194882402430360927 2087418292323603645541391)
              ·
                refine ⟨3131127438485405468312087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2087418292323603645541391 3131127438485405468312087)
                ·
                  refine ⟨4696691157728108202468131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3131127438485405468312087 4696691157728108202468131)
                  ·
                    refine ⟨7045036736592162303702197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4696691157728108202468131 7045036736592162303702197)
                    ·
                      refine ⟨660472194055515215972081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7045036736592162303702197 660472194055515215972081)
                      ·
                        rfl

theorem cell23_1286265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 3, 1, 1, 1, 1, 5].length) (baseStart_1286265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1286265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1286265 prefixEnd_1286265 := by exact prefixLift 1286265
  have htrace : WordTrace (prefixWord ++ tailWord_1286265) baseStart_1286265 baseEnd_1286265 := by
    simpa [prefixWord, tailWord_1286265, baseEnd_1286265] using wordTrace_append hprefix tailTrace_1286265
  have hstable : (prefixWord ++ tailWord_1286265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1286265).length < 2 ^ (prefixWord ++ tailWord_1286265).sum := by decide
  have hdescent : baseEnd_1286265 < baseStart_1286265 := by decide
  rcases family_descends (prefixWord ++ tailWord_1286265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1286273 : List Nat := [1, 2, 4, 2, 4, 1, 2, 2, 1, 1, 3]
def baseStart_1286273 : Nat := 118140960795 + 1286273 * 2 ^ 59
def prefixEnd_1286273 : Nat := 4983230072969 + 3 ^ 40 * 1286273 * 2
def baseEnd_1286273 : Nat := 660476301900751184672045

theorem tailTrace_1286273 : CollatzResearch.WordTrace tailWord_1286273 prefixEnd_1286273 660476301900751184672045 := by
  unfold tailWord_1286273
  simp only [CollatzResearch.WordTrace]
  refine ⟨46914230469060073784055473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31276153646040049189370315 46914230469060073784055473)
  ·
    refine ⟨35185672851795055338041605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46914230469060073784055473 35185672851795055338041605)
    ·
      refine ⟨6597313659711572875882801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 35185672851795055338041605 6597313659711572875882801)
      ·
        refine ⟨4947985244783679656912101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6597313659711572875882801 4947985244783679656912101)
        ·
          refine ⟨927747233396939935671019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4947985244783679656912101 927747233396939935671019)
          ·
            refine ⟨1391620850095409903506529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 927747233396939935671019 1391620850095409903506529)
            ·
              refine ⟨1043715637571557427629897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1391620850095409903506529 1043715637571557427629897)
              ·
                refine ⟨782786728178668070722423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1043715637571557427629897 782786728178668070722423)
                ·
                  refine ⟨1174180092268002106083635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 782786728178668070722423 1174180092268002106083635)
                  ·
                    refine ⟨1761270138402003159125453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1174180092268002106083635 1761270138402003159125453)
                    ·
                      refine ⟨660476301900751184672045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1761270138402003159125453 660476301900751184672045)
                      ·
                        rfl

theorem cell23_1286273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 4, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 4, 1, 2, 2, 1, 1, 3].length) (baseStart_1286273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1286273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1286273 prefixEnd_1286273 := by exact prefixLift 1286273
  have htrace : WordTrace (prefixWord ++ tailWord_1286273) baseStart_1286273 baseEnd_1286273 := by
    simpa [prefixWord, tailWord_1286273, baseEnd_1286273] using wordTrace_append hprefix tailTrace_1286273
  have hstable : (prefixWord ++ tailWord_1286273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1286273).length < 2 ^ (prefixWord ++ tailWord_1286273).sum := by decide
  have hdescent : baseEnd_1286273 < baseStart_1286273 := by decide
  rcases family_descends (prefixWord ++ tailWord_1286273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1286281 : List Nat := [1, 2, 1, 1, 4, 2, 1, 1, 1, 9]
def baseStart_1286281 : Nat := 118140960795 + 1286281 * 2 ^ 59
def prefixEnd_1286281 : Nat := 4983230072969 + 3 ^ 40 * 1286281 * 2
def baseEnd_1286281 : Nat := 220160136581995717790669

theorem tailTrace_1286281 : CollatzResearch.WordTrace tailWord_1286281 prefixEnd_1286281 220160136581995717790669 := by
  unfold tailWord_1286281
  simp only [CollatzResearch.WordTrace]
  refine ⟨46914522253031091150346697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31276348168687394100231131 46914522253031091150346697)
  ·
    refine ⟨35185891689773318362760023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46914522253031091150346697 35185891689773318362760023)
    ·
      refine ⟨52778837534659977544140035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35185891689773318362760023 52778837534659977544140035)
      ·
        refine ⟨79168256301989966316210053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52778837534659977544140035 79168256301989966316210053)
        ·
          refine ⟨14844048056623118684289385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 79168256301989966316210053 14844048056623118684289385)
          ·
            refine ⟨11133036042467339013217039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14844048056623118684289385 11133036042467339013217039)
            ·
              refine ⟨16699554063701008519825559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11133036042467339013217039 16699554063701008519825559)
              ·
                refine ⟨25049331095551512779738339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16699554063701008519825559 25049331095551512779738339)
                ·
                  refine ⟨37573996643327269169607509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25049331095551512779738339 37573996643327269169607509)
                  ·
                    refine ⟨220160136581995717790669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 37573996643327269169607509 220160136581995717790669)
                    ·
                      rfl

theorem cell23_1286281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 1, 1, 9].length) (baseStart_1286281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1286281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1286281 prefixEnd_1286281 := by exact prefixLift 1286281
  have htrace : WordTrace (prefixWord ++ tailWord_1286281) baseStart_1286281 baseEnd_1286281 := by
    simpa [prefixWord, tailWord_1286281, baseEnd_1286281] using wordTrace_append hprefix tailTrace_1286281
  have hstable : (prefixWord ++ tailWord_1286281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1286281).length < 2 ^ (prefixWord ++ tailWord_1286281).sum := by decide
  have hdescent : baseEnd_1286281 < baseStart_1286281 := by decide
  rcases family_descends (prefixWord ++ tailWord_1286281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1286291 : List Nat := [1, 1, 1, 2, 1, 2, 3, 2, 1, 4, 5]
def baseStart_1286291 : Nat := 118140960795 + 1286291 * 2 ^ 59
def prefixEnd_1286291 : Nat := 4983230072969 + 3 ^ 40 * 1286291 * 2
def baseEnd_1286291 : Nat := 660485544552532114246961

theorem tailTrace_1286291 : CollatzResearch.WordTrace tailWord_1286291 prefixEnd_1286291 660485544552532114246961 := by
  unfold tailWord_1286291
  simp only [CollatzResearch.WordTrace]
  refine ⟨46914886982994862858210727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31276591321996575238807151 46914886982994862858210727)
  ·
    refine ⟨70372330474492294287316091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46914886982994862858210727 70372330474492294287316091)
    ·
      refine ⟨105558495711738441430974137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70372330474492294287316091 105558495711738441430974137)
      ·
        refine ⟨79168871783803831073230603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 105558495711738441430974137 79168871783803831073230603)
        ·
          refine ⟨118753307675705746609845905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79168871783803831073230603 118753307675705746609845905)
          ·
            refine ⟨89064980756779309957384429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 118753307675705746609845905 89064980756779309957384429)
            ·
              refine ⟨33399367783792241234019161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 89064980756779309957384429 33399367783792241234019161)
              ·
                refine ⟨25049525837844180925514371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33399367783792241234019161 25049525837844180925514371)
                ·
                  refine ⟨37574288756766271388271557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25049525837844180925514371 37574288756766271388271557)
                  ·
                    refine ⟨7045179141893675885300917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 37574288756766271388271557 7045179141893675885300917)
                    ·
                      refine ⟨660485544552532114246961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7045179141893675885300917 660485544552532114246961)
                      ·
                        rfl

theorem cell23_1286291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 2, 1, 4, 5].length) (baseStart_1286291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1286291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1286291 prefixEnd_1286291 := by exact prefixLift 1286291
  have htrace : WordTrace (prefixWord ++ tailWord_1286291) baseStart_1286291 baseEnd_1286291 := by
    simpa [prefixWord, tailWord_1286291, baseEnd_1286291] using wordTrace_append hprefix tailTrace_1286291
  have hstable : (prefixWord ++ tailWord_1286291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1286291).length < 2 ^ (prefixWord ++ tailWord_1286291).sum := by decide
  have hdescent : baseEnd_1286291 < baseStart_1286291 := by decide
  rcases family_descends (prefixWord ++ tailWord_1286291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1286302 : List Nat := [4, 3, 1, 1, 3, 1, 3, 7]
def baseStart_1286302 : Nat := 118140960795 + 1286302 * 2 ^ 59
def prefixEnd_1286302 : Nat := 4983230072969 + 3 ^ 40 * 1286302 * 2
def baseEnd_1286302 : Nat := 24462636771841910044793

theorem tailTrace_1286302 : CollatzResearch.WordTrace tailWord_1286302 prefixEnd_1286302 24462636771841910044793 := by
  unfold tailWord_1286302
  simp only [CollatzResearch.WordTrace]
  refine ⟨5864411023244376467107645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 31276858790636674491240773 5864411023244376467107645)
  ·
    refine ⟨2199154133716641175165367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5864411023244376467107645 2199154133716641175165367)
    ·
      refine ⟨3298731200574961762748051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2199154133716641175165367 3298731200574961762748051)
      ·
        refine ⟨4948096800862442644122077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3298731200574961762748051 4948096800862442644122077)
        ·
          refine ⟨1855536300323415991545779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4948096800862442644122077 1855536300323415991545779)
          ·
            refine ⟨2783304450485123987318669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1855536300323415991545779 2783304450485123987318669)
            ·
              refine ⟨1043739168931921495244501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2783304450485123987318669 1043739168931921495244501)
              ·
                refine ⟨24462636771841910044793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1043739168931921495244501 24462636771841910044793)
                ·
                  rfl

theorem cell23_1286302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 3, 7].length) (baseStart_1286302 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1286302 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1286302 prefixEnd_1286302 := by exact prefixLift 1286302
  have htrace : WordTrace (prefixWord ++ tailWord_1286302) baseStart_1286302 baseEnd_1286302 := by
    simpa [prefixWord, tailWord_1286302, baseEnd_1286302] using wordTrace_append hprefix tailTrace_1286302
  have hstable : (prefixWord ++ tailWord_1286302).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1286302).length < 2 ^ (prefixWord ++ tailWord_1286302).sum := by decide
  have hdescent : baseEnd_1286302 < baseStart_1286302 := by decide
  rcases family_descends (prefixWord ++ tailWord_1286302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1286322 : List Nat := [3, 2, 1, 1, 1, 3, 3, 3, 1, 3, 2]
def baseStart_1286322 : Nat := 118140960795 + 1286322 * 2 ^ 59
def prefixEnd_1286322 : Nat := 4983230072969 + 3 ^ 40 * 1286322 * 2
def baseEnd_1286322 : Nat := 660501462452821492959319

theorem tailTrace_1286322 : CollatzResearch.WordTrace tailWord_1286322 prefixEnd_1286322 660501462452821492959319 := by
  unfold tailWord_1286322
  simp only [CollatzResearch.WordTrace]
  refine ⟨11729004411470638788147305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31277345097255036768392813 11729004411470638788147305)
  ·
    refine ⟨8796753308602979091110479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11729004411470638788147305 8796753308602979091110479)
    ·
      refine ⟨13195129962904468636665719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8796753308602979091110479 13195129962904468636665719)
      ·
        refine ⟨19792694944356702954998579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13195129962904468636665719 19792694944356702954998579)
        ·
          refine ⟨29689042416535054432497869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19792694944356702954998579 29689042416535054432497869)
          ·
            refine ⟨11133390906200645412186701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29689042416535054432497869 11133390906200645412186701)
            ·
              refine ⟨4175021589825242029570013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11133390906200645412186701 4175021589825242029570013)
              ·
                refine ⟨1565633096184465761088755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4175021589825242029570013 1565633096184465761088755)
                ·
                  refine ⟨2348449644276698641633133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1565633096184465761088755 2348449644276698641633133)
                  ·
                    refine ⟨880668616603761990612425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2348449644276698641633133 880668616603761990612425)
                    ·
                      refine ⟨660501462452821492959319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 880668616603761990612425 660501462452821492959319)
                      ·
                        rfl

theorem cell23_1286322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 3, 3, 1, 3, 2].length) (baseStart_1286322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1286322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1286322 prefixEnd_1286322 := by exact prefixLift 1286322
  have htrace : WordTrace (prefixWord ++ tailWord_1286322) baseStart_1286322 baseEnd_1286322 := by
    simpa [prefixWord, tailWord_1286322, baseEnd_1286322] using wordTrace_append hprefix tailTrace_1286322
  have hstable : (prefixWord ++ tailWord_1286322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1286322).length < 2 ^ (prefixWord ++ tailWord_1286322).sum := by decide
  have hdescent : baseEnd_1286322 < baseStart_1286322 := by decide
  rcases family_descends (prefixWord ++ tailWord_1286322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1286509 : List Nat := [1, 5, 1, 1, 1, 2, 4, 1, 3, 1, 3]
def baseStart_1286509 : Nat := 118140960795 + 1286509 * 2 ^ 59
def prefixEnd_1286509 : Nat := 4983230072969 + 3 ^ 40 * 1286509 * 2
def baseEnd_1286509 : Nat := 660597483335212261320959

theorem tailTrace_1286509 : CollatzResearch.WordTrace tailWord_1286509 prefixEnd_1286509 660597483335212261320959 := by
  unfold tailWord_1286509
  simp only [CollatzResearch.WordTrace]
  refine ⟨46922838096205086089646581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31281892064136724059764387 46922838096205086089646581)
  ·
    refine ⟨4399016071519226820904367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 46922838096205086089646581 4399016071519226820904367)
    ·
      refine ⟨6598524107278840231356551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4399016071519226820904367 6598524107278840231356551)
      ·
        refine ⟨9897786160918260347034827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6598524107278840231356551 9897786160918260347034827)
        ·
          refine ⟨14846679241377390520552241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9897786160918260347034827 14846679241377390520552241)
          ·
            refine ⟨11135009431033042890414181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14846679241377390520552241 11135009431033042890414181)
            ·
              refine ⟨2087814268318695541952659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11135009431033042890414181 2087814268318695541952659)
              ·
                refine ⟨3131721402478043312928989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2087814268318695541952659 3131721402478043312928989)
                ·
                  refine ⟨1174395525929266242348371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3131721402478043312928989 1174395525929266242348371)
                  ·
                    refine ⟨1761593288893899363522557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1174395525929266242348371 1761593288893899363522557)
                    ·
                      refine ⟨660597483335212261320959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1761593288893899363522557 660597483335212261320959)
                      ·
                        rfl

theorem cell23_1286509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 4, 1, 3, 1, 3].length) (baseStart_1286509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1286509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1286509 prefixEnd_1286509 := by exact prefixLift 1286509
  have htrace : WordTrace (prefixWord ++ tailWord_1286509) baseStart_1286509 baseEnd_1286509 := by
    simpa [prefixWord, tailWord_1286509, baseEnd_1286509] using wordTrace_append hprefix tailTrace_1286509
  have hstable : (prefixWord ++ tailWord_1286509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1286509).length < 2 ^ (prefixWord ++ tailWord_1286509).sum := by decide
  have hdescent : baseEnd_1286509 < baseStart_1286509 := by decide
  rcases family_descends (prefixWord ++ tailWord_1286509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1286529 : List Nat := [1, 2, 4, 3, 1, 2, 2, 2, 1, 5]
def baseStart_1286529 : Nat := 118140960795 + 1286529 * 2 ^ 59
def prefixEnd_1286529 : Nat := 4983230072969 + 3 ^ 40 * 1286529 * 2
def baseEnd_1286529 : Nat := 220202584316100727690289

theorem tailTrace_1286529 : CollatzResearch.WordTrace tailWord_1286529 prefixEnd_1286529 220202584316100727690289 := by
  unfold tailWord_1286529
  simp only [CollatzResearch.WordTrace]
  refine ⟨46923567556132629505374641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31282378370755086336916427 46923567556132629505374641)
  ·
    refine ⟨35192675667099472129030981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46923567556132629505374641 35192675667099472129030981)
    ·
      refine ⟨6598626687581151024193309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 35192675667099472129030981 6598626687581151024193309)
      ·
        refine ⟨2474485007842931634072491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6598626687581151024193309 2474485007842931634072491)
        ·
          refine ⟨3711727511764397451108737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2474485007842931634072491 3711727511764397451108737)
          ·
            refine ⟨2783795633823298088331553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3711727511764397451108737 2783795633823298088331553)
            ·
              refine ⟨2087846725367473566248665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2783795633823298088331553 2087846725367473566248665)
              ·
                refine ⟨1565885044025605174686499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2087846725367473566248665 1565885044025605174686499)
                ·
                  refine ⟨2348827566038407762029749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1565885044025605174686499 2348827566038407762029749)
                  ·
                    refine ⟨220202584316100727690289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2348827566038407762029749 220202584316100727690289)
                    ·
                      rfl

theorem cell23_1286529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 2, 2, 1, 5].length) (baseStart_1286529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1286529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1286529 prefixEnd_1286529 := by exact prefixLift 1286529
  have htrace : WordTrace (prefixWord ++ tailWord_1286529) baseStart_1286529 baseEnd_1286529 := by
    simpa [prefixWord, tailWord_1286529, baseEnd_1286529] using wordTrace_append hprefix tailTrace_1286529
  have hstable : (prefixWord ++ tailWord_1286529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1286529).length < 2 ^ (prefixWord ++ tailWord_1286529).sum := by decide
  have hdescent : baseEnd_1286529 < baseStart_1286529 := by decide
  rcases family_descends (prefixWord ++ tailWord_1286529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1286532 : List Nat := [2, 3, 2, 1, 1, 2, 1, 1, 2, 6, 2]
def baseStart_1286532 : Nat := 118140960795 + 1286532 * 2 ^ 59
def prefixEnd_1286532 : Nat := 4983230072969 + 3 ^ 40 * 1286532 * 2
def baseEnd_1286532 : Nat := 660609293390265671333353

theorem tailTrace_1286532 : CollatzResearch.WordTrace tailWord_1286532 prefixEnd_1286532 660609293390265671333353 := by
  unfold tailWord_1286532
  simp only [CollatzResearch.WordTrace]
  refine ⟨23461838487560880508866925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31282451316747840678489233 23461838487560880508866925)
  ·
    refine ⟨8798189432835330190825097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23461838487560880508866925 8798189432835330190825097)
    ·
      refine ⟨6598642074626497643118823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8798189432835330190825097 6598642074626497643118823)
      ·
        refine ⟨9897963111939746464678235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6598642074626497643118823 9897963111939746464678235)
        ·
          refine ⟨14846944667909619697017353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9897963111939746464678235 14846944667909619697017353)
          ·
            refine ⟨11135208500932214772763015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14846944667909619697017353 11135208500932214772763015)
            ·
              refine ⟨16702812751398322159144523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11135208500932214772763015 16702812751398322159144523)
              ·
                refine ⟨25054219127097483238716785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16702812751398322159144523 25054219127097483238716785)
                ·
                  refine ⟨18790664345323112429037589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25054219127097483238716785 18790664345323112429037589)
                  ·
                    refine ⟨880812391187020895111137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18790664345323112429037589 880812391187020895111137)
                    ·
                      refine ⟨660609293390265671333353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 880812391187020895111137 660609293390265671333353)
                      ·
                        rfl

theorem cell23_1286532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 1, 2, 6, 2].length) (baseStart_1286532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1286532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1286532 prefixEnd_1286532 := by exact prefixLift 1286532
  have htrace : WordTrace (prefixWord ++ tailWord_1286532) baseStart_1286532 baseEnd_1286532 := by
    simpa [prefixWord, tailWord_1286532, baseEnd_1286532] using wordTrace_append hprefix tailTrace_1286532
  have hstable : (prefixWord ++ tailWord_1286532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1286532).length < 2 ^ (prefixWord ++ tailWord_1286532).sum := by decide
  have hdescent : baseEnd_1286532 < baseStart_1286532 := by decide
  rcases family_descends (prefixWord ++ tailWord_1286532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1286535 : List Nat := [1, 1, 4, 2, 2, 1, 1, 2, 3, 1, 5]
def baseStart_1286535 : Nat := 118140960795 + 1286535 * 2 ^ 59
def prefixEnd_1286535 : Nat := 4983230072969 + 3 ^ 40 * 1286535 * 2
def baseEnd_1286535 : Nat := 660610833832229159595839

theorem tailTrace_1286535 : CollatzResearch.WordTrace tailWord_1286535 prefixEnd_1286535 660610833832229159595839 := by
  unfold tailWord_1286535
  simp only [CollatzResearch.WordTrace]
  refine ⟨46923786394110892530093059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31282524262740595020062039 46923786394110892530093059)
  ·
    refine ⟨70385679591166338795139589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46923786394110892530093059 70385679591166338795139589)
    ·
      refine ⟨13197314923343688524088673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 70385679591166338795139589 13197314923343688524088673)
      ·
        refine ⟨9897986192507766393066505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13197314923343688524088673 9897986192507766393066505)
        ·
          refine ⟨7423489644380824794799879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9897986192507766393066505 7423489644380824794799879)
          ·
            refine ⟨11135234466571237192199819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7423489644380824794799879 11135234466571237192199819)
            ·
              refine ⟨16702851699856855788299729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11135234466571237192199819 16702851699856855788299729)
              ·
                refine ⟨12527138774892641841224797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16702851699856855788299729 12527138774892641841224797)
                ·
                  refine ⟨4697677040584740690459299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12527138774892641841224797 4697677040584740690459299)
                  ·
                    refine ⟨7046515560877111035688949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4697677040584740690459299 7046515560877111035688949)
                    ·
                      refine ⟨660610833832229159595839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7046515560877111035688949 660610833832229159595839)
                      ·
                        rfl

theorem cell23_1286535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 2, 3, 1, 5].length) (baseStart_1286535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1286535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1286535 prefixEnd_1286535 := by exact prefixLift 1286535
  have htrace : WordTrace (prefixWord ++ tailWord_1286535) baseStart_1286535 baseEnd_1286535 := by
    simpa [prefixWord, tailWord_1286535, baseEnd_1286535] using wordTrace_append hprefix tailTrace_1286535
  have hstable : (prefixWord ++ tailWord_1286535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1286535).length < 2 ^ (prefixWord ++ tailWord_1286535).sum := by decide
  have hdescent : baseEnd_1286535 < baseStart_1286535 := by decide
  rcases family_descends (prefixWord ++ tailWord_1286535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1286552 : List Nat := [2, 1, 2, 5, 1, 1, 1, 3, 1, 1, 5]
def baseStart_1286552 : Nat := 118140960795 + 1286552 * 2 ^ 59
def prefixEnd_1286552 : Nat := 4983230072969 + 3 ^ 40 * 1286552 * 2
def baseEnd_1286552 : Nat := 660619563003355593083261

theorem tailTrace_1286552 : CollatzResearch.WordTrace tailWord_1286552 prefixEnd_1286552 660619563003355593083261 := by
  unfold tailWord_1286552
  simp only [CollatzResearch.WordTrace]
  refine ⟨23462203217524652216730955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31282937623366202955641273 23462203217524652216730955)
  ·
    refine ⟨35193304826286978325096433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23462203217524652216730955 35193304826286978325096433)
    ·
      refine ⟨26394978619715233743822325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35193304826286978325096433 26394978619715233743822325)
      ·
        refine ⟨2474529245598303163483343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 26394978619715233743822325 2474529245598303163483343)
        ·
          refine ⟨3711793868397454745225015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2474529245598303163483343 3711793868397454745225015)
          ·
            refine ⟨5567690802596182117837523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3711793868397454745225015 5567690802596182117837523)
            ·
              refine ⟨8351536203894273176756285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5567690802596182117837523 8351536203894273176756285)
              ·
                refine ⟨3131826076460352441283607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8351536203894273176756285 3131826076460352441283607)
                ·
                  refine ⟨4697739114690528661925411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3131826076460352441283607 4697739114690528661925411)
                  ·
                    refine ⟨7046608672035792992888117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4697739114690528661925411 7046608672035792992888117)
                    ·
                      refine ⟨660619563003355593083261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7046608672035792992888117 660619563003355593083261)
                      ·
                        rfl

theorem cell23_1286552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 1, 3, 1, 1, 5].length) (baseStart_1286552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1286552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1286552 prefixEnd_1286552 := by exact prefixLift 1286552
  have htrace : WordTrace (prefixWord ++ tailWord_1286552) baseStart_1286552 baseEnd_1286552 := by
    simpa [prefixWord, tailWord_1286552, baseEnd_1286552] using wordTrace_append hprefix tailTrace_1286552
  have hstable : (prefixWord ++ tailWord_1286552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1286552).length < 2 ^ (prefixWord ++ tailWord_1286552).sum := by decide
  have hdescent : baseEnd_1286552 < baseStart_1286552 := by decide
  rcases family_descends (prefixWord ++ tailWord_1286552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1286580 : List Nat := [2, 5, 2, 2, 2, 1, 1, 2, 1, 5]
def baseStart_1286580 : Nat := 118140960795 + 1286580 * 2 ^ 59
def prefixEnd_1286580 : Nat := 4983230072969 + 3 ^ 40 * 1286580 * 2
def baseEnd_1286580 : Nat := 220211313487227161177711

theorem tailTrace_1286580 : CollatzResearch.WordTrace tailWord_1286580 prefixEnd_1286580 220211313487227161177711 := by
  unfold tailWord_1286580
  simp only [CollatzResearch.WordTrace]
  refine ⟨23462713839473932607740597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31283618452631910143654129 23462713839473932607740597)
  ·
    refine ⟨2199629422450681181975681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 23462713839473932607740597 2199629422450681181975681)
    ·
      refine ⟨1649722066838010886481761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2199629422450681181975681 1649722066838010886481761)
      ·
        refine ⟨1237291550128508164861321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1649722066838010886481761 1237291550128508164861321)
        ·
          refine ⟨927968662596381123645991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1237291550128508164861321 927968662596381123645991)
          ·
            refine ⟨1391952993894571685468987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 927968662596381123645991 1391952993894571685468987)
            ·
              refine ⟨2087929490841857528203481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1391952993894571685468987 2087929490841857528203481)
              ·
                refine ⟨1565947118131393146152611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2087929490841857528203481 1565947118131393146152611)
                ·
                  refine ⟨2348920677197089719228917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1565947118131393146152611 2348920677197089719228917)
                  ·
                    refine ⟨220211313487227161177711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2348920677197089719228917 220211313487227161177711)
                    ·
                      rfl

theorem cell23_1286580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 2, 1, 1, 2, 1, 5].length) (baseStart_1286580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1286580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1286580 prefixEnd_1286580 := by exact prefixLift 1286580
  have htrace : WordTrace (prefixWord ++ tailWord_1286580) baseStart_1286580 baseEnd_1286580 := by
    simpa [prefixWord, tailWord_1286580, baseEnd_1286580] using wordTrace_append hprefix tailTrace_1286580
  have hstable : (prefixWord ++ tailWord_1286580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1286580).length < 2 ^ (prefixWord ++ tailWord_1286580).sum := by decide
  have hdescent : baseEnd_1286580 < baseStart_1286580 := by decide
  rcases family_descends (prefixWord ++ tailWord_1286580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1286609 : List Nat := [1, 2, 2, 1, 2, 1, 1, 7, 1, 3, 2]
def baseStart_1286609 : Nat := 118140960795 + 1286609 * 2 ^ 59
def prefixEnd_1286609 : Nat := 4983230072969 + 3 ^ 40 * 1286609 * 2
def baseEnd_1286609 : Nat := 660648831400661870070499

theorem tailTrace_1286609 : CollatzResearch.WordTrace tailWord_1286609 prefixEnd_1286609 660648831400661870070499 := by
  unfold tailWord_1286609
  simp only [CollatzResearch.WordTrace]
  refine ⟨46926485395842803168286881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31284323597228535445524587 46926485395842803168286881)
  ·
    refine ⟨35194864046882102376215161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46926485395842803168286881 35194864046882102376215161)
    ·
      refine ⟨26396148035161576782161371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35194864046882102376215161 26396148035161576782161371)
      ·
        refine ⟨39594222052742365173242057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26396148035161576782161371 39594222052742365173242057)
        ·
          refine ⟨29695666539556773879931543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39594222052742365173242057 29695666539556773879931543)
          ·
            refine ⟨44543499809335160819897315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29695666539556773879931543 44543499809335160819897315)
            ·
              refine ⟨66815249714002741229845973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44543499809335160819897315 66815249714002741229845973)
              ·
                refine ⟨1565982415171939247574515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 66815249714002741229845973 1565982415171939247574515)
                ·
                  refine ⟨2348973622757908871361773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1565982415171939247574515 2348973622757908871361773)
                  ·
                    refine ⟨880865108534215826760665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2348973622757908871361773 880865108534215826760665)
                    ·
                      refine ⟨660648831400661870070499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 880865108534215826760665 660648831400661870070499)
                      ·
                        rfl

theorem cell23_1286609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 7, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 7, 1, 3, 2].length) (baseStart_1286609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1286609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1286609 prefixEnd_1286609 := by exact prefixLift 1286609
  have htrace : WordTrace (prefixWord ++ tailWord_1286609) baseStart_1286609 baseEnd_1286609 := by
    simpa [prefixWord, tailWord_1286609, baseEnd_1286609] using wordTrace_append hprefix tailTrace_1286609
  have hstable : (prefixWord ++ tailWord_1286609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1286609).length < 2 ^ (prefixWord ++ tailWord_1286609).sum := by decide
  have hdescent : baseEnd_1286609 < baseStart_1286609 := by decide
  rcases family_descends (prefixWord ++ tailWord_1286609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1286632 : List Nat := [2, 1, 4, 1, 1, 4, 1, 1, 2, 6]
def baseStart_1286632 : Nat := 118140960795 + 1286632 * 2 ^ 59
def prefixEnd_1286632 : Nat := 4983230072969 + 3 ^ 40 * 1286632 * 2
def baseEnd_1286632 : Nat := 220220213818571760027631

theorem tailTrace_1286632 : CollatzResearch.WordTrace tailWord_1286632 prefixEnd_1286632 220220213818571760027631 := by
  unfold tailWord_1286632
  simp only [CollatzResearch.WordTrace]
  refine ⟨23463662137379739048187075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31284882849839652064249433 23463662137379739048187075)
  ·
    refine ⟨35195493206069608572280613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23463662137379739048187075 35195493206069608572280613)
    ·
      refine ⟨6599154976138051607302615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 35195493206069608572280613 6599154976138051607302615)
      ·
        refine ⟨9898732464207077410953923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6599154976138051607302615 9898732464207077410953923)
        ·
          refine ⟨14848098696310616116430885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9898732464207077410953923 14848098696310616116430885)
          ·
            refine ⟨2784018505558240521830791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14848098696310616116430885 2784018505558240521830791)
            ·
              refine ⟨4176027758337360782746187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2784018505558240521830791 4176027758337360782746187)
              ·
                refine ⟨6264041637506041174119281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4176027758337360782746187 6264041637506041174119281)
                ·
                  refine ⟨4698031228129530880589461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6264041637506041174119281 4698031228129530880589461)
                  ·
                    refine ⟨220220213818571760027631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4698031228129530880589461 220220213818571760027631)
                    ·
                      rfl

theorem cell23_1286632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 1, 1, 2, 6].length) (baseStart_1286632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1286632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1286632 prefixEnd_1286632 := by exact prefixLift 1286632
  have htrace : WordTrace (prefixWord ++ tailWord_1286632) baseStart_1286632 baseEnd_1286632 := by
    simpa [prefixWord, tailWord_1286632, baseEnd_1286632] using wordTrace_append hprefix tailTrace_1286632
  have hstable : (prefixWord ++ tailWord_1286632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1286632).length < 2 ^ (prefixWord ++ tailWord_1286632).sum := by decide
  have hdescent : baseEnd_1286632 < baseStart_1286632 := by decide
  rcases family_descends (prefixWord ++ tailWord_1286632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1286639 : List Nat := [1, 1, 2, 1, 4, 1, 1, 2, 6, 2, 2]
def baseStart_1286639 : Nat := 118140960795 + 1286639 * 2 ^ 59
def prefixEnd_1286639 : Nat := 4983230072969 + 3 ^ 40 * 1286639 * 2
def baseEnd_1286639 : Nat := 660664235820296752695361

theorem tailTrace_1286639 : CollatzResearch.WordTrace tailWord_1286639 prefixEnd_1286639 660664235820296752695361 := by
  unfold tailWord_1286639
  simp only [CollatzResearch.WordTrace]
  refine ⟨46927579585734118291878971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31285053057156078861252647 46927579585734118291878971)
  ·
    refine ⟨70391369378601177437818457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46927579585734118291878971 70391369378601177437818457)
    ·
      refine ⟨52793527033950883078363843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70391369378601177437818457 52793527033950883078363843)
      ·
        refine ⟨79190290550926324617545765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52793527033950883078363843 79190290550926324617545765)
        ·
          refine ⟨14848179478298685865789831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 79190290550926324617545765 14848179478298685865789831)
          ·
            refine ⟨22272269217448028798684747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14848179478298685865789831 22272269217448028798684747)
            ·
              refine ⟨33408403826172043198027121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22272269217448028798684747 33408403826172043198027121)
              ·
                refine ⟨25056302869629032398520341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33408403826172043198027121 25056302869629032398520341)
                ·
                  refine ⟨1174514197013860893680641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 25056302869629032398520341 1174514197013860893680641)
                  ·
                    refine ⟨880885647760395670260481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1174514197013860893680641 880885647760395670260481)
                    ·
                      refine ⟨660664235820296752695361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 880885647760395670260481 660664235820296752695361)
                      ·
                        rfl

theorem cell23_1286639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 2, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 2, 6, 2, 2].length) (baseStart_1286639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1286639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1286639 prefixEnd_1286639 := by exact prefixLift 1286639
  have htrace : WordTrace (prefixWord ++ tailWord_1286639) baseStart_1286639 baseEnd_1286639 := by
    simpa [prefixWord, tailWord_1286639, baseEnd_1286639] using wordTrace_append hprefix tailTrace_1286639
  have hstable : (prefixWord ++ tailWord_1286639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1286639).length < 2 ^ (prefixWord ++ tailWord_1286639).sum := by decide
  have hdescent : baseEnd_1286639 < baseStart_1286639 := by decide
  rcases family_descends (prefixWord ++ tailWord_1286639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1286660 : List Nat := [2, 3, 2, 3, 1, 3, 2, 1, 1, 3, 2]
def baseStart_1286660 : Nat := 118140960795 + 1286660 * 2 ^ 59
def prefixEnd_1286660 : Nat := 4983230072969 + 3 ^ 40 * 1286660 * 2
def baseEnd_1286660 : Nat := 660675018914041170532765

theorem tailTrace_1286660 : CollatzResearch.WordTrace tailWord_1286660 prefixEnd_1286660 660675018914041170532765 := by
  unfold tailWord_1286660
  simp only [CollatzResearch.WordTrace]
  refine ⟨23464172759329019439196717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31285563679105359252262289 23464172759329019439196717)
  ·
    refine ⟨8799064784748382289698769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23464172759329019439196717 8799064784748382289698769)
    ·
      refine ⟨6599298588561286717274077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8799064784748382289698769 6599298588561286717274077)
      ·
        refine ⟨2474736970710482518977779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6599298588561286717274077 2474736970710482518977779)
        ·
          refine ⟨3712105456065723778466669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2474736970710482518977779 3712105456065723778466669)
          ·
            refine ⟨1392039546024646416925001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3712105456065723778466669 1392039546024646416925001)
            ·
              refine ⟨1044029659518484812693751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1392039546024646416925001 1044029659518484812693751)
              ·
                refine ⟨1566044489277727219040627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1044029659518484812693751 1566044489277727219040627)
                ·
                  refine ⟨2349066733916590828560941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1566044489277727219040627 2349066733916590828560941)
                  ·
                    refine ⟨880900025218721560710353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2349066733916590828560941 880900025218721560710353)
                    ·
                      refine ⟨660675018914041170532765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 880900025218721560710353 660675018914041170532765)
                      ·
                        rfl

theorem cell23_1286660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 3, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 3, 2, 1, 1, 3, 2].length) (baseStart_1286660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1286660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1286660 prefixEnd_1286660 := by exact prefixLift 1286660
  have htrace : WordTrace (prefixWord ++ tailWord_1286660) baseStart_1286660 baseEnd_1286660 := by
    simpa [prefixWord, tailWord_1286660, baseEnd_1286660] using wordTrace_append hprefix tailTrace_1286660
  have hstable : (prefixWord ++ tailWord_1286660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1286660).length < 2 ^ (prefixWord ++ tailWord_1286660).sum := by decide
  have hdescent : baseEnd_1286660 < baseStart_1286660 := by decide
  rcases family_descends (prefixWord ++ tailWord_1286660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1286712 : List Nat := [2, 1, 2, 1, 4, 1, 1, 3, 1, 3, 4]
def baseStart_1286712 : Nat := 118140960795 + 1286712 * 2 ^ 59
def prefixEnd_1286712 : Nat := 4983230072969 + 3 ^ 40 * 1286712 * 2
def baseEnd_1286712 : Nat := 660701719908074967082525

theorem tailTrace_1286712 : CollatzResearch.WordTrace tailWord_1286712 prefixEnd_1286712 660701719908074967082525 := by
  unfold tailWord_1286712
  simp only [CollatzResearch.WordTrace]
  refine ⟨23465121057234825879643195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31286828076313101172857593 23465121057234825879643195)
  ·
    refine ⟨35197681585852238819464793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23465121057234825879643195 35197681585852238819464793)
    ·
      refine ⟨26398261189389179114598595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35197681585852238819464793 26398261189389179114598595)
      ·
        refine ⟨39597391784083768671897893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26398261189389179114598595 39597391784083768671897893)
        ·
          refine ⟨7424510959515706625980855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 39597391784083768671897893 7424510959515706625980855)
          ·
            refine ⟨11136766439273559938971283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7424510959515706625980855 11136766439273559938971283)
            ·
              refine ⟨16705149658910339908456925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11136766439273559938971283 16705149658910339908456925)
              ·
                refine ⟨6264431122091377465671347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16705149658910339908456925 6264431122091377465671347)
                ·
                  refine ⟨9396646683137066198507021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6264431122091377465671347 9396646683137066198507021)
                  ·
                    refine ⟨3523742506176399824440133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9396646683137066198507021 3523742506176399824440133)
                    ·
                      refine ⟨660701719908074967082525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3523742506176399824440133 660701719908074967082525)
                      ·
                        rfl

theorem cell23_1286712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 3, 1, 3, 4].length) (baseStart_1286712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1286712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1286712 prefixEnd_1286712 := by exact prefixLift 1286712
  have htrace : WordTrace (prefixWord ++ tailWord_1286712) baseStart_1286712 baseEnd_1286712 := by
    simpa [prefixWord, tailWord_1286712, baseEnd_1286712] using wordTrace_append hprefix tailTrace_1286712
  have hstable : (prefixWord ++ tailWord_1286712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1286712).length < 2 ^ (prefixWord ++ tailWord_1286712).sum := by decide
  have hdescent : baseEnd_1286712 < baseStart_1286712 := by decide
  rcases family_descends (prefixWord ++ tailWord_1286712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1286726 : List Nat := [6, 1, 1, 1, 2, 1, 1, 1, 4, 5]
def baseStart_1286726 : Nat := 118140960795 + 1286726 * 2 ^ 59
def prefixEnd_1286726 : Nat := 4983230072969 + 3 ^ 40 * 1286726 * 2
def baseEnd_1286726 : Nat := 220236302879079304102487

theorem tailTrace_1286726 : CollatzResearch.WordTrace tailWord_1286726 prefixEnd_1286726 220236302879079304102487 := by
  unfold tailWord_1286726
  simp only [CollatzResearch.WordTrace]
  refine ⟨1466586023013091629696751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 31287168490945954766864021 1466586023013091629696751)
  ·
    refine ⟨2199879034519637444545127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1466586023013091629696751 2199879034519637444545127)
    ·
      refine ⟨3299818551779456166817691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2199879034519637444545127 3299818551779456166817691)
      ·
        refine ⟨4949727827669184250226537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3299818551779456166817691 4949727827669184250226537)
        ·
          refine ⟨3712295870751888187669903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4949727827669184250226537 3712295870751888187669903)
          ·
            refine ⟨5568443806127832281504855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3712295870751888187669903 5568443806127832281504855)
            ·
              refine ⟨8352665709191748422257283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5568443806127832281504855 8352665709191748422257283)
              ·
                refine ⟨12528998563787622633385925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8352665709191748422257283 12528998563787622633385925)
                ·
                  refine ⟨2349187230710179243759861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12528998563787622633385925 2349187230710179243759861)
                  ·
                    refine ⟨220236302879079304102487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2349187230710179243759861 220236302879079304102487)
                    ·
                      rfl

theorem cell23_1286726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 1, 1, 4, 5].length) (baseStart_1286726 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1286726 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1286726 prefixEnd_1286726 := by exact prefixLift 1286726
  have htrace : WordTrace (prefixWord ++ tailWord_1286726) baseStart_1286726 baseEnd_1286726 := by
    simpa [prefixWord, tailWord_1286726, baseEnd_1286726] using wordTrace_append hprefix tailTrace_1286726
  have hstable : (prefixWord ++ tailWord_1286726).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1286726).length < 2 ^ (prefixWord ++ tailWord_1286726).sum := by decide
  have hdescent : baseEnd_1286726 < baseStart_1286726 := by decide
  rcases family_descends (prefixWord ++ tailWord_1286726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1286766 : List Nat := [4, 1, 2, 2, 2, 1, 1, 3, 2, 2, 3]
def baseStart_1286766 : Nat := 118140960795 + 1286766 * 2 ^ 59
def prefixEnd_1286766 : Nat := 4983230072969 + 3 ^ 40 * 1286766 * 2
def baseEnd_1286766 : Nat := 660729447863417755807277

theorem tailTrace_1286766 : CollatzResearch.WordTrace tailWord_1286766 prefixEnd_1286766 660729447863417755807277 := by
  unfold tailWord_1286766
  simp only [CollatzResearch.WordTrace]
  refine ⟨5866526457034252372719019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 31288141104182679321168101 5866526457034252372719019)
  ·
    refine ⟨8799789685551378559078529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5866526457034252372719019 8799789685551378559078529)
    ·
      refine ⟨6599842264163533919308897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8799789685551378559078529 6599842264163533919308897)
      ·
        refine ⟨4949881698122650439481673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6599842264163533919308897 4949881698122650439481673)
        ·
          refine ⟨3712411273591987829611255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4949881698122650439481673 3712411273591987829611255)
          ·
            refine ⟨5568616910387981744416883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3712411273591987829611255 5568616910387981744416883)
            ·
              refine ⟨8352925365581972616625325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5568616910387981744416883 8352925365581972616625325)
              ·
                refine ⟨3132347012093239731234497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8352925365581972616625325 3132347012093239731234497)
                ·
                  refine ⟨2349260259069929798425873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3132347012093239731234497 2349260259069929798425873)
                  ·
                    refine ⟨1761945194302447348819405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2349260259069929798425873 1761945194302447348819405)
                    ·
                      refine ⟨660729447863417755807277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1761945194302447348819405 660729447863417755807277)
                      ·
                        rfl

theorem cell23_1286766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 1, 3, 2, 2, 3].length) (baseStart_1286766 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1286766 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1286766 prefixEnd_1286766 := by exact prefixLift 1286766
  have htrace : WordTrace (prefixWord ++ tailWord_1286766) baseStart_1286766 baseEnd_1286766 := by
    simpa [prefixWord, tailWord_1286766, baseEnd_1286766] using wordTrace_append hprefix tailTrace_1286766
  have hstable : (prefixWord ++ tailWord_1286766).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1286766).length < 2 ^ (prefixWord ++ tailWord_1286766).sum := by decide
  have hdescent : baseEnd_1286766 < baseStart_1286766 := by decide
  rcases family_descends (prefixWord ++ tailWord_1286766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1286779 : List Nat := [1, 1, 1, 1, 1, 4, 2, 1, 7, 1, 3]
def baseStart_1286779 : Nat := 118140960795 + 1286779 * 2 ^ 59
def prefixEnd_1286779 : Nat := 4983230072969 + 3 ^ 40 * 1286779 * 2
def baseEnd_1286779 : Nat := 660736123111926204944717

theorem tailTrace_1286779 : CollatzResearch.WordTrace tailWord_1286779 prefixEnd_1286779 660736123111926204944717 := by
  unfold tailWord_1286779
  simp only [CollatzResearch.WordTrace]
  refine ⟨46932685805226922201975391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31288457203484614801316927 46932685805226922201975391)
  ·
    refine ⟨70399028707840383302963087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46932685805226922201975391 70399028707840383302963087)
    ·
      refine ⟨105598543061760574954444631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70399028707840383302963087 105598543061760574954444631)
      ·
        refine ⟨158397814592640862431666947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105598543061760574954444631 158397814592640862431666947)
        ·
          refine ⟨237596721888961293647500421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 158397814592640862431666947 237596721888961293647500421)
          ·
            refine ⟨44549385354180242558906329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 237596721888961293647500421 44549385354180242558906329)
            ·
              refine ⟨33412039015635181919179747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44549385354180242558906329 33412039015635181919179747)
              ·
                refine ⟨50118058523452772878769621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33412039015635181919179747 50118058523452772878769621)
                ·
                  refine ⟨1174641996643424364346163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 50118058523452772878769621 1174641996643424364346163)
                  ·
                    refine ⟨1761962994965136546519245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1174641996643424364346163 1761962994965136546519245)
                    ·
                      refine ⟨660736123111926204944717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1761962994965136546519245 660736123111926204944717)
                      ·
                        rfl

theorem cell23_1286779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 1, 7, 1, 3].length) (baseStart_1286779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1286779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1286779 prefixEnd_1286779 := by exact prefixLift 1286779
  have htrace : WordTrace (prefixWord ++ tailWord_1286779) baseStart_1286779 baseEnd_1286779 := by
    simpa [prefixWord, tailWord_1286779, baseEnd_1286779] using wordTrace_append hprefix tailTrace_1286779
  have hstable : (prefixWord ++ tailWord_1286779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1286779).length < 2 ^ (prefixWord ++ tailWord_1286779).sum := by decide
  have hdescent : baseEnd_1286779 < baseStart_1286779 := by decide
  rcases family_descends (prefixWord ++ tailWord_1286779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1286819 : List Nat := [1, 1, 1, 4, 1, 1, 2, 1, 1, 8, 2]
def baseStart_1286819 : Nat := 118140960795 + 1286819 * 2 ^ 59
def prefixEnd_1286819 : Nat := 4983230072969 + 3 ^ 40 * 1286819 * 2
def baseEnd_1286819 : Nat := 660756662338106048444533

theorem tailTrace_1286819 : CollatzResearch.WordTrace tailWord_1286819 prefixEnd_1286819 660756662338106048444533 := by
  unfold tailWord_1286819
  simp only [CollatzResearch.WordTrace]
  refine ⟨46934144725082009033431511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31289429816721339355621007 46934144725082009033431511)
  ·
    refine ⟨70401217087623013550147267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46934144725082009033431511 70401217087623013550147267)
    ·
      refine ⟨105601825631434520325220901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70401217087623013550147267 105601825631434520325220901)
      ·
        refine ⟨19800342305893972560978919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 105601825631434520325220901 19800342305893972560978919)
        ·
          refine ⟨29700513458840958841468379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19800342305893972560978919 29700513458840958841468379)
          ·
            refine ⟨44550770188261438262202569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29700513458840958841468379 44550770188261438262202569)
            ·
              refine ⟨33413077641196078696651927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44550770188261438262202569 33413077641196078696651927)
              ·
                refine ⟨50119616461794118044977891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33413077641196078696651927 50119616461794118044977891)
                ·
                  refine ⟨75179424692691177067466837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 50119616461794118044977891 75179424692691177067466837)
                  ·
                    refine ⟨881008883117474731259377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 75179424692691177067466837 881008883117474731259377)
                    ·
                      refine ⟨660756662338106048444533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 881008883117474731259377 660756662338106048444533)
                      ·
                        rfl

theorem cell23_1286819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 1, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 1, 1, 8, 2].length) (baseStart_1286819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1286819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1286819 prefixEnd_1286819 := by exact prefixLift 1286819
  have htrace : WordTrace (prefixWord ++ tailWord_1286819) baseStart_1286819 baseEnd_1286819 := by
    simpa [prefixWord, tailWord_1286819, baseEnd_1286819] using wordTrace_append hprefix tailTrace_1286819
  have hstable : (prefixWord ++ tailWord_1286819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1286819).length < 2 ^ (prefixWord ++ tailWord_1286819).sum := by decide
  have hdescent : baseEnd_1286819 < baseStart_1286819 := by decide
  rcases family_descends (prefixWord ++ tailWord_1286819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1286832 : List Nat := [2, 1, 1, 1, 2, 1, 3, 2, 3, 1, 6]
def baseStart_1286832 : Nat := 118140960795 + 1286832 * 2 ^ 59
def prefixEnd_1286832 : Nat := 4983230072969 + 3 ^ 40 * 1286832 * 2
def baseEnd_1286832 : Nat := 660763337586614497581973

theorem tailTrace_1286832 : CollatzResearch.WordTrace tailWord_1286832 prefixEnd_1286832 660763337586614497581973 := by
  unfold tailWord_1286832
  simp only [CollatzResearch.WordTrace]
  refine ⟨23467309437017456126827375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31289745916023274835769833 23467309437017456126827375)
  ·
    refine ⟨35200964155526184190241063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23467309437017456126827375 35200964155526184190241063)
    ·
      refine ⟨52801446233289276285361595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35200964155526184190241063 52801446233289276285361595)
      ·
        refine ⟨79202169349933914428042393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52801446233289276285361595 79202169349933914428042393)
        ·
          refine ⟨59401627012450435821031795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79202169349933914428042393 59401627012450435821031795)
          ·
            refine ⟨89102440518675653731547693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59401627012450435821031795 89102440518675653731547693)
            ·
              refine ⟨33413415194503370149330385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 89102440518675653731547693 33413415194503370149330385)
              ·
                refine ⟨25060061395877527611997789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33413415194503370149330385 25060061395877527611997789)
                ·
                  refine ⟨9397523023454072854499171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25060061395877527611997789 9397523023454072854499171)
                  ·
                    refine ⟨14096284535181109281748757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9397523023454072854499171 14096284535181109281748757)
                    ·
                      refine ⟨660763337586614497581973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 14096284535181109281748757 660763337586614497581973)
                      ·
                        rfl

theorem cell23_1286832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 2, 3, 1, 6].length) (baseStart_1286832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1286832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1286832 prefixEnd_1286832 := by exact prefixLift 1286832
  have htrace : WordTrace (prefixWord ++ tailWord_1286832) baseStart_1286832 baseEnd_1286832 := by
    simpa [prefixWord, tailWord_1286832, baseEnd_1286832] using wordTrace_append hprefix tailTrace_1286832
  have hstable : (prefixWord ++ tailWord_1286832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1286832).length < 2 ^ (prefixWord ++ tailWord_1286832).sum := by decide
  have hdescent : baseEnd_1286832 < baseStart_1286832 := by decide
  rcases family_descends (prefixWord ++ tailWord_1286832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1286833 : List Nat := [1, 2, 2, 6, 1, 1, 1, 3, 1, 5]
def baseStart_1286833 : Nat := 118140960795 + 1286833 * 2 ^ 59
def prefixEnd_1286833 : Nat := 4983230072969 + 3 ^ 40 * 1286833 * 2
def baseEnd_1286833 : Nat := 220254617022422997889823

theorem tailTrace_1286833 : CollatzResearch.WordTrace tailWord_1286833 prefixEnd_1286833 220254617022422997889823 := by
  unfold tailWord_1286833
  simp only [CollatzResearch.WordTrace]
  refine ⟨46934655347031289424441153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31289770231354192949627435 46934655347031289424441153)
  ·
    refine ⟨35200991510273467068330865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46934655347031289424441153 35200991510273467068330865)
    ·
      refine ⟨26400743632705100301248149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35200991510273467068330865 26400743632705100301248149)
      ·
        refine ⟨1237534857783051576621007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 26400743632705100301248149 1237534857783051576621007)
        ·
          refine ⟨1856302286674577364931511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1237534857783051576621007 1856302286674577364931511)
          ·
            refine ⟨2784453430011866047397267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1856302286674577364931511 2784453430011866047397267)
            ·
              refine ⟨4176680145017799071095901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2784453430011866047397267 4176680145017799071095901)
              ·
                refine ⟨1566255054381674651660963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4176680145017799071095901 1566255054381674651660963)
                ·
                  refine ⟨2349382581572511977491445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1566255054381674651660963 2349382581572511977491445)
                  ·
                    refine ⟨220254617022422997889823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2349382581572511977491445 220254617022422997889823)
                    ·
                      rfl

theorem cell23_1286833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 1, 3, 1, 5].length) (baseStart_1286833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1286833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1286833 prefixEnd_1286833 := by exact prefixLift 1286833
  have htrace : WordTrace (prefixWord ++ tailWord_1286833) baseStart_1286833 baseEnd_1286833 := by
    simpa [prefixWord, tailWord_1286833, baseEnd_1286833] using wordTrace_append hprefix tailTrace_1286833
  have hstable : (prefixWord ++ tailWord_1286833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1286833).length < 2 ^ (prefixWord ++ tailWord_1286833).sum := by decide
  have hdescent : baseEnd_1286833 < baseStart_1286833 := by decide
  rcases family_descends (prefixWord ++ tailWord_1286833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1286842 : List Nat := [3, 1, 1, 1, 2, 3, 12]
def baseStart_1286842 : Nat := 118140960795 + 1286842 * 2 ^ 59
def prefixEnd_1286842 : Nat := 4983230072969 + 3 ^ 40 * 1286842 * 2
def baseEnd_1286842 : Nat := 8157635461643943931567

theorem tailTrace_1286842 : CollatzResearch.WordTrace tailWord_1286842 prefixEnd_1286842 8157635461643943931567 := by
  unfold tailWord_1286842
  simp only [CollatzResearch.WordTrace]
  refine ⟨11733745900999670990379695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31289989069332455974345853 11733745900999670990379695)
  ·
    refine ⟨17600618851499506485569543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11733745900999670990379695 17600618851499506485569543)
    ·
      refine ⟨26400928277249259728354315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17600618851499506485569543 26400928277249259728354315)
      ·
        refine ⟨39601392415873889592531473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26400928277249259728354315 39601392415873889592531473)
        ·
          refine ⟨29701044311905417194398605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39601392415873889592531473 29701044311905417194398605)
          ·
            refine ⟨11137891616964531447899477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29701044311905417194398605 11137891616964531447899477)
            ·
              refine ⟨8157635461643943931567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 11137891616964531447899477 8157635461643943931567)
              ·
                rfl

theorem cell23_1286842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 12].length) (baseStart_1286842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1286842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1286842 prefixEnd_1286842 := by exact prefixLift 1286842
  have htrace : WordTrace (prefixWord ++ tailWord_1286842) baseStart_1286842 baseEnd_1286842 := by
    simpa [prefixWord, tailWord_1286842, baseEnd_1286842] using wordTrace_append hprefix tailTrace_1286842
  have hstable : (prefixWord ++ tailWord_1286842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1286842).length < 2 ^ (prefixWord ++ tailWord_1286842).sum := by decide
  have hdescent : baseEnd_1286842 < baseStart_1286842 := by decide
  rcases family_descends (prefixWord ++ tailWord_1286842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1286846 : List Nat := [4, 2, 1, 1, 2, 1, 3, 1, 4, 4]
def baseStart_1286846 : Nat := 118140960795 + 1286846 * 2 ^ 59
def prefixEnd_1286846 : Nat := 4983230072969 + 3 ^ 40 * 1286846 * 2
def baseEnd_1286846 : Nat := 220256842105259147602303

theorem tailTrace_1286846 : CollatzResearch.WordTrace tailWord_1286846 prefixEnd_1286846 220256842105259147602303 := by
  unfold tailWord_1286846
  simp only [CollatzResearch.WordTrace]
  refine ⟨5866891186998024080583049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 31290086330656128429776261 5866891186998024080583049)
  ·
    refine ⟨4400168390248518060437287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5866891186998024080583049 4400168390248518060437287)
    ·
      refine ⟨6600252585372777090655931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4400168390248518060437287 6600252585372777090655931)
      ·
        refine ⟨9900378878059165635983897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6600252585372777090655931 9900378878059165635983897)
        ·
          refine ⟨7425284158544374226987923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9900378878059165635983897 7425284158544374226987923)
          ·
            refine ⟨11137926237816561340481885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7425284158544374226987923 11137926237816561340481885)
            ·
              refine ⟨4176722339181210502680707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11137926237816561340481885 4176722339181210502680707)
              ·
                refine ⟨6265083508771815754021061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4176722339181210502680707 6265083508771815754021061)
                ·
                  refine ⟨1174703157894715453878949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6265083508771815754021061 1174703157894715453878949)
                  ·
                    refine ⟨220256842105259147602303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1174703157894715453878949 220256842105259147602303)
                    ·
                      rfl

theorem cell23_1286846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 3, 1, 4, 4].length) (baseStart_1286846 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1286846 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1286846 prefixEnd_1286846 := by exact prefixLift 1286846
  have htrace : WordTrace (prefixWord ++ tailWord_1286846) baseStart_1286846 baseEnd_1286846 := by
    simpa [prefixWord, tailWord_1286846, baseEnd_1286846] using wordTrace_append hprefix tailTrace_1286846
  have hstable : (prefixWord ++ tailWord_1286846).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1286846).length < 2 ^ (prefixWord ++ tailWord_1286846).sum := by decide
  have hdescent : baseEnd_1286846 < baseStart_1286846 := by decide
  rcases family_descends (prefixWord ++ tailWord_1286846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1286866 : List Nat := [3, 2, 2, 2, 3, 1, 1, 1, 1, 1, 6]
def baseStart_1286866 : Nat := 118140960795 + 1286866 * 2 ^ 59
def prefixEnd_1286866 : Nat := 4983230072969 + 3 ^ 40 * 1286866 * 2
def baseEnd_1286866 : Nat := 660780795928867364556817

theorem tailTrace_1286866 : CollatzResearch.WordTrace tailWord_1286866 prefixEnd_1286866 660780795928867364556817 := by
  unfold tailWord_1286866
  simp only [CollatzResearch.WordTrace]
  refine ⟨11733964738977934015098113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31290572637274490706928301 11733964738977934015098113)
  ·
    refine ⟨8800473554233450511323585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11733964738977934015098113 8800473554233450511323585)
    ·
      refine ⟨6600355165675087883492689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8800473554233450511323585 6600355165675087883492689)
      ·
        refine ⟨4950266374256315912619517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6600355165675087883492689 4950266374256315912619517)
        ·
          refine ⟨1856349890346118467232319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4950266374256315912619517 1856349890346118467232319)
          ·
            refine ⟨2784524835519177700848479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1856349890346118467232319 2784524835519177700848479)
            ·
              refine ⟨4176787253278766551272719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2784524835519177700848479 4176787253278766551272719)
              ·
                refine ⟨6265180879918149826909079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4176787253278766551272719 6265180879918149826909079)
                ·
                  refine ⟨9397771319877224740363619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6265180879918149826909079 9397771319877224740363619)
                  ·
                    refine ⟨14096656979815837110545429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9397771319877224740363619 14096656979815837110545429)
                    ·
                      refine ⟨660780795928867364556817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 14096656979815837110545429 660780795928867364556817)
                      ·
                        rfl

theorem cell23_1286866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 1, 1, 1, 1, 6].length) (baseStart_1286866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1286866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1286866 prefixEnd_1286866 := by exact prefixLift 1286866
  have htrace : WordTrace (prefixWord ++ tailWord_1286866) baseStart_1286866 baseEnd_1286866 := by
    simpa [prefixWord, tailWord_1286866, baseEnd_1286866] using wordTrace_append hprefix tailTrace_1286866
  have hstable : (prefixWord ++ tailWord_1286866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1286866).length < 2 ^ (prefixWord ++ tailWord_1286866).sum := by decide
  have hdescent : baseEnd_1286866 < baseStart_1286866 := by decide
  rcases family_descends (prefixWord ++ tailWord_1286866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1286876 : List Nat := [2, 2, 5, 1, 1, 2, 1, 9]
def baseStart_1286876 : Nat := 118140960795 + 1286876 * 2 ^ 59
def prefixEnd_1286876 : Nat := 4983230072969 + 3 ^ 40 * 1286876 * 2
def baseEnd_1286876 : Nat := 24473552990200456497473

theorem tailTrace_1286876 : CollatzResearch.WordTrace tailWord_1286876 prefixEnd_1286876 24473552990200456497473 := by
  unfold tailWord_1286876
  simp only [CollatzResearch.WordTrace]
  refine ⟨23468111842937753884128241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31290815790583671845504321 23468111842937753884128241)
  ·
    refine ⟨17601083882203315413096181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23468111842937753884128241 17601083882203315413096181)
    ·
      refine ⟨1650101613956560819977767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 17601083882203315413096181 1650101613956560819977767)
      ·
        refine ⟨2475152420934841229966651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1650101613956560819977767 2475152420934841229966651)
        ·
          refine ⟨3712728631402261844949977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2475152420934841229966651 3712728631402261844949977)
          ·
            refine ⟨2784546473551696383712483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3712728631402261844949977 2784546473551696383712483)
            ·
              refine ⟨4176819710327544575568725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2784546473551696383712483 4176819710327544575568725)
              ·
                refine ⟨24473552990200456497473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 4176819710327544575568725 24473552990200456497473)
                ·
                  rfl

theorem cell23_1286876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 1, 9].length) (baseStart_1286876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1286876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1286876 prefixEnd_1286876 := by exact prefixLift 1286876
  have htrace : WordTrace (prefixWord ++ tailWord_1286876) baseStart_1286876 baseEnd_1286876 := by
    simpa [prefixWord, tailWord_1286876, baseEnd_1286876] using wordTrace_append hprefix tailTrace_1286876
  have hstable : (prefixWord ++ tailWord_1286876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1286876).length < 2 ^ (prefixWord ++ tailWord_1286876).sum := by decide
  have hdescent : baseEnd_1286876 < baseStart_1286876 := by decide
  rcases family_descends (prefixWord ++ tailWord_1286876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1286909 : List Nat := [1, 4, 1, 1, 1, 1, 4, 1, 2, 3, 4]
def baseStart_1286909 : Nat := 118140960795 + 1286909 * 2 ^ 59
def prefixEnd_1286909 : Nat := 4983230072969 + 3 ^ 40 * 1286909 * 2
def baseEnd_1286909 : Nat := 660802875597010696319119

theorem tailTrace_1286909 : CollatzResearch.WordTrace tailWord_1286909 prefixEnd_1286909 660802875597010696319119 := by
  unfold tailWord_1286909
  simp only [CollatzResearch.WordTrace]
  refine ⟨46937427294755954404207781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31291618196503969602805187 46937427294755954404207781)
  ·
    refine ⟨8800767617766741450788959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 46937427294755954404207781 8800767617766741450788959)
    ·
      refine ⟨13201151426650112176183439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8800767617766741450788959 13201151426650112176183439)
      ·
        refine ⟨19801727139975168264275159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13201151426650112176183439 19801727139975168264275159)
        ·
          refine ⟨29702590709962752396412739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19801727139975168264275159 29702590709962752396412739)
          ·
            refine ⟨44553886064944128594619109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29702590709962752396412739 44553886064944128594619109)
            ·
              refine ⟨8353853637177024111491083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 44553886064944128594619109 8353853637177024111491083)
              ·
                refine ⟨12530780455765536167236625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8353853637177024111491083 12530780455765536167236625)
                ·
                  refine ⟨9398085341824152125427469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12530780455765536167236625 9398085341824152125427469)
                  ·
                    refine ⟨3524282003184057047035301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9398085341824152125427469 3524282003184057047035301)
                    ·
                      refine ⟨660802875597010696319119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3524282003184057047035301 660802875597010696319119)
                      ·
                        rfl

theorem cell23_1286909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 4, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 4, 1, 2, 3, 4].length) (baseStart_1286909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1286909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1286909 prefixEnd_1286909 := by exact prefixLift 1286909
  have htrace : WordTrace (prefixWord ++ tailWord_1286909) baseStart_1286909 baseEnd_1286909 := by
    simpa [prefixWord, tailWord_1286909, baseEnd_1286909] using wordTrace_append hprefix tailTrace_1286909
  have hstable : (prefixWord ++ tailWord_1286909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1286909).length < 2 ^ (prefixWord ++ tailWord_1286909).sum := by decide
  have hdescent : baseEnd_1286909 < baseStart_1286909 := by decide
  rcases family_descends (prefixWord ++ tailWord_1286909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1286920 : List Nat := [2, 1, 3, 2, 2, 2, 4, 1, 2, 1, 3]
def baseStart_1286920 : Nat := 118140960795 + 1286920 * 2 ^ 59
def prefixEnd_1286920 : Nat := 4983230072969 + 3 ^ 40 * 1286920 * 2
def baseEnd_1286920 : Nat := 660808523884210153281569

theorem tailTrace_1286920 : CollatzResearch.WordTrace tailWord_1286920 prefixEnd_1286920 660808523884210153281569 := by
  unfold tailWord_1286920
  simp only [CollatzResearch.WordTrace]
  refine ⟨23468914248858051641429107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31291885665144068855238809 23468914248858051641429107)
  ·
    refine ⟨35203371373287077462143661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23468914248858051641429107 35203371373287077462143661)
    ·
      refine ⟨13201264264982654048303873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35203371373287077462143661 13201264264982654048303873)
      ·
        refine ⟨9900948198736990536227905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13201264264982654048303873 9900948198736990536227905)
        ·
          refine ⟨7425711149052742902170929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9900948198736990536227905 7425711149052742902170929)
          ·
            refine ⟨5569283361789557176628197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7425711149052742902170929 5569283361789557176628197)
            ·
              refine ⟨1044240630335541970617787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5569283361789557176628197 1044240630335541970617787)
              ·
                refine ⟨1566360945503312955926681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1044240630335541970617787 1566360945503312955926681)
                ·
                  refine ⟨1174770709127484716945011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1566360945503312955926681 1174770709127484716945011)
                  ·
                    refine ⟨1762156063691227075417517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1174770709127484716945011 1762156063691227075417517)
                    ·
                      refine ⟨660808523884210153281569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1762156063691227075417517 660808523884210153281569)
                      ·
                        rfl

theorem cell23_1286920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 4, 1, 2, 1, 3].length) (baseStart_1286920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1286920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1286920 prefixEnd_1286920 := by exact prefixLift 1286920
  have htrace : WordTrace (prefixWord ++ tailWord_1286920) baseStart_1286920 baseEnd_1286920 := by
    simpa [prefixWord, tailWord_1286920, baseEnd_1286920] using wordTrace_append hprefix tailTrace_1286920
  have hstable : (prefixWord ++ tailWord_1286920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1286920).length < 2 ^ (prefixWord ++ tailWord_1286920).sum := by decide
  have hdescent : baseEnd_1286920 < baseStart_1286920 := by decide
  rcases family_descends (prefixWord ++ tailWord_1286920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1286929 : List Nat := [1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 5]
def baseStart_1286929 : Nat := 118140960795 + 1286929 * 2 ^ 59
def prefixEnd_1286929 : Nat := 4983230072969 + 3 ^ 40 * 1286929 * 2
def baseEnd_1286929 : Nat := 660813145210100618069027

theorem tailTrace_1286929 : CollatzResearch.WordTrace tailWord_1286929 prefixEnd_1286929 660813145210100618069027 := by
  unfold tailWord_1286929
  simp only [CollatzResearch.WordTrace]
  refine ⟨46938156754683497819935841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31292104503122331879957227 46938156754683497819935841)
  ·
    refine ⟨35203617566012623364951881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46938156754683497819935841 35203617566012623364951881)
    ·
      refine ⟨26402713174509467523713911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35203617566012623364951881 26402713174509467523713911)
      ·
        refine ⟨39604069761764201285570867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26402713174509467523713911 39604069761764201285570867)
        ·
          refine ⟨59406104642646301928356301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39604069761764201285570867 59406104642646301928356301)
          ·
            refine ⟨22277289240992363223133613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 59406104642646301928356301 22277289240992363223133613)
            ·
              refine ⟨8353983465372136208675105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22277289240992363223133613 8353983465372136208675105)
              ·
                refine ⟨6265487599029102156506329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8353983465372136208675105 6265487599029102156506329)
                ·
                  refine ⟨4699115699271826617379747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6265487599029102156506329 4699115699271826617379747)
                  ·
                    refine ⟨7048673548907739926069621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4699115699271826617379747 7048673548907739926069621)
                    ·
                      refine ⟨660813145210100618069027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7048673548907739926069621 660813145210100618069027)
                      ·
                        rfl

theorem cell23_1286929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 5].length) (baseStart_1286929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1286929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1286929 prefixEnd_1286929 := by exact prefixLift 1286929
  have htrace : WordTrace (prefixWord ++ tailWord_1286929) baseStart_1286929 baseEnd_1286929 := by
    simpa [prefixWord, tailWord_1286929, baseEnd_1286929] using wordTrace_append hprefix tailTrace_1286929
  have hstable : (prefixWord ++ tailWord_1286929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1286929).length < 2 ^ (prefixWord ++ tailWord_1286929).sum := by decide
  have hdescent : baseEnd_1286929 < baseStart_1286929 := by decide
  rcases family_descends (prefixWord ++ tailWord_1286929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1286943 : List Nat := [1, 1, 2, 4, 2, 3, 1, 2, 1, 4, 2]
def baseStart_1286943 : Nat := 118140960795 + 1286943 * 2 ^ 59
def prefixEnd_1286943 : Nat := 4983230072969 + 3 ^ 40 * 1286943 * 2
def baseEnd_1286943 : Nat := 660820333939263563293963

theorem tailTrace_1286943 : CollatzResearch.WordTrace tailWord_1286943 prefixEnd_1286943 660820333939263563293963 := by
  unfold tailWord_1286943
  simp only [CollatzResearch.WordTrace]
  refine ⟨46938667376632778210945483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31292444917755185473963655 46938667376632778210945483)
  ·
    refine ⟨70408001064949167316418225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46938667376632778210945483 70408001064949167316418225)
    ·
      refine ⟨52806000798711875487313669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70408001064949167316418225 52806000798711875487313669)
      ·
        refine ⟨9901125149758476653871313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 52806000798711875487313669 9901125149758476653871313)
        ·
          refine ⟨7425843862318857490403485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9901125149758476653871313 7425843862318857490403485)
          ·
            refine ⟨2784691448369571558901307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7425843862318857490403485 2784691448369571558901307)
            ·
              refine ⟨4177037172554357338351961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2784691448369571558901307 4177037172554357338351961)
              ·
                refine ⟨3132777879415768003763971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4177037172554357338351961 3132777879415768003763971)
                ·
                  refine ⟨4699166819123652005645957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3132777879415768003763971 4699166819123652005645957)
                  ·
                    refine ⟨881093778585684751058617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4699166819123652005645957 881093778585684751058617)
                    ·
                      refine ⟨660820333939263563293963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 881093778585684751058617 660820333939263563293963)
                      ·
                        rfl

theorem cell23_1286943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 1, 2, 1, 4, 2].length) (baseStart_1286943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1286943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1286943 prefixEnd_1286943 := by exact prefixLift 1286943
  have htrace : WordTrace (prefixWord ++ tailWord_1286943) baseStart_1286943 baseEnd_1286943 := by
    simpa [prefixWord, tailWord_1286943, baseEnd_1286943] using wordTrace_append hprefix tailTrace_1286943
  have hstable : (prefixWord ++ tailWord_1286943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1286943).length < 2 ^ (prefixWord ++ tailWord_1286943).sum := by decide
  have hdescent : baseEnd_1286943 < baseStart_1286943 := by decide
  rcases family_descends (prefixWord ++ tailWord_1286943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1286946 : List Nat := [3, 3, 1, 1, 2, 2, 2, 1, 2, 1, 5]
def baseStart_1286946 : Nat := 118140960795 + 1286946 * 2 ^ 59
def prefixEnd_1286946 : Nat := 4983230072969 + 3 ^ 40 * 1286946 * 2
def baseEnd_1286946 : Nat := 660821874381227051556449

theorem tailTrace_1286946 : CollatzResearch.WordTrace tailWord_1286946 prefixEnd_1286946 660821874381227051556449 := by
  unfold tailWord_1286946
  simp only [CollatzResearch.WordTrace]
  refine ⟨11734694198905477430826173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31292517863747939815536461 11734694198905477430826173)
  ·
    refine ⟨4400510324589554036559815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11734694198905477430826173 4400510324589554036559815)
    ·
      refine ⟨6600765486884331054839723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4400510324589554036559815 6600765486884331054839723)
      ·
        refine ⟨9901148230326496582259585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6600765486884331054839723 9901148230326496582259585)
        ·
          refine ⟨7425861172744872436694689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9901148230326496582259585 7425861172744872436694689)
          ·
            refine ⟨5569395879558654327521017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7425861172744872436694689 5569395879558654327521017)
            ·
              refine ⟨4177046909668990745640763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5569395879558654327521017 4177046909668990745640763)
              ·
                refine ⟨6265570364503486118461145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4177046909668990745640763 6265570364503486118461145)
                ·
                  refine ⟨4699177773377614588845859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6265570364503486118461145 4699177773377614588845859)
                  ·
                    refine ⟨7048766660066421883268789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4699177773377614588845859 7048766660066421883268789)
                    ·
                      refine ⟨660821874381227051556449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7048766660066421883268789 660821874381227051556449)
                      ·
                        rfl

theorem cell23_1286946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 2, 1, 2, 1, 5].length) (baseStart_1286946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1286946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1286946 prefixEnd_1286946 := by exact prefixLift 1286946
  have htrace : WordTrace (prefixWord ++ tailWord_1286946) baseStart_1286946 baseEnd_1286946 := by
    simpa [prefixWord, tailWord_1286946, baseEnd_1286946] using wordTrace_append hprefix tailTrace_1286946
  have hstable : (prefixWord ++ tailWord_1286946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1286946).length < 2 ^ (prefixWord ++ tailWord_1286946).sum := by decide
  have hdescent : baseEnd_1286946 < baseStart_1286946 := by decide
  rcases family_descends (prefixWord ++ tailWord_1286946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1286973 : List Nat := [1, 4, 1, 4, 2, 1, 1, 1, 2, 2, 4]
def baseStart_1286973 : Nat := 118140960795 + 1286973 * 2 ^ 59
def prefixEnd_1286973 : Nat := 4983230072969 + 3 ^ 40 * 1286973 * 2
def baseEnd_1286973 : Nat := 660835738358898445918825

theorem tailTrace_1286973 : CollatzResearch.WordTrace tailWord_1286973 prefixEnd_1286973 660835738358898445918825 := by
  unfold tailWord_1286973
  simp only [CollatzResearch.WordTrace]
  refine ⟨46939761566524093334537573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31293174377682728889691715 46939761566524093334537573)
  ·
    refine ⟨8801205293723267500225795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 46939761566524093334537573 8801205293723267500225795)
    ·
      refine ⟨13201807940584901250338693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8801205293723267500225795 13201807940584901250338693)
      ·
        refine ⟨2475338988859668984438505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13201807940584901250338693 2475338988859668984438505)
        ·
          refine ⟨1856504241644751738328879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2475338988859668984438505 1856504241644751738328879)
          ·
            refine ⟨2784756362467127607493319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1856504241644751738328879 2784756362467127607493319)
            ·
              refine ⟨4177134543700691411239979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2784756362467127607493319 4177134543700691411239979)
              ·
                refine ⟨6265701815551037116859969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4177134543700691411239979 6265701815551037116859969)
                ·
                  refine ⟨4699276361663277837644977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6265701815551037116859969 4699276361663277837644977)
                  ·
                    refine ⟨3524457271247458378233733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4699276361663277837644977 3524457271247458378233733)
                    ·
                      refine ⟨660835738358898445918825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3524457271247458378233733 660835738358898445918825)
                      ·
                        rfl

theorem cell23_1286973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 1, 1, 2, 2, 4].length) (baseStart_1286973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1286973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1286973 prefixEnd_1286973 := by exact prefixLift 1286973
  have htrace : WordTrace (prefixWord ++ tailWord_1286973) baseStart_1286973 baseEnd_1286973 := by
    simpa [prefixWord, tailWord_1286973, baseEnd_1286973] using wordTrace_append hprefix tailTrace_1286973
  have hstable : (prefixWord ++ tailWord_1286973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1286973).length < 2 ^ (prefixWord ++ tailWord_1286973).sum := by decide
  have hdescent : baseEnd_1286973 < baseStart_1286973 := by decide
  rcases family_descends (prefixWord ++ tailWord_1286973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1286977 : List Nat := [1, 2, 5, 3, 1, 1, 2, 1, 1, 4, 2]
def baseStart_1286977 : Nat := 118140960795 + 1286977 * 2 ^ 59
def prefixEnd_1286977 : Nat := 4983230072969 + 3 ^ 40 * 1286977 * 2
def baseEnd_1286977 : Nat := 660837792281516430268807

theorem tailTrace_1286977 : CollatzResearch.WordTrace tailWord_1286977 prefixEnd_1286977 660837792281516430268807 := by
  unfold tailWord_1286977
  simp only [CollatzResearch.WordTrace]
  refine ⟨46939907458509602017683185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31293271639006401345122123 46939907458509602017683185)
  ·
    refine ⟨35204930593882201513262389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46939907458509602017683185 35204930593882201513262389)
    ·
      refine ⟨3300462243176456391868349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 35204930593882201513262389 3300462243176456391868349)
      ·
        refine ⟨1237673341191171146950631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3300462243176456391868349 1237673341191171146950631)
        ·
          refine ⟨1856510011786756720425947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1237673341191171146950631 1856510011786756720425947)
          ·
            refine ⟨2784765017680135080638921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1856510011786756720425947 2784765017680135080638921)
            ·
              refine ⟨2088573763260101310479191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2784765017680135080638921 2088573763260101310479191)
              ·
                refine ⟨3132860644890151965718787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2088573763260101310479191 3132860644890151965718787)
                ·
                  refine ⟨4699290967335227948578181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3132860644890151965718787 4699290967335227948578181)
                  ·
                    refine ⟨881117056375355240358409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4699290967335227948578181 881117056375355240358409)
                    ·
                      refine ⟨660837792281516430268807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 881117056375355240358409 660837792281516430268807)
                      ·
                        rfl

theorem cell23_1286977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 2, 1, 1, 4, 2].length) (baseStart_1286977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1286977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1286977 prefixEnd_1286977 := by exact prefixLift 1286977
  have htrace : WordTrace (prefixWord ++ tailWord_1286977) baseStart_1286977 baseEnd_1286977 := by
    simpa [prefixWord, tailWord_1286977, baseEnd_1286977] using wordTrace_append hprefix tailTrace_1286977
  have hstable : (prefixWord ++ tailWord_1286977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1286977).length < 2 ^ (prefixWord ++ tailWord_1286977).sum := by decide
  have hdescent : baseEnd_1286977 < baseStart_1286977 := by decide
  rcases family_descends (prefixWord ++ tailWord_1286977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1286979 : List Nat := [1, 1, 1, 3, 1, 4, 2, 2, 1, 7]
def baseStart_1286979 : Nat := 118140960795 + 1286979 * 2 ^ 59
def prefixEnd_1286979 : Nat := 4983230072969 + 3 ^ 40 * 1286979 * 2
def baseEnd_1286979 : Nat := 220279606414275140814599

theorem tailTrace_1286979 : CollatzResearch.WordTrace tailWord_1286979 prefixEnd_1286979 220279606414275140814599 := by
  unfold tailWord_1286979
  simp only [CollatzResearch.WordTrace]
  refine ⟨46939980404502356359255991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31293320269668237572837327 46939980404502356359255991)
  ·
    refine ⟨70409970606753534538883987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46939980404502356359255991 70409970606753534538883987)
    ·
      refine ⟨105614955910130301808325981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70409970606753534538883987 105614955910130301808325981)
      ·
        refine ⟨39605608466298863178122243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 105614955910130301808325981 39605608466298863178122243)
        ·
          refine ⟨59408412699448294767183365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39605608466298863178122243 59408412699448294767183365)
          ·
            refine ⟨11139077381146555268846881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 59408412699448294767183365 11139077381146555268846881)
            ·
              refine ⟨8354308035859916451635161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11139077381146555268846881 8354308035859916451635161)
              ·
                refine ⟨6265731026894937338726371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8354308035859916451635161 6265731026894937338726371)
                ·
                  refine ⟨9398596540342406008089557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6265731026894937338726371 9398596540342406008089557)
                  ·
                    refine ⟨220279606414275140814599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 9398596540342406008089557 220279606414275140814599)
                    ·
                      rfl

theorem cell23_1286979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 2, 2, 1, 7].length) (baseStart_1286979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1286979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1286979 prefixEnd_1286979 := by exact prefixLift 1286979
  have htrace : WordTrace (prefixWord ++ tailWord_1286979) baseStart_1286979 baseEnd_1286979 := by
    simpa [prefixWord, tailWord_1286979, baseEnd_1286979] using wordTrace_append hprefix tailTrace_1286979
  have hstable : (prefixWord ++ tailWord_1286979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1286979).length < 2 ^ (prefixWord ++ tailWord_1286979).sum := by decide
  have hdescent : baseEnd_1286979 < baseStart_1286979 := by decide
  rcases family_descends (prefixWord ++ tailWord_1286979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1287019 : List Nat := [1, 1, 1, 1, 2, 2, 4, 1, 2, 3, 5]
def baseStart_1287019 : Nat := 118140960795 + 1287019 * 2 ^ 59
def prefixEnd_1287019 : Nat := 4983230072969 + 3 ^ 40 * 1287019 * 2
def baseEnd_1287019 : Nat := 660859358469005265943613

theorem tailTrace_1287019 : CollatzResearch.WordTrace tailWord_1287019 prefixEnd_1287019 660859358469005265943613 := by
  unfold tailWord_1287019
  simp only [CollatzResearch.WordTrace]
  refine ⟨46941439324357443190712111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31294292882904962127141407 46941439324357443190712111)
  ·
    refine ⟨70412158986536164786068167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46941439324357443190712111 70412158986536164786068167)
    ·
      refine ⟨105618238479804247179102251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70412158986536164786068167 105618238479804247179102251)
      ·
        refine ⟨158427357719706370768653377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105618238479804247179102251 158427357719706370768653377)
        ·
          refine ⟨118820518289779778076490033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 158427357719706370768653377 118820518289779778076490033)
          ·
            refine ⟨89115388717334833557367525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 118820518289779778076490033 89115388717334833557367525)
            ·
              refine ⟨16709135384500281292006411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 89115388717334833557367525 16709135384500281292006411)
              ·
                refine ⟨25063703076750421938009617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16709135384500281292006411 25063703076750421938009617)
                ·
                  refine ⟨18797777307562816453507213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25063703076750421938009617 18797777307562816453507213)
                  ·
                    refine ⟨7049166490336056170065205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18797777307562816453507213 7049166490336056170065205)
                    ·
                      refine ⟨660859358469005265943613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7049166490336056170065205 660859358469005265943613)
                      ·
                        rfl

theorem cell23_1287019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 1, 2, 3, 5].length) (baseStart_1287019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1287019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1287019 prefixEnd_1287019 := by exact prefixLift 1287019
  have htrace : WordTrace (prefixWord ++ tailWord_1287019) baseStart_1287019 baseEnd_1287019 := by
    simpa [prefixWord, tailWord_1287019, baseEnd_1287019] using wordTrace_append hprefix tailTrace_1287019
  have hstable : (prefixWord ++ tailWord_1287019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1287019).length < 2 ^ (prefixWord ++ tailWord_1287019).sum := by decide
  have hdescent : baseEnd_1287019 < baseStart_1287019 := by decide
  rcases family_descends (prefixWord ++ tailWord_1287019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1287033 : List Nat := [1, 2, 1, 3, 2, 3, 2, 1, 2, 4, 2]
def baseStart_1287033 : Nat := 118140960795 + 1287033 * 2 ^ 59
def prefixEnd_1287033 : Nat := 4983230072969 + 3 ^ 40 * 1287033 * 2
def baseEnd_1287033 : Nat := 660866547198168211168549

theorem tailTrace_1287033 : CollatzResearch.WordTrace tailWord_1287033 prefixEnd_1287033 660866547198168211168549 := by
  unfold tailWord_1287033
  simp only [CollatzResearch.WordTrace]
  refine ⟨46941949946306723581721753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31294633297537815721147835 46941949946306723581721753)
  ·
    refine ⟨35206462459730042686291315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46941949946306723581721753 35206462459730042686291315)
    ·
      refine ⟨52809693689595064029436973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35206462459730042686291315 52809693689595064029436973)
      ·
        refine ⟨19803635133598149011038865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52809693689595064029436973 19803635133598149011038865)
        ·
          refine ⟨14852726350198611758279149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19803635133598149011038865 14852726350198611758279149)
          ·
            refine ⟨5569772381324479409354681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14852726350198611758279149 5569772381324479409354681)
            ·
              refine ⟨4177329285993359557016011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5569772381324479409354681 4177329285993359557016011)
              ·
                refine ⟨6265993928990039335524017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4177329285993359557016011 6265993928990039335524017)
                ·
                  refine ⟨4699495446742529501643013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6265993928990039335524017 4699495446742529501643013)
                  ·
                    refine ⟨881155396264224281558065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4699495446742529501643013 881155396264224281558065)
                    ·
                      refine ⟨660866547198168211168549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 881155396264224281558065 660866547198168211168549)
                      ·
                        rfl

theorem cell23_1287033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 2, 1, 2, 4, 2].length) (baseStart_1287033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1287033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1287033 prefixEnd_1287033 := by exact prefixLift 1287033
  have htrace : WordTrace (prefixWord ++ tailWord_1287033) baseStart_1287033 baseEnd_1287033 := by
    simpa [prefixWord, tailWord_1287033, baseEnd_1287033] using wordTrace_append hprefix tailTrace_1287033
  have hstable : (prefixWord ++ tailWord_1287033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1287033).length < 2 ^ (prefixWord ++ tailWord_1287033).sum := by decide
  have hdescent : baseEnd_1287033 < baseStart_1287033 := by decide
  rcases family_descends (prefixWord ++ tailWord_1287033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1287059 : List Nat := [1, 1, 1, 2, 1, 2, 1, 4, 1, 1, 8]
def baseStart_1287059 : Nat := 118140960795 + 1287059 * 2 ^ 59
def prefixEnd_1287059 : Nat := 4983230072969 + 3 ^ 40 * 1287059 * 2
def baseEnd_1287059 : Nat := 660879897695185109443429

theorem tailTrace_1287059 : CollatzResearch.WordTrace tailWord_1287059 prefixEnd_1287059 660879897695185109443429 := by
  unfold tailWord_1287059
  simp only [CollatzResearch.WordTrace]
  refine ⟨46942898244212530022168231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31295265496141686681445487 46942898244212530022168231)
  ·
    refine ⟨70414347366318795033252347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46942898244212530022168231 70414347366318795033252347)
    ·
      refine ⟨105621521049478192549878521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70414347366318795033252347 105621521049478192549878521)
      ·
        refine ⟨79216140787108644412408891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 105621521049478192549878521 79216140787108644412408891)
        ·
          refine ⟨118824211180662966618613337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79216140787108644412408891 118824211180662966618613337)
          ·
            refine ⟨89118158385497224963960003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 118824211180662966618613337 89118158385497224963960003)
            ·
              refine ⟨133677237578245837445940005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 89118158385497224963960003 133677237578245837445940005)
              ·
                refine ⟨25064482045921094521113751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 133677237578245837445940005 25064482045921094521113751)
                ·
                  refine ⟨37596723068881641781670627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25064482045921094521113751 37596723068881641781670627)
                  ·
                    refine ⟨56395084603322462672505941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 37596723068881641781670627 56395084603322462672505941)
                    ·
                      refine ⟨660879897695185109443429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 56395084603322462672505941 660879897695185109443429)
                      ·
                        rfl

theorem cell23_1287059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 4, 1, 1, 8].length) (baseStart_1287059 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1287059 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1287059 prefixEnd_1287059 := by exact prefixLift 1287059
  have htrace : WordTrace (prefixWord ++ tailWord_1287059) baseStart_1287059 baseEnd_1287059 := by
    simpa [prefixWord, tailWord_1287059, baseEnd_1287059] using wordTrace_append hprefix tailTrace_1287059
  have hstable : (prefixWord ++ tailWord_1287059).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1287059).length < 2 ^ (prefixWord ++ tailWord_1287059).sum := by decide
  have hdescent : baseEnd_1287059 < baseStart_1287059 := by decide
  rcases family_descends (prefixWord ++ tailWord_1287059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1287150 : List Nat := [4, 1, 2, 1, 4, 1, 2, 1, 1, 6]
def baseStart_1287150 : Nat := 118140960795 + 1287150 * 2 ^ 59
def prefixEnd_1287150 : Nat := 4983230072969 + 3 ^ 40 * 1287150 * 2
def baseEnd_1287150 : Nat := 220308874811581417801837

theorem tailTrace_1287150 : CollatzResearch.WordTrace tailWord_1287150 prefixEnd_1287150 220308874811581417801837 := by
  unfold tailWord_1287150
  simp only [CollatzResearch.WordTrace]
  refine ⟨5868277160860356570466363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 31297478191255235042487269 5868277160860356570466363)
  ·
    refine ⟨8802415741290534855699545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5868277160860356570466363 8802415741290534855699545)
    ·
      refine ⟨6601811805967901141774659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8802415741290534855699545 6601811805967901141774659)
      ·
        refine ⟨9902717708951851712661989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6601811805967901141774659 9902717708951851712661989)
        ·
          refine ⟨1856759570428472196124123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9902717708951851712661989 1856759570428472196124123)
          ·
            refine ⟨2785139355642708294186185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1856759570428472196124123 2785139355642708294186185)
            ·
              refine ⟨2088854516732031220639639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2785139355642708294186185 2088854516732031220639639)
              ·
                refine ⟨3133281775098046830959459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2088854516732031220639639 3133281775098046830959459)
                ·
                  refine ⟨4699922662647070246439189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3133281775098046830959459 4699922662647070246439189)
                  ·
                    refine ⟨220308874811581417801837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4699922662647070246439189 220308874811581417801837)
                    ·
                      rfl

theorem cell23_1287150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 2, 1, 1, 6].length) (baseStart_1287150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1287150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1287150 prefixEnd_1287150 := by exact prefixLift 1287150
  have htrace : WordTrace (prefixWord ++ tailWord_1287150) baseStart_1287150 baseEnd_1287150 := by
    simpa [prefixWord, tailWord_1287150, baseEnd_1287150] using wordTrace_append hprefix tailTrace_1287150
  have hstable : (prefixWord ++ tailWord_1287150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1287150).length < 2 ^ (prefixWord ++ tailWord_1287150).sum := by decide
  have hdescent : baseEnd_1287150 < baseStart_1287150 := by decide
  rcases family_descends (prefixWord ++ tailWord_1287150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1287153 : List Nat := [1, 2, 2, 2, 4, 1, 1, 3, 1, 2, 4]
def baseStart_1287153 : Nat := 118140960795 + 1287153 * 2 ^ 59
def prefixEnd_1287153 : Nat := 4983230072969 + 3 ^ 40 * 1287153 * 2
def baseEnd_1287153 : Nat := 660928164876707741667997

theorem tailTrace_1287153 : CollatzResearch.WordTrace tailWord_1287153 prefixEnd_1287153 660928164876707741667997 := by
  unfold tailWord_1287153
  simp only [CollatzResearch.WordTrace]
  refine ⟨46946326705871984076090113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31297551137247989384060075 46946326705871984076090113)
  ·
    refine ⟨35209745029403988057067585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46946326705871984076090113 35209745029403988057067585)
    ·
      refine ⟨26407308772052991042800689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35209745029403988057067585 26407308772052991042800689)
      ·
        refine ⟨19805481579039743282100517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26407308772052991042800689 19805481579039743282100517)
        ·
          refine ⟨3713527796069951865393847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19805481579039743282100517 3713527796069951865393847)
          ·
            refine ⟨5570291694104927798090771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3713527796069951865393847 5570291694104927798090771)
            ·
              refine ⟨8355437541157391697136157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5570291694104927798090771 8355437541157391697136157)
              ·
                refine ⟨3133289077934021886426059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8355437541157391697136157 3133289077934021886426059)
                ·
                  refine ⟨4699933616901032829639089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3133289077934021886426059 4699933616901032829639089)
                  ·
                    refine ⟨3524950212675774622229317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4699933616901032829639089 3524950212675774622229317)
                    ·
                      refine ⟨660928164876707741667997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3524950212675774622229317 660928164876707741667997)
                      ·
                        rfl

theorem cell23_1287153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 1, 3, 1, 2, 4].length) (baseStart_1287153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1287153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1287153 prefixEnd_1287153 := by exact prefixLift 1287153
  have htrace : WordTrace (prefixWord ++ tailWord_1287153) baseStart_1287153 baseEnd_1287153 := by
    simpa [prefixWord, tailWord_1287153, baseEnd_1287153] using wordTrace_append hprefix tailTrace_1287153
  have hstable : (prefixWord ++ tailWord_1287153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1287153).length < 2 ^ (prefixWord ++ tailWord_1287153).sum := by decide
  have hdescent : baseEnd_1287153 < baseStart_1287153 := by decide
  rcases family_descends (prefixWord ++ tailWord_1287153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1287173 : List Nat := [1, 3, 1, 1, 2, 3, 1, 4, 1, 3, 3]
def baseStart_1287173 : Nat := 118140960795 + 1287173 * 2 ^ 59
def prefixEnd_1287173 : Nat := 4983230072969 + 3 ^ 40 * 1287173 * 2
def baseEnd_1287173 : Nat := 660938434489797663417905

theorem tailTrace_1287173 : CollatzResearch.WordTrace tailWord_1287173 prefixEnd_1287173 660938434489797663417905 := by
  unfold tailWord_1287173
  simp only [CollatzResearch.WordTrace]
  refine ⟨46947056165799527491818173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31298037443866351661212115 46947056165799527491818173)
  ·
    refine ⟨17605146062174822809431815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46947056165799527491818173 17605146062174822809431815)
    ·
      refine ⟨26407719093262234214147723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17605146062174822809431815 26407719093262234214147723)
      ·
        refine ⟨39611578639893351321221585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26407719093262234214147723 39611578639893351321221585)
        ·
          refine ⟨29708683979920013490916189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39611578639893351321221585 29708683979920013490916189)
          ·
            refine ⟨11140756492470005059093571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29708683979920013490916189 11140756492470005059093571)
            ·
              refine ⟨16711134738705007588640357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11140756492470005059093571 16711134738705007588640357)
              ·
                refine ⟨3133337763507188922870067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16711134738705007588640357 3133337763507188922870067)
                ·
                  refine ⟨4700006645260783384305101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3133337763507188922870067 4700006645260783384305101)
                  ·
                    refine ⟨1762502491972793769114413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4700006645260783384305101 1762502491972793769114413)
                    ·
                      refine ⟨660938434489797663417905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1762502491972793769114413 660938434489797663417905)
                      ·
                        rfl

theorem cell23_1287173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 4, 1, 3, 3].length) (baseStart_1287173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1287173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1287173 prefixEnd_1287173 := by exact prefixLift 1287173
  have htrace : WordTrace (prefixWord ++ tailWord_1287173) baseStart_1287173 baseEnd_1287173 := by
    simpa [prefixWord, tailWord_1287173, baseEnd_1287173] using wordTrace_append hprefix tailTrace_1287173
  have hstable : (prefixWord ++ tailWord_1287173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1287173).length < 2 ^ (prefixWord ++ tailWord_1287173).sum := by decide
  have hdescent : baseEnd_1287173 < baseStart_1287173 := by decide
  rcases family_descends (prefixWord ++ tailWord_1287173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1287207 : List Nat := [1, 1, 7, 1, 1, 1, 3, 1, 1, 3, 3]
def baseStart_1287207 : Nat := 118140960795 + 1287207 * 2 ^ 59
def prefixEnd_1287207 : Nat := 4983230072969 + 3 ^ 40 * 1287207 * 2
def baseEnd_1287207 : Nat := 660955892832050530392749

theorem tailTrace_1287207 : CollatzResearch.WordTrace tailWord_1287207 prefixEnd_1287207 660955892832050530392749 := by
  unfold tailWord_1287207
  simp only [CollatzResearch.WordTrace]
  refine ⟨46948296247676351298555875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31298864165117567532370583 46948296247676351298555875)
  ·
    refine ⟨70422444371514526947833813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46948296247676351298555875 70422444371514526947833813)
    ·
      refine ⟨1650526039957371725339855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 70422444371514526947833813 1650526039957371725339855)
      ·
        refine ⟨2475789059936057588009783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1650526039957371725339855 2475789059936057588009783)
        ·
          refine ⟨3713683589904086382014675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2475789059936057588009783 3713683589904086382014675)
          ·
            refine ⟨5570525384856129573022013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3713683589904086382014675 5570525384856129573022013)
            ·
              refine ⟨2088947019321048589883255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5570525384856129573022013 2088947019321048589883255)
              ·
                refine ⟨3133420528981572884824883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2088947019321048589883255 3133420528981572884824883)
                ·
                  refine ⟨4700130793472359327237325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3133420528981572884824883 4700130793472359327237325)
                  ·
                    refine ⟨1762549047552134747713997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4700130793472359327237325 1762549047552134747713997)
                    ·
                      refine ⟨660955892832050530392749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1762549047552134747713997 660955892832050530392749)
                      ·
                        rfl

theorem cell23_1287207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 3, 1, 1, 3, 3].length) (baseStart_1287207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1287207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1287207 prefixEnd_1287207 := by exact prefixLift 1287207
  have htrace : WordTrace (prefixWord ++ tailWord_1287207) baseStart_1287207 baseEnd_1287207 := by
    simpa [prefixWord, tailWord_1287207, baseEnd_1287207] using wordTrace_append hprefix tailTrace_1287207
  have hstable : (prefixWord ++ tailWord_1287207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1287207).length < 2 ^ (prefixWord ++ tailWord_1287207).sum := by decide
  have hdescent : baseEnd_1287207 < baseStart_1287207 := by decide
  rcases family_descends (prefixWord ++ tailWord_1287207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1287217 : List Nat := [1, 2, 2, 3, 1, 2, 4, 2, 1, 3, 2]
def baseStart_1287217 : Nat := 118140960795 + 1287217 * 2 ^ 59
def prefixEnd_1287217 : Nat := 4983230072969 + 3 ^ 40 * 1287217 * 2
def baseEnd_1287217 : Nat := 660961027638595491267703

theorem tailTrace_1287217 : CollatzResearch.WordTrace tailWord_1287217 prefixEnd_1287217 660961027638595491267703 := by
  unfold tailWord_1287217
  simp only [CollatzResearch.WordTrace]
  refine ⟨46948660977640123006419905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31299107318426748670946603 46948660977640123006419905)
  ·
    refine ⟨35211495733230092254814929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46948660977640123006419905 35211495733230092254814929)
    ·
      refine ⟨26408621799922569191111197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35211495733230092254814929 26408621799922569191111197)
      ·
        refine ⟨9903233174970963446666699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26408621799922569191111197 9903233174970963446666699)
        ·
          refine ⟨14854849762456445170000049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9903233174970963446666699 14854849762456445170000049)
          ·
            refine ⟨11141137321842333877500037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14854849762456445170000049 11141137321842333877500037)
            ·
              refine ⟨2088963247845437602031257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11141137321842333877500037 2088963247845437602031257)
              ·
                refine ⟨1566722435884078201523443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2088963247845437602031257 1566722435884078201523443)
                ·
                  refine ⟨2350083653826117302285165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1566722435884078201523443 2350083653826117302285165)
                  ·
                    refine ⟨881281370184793988356937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2350083653826117302285165 881281370184793988356937)
                    ·
                      refine ⟨660961027638595491267703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 881281370184793988356937 660961027638595491267703)
                      ·
                        rfl

theorem cell23_1287217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 4, 2, 1, 3, 2].length) (baseStart_1287217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1287217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1287217 prefixEnd_1287217 := by exact prefixLift 1287217
  have htrace : WordTrace (prefixWord ++ tailWord_1287217) baseStart_1287217 baseEnd_1287217 := by
    simpa [prefixWord, tailWord_1287217, baseEnd_1287217] using wordTrace_append hprefix tailTrace_1287217
  have hstable : (prefixWord ++ tailWord_1287217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1287217).length < 2 ^ (prefixWord ++ tailWord_1287217).sum := by decide
  have hdescent : baseEnd_1287217 < baseStart_1287217 := by decide
  rcases family_descends (prefixWord ++ tailWord_1287217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1287220 : List Nat := [2, 5, 1, 2, 1, 1, 1, 1, 2, 2, 5]
def baseStart_1287220 : Nat := 118140960795 + 1287220 * 2 ^ 59
def prefixEnd_1287220 : Nat := 4983230072969 + 3 ^ 40 * 1287220 * 2
def baseEnd_1287220 : Nat := 660962568080558979530189

theorem tailTrace_1287220 : CollatzResearch.WordTrace tailWord_1287220 prefixEnd_1287220 660962568080558979530189 := by
  unfold tailWord_1287220
  simp only [CollatzResearch.WordTrace]
  refine ⟨23474385198314627259389557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31299180264419503012519409 23474385198314627259389557)
  ·
    refine ⟨2200723612341996305567771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 23474385198314627259389557 2200723612341996305567771)
    ·
      refine ⟨3301085418512994458351657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2200723612341996305567771 3301085418512994458351657)
      ·
        refine ⟨2475814063884745843763743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3301085418512994458351657 2475814063884745843763743)
        ·
          refine ⟨3713721095827118765645615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2475814063884745843763743 3713721095827118765645615)
          ·
            refine ⟨5570581643740678148468423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3713721095827118765645615 5570581643740678148468423)
            ·
              refine ⟨8355872465611017222702635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5570581643740678148468423 8355872465611017222702635)
              ·
                refine ⟨12533808698416525834053953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8355872465611017222702635 12533808698416525834053953)
                ·
                  refine ⟨9400356523812394375540465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12533808698416525834053953 9400356523812394375540465)
                  ·
                    refine ⟨7050267392859295781655349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9400356523812394375540465 7050267392859295781655349)
                    ·
                      refine ⟨660962568080558979530189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7050267392859295781655349 660962568080558979530189)
                      ·
                        rfl

theorem cell23_1287220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 1, 1, 2, 2, 5].length) (baseStart_1287220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1287220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1287220 prefixEnd_1287220 := by exact prefixLift 1287220
  have htrace : WordTrace (prefixWord ++ tailWord_1287220) baseStart_1287220 baseEnd_1287220 := by
    simpa [prefixWord, tailWord_1287220, baseEnd_1287220] using wordTrace_append hprefix tailTrace_1287220
  have hstable : (prefixWord ++ tailWord_1287220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1287220).length < 2 ^ (prefixWord ++ tailWord_1287220).sum := by decide
  have hdescent : baseEnd_1287220 < baseStart_1287220 := by decide
  rcases family_descends (prefixWord ++ tailWord_1287220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1287263 : List Nat := [1, 1, 2, 3, 1, 1, 4, 1, 1, 5, 3]
def baseStart_1287263 : Nat := 118140960795 + 1287263 * 2 ^ 59
def prefixEnd_1287263 : Nat := 4983230072969 + 3 ^ 40 * 1287263 * 2
def baseEnd_1287263 : Nat := 660984647748702311292491

theorem tailTrace_1287263 : CollatzResearch.WordTrace tailWord_1287263 prefixEnd_1287263 660984647748702311292491 := by
  unfold tailWord_1287263
  simp only [CollatzResearch.WordTrace]
  refine ⟨46950338735473472862594443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31300225823648981908396295 46950338735473472862594443)
  ·
    refine ⟨70425508103210209293891665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46950338735473472862594443 70425508103210209293891665)
    ·
      refine ⟨52819131077407656970418749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70425508103210209293891665 52819131077407656970418749)
      ·
        refine ⟨19807174154027871363907031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52819131077407656970418749 19807174154027871363907031)
        ·
          refine ⟨29710761231041807045860547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19807174154027871363907031 29710761231041807045860547)
          ·
            refine ⟨44566141846562710568790821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29710761231041807045860547 44566141846562710568790821)
            ·
              refine ⟨8356151596230508231648279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 44566141846562710568790821 8356151596230508231648279)
              ·
                refine ⟨12534227394345762347472419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8356151596230508231648279 12534227394345762347472419)
                ·
                  refine ⟨18801341091518643521208629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12534227394345762347472419 18801341091518643521208629)
                  ·
                    refine ⟨1762625727329872830113309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 18801341091518643521208629 1762625727329872830113309)
                    ·
                      refine ⟨660984647748702311292491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1762625727329872830113309 660984647748702311292491)
                      ·
                        rfl

theorem cell23_1287263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 4, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 4, 1, 1, 5, 3].length) (baseStart_1287263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1287263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1287263 prefixEnd_1287263 := by exact prefixLift 1287263
  have htrace : WordTrace (prefixWord ++ tailWord_1287263) baseStart_1287263 baseEnd_1287263 := by
    simpa [prefixWord, tailWord_1287263, baseEnd_1287263] using wordTrace_append hprefix tailTrace_1287263
  have hstable : (prefixWord ++ tailWord_1287263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1287263).length < 2 ^ (prefixWord ++ tailWord_1287263).sum := by decide
  have hdescent : baseEnd_1287263 < baseStart_1287263 := by decide
  rcases family_descends (prefixWord ++ tailWord_1287263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1287293 : List Nat := [1, 4, 1, 1, 3, 1, 1, 1, 3, 2, 5]
def baseStart_1287293 : Nat := 118140960795 + 1287293 * 2 ^ 59
def prefixEnd_1287293 : Nat := 4983230072969 + 3 ^ 40 * 1287293 * 2
def baseEnd_1287293 : Nat := 661000052168337193917353

theorem tailTrace_1287293 : CollatzResearch.WordTrace tailWord_1287293 prefixEnd_1287293 661000052168337193917353 := by
  unfold tailWord_1287293
  simp only [CollatzResearch.WordTrace]
  refine ⟨46951432925364787986186533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31300955283576525324124355 46951432925364787986186533)
  ·
    refine ⟨8803393673505897747409975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 46951432925364787986186533 8803393673505897747409975)
    ·
      refine ⟨13205090510258846621114963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8803393673505897747409975 13205090510258846621114963)
      ·
        refine ⟨19807635765388269931672445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13205090510258846621114963 19807635765388269931672445)
        ·
          refine ⟨7427863412020601224377167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19807635765388269931672445 7427863412020601224377167)
          ·
            refine ⟨11141795118030901836565751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7427863412020601224377167 11141795118030901836565751)
            ·
              refine ⟨16712692677046352754848627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11141795118030901836565751 16712692677046352754848627)
              ·
                refine ⟨25069039015569529132272941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16712692677046352754848627 25069039015569529132272941)
                ·
                  refine ⟨9400889630838573424602353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25069039015569529132272941 9400889630838573424602353)
                  ·
                    refine ⟨7050667223128930068451765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9400889630838573424602353 7050667223128930068451765)
                    ·
                      refine ⟨661000052168337193917353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7050667223128930068451765 661000052168337193917353)
                      ·
                        rfl

theorem cell23_1287293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 1, 3, 2, 5].length) (baseStart_1287293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1287293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1287293 prefixEnd_1287293 := by exact prefixLift 1287293
  have htrace : WordTrace (prefixWord ++ tailWord_1287293) baseStart_1287293 baseEnd_1287293 := by
    simpa [prefixWord, tailWord_1287293, baseEnd_1287293] using wordTrace_append hprefix tailTrace_1287293
  have hstable : (prefixWord ++ tailWord_1287293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1287293).length < 2 ^ (prefixWord ++ tailWord_1287293).sum := by decide
  have hdescent : baseEnd_1287293 < baseStart_1287293 := by decide
  rcases family_descends (prefixWord ++ tailWord_1287293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1287300 : List Nat := [2, 3, 2, 1, 2, 2, 2, 2, 2, 5]
def baseStart_1287300 : Nat := 118140960795 + 1287300 * 2 ^ 59
def prefixEnd_1287300 : Nat := 4983230072969 + 3 ^ 40 * 1287300 * 2
def baseEnd_1287300 : Nat := 220334548844306222176607

theorem tailTrace_1287300 : CollatzResearch.WordTrace tailWord_1287300 prefixEnd_1287300 220334548844306222176607 := by
  unfold tailWord_1287300
  simp only [CollatzResearch.WordTrace]
  refine ⟨23475844118169714090845677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31301125490892952121127569 23475844118169714090845677)
  ·
    refine ⟨8803441544313642784067129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23475844118169714090845677 8803441544313642784067129)
    ·
      refine ⟨6602581158235232088050347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8803441544313642784067129 6602581158235232088050347)
      ·
        refine ⟨9903871737352848132075521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6602581158235232088050347 9903871737352848132075521)
        ·
          refine ⟨7427903803014636099056641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9903871737352848132075521 7427903803014636099056641)
          ·
            refine ⟨5570927852260977074292481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7427903803014636099056641 5570927852260977074292481)
            ·
              refine ⟨4178195889195732805719361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5570927852260977074292481 4178195889195732805719361)
              ·
                refine ⟨3133646916896799604289521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4178195889195732805719361 3133646916896799604289521)
                ·
                  refine ⟨2350235187672599703217141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3133646916896799604289521 2350235187672599703217141)
                  ·
                    refine ⟨220334548844306222176607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2350235187672599703217141 220334548844306222176607)
                    ·
                      rfl

theorem cell23_1287300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 2, 2, 2, 5].length) (baseStart_1287300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1287300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1287300 prefixEnd_1287300 := by exact prefixLift 1287300
  have htrace : WordTrace (prefixWord ++ tailWord_1287300) baseStart_1287300 baseEnd_1287300 := by
    simpa [prefixWord, tailWord_1287300, baseEnd_1287300] using wordTrace_append hprefix tailTrace_1287300
  have hstable : (prefixWord ++ tailWord_1287300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1287300).length < 2 ^ (prefixWord ++ tailWord_1287300).sum := by decide
  have hdescent : baseEnd_1287300 < baseStart_1287300 := by decide
  rcases family_descends (prefixWord ++ tailWord_1287300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1287303 : List Nat := [1, 1, 4, 2, 1, 1, 1, 2, 3, 3, 4]
def baseStart_1287303 : Nat := 118140960795 + 1287303 * 2 ^ 59
def prefixEnd_1287303 : Nat := 4983230072969 + 3 ^ 40 * 1287303 * 2
def baseEnd_1287303 : Nat := 661005186974882154792307

theorem tailTrace_1287303 : CollatzResearch.WordTrace tailWord_1287303 prefixEnd_1287303 661005186974882154792307 := by
  unfold tailWord_1287303
  simp only [CollatzResearch.WordTrace]
  refine ⟨46951797655328559694050563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31301198436885706462700375 46951797655328559694050563)
  ·
    refine ⟨70427696482992839541075845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46951797655328559694050563 70427696482992839541075845)
    ·
      refine ⟨13205193090561157413951721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 70427696482992839541075845 13205193090561157413951721)
      ·
        refine ⟨9903894817920868060463791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13205193090561157413951721 9903894817920868060463791)
        ·
          refine ⟨14855842226881302090695687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9903894817920868060463791 14855842226881302090695687)
          ·
            refine ⟨22283763340321953136043531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14855842226881302090695687 22283763340321953136043531)
            ·
              refine ⟨33425645010482929704065297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22283763340321953136043531 33425645010482929704065297)
              ·
                refine ⟨25069233757862197278048973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33425645010482929704065297 25069233757862197278048973)
                ·
                  refine ⟨9400962659198323979268365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25069233757862197278048973 9400962659198323979268365)
                  ·
                    refine ⟨3525360997199371492225637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9400962659198323979268365 3525360997199371492225637)
                    ·
                      refine ⟨661005186974882154792307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3525360997199371492225637 661005186974882154792307)
                      ·
                        rfl

theorem cell23_1287303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 2, 3, 3, 4].length) (baseStart_1287303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1287303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1287303 prefixEnd_1287303 := by exact prefixLift 1287303
  have htrace : WordTrace (prefixWord ++ tailWord_1287303) baseStart_1287303 baseEnd_1287303 := by
    simpa [prefixWord, tailWord_1287303, baseEnd_1287303] using wordTrace_append hprefix tailTrace_1287303
  have hstable : (prefixWord ++ tailWord_1287303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1287303).length < 2 ^ (prefixWord ++ tailWord_1287303).sum := by decide
  have hdescent : baseEnd_1287303 < baseStart_1287303 := by decide
  rcases family_descends (prefixWord ++ tailWord_1287303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1287310 : List Nat := [4, 1, 1, 3, 2, 1, 2, 1, 1, 2, 5]
def baseStart_1287310 : Nat := 118140960795 + 1287310 * 2 ^ 59
def prefixEnd_1287310 : Nat := 4983230072969 + 3 ^ 40 * 1287310 * 2
def baseEnd_1287310 : Nat := 661008781339463627404775

theorem tailTrace_1287310 : CollatzResearch.WordTrace tailWord_1287310 prefixEnd_1287310 661008781339463627404775 := by
  unfold tailWord_1287310
  simp only [CollatzResearch.WordTrace]
  refine ⟨5869006620787899986194423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 31301368644202133259703589 5869006620787899986194423)
  ·
    refine ⟨8803509931181849979291635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5869006620787899986194423 8803509931181849979291635)
    ·
      refine ⟨13205264896772774968937453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8803509931181849979291635 13205264896772774968937453)
      ·
        refine ⟨4951974336289790613351545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13205264896772774968937453 4951974336289790613351545)
        ·
          refine ⟨3713980752217342960013659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4951974336289790613351545 3713980752217342960013659)
          ·
            refine ⟨5570971128326014440020489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3713980752217342960013659 5570971128326014440020489)
            ·
              refine ⟨4178228346244510830015367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5570971128326014440020489 4178228346244510830015367)
              ·
                refine ⟨6267342519366766245023051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4178228346244510830015367 6267342519366766245023051)
                ·
                  refine ⟨9401013779050149367534577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6267342519366766245023051 9401013779050149367534577)
                  ·
                    refine ⟨7050760334287612025650933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9401013779050149367534577 7050760334287612025650933)
                    ·
                      refine ⟨661008781339463627404775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7050760334287612025650933 661008781339463627404775)
                      ·
                        rfl

theorem cell23_1287310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 2, 1, 1, 2, 5].length) (baseStart_1287310 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1287310 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1287310 prefixEnd_1287310 := by exact prefixLift 1287310
  have htrace : WordTrace (prefixWord ++ tailWord_1287310) baseStart_1287310 baseEnd_1287310 := by
    simpa [prefixWord, tailWord_1287310, baseEnd_1287310] using wordTrace_append hprefix tailTrace_1287310
  have hstable : (prefixWord ++ tailWord_1287310).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1287310).length < 2 ^ (prefixWord ++ tailWord_1287310).sum := by decide
  have hdescent : baseEnd_1287310 < baseStart_1287310 := by decide
  rcases family_descends (prefixWord ++ tailWord_1287310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1287340 : List Nat := [2, 2, 1, 1, 1, 1, 1, 7, 2, 2, 3]
def baseStart_1287340 : Nat := 118140960795 + 1287340 * 2 ^ 59
def prefixEnd_1287340 : Nat := 4983230072969 + 3 ^ 40 * 1287340 * 2
def baseEnd_1287340 : Nat := 661024185759098510029637

theorem tailTrace_1287340 : CollatzResearch.WordTrace tailWord_1287340 prefixEnd_1287340 661024185759098510029637 := by
  unfold tailWord_1287340
  simp only [CollatzResearch.WordTrace]
  refine ⟨23476573578097257506573737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31302098104129676675431649 23476573578097257506573737)
  ·
    refine ⟨17607430183572943129930303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23476573578097257506573737 17607430183572943129930303)
    ·
      refine ⟨26411145275359414694895455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17607430183572943129930303 26411145275359414694895455)
      ·
        refine ⟨39616717913039122042343183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26411145275359414694895455 39616717913039122042343183)
        ·
          refine ⟨59425076869558683063514775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39616717913039122042343183 59425076869558683063514775)
          ·
            refine ⟨89137615304338024595272163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59425076869558683063514775 89137615304338024595272163)
            ·
              refine ⟨133706422956507036892908245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 89137615304338024595272163 133706422956507036892908245)
              ·
                refine ⟨3133744288043133677177537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 133706422956507036892908245 3133744288043133677177537)
                ·
                  refine ⟨2350308216032350257883153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3133744288043133677177537 2350308216032350257883153)
                  ·
                    refine ⟨1762731162024262693412365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2350308216032350257883153 1762731162024262693412365)
                    ·
                      refine ⟨661024185759098510029637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1762731162024262693412365 661024185759098510029637)
                      ·
                        rfl

theorem cell23_1287340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 2, 3].length) (baseStart_1287340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1287340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1287340 prefixEnd_1287340 := by exact prefixLift 1287340
  have htrace : WordTrace (prefixWord ++ tailWord_1287340) baseStart_1287340 baseEnd_1287340 := by
    simpa [prefixWord, tailWord_1287340, baseEnd_1287340] using wordTrace_append hprefix tailTrace_1287340
  have hstable : (prefixWord ++ tailWord_1287340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1287340).length < 2 ^ (prefixWord ++ tailWord_1287340).sum := by decide
  have hdescent : baseEnd_1287340 < baseStart_1287340 := by decide
  rcases family_descends (prefixWord ++ tailWord_1287340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1287347 : List Nat := [1, 1, 1, 2, 3, 2, 3, 5, 1, 4]
def baseStart_1287347 : Nat := 118140960795 + 1287347 * 2 ^ 59
def prefixEnd_1287347 : Nat := 4983230072969 + 3 ^ 40 * 1287347 * 2
def baseEnd_1287347 : Nat := 220342593374559994214035

theorem tailTrace_1287347 : CollatzResearch.WordTrace tailWord_1287347 prefixEnd_1287347 220342593374559994214035 := by
  unfold tailWord_1287347
  simp only [CollatzResearch.WordTrace]
  refine ⟨46953402467169155208652295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31302268311446103472434863 46953402467169155208652295)
  ·
    refine ⟨70430103700753732812978443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46953402467169155208652295 70430103700753732812978443)
    ·
      refine ⟨105645155551130599219467665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70430103700753732812978443 105645155551130599219467665)
      ·
        refine ⟨79233866663347949414600749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 105645155551130599219467665 79233866663347949414600749)
        ·
          refine ⟨29712699998755481030475281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 79233866663347949414600749 29712699998755481030475281)
          ·
            refine ⟨22284524999066610772856461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29712699998755481030475281 22284524999066610772856461)
            ·
              refine ⟨8356696874649979039821173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22284524999066610772856461 8356696874649979039821173)
              ·
                refine ⟨783440331998435534983235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8356696874649979039821173 783440331998435534983235)
                ·
                  refine ⟨1175160497997653302474853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 783440331998435534983235 1175160497997653302474853)
                  ·
                    refine ⟨220342593374559994214035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1175160497997653302474853 220342593374559994214035)
                    ·
                      rfl

theorem cell23_1287347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 3, 5, 1, 4].length) (baseStart_1287347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1287347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1287347 prefixEnd_1287347 := by exact prefixLift 1287347
  have htrace : WordTrace (prefixWord ++ tailWord_1287347) baseStart_1287347 baseEnd_1287347 := by
    simpa [prefixWord, tailWord_1287347, baseEnd_1287347] using wordTrace_append hprefix tailTrace_1287347
  have hstable : (prefixWord ++ tailWord_1287347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1287347).length < 2 ^ (prefixWord ++ tailWord_1287347).sum := by decide
  have hdescent : baseEnd_1287347 < baseStart_1287347 := by decide
  rcases family_descends (prefixWord ++ tailWord_1287347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1287360 : List Nat := [2, 1, 1, 2, 6, 1, 1, 1, 8]
def baseStart_1287360 : Nat := 118140960795 + 1287360 * 2 ^ 59
def prefixEnd_1287360 : Nat := 4983230072969 + 3 ^ 40 * 1287360 * 2
def baseEnd_1287360 : Nat := 73448272819132047975505

theorem tailTrace_1287360 : CollatzResearch.WordTrace tailWord_1287360 prefixEnd_1287360 73448272819132047975505 := by
  unfold tailWord_1287360
  simp only [CollatzResearch.WordTrace]
  refine ⟨23476938308061029214437767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31302584410748038952583689 23476938308061029214437767)
  ·
    refine ⟨35215407462091543821656651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23476938308061029214437767 35215407462091543821656651)
    ·
      refine ⟨52823111193137315732484977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35215407462091543821656651 52823111193137315732484977)
      ·
        refine ⟨39617333394852986799363733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52823111193137315732484977 39617333394852986799363733)
        ·
          refine ⟨1857062502883733756220175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 39617333394852986799363733 1857062502883733756220175)
          ·
            refine ⟨2785593754325600634330263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1857062502883733756220175 2785593754325600634330263)
            ·
              refine ⟨4178390631488400951495395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2785593754325600634330263 4178390631488400951495395)
              ·
                refine ⟨6267585947232601427243093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4178390631488400951495395 6267585947232601427243093)
                ·
                  refine ⟨73448272819132047975505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 6267585947232601427243093 73448272819132047975505)
                  ·
                    rfl

theorem cell23_1287360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 1, 1, 8].length) (baseStart_1287360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1287360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1287360 prefixEnd_1287360 := by exact prefixLift 1287360
  have htrace : WordTrace (prefixWord ++ tailWord_1287360) baseStart_1287360 baseEnd_1287360 := by
    simpa [prefixWord, tailWord_1287360, baseEnd_1287360] using wordTrace_append hprefix tailTrace_1287360
  have hstable : (prefixWord ++ tailWord_1287360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1287360).length < 2 ^ (prefixWord ++ tailWord_1287360).sum := by decide
  have hdescent : baseEnd_1287360 < baseStart_1287360 := by decide
  rcases family_descends (prefixWord ++ tailWord_1287360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1287364 : List Nat := [2, 3, 3, 1, 3, 1, 2, 1, 3, 4]
def baseStart_1287364 : Nat := 118140960795 + 1287364 * 2 ^ 59
def prefixEnd_1287364 : Nat := 4983230072969 + 3 ^ 40 * 1287364 * 2
def baseEnd_1287364 : Nat := 220345503098268805376509

theorem tailTrace_1287364 : CollatzResearch.WordTrace tailWord_1287364 prefixEnd_1287364 220345503098268805376509 := by
  unfold tailWord_1287364
  simp only [CollatzResearch.WordTrace]
  refine ⟨23477011254053783556010573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31302681672071711408014097 23477011254053783556010573)
  ·
    refine ⟨8803879220270168833503965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23477011254053783556010573 8803879220270168833503965)
    ·
      refine ⟨3301454707601313312563987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8803879220270168833503965 3301454707601313312563987)
      ·
        refine ⟨4952182061401969968845981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3301454707601313312563987 4952182061401969968845981)
        ·
          refine ⟨1857068273025738738317243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4952182061401969968845981 1857068273025738738317243)
          ·
            refine ⟨2785602409538608107475865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1857068273025738738317243 2785602409538608107475865)
            ·
              refine ⟨2089201807153956080606899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2785602409538608107475865 2089201807153956080606899)
              ·
                refine ⟨3133802710730934120910349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2089201807153956080606899 3133802710730934120910349)
                ·
                  refine ⟨1175176016524100295341381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3133802710730934120910349 1175176016524100295341381)
                  ·
                    refine ⟨220345503098268805376509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1175176016524100295341381 220345503098268805376509)
                    ·
                      rfl

theorem cell23_1287364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 2, 1, 3, 4].length) (baseStart_1287364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1287364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1287364 prefixEnd_1287364 := by exact prefixLift 1287364
  have htrace : WordTrace (prefixWord ++ tailWord_1287364) baseStart_1287364 baseEnd_1287364 := by
    simpa [prefixWord, tailWord_1287364, baseEnd_1287364] using wordTrace_append hprefix tailTrace_1287364
  have hstable : (prefixWord ++ tailWord_1287364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1287364).length < 2 ^ (prefixWord ++ tailWord_1287364).sum := by decide
  have hdescent : baseEnd_1287364 < baseStart_1287364 := by decide
  rcases family_descends (prefixWord ++ tailWord_1287364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1287383 : List Nat := [1, 1, 3, 2, 1, 2, 2, 1, 2, 1, 7]
def baseStart_1287383 : Nat := 118140960795 + 1287383 * 2 ^ 59
def prefixEnd_1287383 : Nat := 4983230072969 + 3 ^ 40 * 1287383 * 2
def baseEnd_1287383 : Nat := 661046265427241841791939

theorem tailTrace_1287383 : CollatzResearch.WordTrace tailWord_1287383 prefixEnd_1287383 661046265427241841791939 := by
  unfold tailWord_1287383
  simp only [CollatzResearch.WordTrace]
  refine ⟨46954715495038733356962803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31303143663359155571308535 46954715495038733356962803)
  ·
    refine ⟨70432073242558100035444205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46954715495038733356962803 70432073242558100035444205)
    ·
      refine ⟨26412027465959287513291577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 70432073242558100035444205 26412027465959287513291577)
      ·
        refine ⟨19809020599469465634968683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26412027465959287513291577 19809020599469465634968683)
        ·
          refine ⟨29713530899204198452453025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19809020599469465634968683 29713530899204198452453025)
          ·
            refine ⟨22285148174403148839339769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29713530899204198452453025 22285148174403148839339769)
            ·
              refine ⟨16713861130802361629504827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22285148174403148839339769 16713861130802361629504827)
              ·
                refine ⟨25070791696203542444257241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16713861130802361629504827 25070791696203542444257241)
                ·
                  refine ⟨18803093772152656833192931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25070791696203542444257241 18803093772152656833192931)
                  ·
                    refine ⟨28204640658228985249789397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18803093772152656833192931 28204640658228985249789397)
                    ·
                      refine ⟨661046265427241841791939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 28204640658228985249789397 661046265427241841791939)
                      ·
                        rfl

theorem cell23_1287383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 1, 2, 1, 7].length) (baseStart_1287383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1287383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1287383 prefixEnd_1287383 := by exact prefixLift 1287383
  have htrace : WordTrace (prefixWord ++ tailWord_1287383) baseStart_1287383 baseEnd_1287383 := by
    simpa [prefixWord, tailWord_1287383, baseEnd_1287383] using wordTrace_append hprefix tailTrace_1287383
  have hstable : (prefixWord ++ tailWord_1287383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1287383).length < 2 ^ (prefixWord ++ tailWord_1287383).sum := by decide
  have hdescent : baseEnd_1287383 < baseStart_1287383 := by decide
  rcases family_descends (prefixWord ++ tailWord_1287383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1287447 : List Nat := [1, 1, 3, 4, 1, 1, 3, 1, 3, 2, 3]
def baseStart_1287447 : Nat := 118140960795 + 1287447 * 2 ^ 59
def prefixEnd_1287447 : Nat := 4983230072969 + 3 ^ 40 * 1287447 * 2
def baseEnd_1287447 : Nat := 661079128189129591391645

theorem tailTrace_1287447 : CollatzResearch.WordTrace tailWord_1287447 prefixEnd_1287447 661079128189129591391645 := by
  unfold tailWord_1287447
  simp only [CollatzResearch.WordTrace]
  refine ⟨46957049766806872287292595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31304699844537914858195063 46957049766806872287292595)
  ·
    refine ⟨70435574650210308430938893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46957049766806872287292595 70435574650210308430938893)
    ·
      refine ⟨26413340493828865661602085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 70435574650210308430938893 26413340493828865661602085)
      ·
        refine ⟨4952501342592912311550391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26413340493828865661602085 4952501342592912311550391)
        ·
          refine ⟨7428752013889368467325587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4952501342592912311550391 7428752013889368467325587)
          ·
            refine ⟨11143128020834052700988381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7428752013889368467325587 11143128020834052700988381)
            ·
              refine ⟨4178673007812769762870643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11143128020834052700988381 4178673007812769762870643)
              ·
                refine ⟨6268009511719154644305965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4178673007812769762870643 6268009511719154644305965)
                ·
                  refine ⟨2350503566894682991614737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6268009511719154644305965 2350503566894682991614737)
                  ·
                    refine ⟨1762877675171012243711053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2350503566894682991614737 1762877675171012243711053)
                    ·
                      refine ⟨661079128189129591391645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1762877675171012243711053 661079128189129591391645)
                      ·
                        rfl

theorem cell23_1287447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 3, 1, 3, 2, 3].length) (baseStart_1287447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1287447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1287447 prefixEnd_1287447 := by exact prefixLift 1287447
  have htrace : WordTrace (prefixWord ++ tailWord_1287447) baseStart_1287447 baseEnd_1287447 := by
    simpa [prefixWord, tailWord_1287447, baseEnd_1287447] using wordTrace_append hprefix tailTrace_1287447
  have hstable : (prefixWord ++ tailWord_1287447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1287447).length < 2 ^ (prefixWord ++ tailWord_1287447).sum := by decide
  have hdescent : baseEnd_1287447 < baseStart_1287447 := by decide
  rcases family_descends (prefixWord ++ tailWord_1287447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1287450 : List Nat := [3, 1, 1, 3, 3, 1, 2, 9]
def baseStart_1287450 : Nat := 118140960795 + 1287450 * 2 ^ 59
def prefixEnd_1287450 : Nat := 4983230072969 + 3 ^ 40 * 1287450 * 2
def baseEnd_1287450 : Nat := 24484469208559002950153

theorem tailTrace_1287450 : CollatzResearch.WordTrace tailWord_1287450 prefixEnd_1287450 24484469208559002950153 := by
  unfold tailWord_1287450
  simp only [CollatzResearch.WordTrace]
  refine ⟨11739289796449000949912951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31304772790530669199767869 11739289796449000949912951)
  ·
    refine ⟨17608934694673501424869427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11739289796449000949912951 17608934694673501424869427)
    ·
      refine ⟨26413402042010252137304141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17608934694673501424869427 26413402042010252137304141)
      ·
        refine ⟨9905025765753844551489053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26413402042010252137304141 9905025765753844551489053)
        ·
          refine ⟨3714384662157691706808395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9905025765753844551489053 3714384662157691706808395)
          ·
            refine ⟨5571576993236537560212593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3714384662157691706808395 5571576993236537560212593)
            ·
              refine ⟨4178682744927403170159445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5571576993236537560212593 4178682744927403170159445)
              ·
                refine ⟨24484469208559002950153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 4178682744927403170159445 24484469208559002950153)
                ·
                  rfl

theorem cell23_1287450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 2, 9].length) (baseStart_1287450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1287450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1287450 prefixEnd_1287450 := by exact prefixLift 1287450
  have htrace : WordTrace (prefixWord ++ tailWord_1287450) baseStart_1287450 baseEnd_1287450 := by
    simpa [prefixWord, tailWord_1287450, baseEnd_1287450] using wordTrace_append hprefix tailTrace_1287450
  have hstable : (prefixWord ++ tailWord_1287450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1287450).length < 2 ^ (prefixWord ++ tailWord_1287450).sum := by decide
  have hdescent : baseEnd_1287450 < baseStart_1287450 := by decide
  rcases family_descends (prefixWord ++ tailWord_1287450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1287464 : List Nat := [2, 1, 5, 1, 2, 3, 1, 1, 1, 1, 5]
def baseStart_1287464 : Nat := 118140960795 + 1287464 * 2 ^ 59
def prefixEnd_1287464 : Nat := 4983230072969 + 3 ^ 40 * 1287464 * 2
def baseEnd_1287464 : Nat := 661087857360256024879067

theorem tailTrace_1287464 : CollatzResearch.WordTrace tailWord_1287464 prefixEnd_1287464 661087857360256024879067 := by
  unfold tailWord_1287464
  simp only [CollatzResearch.WordTrace]
  refine ⟨23478834903872642095330723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31305113205163522793774297 23478834903872642095330723)
  ·
    refine ⟨35218252355808963142996085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23478834903872642095330723 35218252355808963142996085)
    ·
      refine ⟨3301711158357090294655883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 35218252355808963142996085 3301711158357090294655883)
      ·
        refine ⟨4952566737535635441983825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3301711158357090294655883 4952566737535635441983825)
        ·
          refine ⟨3714425053151726581487869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4952566737535635441983825 3714425053151726581487869)
          ·
            refine ⟨1392909394931897468057951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3714425053151726581487869 1392909394931897468057951)
            ·
              refine ⟨2089364092397846202086927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1392909394931897468057951 2089364092397846202086927)
              ·
                refine ⟨3134046138596769303130391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2089364092397846202086927 3134046138596769303130391)
                ·
                  refine ⟨4701069207895153954695587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3134046138596769303130391 4701069207895153954695587)
                  ·
                    refine ⟨7051603811842730932043381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4701069207895153954695587 7051603811842730932043381)
                    ·
                      refine ⟨661087857360256024879067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7051603811842730932043381 661087857360256024879067)
                      ·
                        rfl

theorem cell23_1287464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 3, 1, 1, 1, 1, 5].length) (baseStart_1287464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1287464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1287464 prefixEnd_1287464 := by exact prefixLift 1287464
  have htrace : WordTrace (prefixWord ++ tailWord_1287464) baseStart_1287464 baseEnd_1287464 := by
    simpa [prefixWord, tailWord_1287464, baseEnd_1287464] using wordTrace_append hprefix tailTrace_1287464
  have hstable : (prefixWord ++ tailWord_1287464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1287464).length < 2 ^ (prefixWord ++ tailWord_1287464).sum := by decide
  have hdescent : baseEnd_1287464 < baseStart_1287464 := by decide
  rcases family_descends (prefixWord ++ tailWord_1287464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1287501 : List Nat := [1, 6, 1, 3, 1, 1, 3, 7]
def baseStart_1287501 : Nat := 118140960795 + 1287501 * 2 ^ 59
def prefixEnd_1287501 : Nat := 4983230072969 + 3 ^ 40 * 1287501 * 2
def baseEnd_1287501 : Nat := 24485439116461940004311

theorem tailTrace_1287501 : CollatzResearch.WordTrace tailWord_1287501 prefixEnd_1287501 24485439116461940004311 := by
  unfold tailWord_1287501
  simp only [CollatzResearch.WordTrace]
  refine ⟨46959019308611239509758357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31306012872407493006505571 46959019308611239509758357)
  ·
    refine ⟨2201204030091151852019923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 46959019308611239509758357 2201204030091151852019923)
    ·
      refine ⟨3301806045136727778029885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2201204030091151852019923 3301806045136727778029885)
      ·
        refine ⟨1238177266926272916761207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3301806045136727778029885 1238177266926272916761207)
        ·
          refine ⟨1857265900389409375141811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1238177266926272916761207 1857265900389409375141811)
          ·
            refine ⟨2785898850584114062712717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1857265900389409375141811 2785898850584114062712717)
            ·
              refine ⟨1044712068969042773517269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2785898850584114062712717 1044712068969042773517269)
              ·
                refine ⟨24485439116461940004311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1044712068969042773517269 24485439116461940004311)
                ·
                  rfl

theorem cell23_1287501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 3, 7].length) (baseStart_1287501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1287501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1287501 prefixEnd_1287501 := by exact prefixLift 1287501
  have htrace : WordTrace (prefixWord ++ tailWord_1287501) baseStart_1287501 baseEnd_1287501 := by
    simpa [prefixWord, tailWord_1287501, baseEnd_1287501] using wordTrace_append hprefix tailTrace_1287501
  have hstable : (prefixWord ++ tailWord_1287501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1287501).length < 2 ^ (prefixWord ++ tailWord_1287501).sum := by decide
  have hdescent : baseEnd_1287501 < baseStart_1287501 := by decide
  rcases family_descends (prefixWord ++ tailWord_1287501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1287504 : List Nat := [2, 1, 1, 1, 1, 5, 2, 4, 1, 3, 2]
def baseStart_1287504 : Nat := 118140960795 + 1287504 * 2 ^ 59
def prefixEnd_1287504 : Nat := 4983230072969 + 3 ^ 40 * 1287504 * 2
def baseEnd_1287504 : Nat := 661108396586435868378883

theorem tailTrace_1287504 : CollatzResearch.WordTrace tailWord_1287504 prefixEnd_1287504 661108396586435868378883 := by
  unfold tailWord_1287504
  simp only [CollatzResearch.WordTrace]
  refine ⟨23479564363800185511058783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31306085818400247348078377 23479564363800185511058783)
  ·
    refine ⟨35219346545700278266588175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23479564363800185511058783 35219346545700278266588175)
    ·
      refine ⟨52829019818550417399882263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35219346545700278266588175 52829019818550417399882263)
      ·
        refine ⟨79243529727825626099823395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52829019818550417399882263 79243529727825626099823395)
        ·
          refine ⟨118865294591738439149735093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79243529727825626099823395 118865294591738439149735093)
          ·
            refine ⟨11143621367975478670287665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 118865294591738439149735093 11143621367975478670287665)
            ·
              refine ⟨8357716025981609002715749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11143621367975478670287665 8357716025981609002715749)
              ·
                refine ⟨1567071754871551688009203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8357716025981609002715749 1567071754871551688009203)
                ·
                  refine ⟨2350607632307327532013805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1567071754871551688009203 2350607632307327532013805)
                  ·
                    refine ⟨881477862115247824505177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2350607632307327532013805 881477862115247824505177)
                    ·
                      refine ⟨661108396586435868378883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 881477862115247824505177 661108396586435868378883)
                      ·
                        rfl

theorem cell23_1287504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 2, 4, 1, 3, 2].length) (baseStart_1287504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1287504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1287504 prefixEnd_1287504 := by exact prefixLift 1287504
  have htrace : WordTrace (prefixWord ++ tailWord_1287504) baseStart_1287504 baseEnd_1287504 := by
    simpa [prefixWord, tailWord_1287504, baseEnd_1287504] using wordTrace_append hprefix tailTrace_1287504
  have hstable : (prefixWord ++ tailWord_1287504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1287504).length < 2 ^ (prefixWord ++ tailWord_1287504).sum := by decide
  have hdescent : baseEnd_1287504 < baseStart_1287504 := by decide
  rcases family_descends (prefixWord ++ tailWord_1287504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1287528 : List Nat := [2, 1, 4, 2, 3, 2, 1, 2, 2, 1, 3]
def baseStart_1287528 : Nat := 118140960795 + 1287528 * 2 ^ 59
def prefixEnd_1287528 : Nat := 4983230072969 + 3 ^ 40 * 1287528 * 2
def baseEnd_1287528 : Nat := 661120720122143774478773

theorem tailTrace_1287528 : CollatzResearch.WordTrace tailWord_1287528 prefixEnd_1287528 661120720122143774478773 := by
  unfold tailWord_1287528
  simp only [CollatzResearch.WordTrace]
  refine ⟨23480002039756711560495619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31306669386342282080660825 23480002039756711560495619)
  ·
    refine ⟨35220003059635067340743429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23480002039756711560495619 35220003059635067340743429)
    ·
      refine ⟨6603750573681575126389393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 35220003059635067340743429 6603750573681575126389393)
      ·
        refine ⟨4952812930261181344792045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6603750573681575126389393 4952812930261181344792045)
        ·
          refine ⟨1857304848847943004297017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4952812930261181344792045 1857304848847943004297017)
          ·
            refine ⟨1392978636635957253222763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1857304848847943004297017 1392978636635957253222763)
            ·
              refine ⟨2089467954953935879834145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1392978636635957253222763 2089467954953935879834145)
              ·
                refine ⟨1567100966215451909875609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2089467954953935879834145 1567100966215451909875609)
                ·
                  refine ⟨1175325724661588932406707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1567100966215451909875609 1175325724661588932406707)
                  ·
                    refine ⟨1762988586992383398610061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1175325724661588932406707 1762988586992383398610061)
                    ·
                      refine ⟨661120720122143774478773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1762988586992383398610061 661120720122143774478773)
                      ·
                        rfl

theorem cell23_1287528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 2, 1, 2, 2, 1, 3].length) (baseStart_1287528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1287528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1287528 prefixEnd_1287528 := by exact prefixLift 1287528
  have htrace : WordTrace (prefixWord ++ tailWord_1287528) baseStart_1287528 baseEnd_1287528 := by
    simpa [prefixWord, tailWord_1287528, baseEnd_1287528] using wordTrace_append hprefix tailTrace_1287528
  have hstable : (prefixWord ++ tailWord_1287528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1287528).length < 2 ^ (prefixWord ++ tailWord_1287528).sum := by decide
  have hdescent : baseEnd_1287528 < baseStart_1287528 := by decide
  rcases family_descends (prefixWord ++ tailWord_1287528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1287587 : List Nat := [1, 1, 1, 4, 1, 3, 3, 2, 2, 5]
def baseStart_1287587 : Nat := 118140960795 + 1287587 * 2 ^ 59
def prefixEnd_1287587 : Nat := 4983230072969 + 3 ^ 40 * 1287587 * 2
def baseEnd_1287587 : Nat := 220383671826919681213667

theorem tailTrace_1287587 : CollatzResearch.WordTrace tailWord_1287587 prefixEnd_1287587 220383671826919681213667 := by
  unfold tailWord_1287587
  simp only [CollatzResearch.WordTrace]
  refine ⟨46962155986299676197389015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31308103990866450798259343 46962155986299676197389015)
  ·
    refine ⟨70443233979449514296083523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46962155986299676197389015 70443233979449514296083523)
    ·
      refine ⟨105664850969174271444125285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70443233979449514296083523 105664850969174271444125285)
      ·
        refine ⟨19812159556720175895773491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 105664850969174271444125285 19812159556720175895773491)
        ·
          refine ⟨29718239335080263843660237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19812159556720175895773491 29718239335080263843660237)
          ·
            refine ⟨11144339750655098941372589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29718239335080263843660237 11144339750655098941372589)
            ·
              refine ⟨4179127406495662103014721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11144339750655098941372589 4179127406495662103014721)
              ·
                refine ⟨3134345554871746577261041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4179127406495662103014721 3134345554871746577261041)
                ·
                  refine ⟨2350759166153809932945781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3134345554871746577261041 2350759166153809932945781)
                  ·
                    refine ⟨220383671826919681213667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2350759166153809932945781 220383671826919681213667)
                    ·
                      rfl

theorem cell23_1287587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 3, 2, 2, 5].length) (baseStart_1287587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1287587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1287587 prefixEnd_1287587 := by exact prefixLift 1287587
  have htrace : WordTrace (prefixWord ++ tailWord_1287587) baseStart_1287587 baseEnd_1287587 := by
    simpa [prefixWord, tailWord_1287587, baseEnd_1287587] using wordTrace_append hprefix tailTrace_1287587
  have hstable : (prefixWord ++ tailWord_1287587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1287587).length < 2 ^ (prefixWord ++ tailWord_1287587).sum := by decide
  have hdescent : baseEnd_1287587 < baseStart_1287587 := by decide
  rcases family_descends (prefixWord ++ tailWord_1287587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1287591 : List Nat := [1, 1, 6, 1, 1, 1, 5, 2, 5]
def baseStart_1287591 : Nat := 118140960795 + 1287591 * 2 ^ 59
def prefixEnd_1287591 : Nat := 4983230072969 + 3 ^ 40 * 1287591 * 2
def baseEnd_1287591 : Nat := 73461452155930780887887

theorem tailTrace_1287591 : CollatzResearch.WordTrace tailWord_1287591 prefixEnd_1287591 73461452155930780887887 := by
  unfold tailWord_1287591
  simp only [CollatzResearch.WordTrace]
  refine ⟨46962301878285184880534627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31308201252190123253689751 46962301878285184880534627)
  ·
    refine ⟨70443452817427777320801941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46962301878285184880534627 70443452817427777320801941)
    ·
      refine ⟨3302036850816927061912591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 70443452817427777320801941 3302036850816927061912591)
      ·
        refine ⟨4953055276225390592868887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3302036850816927061912591 4953055276225390592868887)
        ·
          refine ⟨7429582914338085889303331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4953055276225390592868887 7429582914338085889303331)
          ·
            refine ⟨11144374371507128833954997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7429582914338085889303331 11144374371507128833954997)
            ·
              refine ⟨1044785097328793328183281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 11144374371507128833954997 1044785097328793328183281)
              ·
                refine ⟨783588822996594996137461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1044785097328793328183281 783588822996594996137461)
                ·
                  refine ⟨73461452155930780887887, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 783588822996594996137461 73461452155930780887887)
                  ·
                    rfl

theorem cell23_1287591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 5, 2, 5].length) (baseStart_1287591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1287591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1287591 prefixEnd_1287591 := by exact prefixLift 1287591
  have htrace : WordTrace (prefixWord ++ tailWord_1287591) baseStart_1287591 baseEnd_1287591 := by
    simpa [prefixWord, tailWord_1287591, baseEnd_1287591] using wordTrace_append hprefix tailTrace_1287591
  have hstable : (prefixWord ++ tailWord_1287591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1287591).length < 2 ^ (prefixWord ++ tailWord_1287591).sum := by decide
  have hdescent : baseEnd_1287591 < baseStart_1287591 := by decide
  rcases family_descends (prefixWord ++ tailWord_1287591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1287600 : List Nat := [2, 1, 1, 1, 2, 1, 1, 4, 2, 8]
def baseStart_1287600 : Nat := 118140960795 + 1287600 * 2 ^ 59
def prefixEnd_1287600 : Nat := 4983230072969 + 3 ^ 40 * 1287600 * 2
def baseEnd_1287600 : Nat := 220385896909755830926147

theorem tailTrace_1287600 : CollatzResearch.WordTrace tailWord_1287600 prefixEnd_1287600 220385896909755830926147 := by
  unfold tailWord_1287600
  simp only [CollatzResearch.WordTrace]
  refine ⟨23481315067626289708806127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31308420090168386278408169 23481315067626289708806127)
  ·
    refine ⟨35221972601439434563209191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23481315067626289708806127 35221972601439434563209191)
    ·
      refine ⟨52832958902159151844813787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35221972601439434563209191 52832958902159151844813787)
      ·
        refine ⟨79249438353238727767220681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52832958902159151844813787 79249438353238727767220681)
        ·
          refine ⟨59437078764929045825415511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79249438353238727767220681 59437078764929045825415511)
          ·
            refine ⟨89155618147393568738123267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59437078764929045825415511 89155618147393568738123267)
            ·
              refine ⟨133733427221090353107184901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 89155618147393568738123267 133733427221090353107184901)
              ·
                refine ⟨25075017603954441207597169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 133733427221090353107184901 25075017603954441207597169)
                ·
                  refine ⟨18806263202965830905697877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25075017603954441207597169 18806263202965830905697877)
                  ·
                    refine ⟨220385896909755830926147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 18806263202965830905697877 220385896909755830926147)
                    ·
                      rfl

theorem cell23_1287600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 4, 2, 8].length) (baseStart_1287600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1287600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1287600 prefixEnd_1287600 := by exact prefixLift 1287600
  have htrace : WordTrace (prefixWord ++ tailWord_1287600) baseStart_1287600 baseEnd_1287600 := by
    simpa [prefixWord, tailWord_1287600, baseEnd_1287600] using wordTrace_append hprefix tailTrace_1287600
  have hstable : (prefixWord ++ tailWord_1287600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1287600).length < 2 ^ (prefixWord ++ tailWord_1287600).sum := by decide
  have hdescent : baseEnd_1287600 < baseStart_1287600 := by decide
  rcases family_descends (prefixWord ++ tailWord_1287600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1287607 : List Nat := [1, 1, 3, 1, 3, 2, 1, 2, 4, 1, 4]
def baseStart_1287607 : Nat := 118140960795 + 1287607 * 2 ^ 59
def prefixEnd_1287607 : Nat := 4983230072969 + 3 ^ 40 * 1287607 * 2
def baseEnd_1287607 : Nat := 661161285093848965390909

theorem tailTrace_1287607 : CollatzResearch.WordTrace tailWord_1287607 prefixEnd_1287607 661161285093848965390909 := by
  unfold tailWord_1287607
  simp only [CollatzResearch.WordTrace]
  refine ⟨46962885446227219613117075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31308590297484813075411383 46962885446227219613117075)
  ·
    refine ⟨70444328169340829419675613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46962885446227219613117075 70444328169340829419675613)
    ·
      refine ⟨26416623063502811032378355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 70444328169340829419675613 26416623063502811032378355)
      ·
        refine ⟨39624934595254216548567533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26416623063502811032378355 39624934595254216548567533)
        ·
          refine ⟨14859350473220331205712825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39624934595254216548567533 14859350473220331205712825)
          ·
            refine ⟨11144512854915248404284619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14859350473220331205712825 11144512854915248404284619)
            ·
              refine ⟨16716769282372872606426929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11144512854915248404284619 16716769282372872606426929)
              ·
                refine ⟨12537576961779654454820197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16716769282372872606426929 12537576961779654454820197)
                ·
                  refine ⟨2350795680333685210278787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12537576961779654454820197 2350795680333685210278787)
                  ·
                    refine ⟨3526193520500527815418181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2350795680333685210278787 3526193520500527815418181)
                    ·
                      refine ⟨661161285093848965390909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3526193520500527815418181 661161285093848965390909)
                      ·
                        rfl

theorem cell23_1287607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 2, 4, 1, 4].length) (baseStart_1287607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1287607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1287607 prefixEnd_1287607 := by exact prefixLift 1287607
  have htrace : WordTrace (prefixWord ++ tailWord_1287607) baseStart_1287607 baseEnd_1287607 := by
    simpa [prefixWord, tailWord_1287607, baseEnd_1287607] using wordTrace_append hprefix tailTrace_1287607
  have hstable : (prefixWord ++ tailWord_1287607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1287607).length < 2 ^ (prefixWord ++ tailWord_1287607).sum := by decide
  have hdescent : baseEnd_1287607 < baseStart_1287607 := by decide
  rcases family_descends (prefixWord ++ tailWord_1287607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1287624 : List Nat := [2, 1, 3, 1, 3, 1, 4, 1, 2, 1, 4]
def baseStart_1287624 : Nat := 118140960795 + 1287624 * 2 ^ 59
def prefixEnd_1287624 : Nat := 4983230072969 + 3 ^ 40 * 1287624 * 2
def baseEnd_1287624 : Nat := 661170014264975398878331

theorem tailTrace_1287624 : CollatzResearch.WordTrace tailWord_1287624 prefixEnd_1287624 661170014264975398878331 := by
  unfold tailWord_1287624
  simp only [CollatzResearch.WordTrace]
  refine ⟨23481752743582815758242963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31309003658110421010990617 23481752743582815758242963)
  ·
    refine ⟨35222629115374223637364445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23481752743582815758242963 35222629115374223637364445)
    ·
      refine ⟨13208485918265333864011667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35222629115374223637364445 13208485918265333864011667)
      ·
        refine ⟨19812728877398000796017501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13208485918265333864011667 19812728877398000796017501)
        ·
          refine ⟨7429773329024250298506563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19812728877398000796017501 7429773329024250298506563)
          ·
            refine ⟨11144659993536375447759845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7429773329024250298506563 11144659993536375447759845)
            ·
              refine ⟨2089623748788070396454971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11144659993536375447759845 2089623748788070396454971)
              ·
                refine ⟨3134435623182105594682457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2089623748788070396454971 3134435623182105594682457)
                ·
                  refine ⟨2350826717386579196011843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3134435623182105594682457 2350826717386579196011843)
                  ·
                    refine ⟨3526240076079868794017765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2350826717386579196011843 3526240076079868794017765)
                    ·
                      refine ⟨661170014264975398878331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3526240076079868794017765 661170014264975398878331)
                      ·
                        rfl

theorem cell23_1287624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 4, 1, 2, 1, 4].length) (baseStart_1287624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1287624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1287624 prefixEnd_1287624 := by exact prefixLift 1287624
  have htrace : WordTrace (prefixWord ++ tailWord_1287624) baseStart_1287624 baseEnd_1287624 := by
    simpa [prefixWord, tailWord_1287624, baseEnd_1287624] using wordTrace_append hprefix tailTrace_1287624
  have hstable : (prefixWord ++ tailWord_1287624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1287624).length < 2 ^ (prefixWord ++ tailWord_1287624).sum := by decide
  have hdescent : baseEnd_1287624 < baseStart_1287624 := by decide
  rcases family_descends (prefixWord ++ tailWord_1287624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1287627 : List Nat := [1, 1, 1, 1, 3, 3, 2, 3, 1, 4, 3]
def baseStart_1287627 : Nat := 118140960795 + 1287627 * 2 ^ 59
def prefixEnd_1287627 : Nat := 4983230072969 + 3 ^ 40 * 1287627 * 2
def baseEnd_1287627 : Nat := 661171554706938887140817

theorem tailTrace_1287627 : CollatzResearch.WordTrace tailWord_1287627 prefixEnd_1287627 661171554706938887140817 := by
  unfold tailWord_1287627
  simp only [CollatzResearch.WordTrace]
  refine ⟨46963614906154763028845135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31309076604103175352563423 46963614906154763028845135)
  ·
    refine ⟨70445422359232144543267703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46963614906154763028845135 70445422359232144543267703)
    ·
      refine ⟨105668133538848216814901555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70445422359232144543267703 105668133538848216814901555)
      ·
        refine ⟨158502200308272325222352333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105668133538848216814901555 158502200308272325222352333)
        ·
          refine ⟨59438325115602121958382125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 158502200308272325222352333 59438325115602121958382125)
          ·
            refine ⟨22289371918350795734393297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 59438325115602121958382125 22289371918350795734393297)
            ·
              refine ⟨16717028938763096800794973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22289371918350795734393297 16717028938763096800794973)
              ·
                refine ⟨6268885852036161300298115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16717028938763096800794973 6268885852036161300298115)
                ·
                  refine ⟨9403328778054241950447173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6268885852036161300298115 9403328778054241950447173)
                  ·
                    refine ⟨1763124145885170365708845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9403328778054241950447173 1763124145885170365708845)
                    ·
                      refine ⟨661171554706938887140817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1763124145885170365708845 661171554706938887140817)
                      ·
                        rfl

theorem cell23_1287627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 3, 1, 4, 3].length) (baseStart_1287627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1287627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1287627 prefixEnd_1287627 := by exact prefixLift 1287627
  have htrace : WordTrace (prefixWord ++ tailWord_1287627) baseStart_1287627 baseEnd_1287627 := by
    simpa [prefixWord, tailWord_1287627, baseEnd_1287627] using wordTrace_append hprefix tailTrace_1287627
  have hstable : (prefixWord ++ tailWord_1287627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1287627).length < 2 ^ (prefixWord ++ tailWord_1287627).sum := by decide
  have hdescent : baseEnd_1287627 < baseStart_1287627 := by decide
  rcases family_descends (prefixWord ++ tailWord_1287627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1287637 : List Nat := [1, 3, 2, 3, 1, 1, 2, 1, 2, 1, 6]
def baseStart_1287637 : Nat := 118140960795 + 1287637 * 2 ^ 59
def prefixEnd_1287637 : Nat := 4983230072969 + 3 ^ 40 * 1287637 * 2
def baseEnd_1287637 : Nat := 661176689513483848015771

theorem tailTrace_1287637 : CollatzResearch.WordTrace tailWord_1287637 prefixEnd_1287637 661176689513483848015771 := by
  unfold tailWord_1287637
  simp only [CollatzResearch.WordTrace]
  refine ⟨46963979636118534736709165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31309319757412356491139443 46963979636118534736709165)
  ·
    refine ⟨17611492363544450526265937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46963979636118534736709165 17611492363544450526265937)
    ·
      refine ⟨13208619272658337894699453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17611492363544450526265937 13208619272658337894699453)
      ·
        refine ⟨4953232227246876710512295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13208619272658337894699453 4953232227246876710512295)
        ·
          refine ⟨7429848340870315065768443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4953232227246876710512295 7429848340870315065768443)
          ·
            refine ⟨11144772511305472598652665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7429848340870315065768443 11144772511305472598652665)
            ·
              refine ⟨8358579383479104448989499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11144772511305472598652665 8358579383479104448989499)
              ·
                refine ⟨12537869075218656673484249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8358579383479104448989499 12537869075218656673484249)
                ·
                  refine ⟨9403401806413992505113187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12537869075218656673484249 9403401806413992505113187)
                  ·
                    refine ⟨14105102709620988757669781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9403401806413992505113187 14105102709620988757669781)
                    ·
                      refine ⟨661176689513483848015771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 14105102709620988757669781 661176689513483848015771)
                      ·
                        rfl

theorem cell23_1287637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 2, 1, 2, 1, 6].length) (baseStart_1287637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1287637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1287637 prefixEnd_1287637 := by exact prefixLift 1287637
  have htrace : WordTrace (prefixWord ++ tailWord_1287637) baseStart_1287637 baseEnd_1287637 := by
    simpa [prefixWord, tailWord_1287637, baseEnd_1287637] using wordTrace_append hprefix tailTrace_1287637
  have hstable : (prefixWord ++ tailWord_1287637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1287637).length < 2 ^ (prefixWord ++ tailWord_1287637).sum := by decide
  have hdescent : baseEnd_1287637 < baseStart_1287637 := by decide
  rcases family_descends (prefixWord ++ tailWord_1287637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1287678 : List Nat := [4, 2, 2, 3, 1, 1, 1, 1, 1, 4, 3]
def baseStart_1287678 : Nat := 118140960795 + 1287678 * 2 ^ 59
def prefixEnd_1287678 : Nat := 4983230072969 + 3 ^ 40 * 1287678 * 2
def baseEnd_1287678 : Nat := 661197742220318187603083

theorem tailTrace_1287678 : CollatzResearch.WordTrace tailWord_1287678 prefixEnd_1287678 661197742220318187603083 := by
  unfold tailWord_1287678
  simp only [CollatzResearch.WordTrace]
  refine ⟨5870684378621249842368961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 31310316685979999159301125 5870684378621249842368961)
  ·
    refine ⟨4403013283965937381776721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5870684378621249842368961 4403013283965937381776721)
    ·
      refine ⟨3302259962974453036332541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4403013283965937381776721 3302259962974453036332541)
      ·
        refine ⟨1238347486115419888624703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3302259962974453036332541 1238347486115419888624703)
        ·
          refine ⟨1857521229173129832937055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1238347486115419888624703 1857521229173129832937055)
          ·
            refine ⟨2786281843759694749405583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1857521229173129832937055 2786281843759694749405583)
            ·
              refine ⟨4179422765639542124108375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2786281843759694749405583 4179422765639542124108375)
              ·
                refine ⟨6269134148459313186162563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4179422765639542124108375 6269134148459313186162563)
                ·
                  refine ⟨9403701222688969779243845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6269134148459313186162563 9403701222688969779243845)
                  ·
                    refine ⟨1763193979254181833608221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9403701222688969779243845 1763193979254181833608221)
                    ·
                      refine ⟨661197742220318187603083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1763193979254181833608221 661197742220318187603083)
                      ·
                        rfl

theorem cell23_1287678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 1, 1, 1, 4, 3].length) (baseStart_1287678 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1287678 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1287678 prefixEnd_1287678 := by exact prefixLift 1287678
  have htrace : WordTrace (prefixWord ++ tailWord_1287678) baseStart_1287678 baseEnd_1287678 := by
    simpa [prefixWord, tailWord_1287678, baseEnd_1287678] using wordTrace_append hprefix tailTrace_1287678
  have hstable : (prefixWord ++ tailWord_1287678).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1287678).length < 2 ^ (prefixWord ++ tailWord_1287678).sum := by decide
  have hdescent : baseEnd_1287678 < baseStart_1287678 := by decide
  rcases family_descends (prefixWord ++ tailWord_1287678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1287708 : List Nat := [2, 2, 3, 1, 2, 1, 1, 6, 1, 1, 3]
def baseStart_1287708 : Nat := 118140960795 + 1287708 * 2 ^ 59
def prefixEnd_1287708 : Nat := 4983230072969 + 3 ^ 40 * 1287708 * 2
def baseEnd_1287708 : Nat := 661213146639953070227945

theorem tailTrace_1287708 : CollatzResearch.WordTrace tailWord_1287708 prefixEnd_1287708 661213146639953070227945 := by
  unfold tailWord_1287708
  simp only [CollatzResearch.WordTrace]
  refine ⟨23483284609430656931271889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31311046145907542575029185 23483284609430656931271889)
  ·
    refine ⟨17612463457072992698453917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23483284609430656931271889 17612463457072992698453917)
    ·
      refine ⟨6604673796402372261920219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17612463457072992698453917 6604673796402372261920219)
      ·
        refine ⟨9907010694603558392880329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6604673796402372261920219 9907010694603558392880329)
        ·
          refine ⟨7430258020952668794660247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9907010694603558392880329 7430258020952668794660247)
          ·
            refine ⟨11145387031429003191990371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7430258020952668794660247 11145387031429003191990371)
            ·
              refine ⟨16718080547143504787985557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11145387031429003191990371 16718080547143504787985557)
              ·
                refine ⟨783660025647351786936823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 16718080547143504787985557 783660025647351786936823)
                ·
                  refine ⟨1175490038471027680405235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 783660025647351786936823 1175490038471027680405235)
                  ·
                    refine ⟨1763235057706541520607853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1175490038471027680405235 1763235057706541520607853)
                    ·
                      refine ⟨661213146639953070227945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1763235057706541520607853 661213146639953070227945)
                      ·
                        rfl

theorem cell23_1287708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 6, 1, 1, 3].length) (baseStart_1287708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1287708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1287708 prefixEnd_1287708 := by exact prefixLift 1287708
  have htrace : WordTrace (prefixWord ++ tailWord_1287708) baseStart_1287708 baseEnd_1287708 := by
    simpa [prefixWord, tailWord_1287708, baseEnd_1287708] using wordTrace_append hprefix tailTrace_1287708
  have hstable : (prefixWord ++ tailWord_1287708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1287708).length < 2 ^ (prefixWord ++ tailWord_1287708).sum := by decide
  have hdescent : baseEnd_1287708 < baseStart_1287708 := by decide
  rcases family_descends (prefixWord ++ tailWord_1287708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1287714 : List Nat := [3, 3, 1, 1, 1, 1, 2, 1, 5, 1, 4]
def baseStart_1287714 : Nat := 118140960795 + 1287714 * 2 ^ 59
def prefixEnd_1287714 : Nat := 4983230072969 + 3 ^ 40 * 1287714 * 2
def baseEnd_1287714 : Nat := 661216227523880046752917

theorem tailTrace_1287714 : CollatzResearch.WordTrace tailWord_1287714 prefixEnd_1287714 661216227523880046752917 := by
  unfold tailWord_1287714
  simp only [CollatzResearch.WordTrace]
  refine ⟨11741697014209894221815549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31311192037893051258174797 11741697014209894221815549)
  ·
    refine ⟨4403136380328710333180831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11741697014209894221815549 4403136380328710333180831)
    ·
      refine ⟨6604704570493065499771247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4403136380328710333180831 6604704570493065499771247)
      ·
        refine ⟨9907056855739598249656871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6604704570493065499771247 9907056855739598249656871)
        ·
          refine ⟨14860585283609397374485307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9907056855739598249656871 14860585283609397374485307)
          ·
            refine ⟨22290877925414096061727961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14860585283609397374485307 22290877925414096061727961)
            ·
              refine ⟨16718158444060572046295971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22290877925414096061727961 16718158444060572046295971)
              ·
                refine ⟨25077237666090858069443957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16718158444060572046295971 25077237666090858069443957)
                ·
                  refine ⟨2350991031196017944010371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 25077237666090858069443957 2350991031196017944010371)
                  ·
                    refine ⟨3526486546794026916015557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2350991031196017944010371 3526486546794026916015557)
                    ·
                      refine ⟨661216227523880046752917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3526486546794026916015557 661216227523880046752917)
                      ·
                        rfl

theorem cell23_1287714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 1, 5, 1, 4].length) (baseStart_1287714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1287714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1287714 prefixEnd_1287714 := by exact prefixLift 1287714
  have htrace : WordTrace (prefixWord ++ tailWord_1287714) baseStart_1287714 baseEnd_1287714 := by
    simpa [prefixWord, tailWord_1287714, baseEnd_1287714] using wordTrace_append hprefix tailTrace_1287714
  have hstable : (prefixWord ++ tailWord_1287714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1287714).length < 2 ^ (prefixWord ++ tailWord_1287714).sum := by decide
  have hdescent : baseEnd_1287714 < baseStart_1287714 := by decide
  rcases family_descends (prefixWord ++ tailWord_1287714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1287731 : List Nat := [1, 1, 1, 2, 4, 4, 2, 2, 1, 1, 4]
def baseStart_1287731 : Nat := 118140960795 + 1287731 * 2 ^ 59
def prefixEnd_1287731 : Nat := 4983230072969 + 3 ^ 40 * 1287731 * 2
def baseEnd_1287731 : Nat := 661224956695006480240339

theorem tailTrace_1287731 : CollatzResearch.WordTrace tailWord_1287731 prefixEnd_1287731 661224956695006480240339 := by
  unfold tailWord_1287731
  simp only [CollatzResearch.WordTrace]
  refine ⟨46967408097777988790631047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31311605398518659193754031 46967408097777988790631047)
  ·
    refine ⟨70451112146666983185946571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46967408097777988790631047 70451112146666983185946571)
    ·
      refine ⟨105676668220000474778919857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70451112146666983185946571 105676668220000474778919857)
      ·
        refine ⟨79257501165000356084189893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 105676668220000474778919857 79257501165000356084189893)
        ·
          refine ⟨14860781468437566765785605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 79257501165000356084189893 14860781468437566765785605)
          ·
            refine ⟨2786396525332043768584801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14860781468437566765785605 2786396525332043768584801)
            ·
              refine ⟨2089797393999032826438601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2786396525332043768584801 2089797393999032826438601)
              ·
                refine ⟨1567348045499274619828951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2089797393999032826438601 1567348045499274619828951)
                ·
                  refine ⟨2351022068248911929743427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1567348045499274619828951 2351022068248911929743427)
                  ·
                    refine ⟨3526533102373367894615141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2351022068248911929743427 3526533102373367894615141)
                    ·
                      refine ⟨661224956695006480240339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3526533102373367894615141 661224956695006480240339)
                      ·
                        rfl

theorem cell23_1287731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 2, 2, 1, 1, 4].length) (baseStart_1287731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1287731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1287731 prefixEnd_1287731 := by exact prefixLift 1287731
  have htrace : WordTrace (prefixWord ++ tailWord_1287731) baseStart_1287731 baseEnd_1287731 := by
    simpa [prefixWord, tailWord_1287731, baseEnd_1287731] using wordTrace_append hprefix tailTrace_1287731
  have hstable : (prefixWord ++ tailWord_1287731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1287731).length < 2 ^ (prefixWord ++ tailWord_1287731).sum := by decide
  have hdescent : baseEnd_1287731 < baseStart_1287731 := by decide
  rcases family_descends (prefixWord ++ tailWord_1287731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1287751 : List Nat := [1, 1, 4, 1, 5, 1, 2, 1, 1, 1, 5]
def baseStart_1287751 : Nat := 118140960795 + 1287751 * 2 ^ 59
def prefixEnd_1287751 : Nat := 4983230072969 + 3 ^ 40 * 1287751 * 2
def baseEnd_1287751 : Nat := 661235226308096401990247

theorem tailTrace_1287751 : CollatzResearch.WordTrace tailWord_1287751 prefixEnd_1287751 661235226308096401990247 := by
  unfold tailWord_1287751
  simp only [CollatzResearch.WordTrace]
  refine ⟨46968137557705532206359107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31312091705137021470906071 46968137557705532206359107)
  ·
    refine ⟨70452206336558298309538661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46968137557705532206359107 70452206336558298309538661)
    ·
      refine ⟨13209788688104680933038499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 70452206336558298309538661 13209788688104680933038499)
      ·
        refine ⟨19814683032157021399557749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13209788688104680933038499 19814683032157021399557749)
        ·
          refine ⟨1857626534264720756208539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 19814683032157021399557749 1857626534264720756208539)
          ·
            refine ⟨2786439801397081134312809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1857626534264720756208539 2786439801397081134312809)
            ·
              refine ⟨2089829851047810850734607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2786439801397081134312809 2089829851047810850734607)
              ·
                refine ⟨3134744776571716276101911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2089829851047810850734607 3134744776571716276101911)
                ·
                  refine ⟨4702117164857574414152867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3134744776571716276101911 4702117164857574414152867)
                  ·
                    refine ⟨7053175747286361621229301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4702117164857574414152867 7053175747286361621229301)
                    ·
                      refine ⟨661235226308096401990247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7053175747286361621229301 661235226308096401990247)
                      ·
                        rfl

theorem cell23_1287751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 2, 1, 1, 1, 5].length) (baseStart_1287751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1287751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1287751 prefixEnd_1287751 := by exact prefixLift 1287751
  have htrace : WordTrace (prefixWord ++ tailWord_1287751) baseStart_1287751 baseEnd_1287751 := by
    simpa [prefixWord, tailWord_1287751, baseEnd_1287751] using wordTrace_append hprefix tailTrace_1287751
  have hstable : (prefixWord ++ tailWord_1287751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1287751).length < 2 ^ (prefixWord ++ tailWord_1287751).sum := by decide
  have hdescent : baseEnd_1287751 < baseStart_1287751 := by decide
  rcases family_descends (prefixWord ++ tailWord_1287751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1287798 : List Nat := [5, 1, 1, 2, 2, 2, 1, 2, 1, 3, 3]
def baseStart_1287798 : Nat := 118140960795 + 1287798 * 2 ^ 59
def prefixEnd_1287798 : Nat := 4983230072969 + 3 ^ 40 * 1287798 * 2
def baseEnd_1287798 : Nat := 661259359898857718102531

theorem tailTrace_1287798 : CollatzResearch.WordTrace tailWord_1287798 prefixEnd_1287798 661259359898857718102531 := by
  unfold tailWord_1287798
  simp only [CollatzResearch.WordTrace]
  refine ⟨2935615736783453702082503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 31313234525690172822213365 2935615736783453702082503)
  ·
    refine ⟨4403423605175180553123755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2935615736783453702082503 4403423605175180553123755)
    ·
      refine ⟨6605135407762770829685633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4403423605175180553123755 6605135407762770829685633)
      ·
        refine ⟨4953851555822078122264225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6605135407762770829685633 4953851555822078122264225)
        ·
          refine ⟨3715388666866558591698169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4953851555822078122264225 3715388666866558591698169)
          ·
            refine ⟨2786541500149918943773627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3715388666866558591698169 2786541500149918943773627)
            ·
              refine ⟨4179812250224878415660441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2786541500149918943773627 4179812250224878415660441)
              ·
                refine ⟨3134859187668658811745331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4179812250224878415660441 3134859187668658811745331)
                ·
                  refine ⟨4702288781502988217617997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3134859187668658811745331 4702288781502988217617997)
                  ·
                    refine ⟨1763358293063620581606749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4702288781502988217617997 1763358293063620581606749)
                    ·
                      refine ⟨661259359898857718102531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1763358293063620581606749 661259359898857718102531)
                      ·
                        rfl

theorem cell23_1287798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 1, 2, 1, 3, 3].length) (baseStart_1287798 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1287798 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1287798 prefixEnd_1287798 := by exact prefixLift 1287798
  have htrace : WordTrace (prefixWord ++ tailWord_1287798) baseStart_1287798 baseEnd_1287798 := by
    simpa [prefixWord, tailWord_1287798, baseEnd_1287798] using wordTrace_append hprefix tailTrace_1287798
  have hstable : (prefixWord ++ tailWord_1287798).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1287798).length < 2 ^ (prefixWord ++ tailWord_1287798).sum := by decide
  have hdescent : baseEnd_1287798 < baseStart_1287798 := by decide
  rcases family_descends (prefixWord ++ tailWord_1287798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1287816 : List Nat := [2, 1, 3, 5, 1, 2, 2, 2, 1, 2, 2]
def baseStart_1287816 : Nat := 118140960795 + 1287816 * 2 ^ 59
def prefixEnd_1287816 : Nat := 4983230072969 + 3 ^ 40 * 1287816 * 2
def baseEnd_1287816 : Nat := 661268602550638647677449

theorem tailTrace_1287816 : CollatzResearch.WordTrace tailWord_1287816 prefixEnd_1287816 661268602550638647677449 := by
  unfold tailWord_1287816
  simp only [CollatzResearch.WordTrace]
  refine ⟨23485254151235024153737651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31313672201646698871650201 23485254151235024153737651)
  ·
    refine ⟨35227881226852536230606477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23485254151235024153737651 35227881226852536230606477)
    ·
      refine ⟨13210455460069701086477429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35227881226852536230606477 13210455460069701086477429)
      ·
        refine ⟨1238480199381534476857259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 13210455460069701086477429 1238480199381534476857259)
        ·
          refine ⟨1857720299072301715285889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1238480199381534476857259 1857720299072301715285889)
          ·
            refine ⟨1393290224304226286464417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1857720299072301715285889 1393290224304226286464417)
            ·
              refine ⟨1044967668228169714848313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1393290224304226286464417 1044967668228169714848313)
              ·
                refine ⟨783725751171127286136235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1044967668228169714848313 783725751171127286136235)
                ·
                  refine ⟨1175588626756690929204353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 783725751171127286136235 1175588626756690929204353)
                  ·
                    refine ⟨881691470067518196903265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1175588626756690929204353 881691470067518196903265)
                    ·
                      refine ⟨661268602550638647677449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 881691470067518196903265 661268602550638647677449)
                      ·
                        rfl

theorem cell23_1287816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 2, 2, 2, 1, 2, 2].length) (baseStart_1287816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1287816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1287816 prefixEnd_1287816 := by exact prefixLift 1287816
  have htrace : WordTrace (prefixWord ++ tailWord_1287816) baseStart_1287816 baseEnd_1287816 := by
    simpa [prefixWord, tailWord_1287816, baseEnd_1287816] using wordTrace_append hprefix tailTrace_1287816
  have hstable : (prefixWord ++ tailWord_1287816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1287816).length < 2 ^ (prefixWord ++ tailWord_1287816).sum := by decide
  have hdescent : baseEnd_1287816 < baseStart_1287816 := by decide
  rcases family_descends (prefixWord ++ tailWord_1287816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1287844 : List Nat := [2, 3, 1, 2, 2, 2, 1, 1, 9]
def baseStart_1287844 : Nat := 118140960795 + 1287844 * 2 ^ 59
def prefixEnd_1287844 : Nat := 4983230072969 + 3 ^ 40 * 1287844 * 2
def baseEnd_1287844 : Nat := 73475886667662726458591

theorem tailTrace_1287844 : CollatzResearch.WordTrace tailWord_1287844 prefixEnd_1287844 73475886667662726458591 := by
  unfold tailWord_1287844
  simp only [CollatzResearch.WordTrace]
  refine ⟨23485764773184304544747293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31314353030912406059663057 23485764773184304544747293)
  ·
    refine ⟨8807161789944114204280235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23485764773184304544747293 8807161789944114204280235)
    ·
      refine ⟨13210742684916171306420353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8807161789944114204280235 13210742684916171306420353)
      ·
        refine ⟨9908057013687128479815265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13210742684916171306420353 9908057013687128479815265)
        ·
          refine ⟨7431042760265346359861449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9908057013687128479815265 7431042760265346359861449)
          ·
            refine ⟨5573282070199009769896087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7431042760265346359861449 5573282070199009769896087)
            ·
              refine ⟨8359923105298514654844131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5573282070199009769896087 8359923105298514654844131)
              ·
                refine ⟨12539884657947771982266197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8359923105298514654844131 12539884657947771982266197)
                ·
                  refine ⟨73475886667662726458591, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 12539884657947771982266197 73475886667662726458591)
                  ·
                    rfl

theorem cell23_1287844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 1, 1, 9].length) (baseStart_1287844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1287844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1287844 prefixEnd_1287844 := by exact prefixLift 1287844
  have htrace : WordTrace (prefixWord ++ tailWord_1287844) baseStart_1287844 baseEnd_1287844 := by
    simpa [prefixWord, tailWord_1287844, baseEnd_1287844] using wordTrace_append hprefix tailTrace_1287844
  have hstable : (prefixWord ++ tailWord_1287844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1287844).length < 2 ^ (prefixWord ++ tailWord_1287844).sum := by decide
  have hdescent : baseEnd_1287844 < baseStart_1287844 := by decide
  rcases family_descends (prefixWord ++ tailWord_1287844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1287989 : List Nat := [1, 3, 3, 1, 4, 2, 2, 2, 1, 4]
def baseStart_1287989 : Nat := 118140960795 + 1287989 * 2 ^ 59
def prefixEnd_1287989 : Nat := 4983230072969 + 3 ^ 40 * 1287989 * 2
def baseEnd_1287989 : Nat := 220452478234622156938051

theorem tailTrace_1287989 : CollatzResearch.WordTrace tailWord_1287989 prefixEnd_1287989 220452478234622156938051 := by
  unfold tailWord_1287989
  simp only [CollatzResearch.WordTrace]
  refine ⟨46976818130843298853523021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31317878753895532569015347 46976818130843298853523021)
  ·
    refine ⟨17616306799066237070071133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46976818130843298853523021 17616306799066237070071133)
    ·
      refine ⟨6606115049649838901276675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17616306799066237070071133 6606115049649838901276675)
      ·
        refine ⟨9909172574474758351915013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6606115049649838901276675 9909172574474758351915013)
        ·
          refine ⟨1857969857714017190984065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9909172574474758351915013 1857969857714017190984065)
          ·
            refine ⟨1393477393285512893238049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1857969857714017190984065 1393477393285512893238049)
            ·
              refine ⟨1045108044964134669928537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1393477393285512893238049 1045108044964134669928537)
              ·
                refine ⟨783831033723101002446403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1045108044964134669928537 783831033723101002446403)
                ·
                  refine ⟨1175746550584651503669605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 783831033723101002446403 1175746550584651503669605)
                  ·
                    refine ⟨220452478234622156938051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1175746550584651503669605 220452478234622156938051)
                    ·
                      rfl

theorem cell23_1287989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 2, 2, 2, 1, 4].length) (baseStart_1287989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1287989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1287989 prefixEnd_1287989 := by exact prefixLift 1287989
  have htrace : WordTrace (prefixWord ++ tailWord_1287989) baseStart_1287989 baseEnd_1287989 := by
    simpa [prefixWord, tailWord_1287989, baseEnd_1287989] using wordTrace_append hprefix tailTrace_1287989
  have hstable : (prefixWord ++ tailWord_1287989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1287989).length < 2 ^ (prefixWord ++ tailWord_1287989).sum := by decide
  have hdescent : baseEnd_1287989 < baseStart_1287989 := by decide
  rcases family_descends (prefixWord ++ tailWord_1287989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1287998 : List Nat := [4, 2, 1, 2, 2, 1, 1, 2, 3, 5]
def baseStart_1287998 : Nat := 118140960795 + 1287998 * 2 ^ 59
def prefixEnd_1287998 : Nat := 4983230072969 + 3 ^ 40 * 1287998 * 2
def baseEnd_1287998 : Nat := 220454018676585645200537

theorem tailTrace_1287998 : CollatzResearch.WordTrace tailWord_1287998 prefixEnd_1287998 220454018676585645200537 := by
  unfold tailWord_1287998
  simp only [CollatzResearch.WordTrace]
  refine ⟨5872143298476336673825081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 31318097591873795593733765 5872143298476336673825081)
  ·
    refine ⟨4404107473857252505368811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5872143298476336673825081 4404107473857252505368811)
    ·
      refine ⟨6606161210785878758053217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4404107473857252505368811 6606161210785878758053217)
      ·
        refine ⟨4954620908089409068539913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6606161210785878758053217 4954620908089409068539913)
        ·
          refine ⟨3715965681067056801404935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4954620908089409068539913 3715965681067056801404935)
          ·
            refine ⟨5573948521600585202107403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3715965681067056801404935 5573948521600585202107403)
            ·
              refine ⟨8360922782400877803161105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5573948521600585202107403 8360922782400877803161105)
              ·
                refine ⟨6270692086800658352370829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8360922782400877803161105 6270692086800658352370829)
                ·
                  refine ⟨2351509532550246882139061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6270692086800658352370829 2351509532550246882139061)
                  ·
                    refine ⟨220454018676585645200537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2351509532550246882139061 220454018676585645200537)
                    ·
                      rfl

theorem cell23_1287998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 1, 2, 3, 5].length) (baseStart_1287998 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1287998 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1287998 prefixEnd_1287998 := by exact prefixLift 1287998
  have htrace : WordTrace (prefixWord ++ tailWord_1287998) baseStart_1287998 baseEnd_1287998 := by
    simpa [prefixWord, tailWord_1287998, baseEnd_1287998] using wordTrace_append hprefix tailTrace_1287998
  have hstable : (prefixWord ++ tailWord_1287998).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1287998).length < 2 ^ (prefixWord ++ tailWord_1287998).sum := by decide
  have hdescent : baseEnd_1287998 < baseStart_1287998 := by decide
  rcases family_descends (prefixWord ++ tailWord_1287998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1288018 : List Nat := [3, 2, 2, 1, 1, 3, 2, 1, 3, 1, 4]
def baseStart_1288018 : Nat := 118140960795 + 1288018 * 2 ^ 59
def prefixEnd_1288018 : Nat := 4983230072969 + 3 ^ 40 * 1288018 * 2
def baseEnd_1288018 : Nat := 661372325642846857351519

theorem tailTrace_1288018 : CollatzResearch.WordTrace tailWord_1288018 prefixEnd_1288018 661372325642846857351519 := by
  unfold tailWord_1288018
  simp only [CollatzResearch.WordTrace]
  refine ⟨11744468961934559201582177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31318583898492157870885805 11744468961934559201582177)
  ·
    refine ⟨8808351721450919401186633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11744468961934559201582177 8808351721450919401186633)
    ·
      refine ⟨6606263791088189550889975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8808351721450919401186633 6606263791088189550889975)
      ·
        refine ⟨9909395686632284326334963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6606263791088189550889975 9909395686632284326334963)
        ·
          refine ⟨14864093529948426489502445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9909395686632284326334963 14864093529948426489502445)
          ·
            refine ⟨5574035073730659933563417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14864093529948426489502445 5574035073730659933563417)
            ·
              refine ⟨4180526305297994950172563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5574035073730659933563417 4180526305297994950172563)
              ·
                refine ⟨6270789457946992425258845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4180526305297994950172563 6270789457946992425258845)
                ·
                  refine ⟨2351546046730122159472067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6270789457946992425258845 2351546046730122159472067)
                  ·
                    refine ⟨3527319070095183239208101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2351546046730122159472067 3527319070095183239208101)
                    ·
                      refine ⟨661372325642846857351519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3527319070095183239208101 661372325642846857351519)
                      ·
                        rfl

theorem cell23_1288018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 2, 1, 3, 1, 4].length) (baseStart_1288018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1288018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1288018 prefixEnd_1288018 := by exact prefixLift 1288018
  have htrace : WordTrace (prefixWord ++ tailWord_1288018) baseStart_1288018 baseEnd_1288018 := by
    simpa [prefixWord, tailWord_1288018, baseEnd_1288018] using wordTrace_append hprefix tailTrace_1288018
  have hstable : (prefixWord ++ tailWord_1288018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1288018).length < 2 ^ (prefixWord ++ tailWord_1288018).sum := by decide
  have hdescent : baseEnd_1288018 < baseStart_1288018 := by decide
  rcases family_descends (prefixWord ++ tailWord_1288018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1288035 : List Nat := [1, 1, 1, 5, 4, 1, 1, 3, 1, 1, 4]
def baseStart_1288035 : Nat := 118140960795 + 1288035 * 2 ^ 59
def prefixEnd_1288035 : Nat := 4983230072969 + 3 ^ 40 * 1288035 * 2
def baseEnd_1288035 : Nat := 661381054813973290838941

theorem tailTrace_1288035 : CollatzResearch.WordTrace tailWord_1288035 prefixEnd_1288035 661381054813973290838941 := by
  unfold tailWord_1288035
  simp only [CollatzResearch.WordTrace]
  refine ⟨46978495888676648709697559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31318997259117765806465039 46978495888676648709697559)
  ·
    refine ⟨70467743833014973064546339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46978495888676648709697559 70467743833014973064546339)
    ·
      refine ⟨105701615749522459596819509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70467743833014973064546339 105701615749522459596819509)
      ·
        refine ⟨9909526476517730587201829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 105701615749522459596819509 9909526476517730587201829)
        ·
          refine ⟨1858036214347074485100343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9909526476517730587201829 1858036214347074485100343)
          ·
            refine ⟨2787054321520611727650515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1858036214347074485100343 2787054321520611727650515)
            ·
              refine ⟨4180581482280917591475773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2787054321520611727650515 4180581482280917591475773)
              ·
                refine ⟨1567718055855344096803415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4180581482280917591475773 1567718055855344096803415)
                ·
                  refine ⟨2351577083783016145205123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1567718055855344096803415 2351577083783016145205123)
                  ·
                    refine ⟨3527365625674524217807685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2351577083783016145205123 3527365625674524217807685)
                    ·
                      refine ⟨661381054813973290838941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3527365625674524217807685 661381054813973290838941)
                      ·
                        rfl

theorem cell23_1288035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 1, 3, 1, 1, 4].length) (baseStart_1288035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1288035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1288035 prefixEnd_1288035 := by exact prefixLift 1288035
  have htrace : WordTrace (prefixWord ++ tailWord_1288035) baseStart_1288035 baseEnd_1288035 := by
    simpa [prefixWord, tailWord_1288035, baseEnd_1288035] using wordTrace_append hprefix tailTrace_1288035
  have hstable : (prefixWord ++ tailWord_1288035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1288035).length < 2 ^ (prefixWord ++ tailWord_1288035).sum := by decide
  have hdescent : baseEnd_1288035 < baseStart_1288035 := by decide
  rcases family_descends (prefixWord ++ tailWord_1288035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1288045 : List Nat := [1, 5, 1, 1, 1, 1, 5, 2, 2, 4]
def baseStart_1288045 : Nat := 118140960795 + 1288045 * 2 ^ 59
def prefixEnd_1288045 : Nat := 4983230072969 + 3 ^ 40 * 1288045 * 2
def baseEnd_1288045 : Nat := 220462063206839417237965

theorem tailTrace_1288045 : CollatzResearch.WordTrace tailWord_1288045 prefixEnd_1288045 220462063206839417237965 := by
  unfold tailWord_1288045
  simp only [CollatzResearch.WordTrace]
  refine ⟨46978860618640420417561589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31319240412426946945041059 46978860618640420417561589)
  ·
    refine ⟨4404268182997539414146399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 46978860618640420417561589 4404268182997539414146399)
    ·
      refine ⟨6606402274496309121219599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4404268182997539414146399 6606402274496309121219599)
      ·
        refine ⟨9909603411744463681829399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6606402274496309121219599 9909603411744463681829399)
        ·
          refine ⟨14864405117616695522744099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9909603411744463681829399 14864405117616695522744099)
          ·
            refine ⟨22296607676425043284116149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14864405117616695522744099 22296607676425043284116149)
            ·
              refine ⟨2090306969664847807885889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 22296607676425043284116149 2090306969664847807885889)
              ·
                refine ⟨1567730227248635855914417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2090306969664847807885889 1567730227248635855914417)
                ·
                  refine ⟨1175797670436476891935813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1567730227248635855914417 1175797670436476891935813)
                  ·
                    refine ⟨220462063206839417237965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1175797670436476891935813 220462063206839417237965)
                    ·
                      rfl

theorem cell23_1288045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 5, 2, 2, 4].length) (baseStart_1288045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1288045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1288045 prefixEnd_1288045 := by exact prefixLift 1288045
  have htrace : WordTrace (prefixWord ++ tailWord_1288045) baseStart_1288045 baseEnd_1288045 := by
    simpa [prefixWord, tailWord_1288045, baseEnd_1288045] using wordTrace_append hprefix tailTrace_1288045
  have hstable : (prefixWord ++ tailWord_1288045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1288045).length < 2 ^ (prefixWord ++ tailWord_1288045).sum := by decide
  have hdescent : baseEnd_1288045 < baseStart_1288045 := by decide
  rcases family_descends (prefixWord ++ tailWord_1288045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1288062 : List Nat := [4, 2, 3, 1, 1, 3, 1, 1, 1, 6]
def baseStart_1288062 : Nat := 118140960795 + 1288062 * 2 ^ 59
def prefixEnd_1288062 : Nat := 4983230072969 + 3 ^ 40 * 1288062 * 2
def baseEnd_1288062 : Nat := 220464972930548228400439

theorem tailTrace_1288062 : CollatzResearch.WordTrace tailWord_1288062 prefixEnd_1288062 220464972930548228400439 := by
  unfold tailWord_1288062
  simp only [CollatzResearch.WordTrace]
  refine ⟨5872435082447354040116305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 31319653773052554880620293 5872435082447354040116305)
  ·
    refine ⟨4404326311835515530087229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5872435082447354040116305 4404326311835515530087229)
    ·
      refine ⟨1651622366938318323782711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4404326311835515530087229 1651622366938318323782711)
      ·
        refine ⟨2477433550407477485674067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1651622366938318323782711 2477433550407477485674067)
        ·
          refine ⟨3716150325611216228511101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2477433550407477485674067 3716150325611216228511101)
          ·
            refine ⟨1393556372104206085691663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3716150325611216228511101 1393556372104206085691663)
            ·
              refine ⟨2090334558156309128537495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1393556372104206085691663 2090334558156309128537495)
              ·
                refine ⟨3135501837234463692806243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2090334558156309128537495 3135501837234463692806243)
                ·
                  refine ⟨4703252755851695539209365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3135501837234463692806243 4703252755851695539209365)
                  ·
                    refine ⟨220464972930548228400439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4703252755851695539209365 220464972930548228400439)
                    ·
                      rfl

theorem cell23_1288062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 3, 1, 1, 1, 6].length) (baseStart_1288062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1288062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1288062 prefixEnd_1288062 := by exact prefixLift 1288062
  have htrace : WordTrace (prefixWord ++ tailWord_1288062) baseStart_1288062 baseEnd_1288062 := by
    simpa [prefixWord, tailWord_1288062, baseEnd_1288062] using wordTrace_append hprefix tailTrace_1288062
  have hstable : (prefixWord ++ tailWord_1288062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1288062).length < 2 ^ (prefixWord ++ tailWord_1288062).sum := by decide
  have hdescent : baseEnd_1288062 < baseStart_1288062 := by decide
  rcases family_descends (prefixWord ++ tailWord_1288062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1288065 : List Nat := [1, 2, 4, 4, 1, 1, 1, 1, 1, 1, 6]
def baseStart_1288065 : Nat := 118140960795 + 1288065 * 2 ^ 59
def prefixEnd_1288065 : Nat := 4983230072969 + 3 ^ 40 * 1288065 * 2
def baseEnd_1288065 : Nat := 661396459233608173463803

theorem tailTrace_1288065 : CollatzResearch.WordTrace tailWord_1288065 prefixEnd_1288065 661396459233608173463803 := by
  unfold tailWord_1288065
  simp only [CollatzResearch.WordTrace]
  refine ⟨46979590078567963833289649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31319726719045309222193099 46979590078567963833289649)
  ·
    refine ⟨35234692558925972874967237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46979590078567963833289649 35234692558925972874967237)
    ·
      refine ⟨6606504854798619914056357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 35234692558925972874967237 6606504854798619914056357)
      ·
        refine ⟨1238719660274741233885567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6606504854798619914056357 1238719660274741233885567)
        ·
          refine ⟨1858079490412111850828351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1238719660274741233885567 1858079490412111850828351)
          ·
            refine ⟨2787119235618167776242527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1858079490412111850828351 2787119235618167776242527)
            ·
              refine ⟨4180678853427251664363791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2787119235618167776242527 4180678853427251664363791)
              ·
                refine ⟨6271018280140877496545687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4180678853427251664363791 6271018280140877496545687)
                ·
                  refine ⟨9406527420211316244818531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6271018280140877496545687 9406527420211316244818531)
                  ·
                    refine ⟨14109791130316974367227797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9406527420211316244818531 14109791130316974367227797)
                    ·
                      refine ⟨661396459233608173463803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 14109791130316974367227797 661396459233608173463803)
                      ·
                        rfl

theorem cell23_1288065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 1, 1, 1, 1, 6].length) (baseStart_1288065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1288065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1288065 prefixEnd_1288065 := by exact prefixLift 1288065
  have htrace : WordTrace (prefixWord ++ tailWord_1288065) baseStart_1288065 baseEnd_1288065 := by
    simpa [prefixWord, tailWord_1288065, baseEnd_1288065] using wordTrace_append hprefix tailTrace_1288065
  have hstable : (prefixWord ++ tailWord_1288065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1288065).length < 2 ^ (prefixWord ++ tailWord_1288065).sum := by decide
  have hdescent : baseEnd_1288065 < baseStart_1288065 := by decide
  rcases family_descends (prefixWord ++ tailWord_1288065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1288072 : List Nat := [2, 1, 3, 3, 3, 1, 2, 2, 1, 2, 3]
def baseStart_1288072 : Nat := 118140960795 + 1288072 * 2 ^ 59
def prefixEnd_1288072 : Nat := 4983230072969 + 3 ^ 40 * 1288072 * 2
def baseEnd_1288072 : Nat := 661400053598189646076271

theorem tailTrace_1288072 : CollatzResearch.WordTrace tailWord_1288072 prefixEnd_1288072 661400053598189646076271 := by
  unfold tailWord_1288072
  simp only [CollatzResearch.WordTrace]
  refine ⟨23489922694771302014397235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31319896926361736019196313 23489922694771302014397235)
  ·
    refine ⟨35234884042156953021595853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23489922694771302014397235 35234884042156953021595853)
    ·
      refine ⟨13213081515808857383098445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35234884042156953021595853 13213081515808857383098445)
      ·
        refine ⟨4954905568428321518661917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13213081515808857383098445 4954905568428321518661917)
        ·
          refine ⟨1858089588160620569498219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4954905568428321518661917 1858089588160620569498219)
          ·
            refine ⟨2787134382240930854247329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1858089588160620569498219 2787134382240930854247329)
            ·
              refine ⟨2090350786680698140685497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2787134382240930854247329 2090350786680698140685497)
              ·
                refine ⟨1567763090010523605514123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2090350786680698140685497 1567763090010523605514123)
                ·
                  refine ⟨2351644635015785408271185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1567763090010523605514123 2351644635015785408271185)
                  ·
                    refine ⟨1763733476261839056203389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2351644635015785408271185 1763733476261839056203389)
                    ·
                      refine ⟨661400053598189646076271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1763733476261839056203389 661400053598189646076271)
                      ·
                        rfl

theorem cell23_1288072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 2, 2, 1, 2, 3].length) (baseStart_1288072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1288072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1288072 prefixEnd_1288072 := by exact prefixLift 1288072
  have htrace : WordTrace (prefixWord ++ tailWord_1288072) baseStart_1288072 baseEnd_1288072 := by
    simpa [prefixWord, tailWord_1288072, baseEnd_1288072] using wordTrace_append hprefix tailTrace_1288072
  have hstable : (prefixWord ++ tailWord_1288072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1288072).length < 2 ^ (prefixWord ++ tailWord_1288072).sum := by decide
  have hdescent : baseEnd_1288072 < baseStart_1288072 := by decide
  rcases family_descends (prefixWord ++ tailWord_1288072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1288081 : List Nat := [1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 5]
def baseStart_1288081 : Nat := 118140960795 + 1288081 * 2 ^ 59
def prefixEnd_1288081 : Nat := 4983230072969 + 3 ^ 40 * 1288081 * 2
def baseEnd_1288081 : Nat := 661404674924080110863729

theorem tailTrace_1288081 : CollatzResearch.WordTrace tailWord_1288081 prefixEnd_1288081 661404674924080110863729 := by
  unfold tailWord_1288081
  simp only [CollatzResearch.WordTrace]
  refine ⟨46980173646509998565872097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31320115764339999043914731 46980173646509998565872097)
  ·
    refine ⟨35235130234882498924404073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46980173646509998565872097 35235130234882498924404073)
    ·
      refine ⟨26426347676161874193303055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35235130234882498924404073 26426347676161874193303055)
      ·
        refine ⟨39639521514242811289954583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26426347676161874193303055 39639521514242811289954583)
        ·
          refine ⟨59459282271364216934931875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39639521514242811289954583 59459282271364216934931875)
          ·
            refine ⟨89188923407046325402397813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59459282271364216934931875 89188923407046325402397813)
            ·
              refine ⟨8361461569410593006474795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 89188923407046325402397813 8361461569410593006474795)
              ·
                refine ⟨12542192354115889509712193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8361461569410593006474795 12542192354115889509712193)
                ·
                  refine ⟨9406644265586917132284145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12542192354115889509712193 9406644265586917132284145)
                  ·
                    refine ⟨7054983199190187849213109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9406644265586917132284145 7054983199190187849213109)
                    ·
                      refine ⟨661404674924080110863729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7054983199190187849213109 661404674924080110863729)
                      ·
                        rfl

theorem cell23_1288081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 5].length) (baseStart_1288081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1288081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1288081 prefixEnd_1288081 := by exact prefixLift 1288081
  have htrace : WordTrace (prefixWord ++ tailWord_1288081) baseStart_1288081 baseEnd_1288081 := by
    simpa [prefixWord, tailWord_1288081, baseEnd_1288081] using wordTrace_append hprefix tailTrace_1288081
  have hstable : (prefixWord ++ tailWord_1288081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1288081).length < 2 ^ (prefixWord ++ tailWord_1288081).sum := by decide
  have hdescent : baseEnd_1288081 < baseStart_1288081 := by decide
  rcases family_descends (prefixWord ++ tailWord_1288081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1288101 : List Nat := [1, 3, 1, 2, 1, 1, 1, 3, 4, 6]
def baseStart_1288101 : Nat := 118140960795 + 1288101 * 2 ^ 59
def prefixEnd_1288101 : Nat := 4983230072969 + 3 ^ 40 * 1288101 * 2
def baseEnd_1288101 : Nat := 220471648179056677537879

theorem tailTrace_1288101 : CollatzResearch.WordTrace tailWord_1288101 prefixEnd_1288101 220471648179056677537879 := by
  unfold tailWord_1288101
  simp only [CollatzResearch.WordTrace]
  refine ⟨46980903106437541981600157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31320602070958361321066771 46980903106437541981600157)
  ·
    refine ⟨17617838664914078243100059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46980903106437541981600157 17617838664914078243100059)
    ·
      refine ⟨26426757997371117364650089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17617838664914078243100059 26426757997371117364650089)
      ·
        refine ⟨19820068498028338023487567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26426757997371117364650089 19820068498028338023487567)
        ·
          refine ⟨29730102747042507035231351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19820068498028338023487567 29730102747042507035231351)
          ·
            refine ⟨44595154120563760552847027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29730102747042507035231351 44595154120563760552847027)
            ·
              refine ⟨66892731180845640829270541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44595154120563760552847027 66892731180845640829270541)
              ·
                refine ⟨25084774192817115310976453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 66892731180845640829270541 25084774192817115310976453)
                ·
                  refine ⟨4703395161153209120808085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25084774192817115310976453 4703395161153209120808085)
                  ·
                    refine ⟨220471648179056677537879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4703395161153209120808085 220471648179056677537879)
                    ·
                      rfl

theorem cell23_1288101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 3, 4, 6].length) (baseStart_1288101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1288101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1288101 prefixEnd_1288101 := by exact prefixLift 1288101
  have htrace : WordTrace (prefixWord ++ tailWord_1288101) baseStart_1288101 baseEnd_1288101 := by
    simpa [prefixWord, tailWord_1288101, baseEnd_1288101] using wordTrace_append hprefix tailTrace_1288101
  have hstable : (prefixWord ++ tailWord_1288101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1288101).length < 2 ^ (prefixWord ++ tailWord_1288101).sum := by decide
  have hdescent : baseEnd_1288101 < baseStart_1288101 := by decide
  rcases family_descends (prefixWord ++ tailWord_1288101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1288108 : List Nat := [2, 2, 1, 1, 1, 1, 2, 1, 2, 8, 2]
def baseStart_1288108 : Nat := 118140960795 + 1288108 * 2 ^ 59
def prefixEnd_1288108 : Nat := 4983230072969 + 3 ^ 40 * 1288108 * 2
def baseEnd_1288108 : Nat := 661418538901751505226105

theorem tailTrace_1288108 : CollatzResearch.WordTrace tailWord_1288108 prefixEnd_1288108 661418538901751505226105 := by
  unfold tailWord_1288108
  simp only [CollatzResearch.WordTrace]
  refine ⟨23490579208706091088552489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31320772278274788118069985 23490579208706091088552489)
  ·
    refine ⟨17617934406529568316414367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23490579208706091088552489 17617934406529568316414367)
    ·
      refine ⟨26426901609794352474621551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17617934406529568316414367 26426901609794352474621551)
      ·
        refine ⟨39640352414691528711932327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26426901609794352474621551 39640352414691528711932327)
        ·
          refine ⟨59460528622037293067898491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39640352414691528711932327 59460528622037293067898491)
          ·
            refine ⟨89190792933055939601847737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59460528622037293067898491 89190792933055939601847737)
            ·
              refine ⟨66893094699791954701385803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 89190792933055939601847737 66893094699791954701385803)
              ·
                refine ⟨100339642049687932052078705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 66893094699791954701385803 100339642049687932052078705)
                ·
                  refine ⟨75254731537265949039059029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 100339642049687932052078705 75254731537265949039059029)
                  ·
                    refine ⟨881891385202335340301473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 75254731537265949039059029 881891385202335340301473)
                    ·
                      refine ⟨661418538901751505226105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 881891385202335340301473 661418538901751505226105)
                      ·
                        rfl

theorem cell23_1288108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 8, 2].length) (baseStart_1288108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1288108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1288108 prefixEnd_1288108 := by exact prefixLift 1288108
  have htrace : WordTrace (prefixWord ++ tailWord_1288108) baseStart_1288108 baseEnd_1288108 := by
    simpa [prefixWord, tailWord_1288108, baseEnd_1288108] using wordTrace_append hprefix tailTrace_1288108
  have hstable : (prefixWord ++ tailWord_1288108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1288108).length < 2 ^ (prefixWord ++ tailWord_1288108).sum := by decide
  have hdescent : baseEnd_1288108 < baseStart_1288108 := by decide
  rcases family_descends (prefixWord ++ tailWord_1288108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1288111 : List Nat := [1, 1, 2, 1, 2, 2, 3, 2, 1, 3, 5]
def baseStart_1288111 : Nat := 118140960795 + 1288111 * 2 ^ 59
def prefixEnd_1288111 : Nat := 4983230072969 + 3 ^ 40 * 1288111 * 2
def baseEnd_1288111 : Nat := 661420079343714993488591

theorem tailTrace_1288111 : CollatzResearch.WordTrace tailWord_1288111 prefixEnd_1288111 661420079343714993488591 := by
  unfold tailWord_1288111
  simp only [CollatzResearch.WordTrace]
  refine ⟨46981267836401313689464187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31320845224267542459642791 46981267836401313689464187)
  ·
    refine ⟨70471901754601970534196281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46981267836401313689464187 70471901754601970534196281)
    ·
      refine ⟨52853926315951477900647211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70471901754601970534196281 52853926315951477900647211)
      ·
        refine ⟨79280889473927216850970817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52853926315951477900647211 79280889473927216850970817)
        ·
          refine ⟨59460667105445412638228113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79280889473927216850970817 59460667105445412638228113)
          ·
            refine ⟨44595500329084059478671085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59460667105445412638228113 44595500329084059478671085)
            ·
              refine ⟨16723312623406522304501657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44595500329084059478671085 16723312623406522304501657)
              ·
                refine ⟨12542484467554891728376243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16723312623406522304501657 12542484467554891728376243)
                ·
                  refine ⟨18813726701332337592564365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12542484467554891728376243 18813726701332337592564365)
                  ·
                    refine ⟨7055147512999626597211637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18813726701332337592564365 7055147512999626597211637)
                    ·
                      refine ⟨661420079343714993488591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7055147512999626597211637 661420079343714993488591)
                      ·
                        rfl

theorem cell23_1288111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 2, 1, 3, 5].length) (baseStart_1288111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1288111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1288111 prefixEnd_1288111 := by exact prefixLift 1288111
  have htrace : WordTrace (prefixWord ++ tailWord_1288111) baseStart_1288111 baseEnd_1288111 := by
    simpa [prefixWord, tailWord_1288111, baseEnd_1288111] using wordTrace_append hprefix tailTrace_1288111
  have hstable : (prefixWord ++ tailWord_1288111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1288111).length < 2 ^ (prefixWord ++ tailWord_1288111).sum := by decide
  have hdescent : baseEnd_1288111 < baseStart_1288111 := by decide
  rcases family_descends (prefixWord ++ tailWord_1288111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1288146 : List Nat := [3, 2, 2, 3, 2, 1, 3, 1, 1, 3, 2]
def baseStart_1288146 : Nat := 118140960795 + 1288146 * 2 ^ 59
def prefixEnd_1288146 : Nat := 4983230072969 + 3 ^ 40 * 1288146 * 2
def baseEnd_1288146 : Nat := 661438051166622356550931

theorem tailTrace_1288146 : CollatzResearch.WordTrace tailWord_1288146 prefixEnd_1288146 661438051166622356550931 := by
  unfold tailWord_1288146
  simp only [CollatzResearch.WordTrace]
  refine ⟨11745636097818628666747073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31321696260849676444658861 11745636097818628666747073)
  ·
    refine ⟨8809227073363971500060305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11745636097818628666747073 8809227073363971500060305)
    ·
      refine ⟨6606920305022978625045229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8809227073363971500060305 6606920305022978625045229)
      ·
        refine ⟨2477595114383616984391961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6606920305022978625045229 2477595114383616984391961)
        ·
          refine ⟨1858196335787712738293971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2477595114383616984391961 1858196335787712738293971)
          ·
            refine ⟨2787294503681569107440957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1858196335787712738293971 2787294503681569107440957)
            ·
              refine ⟨1045235438880588415290359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2787294503681569107440957 1045235438880588415290359)
              ·
                refine ⟨1567853158320882622935539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1045235438880588415290359 1567853158320882622935539)
                ·
                  refine ⟨2351779737481323934403309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1567853158320882622935539 2351779737481323934403309)
                  ·
                    refine ⟨881917401555496475401241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2351779737481323934403309 881917401555496475401241)
                    ·
                      refine ⟨661438051166622356550931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 881917401555496475401241 661438051166622356550931)
                      ·
                        rfl

theorem cell23_1288146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 3, 1, 1, 3, 2].length) (baseStart_1288146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1288146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1288146 prefixEnd_1288146 := by exact prefixLift 1288146
  have htrace : WordTrace (prefixWord ++ tailWord_1288146) baseStart_1288146 baseEnd_1288146 := by
    simpa [prefixWord, tailWord_1288146, baseEnd_1288146] using wordTrace_append hprefix tailTrace_1288146
  have hstable : (prefixWord ++ tailWord_1288146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1288146).length < 2 ^ (prefixWord ++ tailWord_1288146).sum := by decide
  have hdescent : baseEnd_1288146 < baseStart_1288146 := by decide
  rcases family_descends (prefixWord ++ tailWord_1288146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1288159 : List Nat := [1, 1, 2, 3, 4, 2, 2, 2, 2, 2, 2]
def baseStart_1288159 : Nat := 118140960795 + 1288159 * 2 ^ 59
def prefixEnd_1288159 : Nat := 4983230072969 + 3 ^ 40 * 1288159 * 2
def baseEnd_1288159 : Nat := 661444726415130805688371

theorem tailTrace_1288159 : CollatzResearch.WordTrace tailWord_1288159 prefixEnd_1288159 661444726415130805688371 := by
  unfold tailWord_1288159
  simp only [CollatzResearch.WordTrace]
  refine ⟨46983018540227417887211531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31322012360151611924807687 46983018540227417887211531)
  ·
    refine ⟨70474527810341126830817297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46983018540227417887211531 70474527810341126830817297)
    ·
      refine ⟨52855895857755845123112973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70474527810341126830817297 52855895857755845123112973)
      ·
        refine ⟨19820960946658441921167365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52855895857755845123112973 19820960946658441921167365)
        ·
          refine ⟨3716430177498457860218881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19820960946658441921167365 3716430177498457860218881)
          ·
            refine ⟨2787322633123843395164161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3716430177498457860218881 2787322633123843395164161)
            ·
              refine ⟨2090491974842882546373121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2787322633123843395164161 2090491974842882546373121)
              ·
                refine ⟨1567868981132161909779841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2090491974842882546373121 1567868981132161909779841)
                ·
                  refine ⟨1175901735849121432334881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1567868981132161909779841 1175901735849121432334881)
                  ·
                    refine ⟨881926301886841074251161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1175901735849121432334881 881926301886841074251161)
                    ·
                      refine ⟨661444726415130805688371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 881926301886841074251161 661444726415130805688371)
                      ·
                        rfl

theorem cell23_1288159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 2, 2, 2, 2, 2].length) (baseStart_1288159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1288159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1288159 prefixEnd_1288159 := by exact prefixLift 1288159
  have htrace : WordTrace (prefixWord ++ tailWord_1288159) baseStart_1288159 baseEnd_1288159 := by
    simpa [prefixWord, tailWord_1288159, baseEnd_1288159] using wordTrace_append hprefix tailTrace_1288159
  have hstable : (prefixWord ++ tailWord_1288159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1288159).length < 2 ^ (prefixWord ++ tailWord_1288159).sum := by decide
  have hdescent : baseEnd_1288159 < baseStart_1288159 := by decide
  rcases family_descends (prefixWord ++ tailWord_1288159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1288305 : List Nat := [1, 2, 2, 2, 1, 1, 5, 1, 3, 1, 4]
def baseStart_1288305 : Nat := 118140960795 + 1288305 * 2 ^ 59
def prefixEnd_1288305 : Nat := 4983230072969 + 3 ^ 40 * 1288305 * 2
def baseEnd_1288305 : Nat := 661519694590687234462699

theorem tailTrace_1288305 : CollatzResearch.WordTrace tailWord_1288305 prefixEnd_1288305 661519694590687234462699 := by
  unfold tailWord_1288305
  simp only [CollatzResearch.WordTrace]
  refine ⟨46988343597698484822026369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31325562398465656548017579 46988343597698484822026369)
  ·
    refine ⟨35241257698273863616519777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46988343597698484822026369 35241257698273863616519777)
    ·
      refine ⟨26430943273705397712389833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35241257698273863616519777 26430943273705397712389833)
      ·
        refine ⟨19823207455279048284292375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26430943273705397712389833 19823207455279048284292375)
        ·
          refine ⟨29734811182918572426438563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19823207455279048284292375 29734811182918572426438563)
          ·
            refine ⟨44602216774377858639657845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29734811182918572426438563 44602216774377858639657845)
            ·
              refine ⟨4181457822597924247467923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 44602216774377858639657845 4181457822597924247467923)
              ·
                refine ⟨6272186733896886371201885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4181457822597924247467923 6272186733896886371201885)
                ·
                  refine ⟨2352070025211332389200707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6272186733896886371201885 2352070025211332389200707)
                  ·
                    refine ⟨3528105037816998583801061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2352070025211332389200707 3528105037816998583801061)
                    ·
                      refine ⟨661519694590687234462699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3528105037816998583801061 661519694590687234462699)
                      ·
                        rfl

theorem cell23_1288305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 5, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 5, 1, 3, 1, 4].length) (baseStart_1288305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1288305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1288305 prefixEnd_1288305 := by exact prefixLift 1288305
  have htrace : WordTrace (prefixWord ++ tailWord_1288305) baseStart_1288305 baseEnd_1288305 := by
    simpa [prefixWord, tailWord_1288305, baseEnd_1288305] using wordTrace_append hprefix tailTrace_1288305
  have hstable : (prefixWord ++ tailWord_1288305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1288305).length < 2 ^ (prefixWord ++ tailWord_1288305).sum := by decide
  have hdescent : baseEnd_1288305 < baseStart_1288305 := by decide
  rcases family_descends (prefixWord ++ tailWord_1288305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1288352 : List Nat := [2, 1, 1, 4, 2, 3, 2, 1, 1, 2, 4]
def baseStart_1288352 : Nat := 118140960795 + 1288352 * 2 ^ 59
def prefixEnd_1288352 : Nat := 4983230072969 + 3 ^ 40 * 1288352 * 2
def baseEnd_1288352 : Nat := 661543828181448550574983

theorem tailTrace_1288352 : CollatzResearch.WordTrace tailWord_1288352 prefixEnd_1288352 661543828181448550574983 := by
  unfold tailWord_1288352
  simp only [CollatzResearch.WordTrace]
  refine ⟨23495028914264105924493655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31326705219018807899324873 23495028914264105924493655)
  ·
    refine ⟨35242543371396158886740483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23495028914264105924493655 35242543371396158886740483)
    ·
      refine ⟨52863815057094238330110725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35242543371396158886740483 52863815057094238330110725)
      ·
        refine ⟨9911965323205169686895761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 52863815057094238330110725 9911965323205169686895761)
        ·
          refine ⟨7433973992403877265171821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9911965323205169686895761 7433973992403877265171821)
          ·
            refine ⟨2787740247151453974439433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7433973992403877265171821 2787740247151453974439433)
            ·
              refine ⟨2090805185363590480829575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2787740247151453974439433 2090805185363590480829575)
              ·
                refine ⟨3136207778045385721244363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2090805185363590480829575 3136207778045385721244363)
                ·
                  refine ⟨4704311667068078581866545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3136207778045385721244363 4704311667068078581866545)
                  ·
                    refine ⟨3528233750301058936399909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4704311667068078581866545 3528233750301058936399909)
                    ·
                      refine ⟨661543828181448550574983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3528233750301058936399909 661543828181448550574983)
                      ·
                        rfl

theorem cell23_1288352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 2, 1, 1, 2, 4].length) (baseStart_1288352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1288352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1288352 prefixEnd_1288352 := by exact prefixLift 1288352
  have htrace : WordTrace (prefixWord ++ tailWord_1288352) baseStart_1288352 baseEnd_1288352 := by
    simpa [prefixWord, tailWord_1288352, baseEnd_1288352] using wordTrace_append hprefix tailTrace_1288352
  have hstable : (prefixWord ++ tailWord_1288352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1288352).length < 2 ^ (prefixWord ++ tailWord_1288352).sum := by decide
  have hdescent : baseEnd_1288352 < baseStart_1288352 := by decide
  rcases family_descends (prefixWord ++ tailWord_1288352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1288356 : List Nat := [2, 3, 1, 2, 4, 1, 1, 2, 3, 2, 2]
def baseStart_1288356 : Nat := 118140960795 + 1288356 * 2 ^ 59
def prefixEnd_1288356 : Nat := 4983230072969 + 3 ^ 40 * 1288356 * 2
def baseEnd_1288356 : Nat := 661545882104066534924965

theorem tailTrace_1288356 : CollatzResearch.WordTrace tailWord_1288356 prefixEnd_1288356 661545882104066534924965 := by
  unfold tailWord_1288356
  simp only [CollatzResearch.WordTrace]
  refine ⟨23495101860256860266066461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31326802480342480354755281 23495101860256860266066461)
  ·
    refine ⟨8810663197596322599774923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23495101860256860266066461 8810663197596322599774923)
    ·
      refine ⟨13215994796394483899662385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8810663197596322599774923 13215994796394483899662385)
      ·
        refine ⟨9911996097295862924746789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13215994796394483899662385 9911996097295862924746789)
        ·
          refine ⟨1858499268242974298390023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9911996097295862924746789 1858499268242974298390023)
          ·
            refine ⟨2787748902364461447585035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1858499268242974298390023 2787748902364461447585035)
            ·
              refine ⟨4181623353546692171377553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2787748902364461447585035 4181623353546692171377553)
              ·
                refine ⟨3136217515160019128533165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4181623353546692171377553 3136217515160019128533165)
                ·
                  refine ⟨1176081568185007173199937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3136217515160019128533165 1176081568185007173199937)
                  ·
                    refine ⟨882061176138755379899953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1176081568185007173199937 882061176138755379899953)
                    ·
                      refine ⟨661545882104066534924965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 882061176138755379899953 661545882104066534924965)
                      ·
                        rfl

theorem cell23_1288356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 1, 2, 3, 2, 2].length) (baseStart_1288356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1288356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1288356 prefixEnd_1288356 := by exact prefixLift 1288356
  have htrace : WordTrace (prefixWord ++ tailWord_1288356) baseStart_1288356 baseEnd_1288356 := by
    simpa [prefixWord, tailWord_1288356, baseEnd_1288356] using wordTrace_append hprefix tailTrace_1288356
  have hstable : (prefixWord ++ tailWord_1288356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1288356).length < 2 ^ (prefixWord ++ tailWord_1288356).sum := by decide
  have hdescent : baseEnd_1288356 < baseStart_1288356 := by decide
  rcases family_descends (prefixWord ++ tailWord_1288356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1288373 : List Nat := [1, 3, 3, 4, 1, 2, 2, 1, 1, 1, 4]
def baseStart_1288373 : Nat := 118140960795 + 1288373 * 2 ^ 59
def prefixEnd_1288373 : Nat := 4983230072969 + 3 ^ 40 * 1288373 * 2
def baseEnd_1288373 : Nat := 661554611275192968412387

theorem tailTrace_1288373 : CollatzResearch.WordTrace tailWord_1288373 prefixEnd_1288373 661554611275192968412387 := by
  unfold tailWord_1288373
  simp only [CollatzResearch.WordTrace]
  refine ⟨46990823761452132435501773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31327215840968088290334515 46990823761452132435501773)
  ·
    refine ⟨17621558910544549663313165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46990823761452132435501773 17621558910544549663313165)
    ·
      refine ⟨6608084591454206123742437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17621558910544549663313165 6608084591454206123742437)
      ·
        refine ⟨1239015860897663648201707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6608084591454206123742437 1239015860897663648201707)
        ·
          refine ⟨1858523791346495472302561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1239015860897663648201707 1858523791346495472302561)
          ·
            refine ⟨1393892843509871604226921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1858523791346495472302561 1393892843509871604226921)
            ·
              refine ⟨1045419632632403703170191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1393892843509871604226921 1045419632632403703170191)
              ·
                refine ⟨1568129448948605554755287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1045419632632403703170191 1568129448948605554755287)
                ·
                  refine ⟨2352194173422908332132931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1568129448948605554755287 2352194173422908332132931)
                  ·
                    refine ⟨3528291260134362498199397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2352194173422908332132931 3528291260134362498199397)
                    ·
                      refine ⟨661554611275192968412387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3528291260134362498199397 661554611275192968412387)
                      ·
                        rfl

theorem cell23_1288373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 2, 2, 1, 1, 1, 4].length) (baseStart_1288373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1288373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1288373 prefixEnd_1288373 := by exact prefixLift 1288373
  have htrace : WordTrace (prefixWord ++ tailWord_1288373) baseStart_1288373 baseEnd_1288373 := by
    simpa [prefixWord, tailWord_1288373, baseEnd_1288373] using wordTrace_append hprefix tailTrace_1288373
  have hstable : (prefixWord ++ tailWord_1288373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1288373).length < 2 ^ (prefixWord ++ tailWord_1288373).sum := by decide
  have hdescent : baseEnd_1288373 < baseStart_1288373 := by decide
  rcases family_descends (prefixWord ++ tailWord_1288373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1288389 : List Nat := [1, 3, 1, 1, 1, 1, 7, 2, 2, 1, 3]
def baseStart_1288389 : Nat := 118140960795 + 1288389 * 2 ^ 59
def prefixEnd_1288389 : Nat := 4983230072969 + 3 ^ 40 * 1288389 * 2
def baseEnd_1288389 : Nat := 661562826965664905812313

theorem tailTrace_1288389 : CollatzResearch.WordTrace tailWord_1288389 prefixEnd_1288389 661562826965664905812313 := by
  unfold tailWord_1288389
  simp only [CollatzResearch.WordTrace]
  refine ⟨46991407329394167168084221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31327604886262778112056147 46991407329394167168084221)
  ·
    refine ⟨17621777748522812688031583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46991407329394167168084221 17621777748522812688031583)
    ·
      refine ⟨26432666622784219032047375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17621777748522812688031583 26432666622784219032047375)
      ·
        refine ⟨39648999934176328548071063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26432666622784219032047375 39648999934176328548071063)
        ·
          refine ⟨59473499901264492822106595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39648999934176328548071063 59473499901264492822106595)
          ·
            refine ⟨89210249851896739233159893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59473499901264492822106595 89210249851896739233159893)
            ·
              refine ⟨2090865230903829825777185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 89210249851896739233159893 2090865230903829825777185)
              ·
                refine ⟨1568148923177872369332889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2090865230903829825777185 1568148923177872369332889)
                ·
                  refine ⟨1176111692383404276999667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1568148923177872369332889 1176111692383404276999667)
                  ·
                    refine ⟨1764167538575106415499501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1176111692383404276999667 1764167538575106415499501)
                    ·
                      refine ⟨661562826965664905812313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1764167538575106415499501 661562826965664905812313)
                      ·
                        rfl

theorem cell23_1288389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 7, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 7, 2, 2, 1, 3].length) (baseStart_1288389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1288389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1288389 prefixEnd_1288389 := by exact prefixLift 1288389
  have htrace : WordTrace (prefixWord ++ tailWord_1288389) baseStart_1288389 baseEnd_1288389 := by
    simpa [prefixWord, tailWord_1288389, baseEnd_1288389] using wordTrace_append hprefix tailTrace_1288389
  have hstable : (prefixWord ++ tailWord_1288389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1288389).length < 2 ^ (prefixWord ++ tailWord_1288389).sum := by decide
  have hdescent : baseEnd_1288389 < baseStart_1288389 := by decide
  rcases family_descends (prefixWord ++ tailWord_1288389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1288406 : List Nat := [5, 2, 1, 2, 1, 1, 3, 1, 1, 3, 3]
def baseStart_1288406 : Nat := 118140960795 + 1288406 * 2 ^ 59
def prefixEnd_1288406 : Nat := 4983230072969 + 3 ^ 40 * 1288406 * 2
def baseEnd_1288406 : Nat := 661571556136791339299735

theorem tailTrace_1288406 : CollatzResearch.WordTrace tailWord_1288406 prefixEnd_1288406 661571556136791339299735 := by
  unfold tailWord_1288406
  simp only [CollatzResearch.WordTrace]
  refine ⟨2937001710645786191965817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 31328018246888386047635381 2937001710645786191965817)
  ·
    refine ⟨2202751282984339643974363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2937001710645786191965817 2202751282984339643974363)
    ·
      refine ⟨3304126924476509465961545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2202751282984339643974363 3304126924476509465961545)
      ·
        refine ⟨2478095193357382099471159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3304126924476509465961545 2478095193357382099471159)
        ·
          refine ⟨3717142790036073149206739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2478095193357382099471159 3717142790036073149206739)
          ·
            refine ⟨5575714185054109723810109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3717142790036073149206739 5575714185054109723810109)
            ·
              refine ⟨2090892819395291146428791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5575714185054109723810109 2090892819395291146428791)
              ·
                refine ⟨3136339229092936719643187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2090892819395291146428791 3136339229092936719643187)
                ·
                  refine ⟨4704508843639405079464781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3136339229092936719643187 4704508843639405079464781)
                  ·
                    refine ⟨1764190816364776904799293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4704508843639405079464781 1764190816364776904799293)
                    ·
                      refine ⟨661571556136791339299735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1764190816364776904799293 661571556136791339299735)
                      ·
                        rfl

theorem cell23_1288406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 3, 1, 1, 3, 3].length) (baseStart_1288406 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1288406 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1288406 prefixEnd_1288406 := by exact prefixLift 1288406
  have htrace : WordTrace (prefixWord ++ tailWord_1288406) baseStart_1288406 baseEnd_1288406 := by
    simpa [prefixWord, tailWord_1288406, baseEnd_1288406] using wordTrace_append hprefix tailTrace_1288406
  have hstable : (prefixWord ++ tailWord_1288406).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1288406).length < 2 ^ (prefixWord ++ tailWord_1288406).sum := by decide
  have hdescent : baseEnd_1288406 < baseStart_1288406 := by decide
  rcases family_descends (prefixWord ++ tailWord_1288406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1288415 : List Nat := [1, 1, 2, 3, 2, 1, 1, 4, 2, 1, 5]
def baseStart_1288415 : Nat := 118140960795 + 1288415 * 2 ^ 59
def prefixEnd_1288415 : Nat := 4983230072969 + 3 ^ 40 * 1288415 * 2
def baseEnd_1288415 : Nat := 661576177462681804087193

theorem tailTrace_1288415 : CollatzResearch.WordTrace tailWord_1288415 prefixEnd_1288415 661576177462681804087193 := by
  unfold tailWord_1288415
  simp only [CollatzResearch.WordTrace]
  refine ⟨46992355627299973608530699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31328237084866649072353799 46992355627299973608530699)
  ·
    refine ⟨70488533440949960412796049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46992355627299973608530699 70488533440949960412796049)
    ·
      refine ⟨52866400080712470309597037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70488533440949960412796049 52866400080712470309597037)
      ·
        refine ⟨19824900030267176366098889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52866400080712470309597037 19824900030267176366098889)
        ·
          refine ⟨14868675022700382274574167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19824900030267176366098889 14868675022700382274574167)
          ·
            refine ⟨22303012534050573411861251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14868675022700382274574167 22303012534050573411861251)
            ·
              refine ⟨33454518801075860117791877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22303012534050573411861251 33454518801075860117791877)
              ·
                refine ⟨6272722275201723772085977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 33454518801075860117791877 6272722275201723772085977)
                ·
                  refine ⟨4704541706401292829064483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6272722275201723772085977 4704541706401292829064483)
                  ·
                    refine ⟨7056812559601939243596725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4704541706401292829064483 7056812559601939243596725)
                    ·
                      refine ⟨661576177462681804087193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7056812559601939243596725 661576177462681804087193)
                      ·
                        rfl

theorem cell23_1288415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 4, 2, 1, 5].length) (baseStart_1288415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1288415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1288415 prefixEnd_1288415 := by exact prefixLift 1288415
  have htrace : WordTrace (prefixWord ++ tailWord_1288415) baseStart_1288415 baseEnd_1288415 := by
    simpa [prefixWord, tailWord_1288415, baseEnd_1288415] using wordTrace_append hprefix tailTrace_1288415
  have hstable : (prefixWord ++ tailWord_1288415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1288415).length < 2 ^ (prefixWord ++ tailWord_1288415).sum := by decide
  have hdescent : baseEnd_1288415 < baseStart_1288415 := by decide
  rcases family_descends (prefixWord ++ tailWord_1288415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1288446 : List Nat := [4, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2]
def baseStart_1288446 : Nat := 118140960795 + 1288446 * 2 ^ 59
def prefixEnd_1288446 : Nat := 4983230072969 + 3 ^ 40 * 1288446 * 2
def baseEnd_1288446 : Nat := 661592095362971182799551

theorem tailTrace_1288446 : CollatzResearch.WordTrace tailWord_1288446 prefixEnd_1288446 661592095362971182799551 := by
  unfold tailWord_1288446
  simp only [CollatzResearch.WordTrace]
  refine ⟨5874185786273458237863649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 31328990860125110601939461 5874185786273458237863649)
  ·
    refine ⟨4405639339705093678397737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5874185786273458237863649 4405639339705093678397737)
    ·
      refine ⟨3304229504778820258798303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4405639339705093678397737 3304229504778820258798303)
      ·
        refine ⟨4956344257168230388197455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3304229504778820258798303 4956344257168230388197455)
        ·
          refine ⟨7434516385752345582296183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4956344257168230388197455 7434516385752345582296183)
          ·
            refine ⟨11151774578628518373444275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7434516385752345582296183 11151774578628518373444275)
            ·
              refine ⟨16727661867942777560166413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11151774578628518373444275 16727661867942777560166413)
              ·
                refine ⟨6272873200478541585062405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16727661867942777560166413 6272873200478541585062405)
                ·
                  refine ⟨1176163725089726547199201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6272873200478541585062405 1176163725089726547199201)
                  ·
                    refine ⟨882122793817294910399401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1176163725089726547199201 882122793817294910399401)
                    ·
                      refine ⟨661592095362971182799551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 882122793817294910399401 661592095362971182799551)
                      ·
                        rfl

theorem cell23_1288446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2].length) (baseStart_1288446 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1288446 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1288446 prefixEnd_1288446 := by exact prefixLift 1288446
  have htrace : WordTrace (prefixWord ++ tailWord_1288446) baseStart_1288446 baseEnd_1288446 := by
    simpa [prefixWord, tailWord_1288446, baseEnd_1288446] using wordTrace_append hprefix tailTrace_1288446
  have hstable : (prefixWord ++ tailWord_1288446).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1288446).length < 2 ^ (prefixWord ++ tailWord_1288446).sum := by decide
  have hdescent : baseEnd_1288446 < baseStart_1288446 := by decide
  rcases family_descends (prefixWord ++ tailWord_1288446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1288462 : List Nat := [4, 1, 1, 2, 1, 2, 2, 1, 1, 5, 3]
def baseStart_1288462 : Nat := 118140960795 + 1288462 * 2 ^ 59
def prefixEnd_1288462 : Nat := 4983230072969 + 3 ^ 40 * 1288462 * 2
def baseEnd_1288462 : Nat := 661600311053443120199477

theorem tailTrace_1288462 : CollatzResearch.WordTrace tailWord_1288462 prefixEnd_1288462 661600311053443120199477 := by
  unfold tailWord_1288462
  simp only [CollatzResearch.WordTrace]
  refine ⟨5874258732266212579436455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 31329379905419800423661093 5874258732266212579436455)
  ·
    refine ⟨8811388098399318869154683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5874258732266212579436455 8811388098399318869154683)
    ·
      refine ⟨13217082147598978303732025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8811388098399318869154683 13217082147598978303732025)
      ·
        refine ⟨9912811610699233727799019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13217082147598978303732025 9912811610699233727799019)
        ·
          refine ⟨14869217416048850591698529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9912811610699233727799019 14869217416048850591698529)
          ·
            refine ⟨11151913062036637943773897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14869217416048850591698529 11151913062036637943773897)
            ·
              refine ⟨8363934796527478457830423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11151913062036637943773897 8363934796527478457830423)
              ·
                refine ⟨12545902194791217686745635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8363934796527478457830423 12545902194791217686745635)
                ·
                  refine ⟨18818853292186826530118453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12545902194791217686745635 18818853292186826530118453)
                  ·
                    refine ⟨1764267496142514987198605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 18818853292186826530118453 1764267496142514987198605)
                    ·
                      refine ⟨661600311053443120199477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1764267496142514987198605 661600311053443120199477)
                      ·
                        rfl

theorem cell23_1288462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 2, 1, 1, 5, 3].length) (baseStart_1288462 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1288462 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1288462 prefixEnd_1288462 := by exact prefixLift 1288462
  have htrace : WordTrace (prefixWord ++ tailWord_1288462) baseStart_1288462 baseEnd_1288462 := by
    simpa [prefixWord, tailWord_1288462, baseEnd_1288462] using wordTrace_append hprefix tailTrace_1288462
  have hstable : (prefixWord ++ tailWord_1288462).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1288462).length < 2 ^ (prefixWord ++ tailWord_1288462).sum := by decide
  have hdescent : baseEnd_1288462 < baseStart_1288462 := by decide
  rcases family_descends (prefixWord ++ tailWord_1288462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1288519 : List Nat := [1, 1, 4, 1, 2, 2, 3, 1, 2, 4, 2]
def baseStart_1288519 : Nat := 118140960795 + 1288519 * 2 ^ 59
def prefixEnd_1288519 : Nat := 4983230072969 + 3 ^ 40 * 1288519 * 2
def baseEnd_1288519 : Nat := 661629579450749397186715

theorem tailTrace_1288519 : CollatzResearch.WordTrace tailWord_1288519 prefixEnd_1288519 661629579450749397186715 := by
  unfold tailWord_1288519
  simp only [CollatzResearch.WordTrace]
  refine ⟨46996148818923199370316611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31330765879282132913544407 46996148818923199370316611)
  ·
    refine ⟨70494223228384799055474917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46996148818923199370316611 70494223228384799055474917)
    ·
      refine ⟨13217666855322149822901547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 70494223228384799055474917 13217666855322149822901547)
      ·
        refine ⟨19826500282983224734352321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13217666855322149822901547 19826500282983224734352321)
        ·
          refine ⟨14869875212237418550764241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19826500282983224734352321 14869875212237418550764241)
          ·
            refine ⟨11152406409178063913073181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14869875212237418550764241 11152406409178063913073181)
            ·
              refine ⟨4182152403441773967402443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11152406409178063913073181 4182152403441773967402443)
              ·
                refine ⟨6273228605162660951103665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4182152403441773967402443 6273228605162660951103665)
                ·
                  refine ⟨4704921453871995713327749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6273228605162660951103665 4704921453871995713327749)
                  ·
                    refine ⟨882172772600999196248953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4704921453871995713327749 882172772600999196248953)
                    ·
                      refine ⟨661629579450749397186715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 882172772600999196248953 661629579450749397186715)
                      ·
                        rfl

theorem cell23_1288519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 3, 1, 2, 4, 2].length) (baseStart_1288519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1288519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1288519 prefixEnd_1288519 := by exact prefixLift 1288519
  have htrace : WordTrace (prefixWord ++ tailWord_1288519) baseStart_1288519 baseEnd_1288519 := by
    simpa [prefixWord, tailWord_1288519, baseEnd_1288519] using wordTrace_append hprefix tailTrace_1288519
  have hstable : (prefixWord ++ tailWord_1288519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1288519).length < 2 ^ (prefixWord ++ tailWord_1288519).sum := by decide
  have hdescent : baseEnd_1288519 < baseStart_1288519 := by decide
  rcases family_descends (prefixWord ++ tailWord_1288519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1288529 : List Nat := [1, 2, 2, 1, 4, 3, 1, 2, 3, 4]
def baseStart_1288529 : Nat := 118140960795 + 1288529 * 2 ^ 59
def prefixEnd_1288529 : Nat := 4983230072969 + 3 ^ 40 * 1288529 * 2
def baseEnd_1288529 : Nat := 220544904752431452687223

theorem tailTrace_1288529 : CollatzResearch.WordTrace tailWord_1288529 prefixEnd_1288529 220544904752431452687223 := by
  unfold tailWord_1288529
  simp only [CollatzResearch.WordTrace]
  refine ⟨46996513548886971078180641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31331009032591314052120427 46996513548886971078180641)
  ·
    refine ⟨35247385161665228308635481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46996513548886971078180641 35247385161665228308635481)
    ·
      refine ⟨26435538871248921231476611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35247385161665228308635481 26435538871248921231476611)
      ·
        refine ⟨39653308306873381847214917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26435538871248921231476611 39653308306873381847214917)
        ·
          refine ⟨7434995307538759096352797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 39653308306873381847214917 7434995307538759096352797)
          ·
            refine ⟨2788123240327034661132299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7434995307538759096352797 2788123240327034661132299)
            ·
              refine ⟨4182184860490551991698449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2788123240327034661132299 4182184860490551991698449)
              ·
                refine ⟨3136638645367913993773837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4182184860490551991698449 3136638645367913993773837)
                ·
                  refine ⟨1176239492012967747665189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3136638645367913993773837 1176239492012967747665189)
                  ·
                    refine ⟨220544904752431452687223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1176239492012967747665189 220544904752431452687223)
                    ·
                      rfl

theorem cell23_1288529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 1, 2, 3, 4].length) (baseStart_1288529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1288529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1288529 prefixEnd_1288529 := by exact prefixLift 1288529
  have htrace : WordTrace (prefixWord ++ tailWord_1288529) baseStart_1288529 baseEnd_1288529 := by
    simpa [prefixWord, tailWord_1288529, baseEnd_1288529] using wordTrace_append hprefix tailTrace_1288529
  have hstable : (prefixWord ++ tailWord_1288529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1288529).length < 2 ^ (prefixWord ++ tailWord_1288529).sum := by decide
  have hdescent : baseEnd_1288529 < baseStart_1288529 := by decide
  rcases family_descends (prefixWord ++ tailWord_1288529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1288562 : List Nat := [3, 2, 1, 2, 1, 3, 1, 1, 1, 2, 6]
def baseStart_1288562 : Nat := 118140960795 + 1288562 * 2 ^ 59
def prefixEnd_1288562 : Nat := 4983230072969 + 3 ^ 40 * 1288562 * 2
def baseEnd_1288562 : Nat := 661651659118892728949017

theorem tailTrace_1288562 : CollatzResearch.WordTrace tailWord_1288562 prefixEnd_1288562 661651659118892728949017 := by
  unfold tailWord_1288562
  simp only [CollatzResearch.WordTrace]
  refine ⟨11749429289441854428532985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31331811438511611809421293 11749429289441854428532985)
  ·
    refine ⟨8812071967081390821399739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11749429289441854428532985 8812071967081390821399739)
    ·
      refine ⟨13218107950622086232099609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8812071967081390821399739 13218107950622086232099609)
      ·
        refine ⟨9913580962966564674074707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13218107950622086232099609 9913580962966564674074707)
        ·
          refine ⟨14870371444449847011112061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9913580962966564674074707 14870371444449847011112061)
          ·
            refine ⟨5576389291668692629167023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14870371444449847011112061 5576389291668692629167023)
            ·
              refine ⟨8364583937503038943750535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5576389291668692629167023 8364583937503038943750535)
              ·
                refine ⟨12546875906254558415625803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8364583937503038943750535 12546875906254558415625803)
                ·
                  refine ⟨18820313859381837623438705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12546875906254558415625803 18820313859381837623438705)
                  ·
                    refine ⟨14115235394536378217579029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18820313859381837623438705 14115235394536378217579029)
                    ·
                      refine ⟨661651659118892728949017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 14115235394536378217579029 661651659118892728949017)
                      ·
                        rfl

theorem cell23_1288562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 1, 1, 1, 2, 6].length) (baseStart_1288562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1288562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1288562 prefixEnd_1288562 := by exact prefixLift 1288562
  have htrace : WordTrace (prefixWord ++ tailWord_1288562) baseStart_1288562 baseEnd_1288562 := by
    simpa [prefixWord, tailWord_1288562, baseEnd_1288562] using wordTrace_append hprefix tailTrace_1288562
  have hstable : (prefixWord ++ tailWord_1288562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1288562).length < 2 ^ (prefixWord ++ tailWord_1288562).sum := by decide
  have hdescent : baseEnd_1288562 < baseStart_1288562 := by decide
  rcases family_descends (prefixWord ++ tailWord_1288562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1288572 : List Nat := [2, 2, 2, 1, 1, 1, 2, 4, 3, 5]
def baseStart_1288572 : Nat := 118140960795 + 1288572 * 2 ^ 59
def prefixEnd_1288572 : Nat := 4983230072969 + 3 ^ 40 * 1288572 * 2
def baseEnd_1288572 : Nat := 220552264641812563274657

theorem tailTrace_1288572 : CollatzResearch.WordTrace tailWord_1288572 prefixEnd_1288572 220552264641812563274657 := by
  unfold tailWord_1288572
  simp only [CollatzResearch.WordTrace]
  refine ⟨23499040943865594710997985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31332054591820792947997313 23499040943865594710997985)
  ·
    refine ⟨17624280707899196033248489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23499040943865594710997985 17624280707899196033248489)
    ·
      refine ⟨13218210530924397024936367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17624280707899196033248489 13218210530924397024936367)
      ·
        refine ⟨19827315796386595537404551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13218210530924397024936367 19827315796386595537404551)
        ·
          refine ⟨29740973694579893306106827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19827315796386595537404551 29740973694579893306106827)
          ·
            refine ⟨44611460541869839959160241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29740973694579893306106827 44611460541869839959160241)
            ·
              refine ⟨33458595406402379969370181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44611460541869839959160241 33458595406402379969370181)
              ·
                refine ⟨6273486638700446244256909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 33458595406402379969370181 6273486638700446244256909)
                ·
                  refine ⟨2352557489512667341596341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6273486638700446244256909 2352557489512667341596341)
                  ·
                    refine ⟨220552264641812563274657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2352557489512667341596341 220552264641812563274657)
                    ·
                      rfl

theorem cell23_1288572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 4, 3, 5].length) (baseStart_1288572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1288572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1288572 prefixEnd_1288572 := by exact prefixLift 1288572
  have htrace : WordTrace (prefixWord ++ tailWord_1288572) baseStart_1288572 baseEnd_1288572 := by
    simpa [prefixWord, tailWord_1288572, baseEnd_1288572] using wordTrace_append hprefix tailTrace_1288572
  have hstable : (prefixWord ++ tailWord_1288572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1288572).length < 2 ^ (prefixWord ++ tailWord_1288572).sum := by decide
  have hdescent : baseEnd_1288572 < baseStart_1288572 := by decide
  rcases family_descends (prefixWord ++ tailWord_1288572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1288677 : List Nat := [1, 3, 1, 5, 2, 1, 1, 4, 1, 2, 2]
def baseStart_1288677 : Nat := 118140960795 + 1288677 * 2 ^ 59
def prefixEnd_1288677 : Nat := 4983230072969 + 3 ^ 40 * 1288677 * 2
def baseEnd_1288677 : Nat := 661710709394159779010989

theorem tailTrace_1288677 : CollatzResearch.WordTrace tailWord_1288677 prefixEnd_1288677 661710709394159779010989 := by
  unfold tailWord_1288677
  simp only [CollatzResearch.WordTrace]
  refine ⟨47001911552350792354568285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31334607701567194903045523 47001911552350792354568285)
  ·
    refine ⟨17625716832131547132963107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47001911552350792354568285 17625716832131547132963107)
    ·
      refine ⟨26438575248197320699444661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17625716832131547132963107 26438575248197320699444661)
      ·
        refine ⟨2478616429518498815572937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 26438575248197320699444661 2478616429518498815572937)
        ·
          refine ⟨1858962322138874111679703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2478616429518498815572937 1858962322138874111679703)
          ·
            refine ⟨2788443483208311167519555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1858962322138874111679703 2788443483208311167519555)
            ·
              refine ⟨4182665224812466751279333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2788443483208311167519555 4182665224812466751279333)
              ·
                refine ⟨784249729652337515864875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4182665224812466751279333 784249729652337515864875)
                ·
                  refine ⟨1176374594478506273797313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 784249729652337515864875 1176374594478506273797313)
                  ·
                    refine ⟨882280945858879705347985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1176374594478506273797313 882280945858879705347985)
                    ·
                      refine ⟨661710709394159779010989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 882280945858879705347985 661710709394159779010989)
                      ·
                        rfl

theorem cell23_1288677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 1, 4, 1, 2, 2].length) (baseStart_1288677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1288677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1288677 prefixEnd_1288677 := by exact prefixLift 1288677
  have htrace : WordTrace (prefixWord ++ tailWord_1288677) baseStart_1288677 baseEnd_1288677 := by
    simpa [prefixWord, tailWord_1288677, baseEnd_1288677] using wordTrace_append hprefix tailTrace_1288677
  have hstable : (prefixWord ++ tailWord_1288677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1288677).length < 2 ^ (prefixWord ++ tailWord_1288677).sum := by decide
  have hdescent : baseEnd_1288677 < baseStart_1288677 := by decide
  rcases family_descends (prefixWord ++ tailWord_1288677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1288727 : List Nat := [1, 1, 3, 6, 1, 2, 1, 2, 2, 1, 3]
def baseStart_1288727 : Nat := 118140960795 + 1288727 * 2 ^ 59
def prefixEnd_1288727 : Nat := 4983230072969 + 3 ^ 40 * 1288727 * 2
def baseEnd_1288727 : Nat := 661736383426884583385759

theorem tailTrace_1288727 : CollatzResearch.WordTrace tailWord_1288727 prefixEnd_1288727 661736383426884583385759 := by
  unfold tailWord_1288727
  simp only [CollatzResearch.WordTrace]
  refine ⟨47003735202169650893888435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31335823468113100595925623 47003735202169650893888435)
  ·
    refine ⟨70505602803254476340832653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47003735202169650893888435 70505602803254476340832653)
    ·
      refine ⟨26439601051220428627812245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 70505602803254476340832653 26439601051220428627812245)
      ·
        refine ⟨1239356299275957591928699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 26439601051220428627812245 1239356299275957591928699)
        ·
          refine ⟨1859034448913936387893049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1239356299275957591928699 1859034448913936387893049)
          ·
            refine ⟨1394275836685452290919787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1859034448913936387893049 1394275836685452290919787)
            ·
              refine ⟨2091413755028178436379681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1394275836685452290919787 2091413755028178436379681)
              ·
                refine ⟨1568560316271133827284761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2091413755028178436379681 1568560316271133827284761)
                ·
                  refine ⟨1176420237203350370463571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1568560316271133827284761 1176420237203350370463571)
                  ·
                    refine ⟨1764630355805025555695357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1176420237203350370463571 1764630355805025555695357)
                    ·
                      refine ⟨661736383426884583385759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1764630355805025555695357 661736383426884583385759)
                      ·
                        rfl

theorem cell23_1288727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 2, 1, 2, 2, 1, 3].length) (baseStart_1288727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1288727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1288727 prefixEnd_1288727 := by exact prefixLift 1288727
  have htrace : WordTrace (prefixWord ++ tailWord_1288727) baseStart_1288727 baseEnd_1288727 := by
    simpa [prefixWord, tailWord_1288727, baseEnd_1288727] using wordTrace_append hprefix tailTrace_1288727
  have hstable : (prefixWord ++ tailWord_1288727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1288727).length < 2 ^ (prefixWord ++ tailWord_1288727).sum := by decide
  have hdescent : baseEnd_1288727 < baseStart_1288727 := by decide
  rcases family_descends (prefixWord ++ tailWord_1288727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1288739 : List Nat := [1, 1, 1, 4, 4, 1, 1, 3, 7]
def baseStart_1288739 : Nat := 118140960795 + 1288739 * 2 ^ 59
def prefixEnd_1288739 : Nat := 4983230072969 + 3 ^ 40 * 1288739 * 2
def baseEnd_1288739 : Nat := 73526949466082059603967

theorem tailTrace_1288739 : CollatzResearch.WordTrace tailWord_1288739 prefixEnd_1288739 73526949466082059603967 := by
  unfold tailWord_1288739
  simp only [CollatzResearch.WordTrace]
  refine ⟨47004172878126176943325271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31336115252084117962216847 47004172878126176943325271)
  ·
    refine ⟨70506259317189265414987907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47004172878126176943325271 70506259317189265414987907)
    ·
      refine ⟨105759388975783898122481861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70506259317189265414987907 105759388975783898122481861)
      ·
        refine ⟨19829885432959480897965349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 105759388975783898122481861 19829885432959480897965349)
        ·
          refine ⟨3718103518679902668368503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19829885432959480897965349 3718103518679902668368503)
          ·
            refine ⟨5577155278019854002552755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3718103518679902668368503 5577155278019854002552755)
            ·
              refine ⟨8365732917029781003829133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5577155278019854002552755 8365732917029781003829133)
              ·
                refine ⟨3137149843886167876435925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8365732917029781003829133 3137149843886167876435925)
                ·
                  refine ⟨73526949466082059603967, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3137149843886167876435925 73526949466082059603967)
                  ·
                    rfl

theorem cell23_1288739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 1, 3, 7].length) (baseStart_1288739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1288739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1288739 prefixEnd_1288739 := by exact prefixLift 1288739
  have htrace : WordTrace (prefixWord ++ tailWord_1288739) baseStart_1288739 baseEnd_1288739 := by
    simpa [prefixWord, tailWord_1288739, baseEnd_1288739] using wordTrace_append hprefix tailTrace_1288739
  have hstable : (prefixWord ++ tailWord_1288739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1288739).length < 2 ^ (prefixWord ++ tailWord_1288739).sum := by decide
  have hdescent : baseEnd_1288739 < baseStart_1288739 := by decide
  rcases family_descends (prefixWord ++ tailWord_1288739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1288746 : List Nat := [3, 1, 4, 1, 1, 2, 2, 1, 2, 2, 4]
def baseStart_1288746 : Nat := 118140960795 + 1288746 * 2 ^ 59
def prefixEnd_1288746 : Nat := 4983230072969 + 3 ^ 40 * 1288746 * 2
def baseEnd_1288746 : Nat := 661746139559320009048171

theorem tailTrace_1288746 : CollatzResearch.WordTrace tailWord_1288746 prefixEnd_1288746 661746139559320009048171 := by
  unfold tailWord_1288746
  simp only [CollatzResearch.WordTrace]
  refine ⟨11751107047275204284707523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31336285459400544759220061 11751107047275204284707523)
  ·
    refine ⟨17626660570912806427061285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11751107047275204284707523 17626660570912806427061285)
    ·
      refine ⟨3304998857046151205073991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17626660570912806427061285 3304998857046151205073991)
      ·
        refine ⟨4957498285569226807610987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3304998857046151205073991 4957498285569226807610987)
        ·
          refine ⟨7436247428353840211416481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4957498285569226807610987 7436247428353840211416481)
          ·
            refine ⟨5577185571265380158562361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7436247428353840211416481 5577185571265380158562361)
            ·
              refine ⟨4182889178449035118921771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5577185571265380158562361 4182889178449035118921771)
              ·
                refine ⟨6274333767673552678382657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4182889178449035118921771 6274333767673552678382657)
                ·
                  refine ⟨4705750325755164508786993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6274333767673552678382657 4705750325755164508786993)
                  ·
                    refine ⟨3529312744316373381590245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4705750325755164508786993 3529312744316373381590245)
                    ·
                      refine ⟨661746139559320009048171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3529312744316373381590245 661746139559320009048171)
                      ·
                        rfl

theorem cell23_1288746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 2, 1, 2, 2, 4].length) (baseStart_1288746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1288746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1288746 prefixEnd_1288746 := by exact prefixLift 1288746
  have htrace : WordTrace (prefixWord ++ tailWord_1288746) baseStart_1288746 baseEnd_1288746 := by
    simpa [prefixWord, tailWord_1288746, baseEnd_1288746] using wordTrace_append hprefix tailTrace_1288746
  have hstable : (prefixWord ++ tailWord_1288746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1288746).length < 2 ^ (prefixWord ++ tailWord_1288746).sum := by decide
  have hdescent : baseEnd_1288746 < baseStart_1288746 := by decide
  rcases family_descends (prefixWord ++ tailWord_1288746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1288773 : List Nat := [1, 3, 1, 1, 1, 7, 1, 3, 5]
def baseStart_1288773 : Nat := 118140960795 + 1288773 * 2 ^ 59
def prefixEnd_1288773 : Nat := 4983230072969 + 3 ^ 40 * 1288773 * 2
def baseEnd_1288773 : Nat := 73528889281887933712283

theorem tailTrace_1288773 : CollatzResearch.WordTrace tailWord_1288773 prefixEnd_1288773 73528889281887933712283 := by
  unfold tailWord_1288773
  simp only [CollatzResearch.WordTrace]
  refine ⟨47005412960003000750062973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31336941973335333833375315 47005412960003000750062973)
  ·
    refine ⟨17627029860001125281273615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47005412960003000750062973 17627029860001125281273615)
    ·
      refine ⟨26440544790001687921910423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17627029860001125281273615 26440544790001687921910423)
      ·
        refine ⟨39660817185002531882865635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26440544790001687921910423 39660817185002531882865635)
        ·
          refine ⟨59491225777503797824298453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39660817185002531882865635 59491225777503797824298453)
          ·
            refine ⟨1394325604160245261506995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 59491225777503797824298453 1394325604160245261506995)
            ·
              refine ⟨2091488406240367892260493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1394325604160245261506995 2091488406240367892260493)
              ·
                refine ⟨784308152340137959597685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2091488406240367892260493 784308152340137959597685)
                ·
                  refine ⟨73528889281887933712283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 784308152340137959597685 73528889281887933712283)
                  ·
                    rfl

theorem cell23_1288773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 7, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 7, 1, 3, 5].length) (baseStart_1288773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1288773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1288773 prefixEnd_1288773 := by exact prefixLift 1288773
  have htrace : WordTrace (prefixWord ++ tailWord_1288773) baseStart_1288773 baseEnd_1288773 := by
    simpa [prefixWord, tailWord_1288773, baseEnd_1288773] using wordTrace_append hprefix tailTrace_1288773
  have hstable : (prefixWord ++ tailWord_1288773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1288773).length < 2 ^ (prefixWord ++ tailWord_1288773).sum := by decide
  have hdescent : baseEnd_1288773 < baseStart_1288773 := by decide
  rcases family_descends (prefixWord ++ tailWord_1288773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1288786 : List Nat := [3, 2, 2, 1, 2, 1, 3, 2, 2, 5]
def baseStart_1288786 : Nat := 118140960795 + 1288786 * 2 ^ 59
def prefixEnd_1288786 : Nat := 4983230072969 + 3 ^ 40 * 1288786 * 2
def baseEnd_1288786 : Nat := 220588892928499950849329

theorem tailTrace_1288786 : CollatzResearch.WordTrace tailWord_1288786 prefixEnd_1288786 220588892928499950849329 := by
  unfold tailWord_1288786
  simp only [CollatzResearch.WordTrace]
  refine ⟨11751471777238975992571553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31337258072637269313524141 11751471777238975992571553)
  ·
    refine ⟨8813603832929231994428665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11751471777238975992571553 8813603832929231994428665)
    ·
      refine ⟨6610202874696923995821499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8813603832929231994428665 6610202874696923995821499)
      ·
        refine ⟨9915304312045385993732249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6610202874696923995821499 9915304312045385993732249)
        ·
          refine ⟨7436478234034039495299187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9915304312045385993732249 7436478234034039495299187)
          ·
            refine ⟨11154717351051059242948781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7436478234034039495299187 11154717351051059242948781)
            ·
              refine ⟨4183019006644147216105793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11154717351051059242948781 4183019006644147216105793)
              ·
                refine ⟨3137264254983110412079345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4183019006644147216105793 3137264254983110412079345)
                ·
                  refine ⟨2352948191237332809059509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3137264254983110412079345 2352948191237332809059509)
                  ·
                    refine ⟨220588892928499950849329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2352948191237332809059509 220588892928499950849329)
                    ·
                      rfl

theorem cell23_1288786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 3, 2, 2, 5].length) (baseStart_1288786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1288786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1288786 prefixEnd_1288786 := by exact prefixLift 1288786
  have htrace : WordTrace (prefixWord ++ tailWord_1288786) baseStart_1288786 baseEnd_1288786 := by
    simpa [prefixWord, tailWord_1288786, baseEnd_1288786] using wordTrace_append hprefix tailTrace_1288786
  have hstable : (prefixWord ++ tailWord_1288786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1288786).length < 2 ^ (prefixWord ++ tailWord_1288786).sum := by decide
  have hdescent : baseEnd_1288786 < baseStart_1288786 := by decide
  rcases family_descends (prefixWord ++ tailWord_1288786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1288869 : List Nat := [1, 3, 1, 2, 1, 2, 1, 1, 1, 3, 7]
def baseStart_1288869 : Nat := 118140960795 + 1288869 * 2 ^ 59
def prefixEnd_1288869 : Nat := 4983230072969 + 3 ^ 40 * 1288869 * 2
def baseEnd_1288869 : Nat := 661809297679823027810105

theorem tailTrace_1288869 : CollatzResearch.WordTrace tailWord_1288869 prefixEnd_1288869 661809297679823027810105 := by
  unfold tailWord_1288869
  simp only [CollatzResearch.WordTrace]
  refine ⟨47008914367655209145557661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31339276245103472763705107 47008914367655209145557661)
  ·
    refine ⟨17628342887870703429584123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47008914367655209145557661 17628342887870703429584123)
    ·
      refine ⟨26442514331806055144376185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17628342887870703429584123 26442514331806055144376185)
      ·
        refine ⟨19831885748854541358282139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26442514331806055144376185 19831885748854541358282139)
        ·
          refine ⟨29747828623281812037423209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19831885748854541358282139 29747828623281812037423209)
          ·
            refine ⟨22310871467461359028067407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29747828623281812037423209 22310871467461359028067407)
            ·
              refine ⟨33466307201192038542101111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22310871467461359028067407 33466307201192038542101111)
              ·
                refine ⟨50199460801788057813151667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33466307201192038542101111 50199460801788057813151667)
                ·
                  refine ⟨75299191202682086719727501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 50199460801788057813151667 75299191202682086719727501)
                  ·
                    refine ⟨28237196701005782519897813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 75299191202682086719727501 28237196701005782519897813)
                    ·
                      refine ⟨661809297679823027810105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 28237196701005782519897813 661809297679823027810105)
                      ·
                        rfl

theorem cell23_1288869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 1, 1, 3, 7].length) (baseStart_1288869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1288869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1288869 prefixEnd_1288869 := by exact prefixLift 1288869
  have htrace : WordTrace (prefixWord ++ tailWord_1288869) baseStart_1288869 baseEnd_1288869 := by
    simpa [prefixWord, tailWord_1288869, baseEnd_1288869] using wordTrace_append hprefix tailTrace_1288869
  have hstable : (prefixWord ++ tailWord_1288869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1288869).length < 2 ^ (prefixWord ++ tailWord_1288869).sum := by decide
  have hdescent : baseEnd_1288869 < baseStart_1288869 := by decide
  rcases family_descends (prefixWord ++ tailWord_1288869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1288874 : List Nat := [3, 1, 5, 2, 2, 1, 1, 1, 2, 1, 4]
def baseStart_1288874 : Nat := 118140960795 + 1288874 * 2 ^ 59
def prefixEnd_1288874 : Nat := 4983230072969 + 3 ^ 40 * 1288874 * 2
def baseEnd_1288874 : Nat := 661811865083095508247583

theorem tailTrace_1288874 : CollatzResearch.WordTrace tailWord_1288874 prefixEnd_1288874 661811865083095508247583 := by
  unfold tailWord_1288874
  simp only [CollatzResearch.WordTrace]
  refine ⟨11752274183159273749872419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31339397821758063332993117 11752274183159273749872419)
  ·
    refine ⟨17628411274738910624808629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11752274183159273749872419 17628411274738910624808629)
    ·
      refine ⟨1652663557006772871075809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 17628411274738910624808629 1652663557006772871075809)
      ·
        refine ⟨1239497667755079653306857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1652663557006772871075809 1239497667755079653306857)
        ·
          refine ⟨929623250816309739980143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1239497667755079653306857 929623250816309739980143)
          ·
            refine ⟨1394434876224464609970215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 929623250816309739980143 1394434876224464609970215)
            ·
              refine ⟨2091652314336696914955323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1394434876224464609970215 2091652314336696914955323)
              ·
                refine ⟨3137478471505045372432985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2091652314336696914955323 3137478471505045372432985)
                ·
                  refine ⟨2353108853628784029324739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3137478471505045372432985 2353108853628784029324739)
                  ·
                    refine ⟨3529663280443176043987109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2353108853628784029324739 3529663280443176043987109)
                    ·
                      refine ⟨661811865083095508247583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3529663280443176043987109 661811865083095508247583)
                      ·
                        rfl

theorem cell23_1288874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 2, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 2, 1, 1, 1, 2, 1, 4].length) (baseStart_1288874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1288874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1288874 prefixEnd_1288874 := by exact prefixLift 1288874
  have htrace : WordTrace (prefixWord ++ tailWord_1288874) baseStart_1288874 baseEnd_1288874 := by
    simpa [prefixWord, tailWord_1288874, baseEnd_1288874] using wordTrace_append hprefix tailTrace_1288874
  have hstable : (prefixWord ++ tailWord_1288874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1288874).length < 2 ^ (prefixWord ++ tailWord_1288874).sum := by decide
  have hdescent : baseEnd_1288874 < baseStart_1288874 := by decide
  rcases family_descends (prefixWord ++ tailWord_1288874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1288883 : List Nat := [1, 1, 1, 2, 3, 5, 1, 1, 1, 5, 2]
def baseStart_1288883 : Nat := 118140960795 + 1288883 * 2 ^ 59
def prefixEnd_1288883 : Nat := 4983230072969 + 3 ^ 40 * 1288883 * 2
def baseEnd_1288883 : Nat := 661816486408985973035041

theorem tailTrace_1288883 : CollatzResearch.WordTrace tailWord_1288883 prefixEnd_1288883 661816486408985973035041 := by
  unfold tailWord_1288883
  simp only [CollatzResearch.WordTrace]
  refine ⟨47009424989604489536567303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31339616659736326357711535 47009424989604489536567303)
  ·
    refine ⟨70514137484406734304850955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47009424989604489536567303 70514137484406734304850955)
    ·
      refine ⟨105771206226610101457276433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70514137484406734304850955 105771206226610101457276433)
      ·
        refine ⟨79328404669957576092957325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 105771206226610101457276433 79328404669957576092957325)
        ·
          refine ⟨29748151751234091034858997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 79328404669957576092957325 29748151751234091034858997)
          ·
            refine ⟨2788889226678196034518031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 29748151751234091034858997 2788889226678196034518031)
            ·
              refine ⟨4183333840017294051777047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2788889226678196034518031 4183333840017294051777047)
              ·
                refine ⟨6275000760025941077665571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4183333840017294051777047 6275000760025941077665571)
                ·
                  refine ⟨9412501140038911616498357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6275000760025941077665571 9412501140038911616498357)
                  ·
                    refine ⟨882421981878647964046721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9412501140038911616498357 882421981878647964046721)
                    ·
                      refine ⟨661816486408985973035041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 882421981878647964046721 661816486408985973035041)
                      ·
                        rfl

theorem cell23_1288883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 1, 1, 1, 5, 2].length) (baseStart_1288883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1288883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1288883 prefixEnd_1288883 := by exact prefixLift 1288883
  have htrace : WordTrace (prefixWord ++ tailWord_1288883) baseStart_1288883 baseEnd_1288883 := by
    simpa [prefixWord, tailWord_1288883, baseEnd_1288883] using wordTrace_append hprefix tailTrace_1288883
  have hstable : (prefixWord ++ tailWord_1288883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1288883).length < 2 ^ (prefixWord ++ tailWord_1288883).sum := by decide
  have hdescent : baseEnd_1288883 < baseStart_1288883 := by decide
  rcases family_descends (prefixWord ++ tailWord_1288883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1288893 : List Nat := [1, 4, 1, 2, 1, 4, 1, 3, 1, 5]
def baseStart_1288893 : Nat := 118140960795 + 1288893 * 2 ^ 59
def prefixEnd_1288893 : Nat := 4983230072969 + 3 ^ 40 * 1288893 * 2
def baseEnd_1288893 : Nat := 220607207071843644636665

theorem tailTrace_1288893 : CollatzResearch.WordTrace tailWord_1288893 prefixEnd_1288893 220607207071843644636665 := by
  unfold tailWord_1288893
  simp only [CollatzResearch.WordTrace]
  refine ⟨47009789719568261244431333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31339859813045507496287555 47009789719568261244431333)
  ·
    refine ⟨8814335572419048983330875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 47009789719568261244431333 8814335572419048983330875)
    ·
      refine ⟨13221503358628573474996313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8814335572419048983330875 13221503358628573474996313)
      ·
        refine ⟨9916127518971430106247235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13221503358628573474996313 9916127518971430106247235)
        ·
          refine ⟨14874191278457145159370853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9916127518971430106247235 14874191278457145159370853)
          ·
            refine ⟨2788910864710714717382035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14874191278457145159370853 2788910864710714717382035)
            ·
              refine ⟨4183366297066072076073053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2788910864710714717382035 4183366297066072076073053)
              ·
                refine ⟨1568762361399777028527395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4183366297066072076073053 1568762361399777028527395)
                ·
                  refine ⟨2353143542099665542791093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1568762361399777028527395 2353143542099665542791093)
                  ·
                    refine ⟨220607207071843644636665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2353143542099665542791093 220607207071843644636665)
                    ·
                      rfl

theorem cell23_1288893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 1, 3, 1, 5].length) (baseStart_1288893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1288893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1288893 prefixEnd_1288893 := by exact prefixLift 1288893
  have htrace : WordTrace (prefixWord ++ tailWord_1288893) baseStart_1288893 baseEnd_1288893 := by
    simpa [prefixWord, tailWord_1288893, baseEnd_1288893] using wordTrace_append hprefix tailTrace_1288893
  have hstable : (prefixWord ++ tailWord_1288893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1288893).length < 2 ^ (prefixWord ++ tailWord_1288893).sum := by decide
  have hdescent : baseEnd_1288893 < baseStart_1288893 := by decide
  rcases family_descends (prefixWord ++ tailWord_1288893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1288897 : List Nat := [1, 2, 6, 2, 1, 2, 1, 2, 6]
def baseStart_1288897 : Nat := 118140960795 + 1288897 * 2 ^ 59
def prefixEnd_1288897 : Nat := 4983230072969 + 3 ^ 40 * 1288897 * 2
def baseEnd_1288897 : Nat := 73535963904238768695553

theorem tailTrace_1288897 : CollatzResearch.WordTrace tailWord_1288897 prefixEnd_1288897 73535963904238768695553 := by
  unfold tailWord_1288897
  simp only [CollatzResearch.WordTrace]
  refine ⟨47009935611553769927576945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31339957074369179951717963 47009935611553769927576945)
  ·
    refine ⟨35257451708665327445682709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47009935611553769927576945 35257451708665327445682709)
    ·
      refine ⟨1652693048843687224016377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 35257451708665327445682709 1652693048843687224016377)
      ·
        refine ⟨1239519786632765418012283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1652693048843687224016377 1239519786632765418012283)
        ·
          refine ⟨1859279679949148127018425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1239519786632765418012283 1859279679949148127018425)
          ·
            refine ⟨1394459759961861095263819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1859279679949148127018425 1394459759961861095263819)
            ·
              refine ⟨2091689639942791642895729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1394459759961861095263819 2091689639942791642895729)
              ·
                refine ⟨1568767229957093732171797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2091689639942791642895729 1568767229957093732171797)
                ·
                  refine ⟨73535963904238768695553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1568767229957093732171797 73535963904238768695553)
                  ·
                    rfl

theorem cell23_1288897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 2, 1, 2, 6].length) (baseStart_1288897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1288897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1288897 prefixEnd_1288897 := by exact prefixLift 1288897
  have htrace : WordTrace (prefixWord ++ tailWord_1288897) baseStart_1288897 baseEnd_1288897 := by
    simpa [prefixWord, tailWord_1288897, baseEnd_1288897] using wordTrace_append hprefix tailTrace_1288897
  have hstable : (prefixWord ++ tailWord_1288897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1288897).length < 2 ^ (prefixWord ++ tailWord_1288897).sum := by decide
  have hdescent : baseEnd_1288897 < baseStart_1288897 := by decide
  rcases family_descends (prefixWord ++ tailWord_1288897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1288950 : List Nat := [5, 1, 1, 1, 1, 2, 1, 5, 1, 2, 3]
def baseStart_1288950 : Nat := 118140960795 + 1288950 * 2 ^ 59
def prefixEnd_1288950 : Nat := 4983230072969 + 3 ^ 40 * 1288950 * 2
def baseEnd_1288950 : Nat := 661850889612837210897233

theorem tailTrace_1288950 : CollatzResearch.WordTrace tailWord_1288950 prefixEnd_1288950 661850889612837210897233 := by
  unfold tailWord_1288950
  simp only [CollatzResearch.WordTrace]
  refine ⟨2938241792522609998703519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 31341245786907839986170869 2938241792522609998703519)
  ·
    refine ⟨4407362688783914998055279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2938241792522609998703519 4407362688783914998055279)
    ·
      refine ⟨6611044033175872497082919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4407362688783914998055279 6611044033175872497082919)
      ·
        refine ⟨9916566049763808745624379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6611044033175872497082919 9916566049763808745624379)
        ·
          refine ⟨14874849074645713118436569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9916566049763808745624379 14874849074645713118436569)
          ·
            refine ⟨11156136805984284838827427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14874849074645713118436569 11156136805984284838827427)
            ·
              refine ⟨16734205208976427258241141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11156136805984284838827427 16734205208976427258241141)
              ·
                refine ⟨1568831738341540055460107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 16734205208976427258241141 1568831738341540055460107)
                ·
                  refine ⟨2353247607512310083190161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1568831738341540055460107 2353247607512310083190161)
                  ·
                    refine ⟨1764935705634232562392621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2353247607512310083190161 1764935705634232562392621)
                    ·
                      refine ⟨661850889612837210897233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1764935705634232562392621 661850889612837210897233)
                      ·
                        rfl

theorem cell23_1288950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 5, 1, 2, 3].length) (baseStart_1288950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1288950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1288950 prefixEnd_1288950 := by exact prefixLift 1288950
  have htrace : WordTrace (prefixWord ++ tailWord_1288950) baseStart_1288950 baseEnd_1288950 := by
    simpa [prefixWord, tailWord_1288950, baseEnd_1288950] using wordTrace_append hprefix tailTrace_1288950
  have hstable : (prefixWord ++ tailWord_1288950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1288950).length < 2 ^ (prefixWord ++ tailWord_1288950).sum := by decide
  have hdescent : baseEnd_1288950 < baseStart_1288950 := by decide
  rcases family_descends (prefixWord ++ tailWord_1288950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1289003 : List Nat := [1, 1, 1, 1, 2, 1, 2, 5, 3, 4, 2]
def baseStart_1289003 : Nat := 118140960795 + 1289003 * 2 ^ 59
def prefixEnd_1289003 : Nat := 4983230072969 + 3 ^ 40 * 1289003 * 2
def baseEnd_1289003 : Nat := 661878104087525503534489

theorem tailTrace_1289003 : CollatzResearch.WordTrace tailWord_1289003 prefixEnd_1289003 661878104087525503534489 := by
  unfold tailWord_1289003
  simp only [CollatzResearch.WordTrace]
  refine ⟨47013801749169750030935663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31342534499446500020623775 47013801749169750030935663)
  ·
    refine ⟨70520702623754625046403495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47013801749169750030935663 70520702623754625046403495)
    ·
      refine ⟨105781053935631937569605243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70520702623754625046403495 105781053935631937569605243)
      ·
        refine ⟨158671580903447906354407865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105781053935631937569605243 158671580903447906354407865)
        ·
          refine ⟨119003685677585929765805899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 158671580903447906354407865 119003685677585929765805899)
          ·
            refine ⟨178505528516378894648708849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 119003685677585929765805899 178505528516378894648708849)
            ·
              refine ⟨133879146387284170986531637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 178505528516378894648708849 133879146387284170986531637)
              ·
                refine ⟨12551169973807891029987341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 133879146387284170986531637 12551169973807891029987341)
                ·
                  refine ⟨4706688740177959136245253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12551169973807891029987341 4706688740177959136245253)
                  ·
                    refine ⟨882504138783367338045985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4706688740177959136245253 882504138783367338045985)
                    ·
                      refine ⟨661878104087525503534489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 882504138783367338045985 661878104087525503534489)
                      ·
                        rfl

theorem cell23_1289003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 5, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 5, 3, 4, 2].length) (baseStart_1289003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1289003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1289003 prefixEnd_1289003 := by exact prefixLift 1289003
  have htrace : WordTrace (prefixWord ++ tailWord_1289003) baseStart_1289003 baseEnd_1289003 := by
    simpa [prefixWord, tailWord_1289003, baseEnd_1289003] using wordTrace_append hprefix tailTrace_1289003
  have hstable : (prefixWord ++ tailWord_1289003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1289003).length < 2 ^ (prefixWord ++ tailWord_1289003).sum := by decide
  have hdescent : baseEnd_1289003 < baseStart_1289003 := by decide
  rcases family_descends (prefixWord ++ tailWord_1289003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1289023 : List Nat := [1, 1, 2, 2, 5, 1, 1, 1, 2, 4, 3]
def baseStart_1289023 : Nat := 118140960795 + 1289023 * 2 ^ 59
def prefixEnd_1289023 : Nat := 4983230072969 + 3 ^ 40 * 1289023 * 2
def baseEnd_1289023 : Nat := 661888373700615425284397

theorem tailTrace_1289023 : CollatzResearch.WordTrace tailWord_1289023 prefixEnd_1289023 661888373700615425284397 := by
  unfold tailWord_1289023
  simp only [CollatzResearch.WordTrace]
  refine ⟨47014531209097293446663723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31343020806064862297775815 47014531209097293446663723)
  ·
    refine ⟨70521796813645940169995585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47014531209097293446663723 70521796813645940169995585)
    ·
      refine ⟨52891347610234455127496689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70521796813645940169995585 52891347610234455127496689)
      ·
        refine ⟨39668510707675841345622517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52891347610234455127496689 39668510707675841345622517)
        ·
          refine ⟨3718922878844610126152111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 39668510707675841345622517 3718922878844610126152111)
          ·
            refine ⟨5578384318266915189228167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3718922878844610126152111 5578384318266915189228167)
            ·
              refine ⟨8367576477400372783842251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5578384318266915189228167 8367576477400372783842251)
              ·
                refine ⟨12551364716100559175763377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8367576477400372783842251 12551364716100559175763377)
                ·
                  refine ⟨9413523537075419381822533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12551364716100559175763377 9413523537075419381822533)
                  ·
                    refine ⟨1765035663201641134091725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9413523537075419381822533 1765035663201641134091725)
                    ·
                      refine ⟨661888373700615425284397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1765035663201641134091725 661888373700615425284397)
                      ·
                        rfl

theorem cell23_1289023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 1, 1, 2, 4, 3].length) (baseStart_1289023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1289023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1289023 prefixEnd_1289023 := by exact prefixLift 1289023
  have htrace : WordTrace (prefixWord ++ tailWord_1289023) baseStart_1289023 baseEnd_1289023 := by
    simpa [prefixWord, tailWord_1289023, baseEnd_1289023] using wordTrace_append hprefix tailTrace_1289023
  have hstable : (prefixWord ++ tailWord_1289023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1289023).length < 2 ^ (prefixWord ++ tailWord_1289023).sum := by decide
  have hdescent : baseEnd_1289023 < baseStart_1289023 := by decide
  rcases family_descends (prefixWord ++ tailWord_1289023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1289033 : List Nat := [1, 2, 1, 1, 2, 6, 1, 1, 2, 2, 4]
def baseStart_1289033 : Nat := 118140960795 + 1289033 * 2 ^ 59
def prefixEnd_1289033 : Nat := 4983230072969 + 3 ^ 40 * 1289033 * 2
def baseEnd_1289033 : Nat := 661893508507160386159351

theorem tailTrace_1289033 : CollatzResearch.WordTrace tailWord_1289033 prefixEnd_1289033 661893508507160386159351 := by
  unfold tailWord_1289033
  simp only [CollatzResearch.WordTrace]
  refine ⟨47014895939061065154527753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31343263959374043436351835 47014895939061065154527753)
  ·
    refine ⟨35261171954295798865895815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47014895939061065154527753 35261171954295798865895815)
    ·
      refine ⟨52891757931443698298843723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35261171954295798865895815 52891757931443698298843723)
      ·
        refine ⟨79337636897165547448265585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52891757931443698298843723 79337636897165547448265585)
        ·
          refine ⟨59503227672874160586199189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79337636897165547448265585 59503227672874160586199189)
          ·
            refine ⟨2789213797165976277478087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 59503227672874160586199189 2789213797165976277478087)
            ·
              refine ⟨4183820695748964416217131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2789213797165976277478087 4183820695748964416217131)
              ·
                refine ⟨6275731043623446624325697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4183820695748964416217131 6275731043623446624325697)
                ·
                  refine ⟨4706798282717584968244273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6275731043623446624325697 4706798282717584968244273)
                  ·
                    refine ⟨3530098712038188726183205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4706798282717584968244273 3530098712038188726183205)
                    ·
                      refine ⟨661893508507160386159351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3530098712038188726183205 661893508507160386159351)
                      ·
                        rfl

theorem cell23_1289033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 1, 1, 2, 2, 4].length) (baseStart_1289033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1289033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1289033 prefixEnd_1289033 := by exact prefixLift 1289033
  have htrace : WordTrace (prefixWord ++ tailWord_1289033) baseStart_1289033 baseEnd_1289033 := by
    simpa [prefixWord, tailWord_1289033, baseEnd_1289033] using wordTrace_append hprefix tailTrace_1289033
  have hstable : (prefixWord ++ tailWord_1289033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1289033).length < 2 ^ (prefixWord ++ tailWord_1289033).sum := by decide
  have hdescent : baseEnd_1289033 < baseStart_1289033 := by decide
  rcases family_descends (prefixWord ++ tailWord_1289033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1289058 : List Nat := [3, 3, 2, 1, 4, 1, 2, 1, 1, 3, 2]
def baseStart_1289058 : Nat := 118140960795 + 1289058 * 2 ^ 59
def prefixEnd_1289058 : Nat := 4983230072969 + 3 ^ 40 * 1289058 * 2
def baseEnd_1289058 : Nat := 661906345523522788346737

theorem tailTrace_1289058 : CollatzResearch.WordTrace tailWord_1289058 prefixEnd_1289058 661906345523522788346737 := by
  unfold tailWord_1289058
  simp only [CollatzResearch.WordTrace]
  refine ⟨11753951940992623606046957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31343871842646996282791885 11753951940992623606046957)
  ·
    refine ⟨4407731977872233852267609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11753951940992623606046957 4407731977872233852267609)
    ·
      refine ⟨3305798983404175389200707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4407731977872233852267609 3305798983404175389200707)
      ·
        refine ⟨4958698475106263083801061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3305798983404175389200707 4958698475106263083801061)
        ·
          refine ⟨929755964082424328212699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4958698475106263083801061 929755964082424328212699)
          ·
            refine ⟨1394633946123636492319049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 929755964082424328212699 1394633946123636492319049)
            ·
              refine ⟨1045975459592727369239287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1394633946123636492319049 1045975459592727369239287)
              ·
                refine ⟨1568963189389091053858931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1045975459592727369239287 1568963189389091053858931)
                ·
                  refine ⟨2353444784083636580788397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1568963189389091053858931 2353444784083636580788397)
                  ·
                    refine ⟨882541794031363717795649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2353444784083636580788397 882541794031363717795649)
                    ·
                      refine ⟨661906345523522788346737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 882541794031363717795649 661906345523522788346737)
                      ·
                        rfl

theorem cell23_1289058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 4, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 4, 1, 2, 1, 1, 3, 2].length) (baseStart_1289058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1289058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1289058 prefixEnd_1289058 := by exact prefixLift 1289058
  have htrace : WordTrace (prefixWord ++ tailWord_1289058) baseStart_1289058 baseEnd_1289058 := by
    simpa [prefixWord, tailWord_1289058, baseEnd_1289058] using wordTrace_append hprefix tailTrace_1289058
  have hstable : (prefixWord ++ tailWord_1289058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1289058).length < 2 ^ (prefixWord ++ tailWord_1289058).sum := by decide
  have hdescent : baseEnd_1289058 < baseStart_1289058 := by decide
  rcases family_descends (prefixWord ++ tailWord_1289058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1289060 : List Nat := [2, 3, 1, 1, 4, 1, 1, 5, 5]
def baseStart_1289060 : Nat := 118140960795 + 1289060 * 2 ^ 59
def prefixEnd_1289060 : Nat := 4983230072969 + 3 ^ 40 * 1289060 * 2
def baseEnd_1289060 : Nat := 73545263609425753391303

theorem tailTrace_1289060 : CollatzResearch.WordTrace tailWord_1289060 prefixEnd_1289060 73545263609425753391303 := by
  unfold tailWord_1289060
  simp only [CollatzResearch.WordTrace]
  refine ⟨23507940354981624382880317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31343920473308832510507089 23507940354981624382880317)
  ·
    refine ⟨8815477633118109143580119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23507940354981624382880317 8815477633118109143580119)
    ·
      refine ⟨13223216449677163715370179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8815477633118109143580119 13223216449677163715370179)
      ·
        refine ⟨19834824674515745573055269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13223216449677163715370179 19834824674515745573055269)
        ·
          refine ⟨3719029626471702294947863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19834824674515745573055269 3719029626471702294947863)
          ·
            refine ⟨5578544439707553442421795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3719029626471702294947863 5578544439707553442421795)
            ·
              refine ⟨8367816659561330163632693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5578544439707553442421795 8367816659561330163632693)
              ·
                refine ⟨784482811833874702840565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8367816659561330163632693 784482811833874702840565)
                ·
                  refine ⟨73545263609425753391303, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 784482811833874702840565 73545263609425753391303)
                  ·
                    rfl

theorem cell23_1289060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 1, 5, 5].length) (baseStart_1289060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1289060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1289060 prefixEnd_1289060 := by exact prefixLift 1289060
  have htrace : WordTrace (prefixWord ++ tailWord_1289060) baseStart_1289060 baseEnd_1289060 := by
    simpa [prefixWord, tailWord_1289060, baseEnd_1289060] using wordTrace_append hprefix tailTrace_1289060
  have hstable : (prefixWord ++ tailWord_1289060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1289060).length < 2 ^ (prefixWord ++ tailWord_1289060).sum := by decide
  have hdescent : baseEnd_1289060 < baseStart_1289060 := by decide
  rcases family_descends (prefixWord ++ tailWord_1289060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1289093 : List Nat := [1, 3, 1, 1, 3, 3, 1, 2, 1, 3, 4]
def baseStart_1289093 : Nat := 118140960795 + 1289093 * 2 ^ 59
def prefixEnd_1289093 : Nat := 4983230072969 + 3 ^ 40 * 1289093 * 2
def baseEnd_1289093 : Nat := 661924317346430151409075

theorem tailTrace_1289093 : CollatzResearch.WordTrace tailWord_1289093 prefixEnd_1289093 661924317346430151409075 := by
  unfold tailWord_1289093
  simp only [CollatzResearch.WordTrace]
  refine ⟨47017084318843695401711933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31344722879229130267807955 47017084318843695401711933)
  ·
    refine ⟨17631406619566385775641975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47017084318843695401711933 17631406619566385775641975)
    ·
      refine ⟨26447109929349578663462963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17631406619566385775641975 26447109929349578663462963)
      ·
        refine ⟨39670664894024367995194445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26447109929349578663462963 39670664894024367995194445)
        ·
          refine ⟨14876499335259137998197917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39670664894024367995194445 14876499335259137998197917)
          ·
            refine ⟨5578687250722176749324219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14876499335259137998197917 5578687250722176749324219)
            ·
              refine ⟨8368030876083265123986329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5578687250722176749324219 8368030876083265123986329)
              ·
                refine ⟨6276023157062448842989747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8368030876083265123986329 6276023157062448842989747)
                ·
                  refine ⟨9414034735593673264484621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6276023157062448842989747 9414034735593673264484621)
                  ·
                    refine ⟨3530263025847627474181733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9414034735593673264484621 3530263025847627474181733)
                    ·
                      refine ⟨661924317346430151409075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3530263025847627474181733 661924317346430151409075)
                      ·
                        rfl

theorem cell23_1289093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 1, 2, 1, 3, 4].length) (baseStart_1289093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1289093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1289093 prefixEnd_1289093 := by exact prefixLift 1289093
  have htrace : WordTrace (prefixWord ++ tailWord_1289093) baseStart_1289093 baseEnd_1289093 := by
    simpa [prefixWord, tailWord_1289093, baseEnd_1289093] using wordTrace_append hprefix tailTrace_1289093
  have hstable : (prefixWord ++ tailWord_1289093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1289093).length < 2 ^ (prefixWord ++ tailWord_1289093).sum := by decide
  have hdescent : baseEnd_1289093 < baseStart_1289093 := by decide
  rcases family_descends (prefixWord ++ tailWord_1289093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1289127 : List Nat := [1, 1, 6, 1, 3, 1, 1, 2, 2, 1, 4]
def baseStart_1289127 : Nat := 118140960795 + 1289127 * 2 ^ 59
def prefixEnd_1289127 : Nat := 4983230072969 + 3 ^ 40 * 1289127 * 2
def baseEnd_1289127 : Nat := 661941775688683018383919

theorem tailTrace_1289127 : CollatzResearch.WordTrace tailWord_1289127 prefixEnd_1289127 661941775688683018383919 := by
  unfold tailWord_1289127
  simp only [CollatzResearch.WordTrace]
  refine ⟨47018324400720519208449635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31345549600480346138966423 47018324400720519208449635)
  ·
    refine ⟨70527486601080778812674453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47018324400720519208449635 70527486601080778812674453)
    ·
      refine ⟨3305975934425661506844115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 70527486601080778812674453 3305975934425661506844115)
      ·
        refine ⟨4958963901638492260266173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3305975934425661506844115 4958963901638492260266173)
        ·
          refine ⟨1859611463114434597599815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4958963901638492260266173 1859611463114434597599815)
          ·
            refine ⟨2789417194671651896399723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1859611463114434597599815 2789417194671651896399723)
            ·
              refine ⟨4184125792007477844599585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2789417194671651896399723 4184125792007477844599585)
              ·
                refine ⟨3138094344005608383449689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4184125792007477844599585 3138094344005608383449689)
                ·
                  refine ⟨2353570758004206287587267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3138094344005608383449689 2353570758004206287587267)
                  ·
                    refine ⟨3530356137006309431380901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2353570758004206287587267 3530356137006309431380901)
                    ·
                      refine ⟨661941775688683018383919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3530356137006309431380901 661941775688683018383919)
                      ·
                        rfl

theorem cell23_1289127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 1, 2, 2, 1, 4].length) (baseStart_1289127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1289127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1289127 prefixEnd_1289127 := by exact prefixLift 1289127
  have htrace : WordTrace (prefixWord ++ tailWord_1289127) baseStart_1289127 baseEnd_1289127 := by
    simpa [prefixWord, tailWord_1289127, baseEnd_1289127] using wordTrace_append hprefix tailTrace_1289127
  have hstable : (prefixWord ++ tailWord_1289127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1289127).length < 2 ^ (prefixWord ++ tailWord_1289127).sum := by decide
  have hdescent : baseEnd_1289127 < baseStart_1289127 := by decide
  rcases family_descends (prefixWord ++ tailWord_1289127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1289150 : List Nat := [4, 2, 1, 1, 1, 2, 3, 3, 6]
def baseStart_1289150 : Nat := 118140960795 + 1289150 * 2 ^ 59
def prefixEnd_1289150 : Nat := 4983230072969 + 3 ^ 40 * 1289150 * 2
def baseEnd_1289150 : Nat := 73550398415970714266257

theorem tailTrace_1289150 : CollatzResearch.WordTrace tailWord_1289150 prefixEnd_1289150 73550398415970714266257 := by
  unfold tailWord_1289150
  simp only [CollatzResearch.WordTrace]
  refine ⟨5877395409954649267067113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 31346108853091462757691269 5877395409954649267067113)
  ·
    refine ⟨4408046557465986950300335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5877395409954649267067113 4408046557465986950300335)
    ·
      refine ⟨6612069836198980425450503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4408046557465986950300335 6612069836198980425450503)
      ·
        refine ⟨9918104754298470638175755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6612069836198980425450503 9918104754298470638175755)
        ·
          refine ⟨14877157131447705957263633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9918104754298470638175755 14877157131447705957263633)
          ·
            refine ⟨11157867848585779467947725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14877157131447705957263633 11157867848585779467947725)
            ·
              refine ⟨4184200443219667300480397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11157867848585779467947725 4184200443219667300480397)
              ·
                refine ⟨1569075166207375237680149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4184200443219667300480397 1569075166207375237680149)
                ·
                  refine ⟨73550398415970714266257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1569075166207375237680149 73550398415970714266257)
                  ·
                    rfl

theorem cell23_1289150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 3, 3, 6].length) (baseStart_1289150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1289150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1289150 prefixEnd_1289150 := by exact prefixLift 1289150
  have htrace : WordTrace (prefixWord ++ tailWord_1289150) baseStart_1289150 baseEnd_1289150 := by
    simpa [prefixWord, tailWord_1289150, baseEnd_1289150] using wordTrace_append hprefix tailTrace_1289150
  have hstable : (prefixWord ++ tailWord_1289150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1289150).length < 2 ^ (prefixWord ++ tailWord_1289150).sum := by decide
  have hdescent : baseEnd_1289150 < baseStart_1289150 := by decide
  rcases family_descends (prefixWord ++ tailWord_1289150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
