import V185TrunkScan23Chunk1318

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_7812345 : List Nat := [1, 2, 1, 3, 1, 1, 3, 3, 2, 6]
def baseStart_7812345 : Nat := 118140960795 + 7812345 * 2 ^ 59
def prefixEnd_7812345 : Nat := 4983230072969 + 3 ^ 40 * 7812345 * 2
def baseEnd_7812345 : Nat := 1337162674583113965986395

theorem tailTrace_7812345 : CollatzResearch.WordTrace tailWord_7812345 prefixEnd_7812345 1337162674583113965986395 := by
  unfold tailWord_7812345
  simp only [CollatzResearch.WordTrace]
  refine ⟨284939630882215782146654489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189959753921477188097769659 284939630882215782146654489)
  ·
    refine ⟨213704723161661836609990867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 284939630882215782146654489 213704723161661836609990867)
    ·
      refine ⟨320557084742492754914986301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213704723161661836609990867 320557084742492754914986301)
      ·
        refine ⟨120208906778434783093119863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 320557084742492754914986301 120208906778434783093119863)
        ·
          refine ⟨180313360167652174639679795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120208906778434783093119863 180313360167652174639679795)
          ·
            refine ⟨270470040251478261959519693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 180313360167652174639679795 270470040251478261959519693)
            ·
              refine ⟨101426265094304348234819885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 270470040251478261959519693 101426265094304348234819885)
              ·
                refine ⟨38034849410364130588057457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 101426265094304348234819885 38034849410364130588057457)
                ·
                  refine ⟨28526137057773097941043093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38034849410364130588057457 28526137057773097941043093)
                  ·
                    refine ⟨1337162674583113965986395, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28526137057773097941043093 1337162674583113965986395)
                    ·
                      rfl

theorem cell23_7812345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 3, 2, 6].length) (baseStart_7812345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7812345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7812345 prefixEnd_7812345 := by exact prefixLift 7812345
  have htrace : WordTrace (prefixWord ++ tailWord_7812345) baseStart_7812345 baseEnd_7812345 := by
    simpa [prefixWord, tailWord_7812345, baseEnd_7812345] using wordTrace_append hprefix tailTrace_7812345
  have hstable : (prefixWord ++ tailWord_7812345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7812345).length < 2 ^ (prefixWord ++ tailWord_7812345).sum := by decide
  have hdescent : baseEnd_7812345 < baseStart_7812345 := by decide
  rcases family_descends (prefixWord ++ tailWord_7812345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7812346 : List Nat := [3, 1, 1, 1, 1, 4, 5, 1, 2, 1, 3]
def baseStart_7812346 : Nat := 118140960795 + 7812346 * 2 ^ 59
def prefixEnd_7812346 : Nat := 4983230072969 + 3 ^ 40 * 7812346 * 2
def baseEnd_7812346 : Nat := 4011488537229996394046681

theorem tailTrace_7812346 : CollatzResearch.WordTrace tailWord_7812346 prefixEnd_7812346 4011488537229996394046681 := by
  unfold tailWord_7812346
  simp only [CollatzResearch.WordTrace]
  refine ⟨71234916838803039829360223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 189959778236808106211627261 71234916838803039829360223)
  ·
    refine ⟨106852375258204559744040335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71234916838803039829360223 106852375258204559744040335)
    ·
      refine ⟨160278562887306839616060503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106852375258204559744040335 160278562887306839616060503)
      ·
        refine ⟨240417844330960259424090755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160278562887306839616060503 240417844330960259424090755)
        ·
          refine ⟨360626766496440389136136133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 240417844330960259424090755 360626766496440389136136133)
          ·
            refine ⟨67617518718082572963025525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 360626766496440389136136133 67617518718082572963025525)
            ·
              refine ⟨6339142379820241215283643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 67617518718082572963025525 6339142379820241215283643)
              ·
                refine ⟨9508713569730361822925465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6339142379820241215283643 9508713569730361822925465)
                ·
                  refine ⟨7131535177297771367194099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9508713569730361822925465 7131535177297771367194099)
                  ·
                    refine ⟨10697302765946657050791149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7131535177297771367194099 10697302765946657050791149)
                    ·
                      refine ⟨4011488537229996394046681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10697302765946657050791149 4011488537229996394046681)
                      ·
                        rfl

theorem cell23_7812346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 5, 1, 2, 1, 3].length) (baseStart_7812346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7812346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7812346 prefixEnd_7812346 := by exact prefixLift 7812346
  have htrace : WordTrace (prefixWord ++ tailWord_7812346) baseStart_7812346 baseEnd_7812346 := by
    simpa [prefixWord, tailWord_7812346, baseEnd_7812346] using wordTrace_append hprefix tailTrace_7812346
  have hstable : (prefixWord ++ tailWord_7812346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7812346).length < 2 ^ (prefixWord ++ tailWord_7812346).sum := by decide
  have hdescent : baseEnd_7812346 < baseStart_7812346 := by decide
  rcases family_descends (prefixWord ++ tailWord_7812346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7812356 : List Nat := [2, 3, 2, 2, 2, 1, 1, 4, 1, 3, 2]
def baseStart_7812356 : Nat := 118140960795 + 7812356 * 2 ^ 59
def prefixEnd_7812356 : Nat := 4983230072969 + 3 ^ 40 * 7812356 * 2
def baseEnd_7812356 : Nat := 4011493672036541354921635

theorem tailTrace_7812356 : CollatzResearch.WordTrace tailWord_7812356 prefixEnd_7812356 4011493672036541354921635 := by
  unfold tailWord_7812356
  simp only [CollatzResearch.WordTrace]
  refine ⟨142470016042587965512652461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189960021390117287350203281 142470016042587965512652461)
  ·
    refine ⟨53426256015970487067244673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 142470016042587965512652461 53426256015970487067244673)
    ·
      refine ⟨40069692011977865300433505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53426256015970487067244673 40069692011977865300433505)
      ·
        refine ⟨30052269008983398975325129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40069692011977865300433505 30052269008983398975325129)
        ·
          refine ⟨22539201756737549231493847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30052269008983398975325129 22539201756737549231493847)
          ·
            refine ⟨33808802635106323847240771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22539201756737549231493847 33808802635106323847240771)
            ·
              refine ⟨50713203952659485770861157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33808802635106323847240771 50713203952659485770861157)
              ·
                refine ⟨9508725741123653582036467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50713203952659485770861157 9508725741123653582036467)
                ·
                  refine ⟨14263088611685480373054701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9508725741123653582036467 14263088611685480373054701)
                  ·
                    refine ⟨5348658229382055139895513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14263088611685480373054701 5348658229382055139895513)
                    ·
                      refine ⟨4011493672036541354921635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5348658229382055139895513 4011493672036541354921635)
                      ·
                        rfl

theorem cell23_7812356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 1, 4, 1, 3, 2].length) (baseStart_7812356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7812356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7812356 prefixEnd_7812356 := by exact prefixLift 7812356
  have htrace : WordTrace (prefixWord ++ tailWord_7812356) baseStart_7812356 baseEnd_7812356 := by
    simpa [prefixWord, tailWord_7812356, baseEnd_7812356] using wordTrace_append hprefix tailTrace_7812356
  have hstable : (prefixWord ++ tailWord_7812356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7812356).length < 2 ^ (prefixWord ++ tailWord_7812356).sum := by decide
  have hdescent : baseEnd_7812356 < baseStart_7812356 := by decide
  rcases family_descends (prefixWord ++ tailWord_7812356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7812369 : List Nat := [1, 2, 2, 1, 1, 4, 1, 1, 6, 2, 2]
def baseStart_7812369 : Nat := 118140960795 + 7812369 * 2 ^ 59
def prefixEnd_7812369 : Nat := 4983230072969 + 3 ^ 40 * 7812369 * 2
def baseEnd_7812369 : Nat := 4011500347285049804059075

theorem tailTrace_7812369 : CollatzResearch.WordTrace tailWord_7812369 prefixEnd_7812369 4011500347285049804059075 := by
  unfold tailWord_7812369
  simp only [CollatzResearch.WordTrace]
  refine ⟨284940506234128834245528161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189960337489419222830352107 284940506234128834245528161)
  ·
    refine ⟨213705379675596625684146121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 284940506234128834245528161 213705379675596625684146121)
    ·
      refine ⟨160279034756697469263109591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 213705379675596625684146121 160279034756697469263109591)
      ·
        refine ⟨240418552135046203894664387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160279034756697469263109591 240418552135046203894664387)
        ·
          refine ⟨360627828202569305841996581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 240418552135046203894664387 360627828202569305841996581)
          ·
            refine ⟨67617717787981744845374359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 360627828202569305841996581 67617717787981744845374359)
            ·
              refine ⟨101426576681972617268061539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67617717787981744845374359 101426576681972617268061539)
              ·
                refine ⟨152139865022958925902092309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 101426576681972617268061539 152139865022958925902092309)
                ·
                  refine ⟨7131556172951199651660577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 152139865022958925902092309 7131556172951199651660577)
                  ·
                    refine ⟨5348667129713399738745433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7131556172951199651660577 5348667129713399738745433)
                    ·
                      refine ⟨4011500347285049804059075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5348667129713399738745433 4011500347285049804059075)
                      ·
                        rfl

theorem cell23_7812369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 1, 6, 2, 2].length) (baseStart_7812369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7812369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7812369 prefixEnd_7812369 := by exact prefixLift 7812369
  have htrace : WordTrace (prefixWord ++ tailWord_7812369) baseStart_7812369 baseEnd_7812369 := by
    simpa [prefixWord, tailWord_7812369, baseEnd_7812369] using wordTrace_append hprefix tailTrace_7812369
  have hstable : (prefixWord ++ tailWord_7812369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7812369).length < 2 ^ (prefixWord ++ tailWord_7812369).sum := by decide
  have hdescent : baseEnd_7812369 < baseStart_7812369 := by decide
  rcases family_descends (prefixWord ++ tailWord_7812369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7812385 : List Nat := [1, 2, 3, 2, 1, 1, 1, 1, 1, 1, 9]
def baseStart_7812385 : Nat := 118140960795 + 7812385 * 2 ^ 59
def prefixEnd_7812385 : Nat := 4983230072969 + 3 ^ 40 * 7812385 * 2
def baseEnd_7812385 : Nat := 4011508562975521741459001

theorem tailTrace_7812385 : CollatzResearch.WordTrace tailWord_7812385 prefixEnd_7812385 4011508562975521741459001 := by
  unfold tailWord_7812385
  simp only [CollatzResearch.WordTrace]
  refine ⟨284941089802070868978110609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189960726534713912652073739 284941089802070868978110609)
  ·
    refine ⟨213705817351553151733582957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 284941089802070868978110609 213705817351553151733582957)
    ·
      refine ⟨80139681506832431900093609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 213705817351553151733582957 80139681506832431900093609)
      ·
        refine ⟨60104761130124323925070207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80139681506832431900093609 60104761130124323925070207)
        ·
          refine ⟨90157141695186485887605311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60104761130124323925070207 90157141695186485887605311)
          ·
            refine ⟨135235712542779728831407967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90157141695186485887605311 135235712542779728831407967)
            ·
              refine ⟨202853568814169593247111951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 135235712542779728831407967 202853568814169593247111951)
              ·
                refine ⟨304280353221254389870667927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 202853568814169593247111951 304280353221254389870667927)
                ·
                  refine ⟨456420529831881584806001891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 304280353221254389870667927 456420529831881584806001891)
                  ·
                    refine ⟨684630794747822377209002837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 456420529831881584806001891 684630794747822377209002837)
                    ·
                      refine ⟨4011508562975521741459001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 684630794747822377209002837 4011508562975521741459001)
                      ·
                        rfl

theorem cell23_7812385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 1, 1, 1, 9].length) (baseStart_7812385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7812385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7812385 prefixEnd_7812385 := by exact prefixLift 7812385
  have htrace : WordTrace (prefixWord ++ tailWord_7812385) baseStart_7812385 baseEnd_7812385 := by
    simpa [prefixWord, tailWord_7812385, baseEnd_7812385] using wordTrace_append hprefix tailTrace_7812385
  have hstable : (prefixWord ++ tailWord_7812385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7812385).length < 2 ^ (prefixWord ++ tailWord_7812385).sum := by decide
  have hdescent : baseEnd_7812385 < baseStart_7812385 := by decide
  rcases family_descends (prefixWord ++ tailWord_7812385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7812403 : List Nat := [1, 1, 1, 2, 5, 2, 4, 1, 2, 2, 2]
def baseStart_7812403 : Nat := 118140960795 + 7812403 * 2 ^ 59
def prefixEnd_7812403 : Nat := 4983230072969 + 3 ^ 40 * 7812403 * 2
def baseEnd_7812403 : Nat := 4011517805627302671033919

theorem tailTrace_7812403 : CollatzResearch.WordTrace tailWord_7812403 prefixEnd_7812403 4011517805627302671033919 := by
  unfold tailWord_7812403
  simp only [CollatzResearch.WordTrace]
  refine ⟨284941746316005658052265863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189961164210670438701510575 284941746316005658052265863)
  ·
    refine ⟨427412619474008487078398795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 284941746316005658052265863 427412619474008487078398795)
    ·
      refine ⟨641118929211012730617598193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 427412619474008487078398795 641118929211012730617598193)
      ·
        refine ⟨480839196908259547963198645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 641118929211012730617598193 480839196908259547963198645)
        ·
          refine ⟨45078674710149332621549873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 480839196908259547963198645 45078674710149332621549873)
          ·
            refine ⟨33809006032611999466162405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45078674710149332621549873 33809006032611999466162405)
            ·
              refine ⟨6339188631114749899905451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33809006032611999466162405 6339188631114749899905451)
              ·
                refine ⟨9508782946672124849858177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6339188631114749899905451 9508782946672124849858177)
                ·
                  refine ⟨7131587210004093637393633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9508782946672124849858177 7131587210004093637393633)
                  ·
                    refine ⟨5348690407503070228045225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7131587210004093637393633 5348690407503070228045225)
                    ·
                      refine ⟨4011517805627302671033919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5348690407503070228045225 4011517805627302671033919)
                      ·
                        rfl

theorem cell23_7812403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 4, 1, 2, 2, 2].length) (baseStart_7812403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7812403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7812403 prefixEnd_7812403 := by exact prefixLift 7812403
  have htrace : WordTrace (prefixWord ++ tailWord_7812403) baseStart_7812403 baseEnd_7812403 := by
    simpa [prefixWord, tailWord_7812403, baseEnd_7812403] using wordTrace_append hprefix tailTrace_7812403
  have hstable : (prefixWord ++ tailWord_7812403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7812403).length < 2 ^ (prefixWord ++ tailWord_7812403).sum := by decide
  have hdescent : baseEnd_7812403 < baseStart_7812403 := by decide
  rcases family_descends (prefixWord ++ tailWord_7812403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7812559 : List Nat := [1, 1, 2, 1, 1, 4, 4, 1, 4, 4]
def baseStart_7812559 : Nat := 118140960795 + 7812559 * 2 ^ 59
def prefixEnd_7812559 : Nat := 4983230072969 + 3 ^ 40 * 7812559 * 2
def baseEnd_7812559 : Nat := 1337199302869801353561067

theorem tailTrace_7812559 : CollatzResearch.WordTrace tailWord_7812559 prefixEnd_7812559 1337199302869801353561067 := by
  unfold tailWord_7812559
  simp only [CollatzResearch.WordTrace]
  refine ⟨284947436103440496694944731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189964957402293664463296487 284947436103440496694944731)
  ·
    refine ⟨427421154155160745042417097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 284947436103440496694944731 427421154155160745042417097)
    ·
      refine ⟨320565865616370558781812823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 427421154155160745042417097 320565865616370558781812823)
      ·
        refine ⟨480848798424555838172719235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 320565865616370558781812823 480848798424555838172719235)
        ·
          refine ⟨721273197636833757259078853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 480848798424555838172719235 721273197636833757259078853)
          ·
            refine ⟨135238724556906329486077285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 721273197636833757259078853 135238724556906329486077285)
            ·
              refine ⟨25357260854419936778639491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 135238724556906329486077285 25357260854419936778639491)
              ·
                refine ⟨38035891281629905167959237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25357260854419936778639491 38035891281629905167959237)
                ·
                  refine ⟨7131729615305607218992357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38035891281629905167959237 7131729615305607218992357)
                  ·
                    refine ⟨1337199302869801353561067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7131729615305607218992357 1337199302869801353561067)
                    ·
                      rfl

theorem cell23_7812559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 4, 1, 4, 4].length) (baseStart_7812559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7812559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7812559 prefixEnd_7812559 := by exact prefixLift 7812559
  have htrace : WordTrace (prefixWord ++ tailWord_7812559) baseStart_7812559 baseEnd_7812559 := by
    simpa [prefixWord, tailWord_7812559, baseEnd_7812559] using wordTrace_append hprefix tailTrace_7812559
  have hstable : (prefixWord ++ tailWord_7812559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7812559).length < 2 ^ (prefixWord ++ tailWord_7812559).sum := by decide
  have hdescent : baseEnd_7812559 < baseStart_7812559 := by decide
  rcases family_descends (prefixWord ++ tailWord_7812559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7812569 : List Nat := [1, 2, 1, 2, 4, 2, 2, 2, 1, 1, 5]
def baseStart_7812569 : Nat := 118140960795 + 7812569 * 2 ^ 59
def prefixEnd_7812569 : Nat := 4983230072969 + 3 ^ 40 * 7812569 * 2
def baseEnd_7812569 : Nat := 4011603043415949021558155

theorem tailTrace_7812569 : CollatzResearch.WordTrace tailWord_7812569 prefixEnd_7812569 4011603043415949021558155 := by
  unfold tailWord_7812569
  simp only [CollatzResearch.WordTrace]
  refine ⟨284947800833404268402808761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189965200555602845601872507 284947800833404268402808761)
  ·
    refine ⟨213710850625053201302106571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 284947800833404268402808761 213710850625053201302106571)
    ·
      refine ⟨320566275937579801953159857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213710850625053201302106571 320566275937579801953159857)
      ·
        refine ⟨240424706953184851464869893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 320566275937579801953159857 240424706953184851464869893)
        ·
          refine ⟨45079632553722159649663105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 240424706953184851464869893 45079632553722159649663105)
          ·
            refine ⟨33809724415291619737247329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45079632553722159649663105 33809724415291619737247329)
            ·
              refine ⟨25357293311468714802935497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33809724415291619737247329 25357293311468714802935497)
              ·
                refine ⟨19017969983601536102201623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25357293311468714802935497 19017969983601536102201623)
                ·
                  refine ⟨28526954975402304153302435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19017969983601536102201623 28526954975402304153302435)
                  ·
                    refine ⟨42790432463103456229953653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28526954975402304153302435 42790432463103456229953653)
                    ·
                      refine ⟨4011603043415949021558155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42790432463103456229953653 4011603043415949021558155)
                      ·
                        rfl

theorem cell23_7812569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 2, 2, 1, 1, 5].length) (baseStart_7812569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7812569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7812569 prefixEnd_7812569 := by exact prefixLift 7812569
  have htrace : WordTrace (prefixWord ++ tailWord_7812569) baseStart_7812569 baseEnd_7812569 := by
    simpa [prefixWord, tailWord_7812569, baseEnd_7812569] using wordTrace_append hprefix tailTrace_7812569
  have hstable : (prefixWord ++ tailWord_7812569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7812569).length < 2 ^ (prefixWord ++ tailWord_7812569).sum := by decide
  have hdescent : baseEnd_7812569 < baseStart_7812569 := by decide
  rcases family_descends (prefixWord ++ tailWord_7812569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7812579 : List Nat := [1, 1, 1, 6, 2, 1, 2, 1, 1, 1, 6]
def baseStart_7812579 : Nat := 118140960795 + 7812579 * 2 ^ 59
def prefixEnd_7812579 : Nat := 4983230072969 + 3 ^ 40 * 7812579 * 2
def baseEnd_7812579 : Nat := 4011608178222493982433109

theorem tailTrace_7812579 : CollatzResearch.WordTrace tailWord_7812579 prefixEnd_7812579 4011608178222493982433109 := by
  unfold tailWord_7812579
  simp only [CollatzResearch.WordTrace]
  refine ⟨284948165563368040110672791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189965443708912026740448527 284948165563368040110672791)
  ·
    refine ⟨427422248345052060166009187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 284948165563368040110672791 427422248345052060166009187)
    ·
      refine ⟨641133372517578090249013781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 427422248345052060166009187 641133372517578090249013781)
      ·
        refine ⟨30053126836761472980422521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 641133372517578090249013781 30053126836761472980422521)
        ·
          refine ⟨22539845127571104735316891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30053126836761472980422521 22539845127571104735316891)
          ·
            refine ⟨33809767691356657102975337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22539845127571104735316891 33809767691356657102975337)
            ·
              refine ⟨25357325768517492827231503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33809767691356657102975337 25357325768517492827231503)
              ·
                refine ⟨38035988652776239240847255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25357325768517492827231503 38035988652776239240847255)
                ·
                  refine ⟨57053982979164358861270883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38035988652776239240847255 57053982979164358861270883)
                  ·
                    refine ⟨85580974468746538291906325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 57053982979164358861270883 85580974468746538291906325)
                    ·
                      refine ⟨4011608178222493982433109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 85580974468746538291906325 4011608178222493982433109)
                      ·
                        rfl

theorem cell23_7812579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 2, 1, 1, 1, 6].length) (baseStart_7812579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7812579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7812579 prefixEnd_7812579 := by exact prefixLift 7812579
  have htrace : WordTrace (prefixWord ++ tailWord_7812579) baseStart_7812579 baseEnd_7812579 := by
    simpa [prefixWord, tailWord_7812579, baseEnd_7812579] using wordTrace_append hprefix tailTrace_7812579
  have hstable : (prefixWord ++ tailWord_7812579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7812579).length < 2 ^ (prefixWord ++ tailWord_7812579).sum := by decide
  have hdescent : baseEnd_7812579 < baseStart_7812579 := by decide
  rcases family_descends (prefixWord ++ tailWord_7812579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7812583 : List Nat := [1, 1, 5, 2, 1, 4, 1, 2, 1, 1, 4]
def baseStart_7812583 : Nat := 118140960795 + 7812583 * 2 ^ 59
def prefixEnd_7812583 : Nat := 4983230072969 + 3 ^ 40 * 7812583 * 2
def baseEnd_7812583 : Nat := 4011610232145111966783091

theorem tailTrace_7812583 : CollatzResearch.WordTrace tailWord_7812583 prefixEnd_7812583 4011610232145111966783091 := by
  unfold tailWord_7812583
  simp only [CollatzResearch.WordTrace]
  refine ⟨284948311455353548793818403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189965540970235699195878935 284948311455353548793818403)
  ·
    refine ⟨427422467183030323190727605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 284948311455353548793818403 427422467183030323190727605)
    ·
      refine ⟨40070856298409092799130713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 427422467183030323190727605 40070856298409092799130713)
      ·
        refine ⟨30053142223806819599348035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40070856298409092799130713 30053142223806819599348035)
        ·
          refine ⟨45079713335710229399022053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30053142223806819599348035 45079713335710229399022053)
          ·
            refine ⟨8452446250445668012316635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45079713335710229399022053 8452446250445668012316635)
            ·
              refine ⟨12678669375668502018474953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8452446250445668012316635 12678669375668502018474953)
              ·
                refine ⟨9509002031751376513856215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12678669375668502018474953 9509002031751376513856215)
                ·
                  refine ⟨14263503047627064770784323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9509002031751376513856215 14263503047627064770784323)
                  ·
                    refine ⟨21395254571440597156176485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14263503047627064770784323 21395254571440597156176485)
                    ·
                      refine ⟨4011610232145111966783091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21395254571440597156176485 4011610232145111966783091)
                      ·
                        rfl

theorem cell23_7812583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 4, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 4, 1, 2, 1, 1, 4].length) (baseStart_7812583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7812583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7812583 prefixEnd_7812583 := by exact prefixLift 7812583
  have htrace : WordTrace (prefixWord ++ tailWord_7812583) baseStart_7812583 baseEnd_7812583 := by
    simpa [prefixWord, tailWord_7812583, baseEnd_7812583] using wordTrace_append hprefix tailTrace_7812583
  have hstable : (prefixWord ++ tailWord_7812583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7812583).length < 2 ^ (prefixWord ++ tailWord_7812583).sum := by decide
  have hdescent : baseEnd_7812583 < baseStart_7812583 := by decide
  rcases family_descends (prefixWord ++ tailWord_7812583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7812606 : List Nat := [4, 2, 2, 3, 1, 11]
def baseStart_7812606 : Nat := 118140960795 + 7812606 * 2 ^ 59
def prefixEnd_7812606 : Nat := 4983230072969 + 3 ^ 40 * 7812606 * 2
def baseEnd_7812606 : Nat := 16508732683951297846895

theorem tailTrace_7812606 : CollatzResearch.WordTrace tailWord_7812606 prefixEnd_7812606 16508732683951297846895 := by
  unfold tailWord_7812606
  simp only [CollatzResearch.WordTrace]
  refine ⟨35618643791783777965238209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 189966100222846815814603781 35618643791783777965238209)
  ·
    refine ⟨26713982843837833473928657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35618643791783777965238209 26713982843837833473928657)
    ·
      refine ⟨20035487132878375105446493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26713982843837833473928657 20035487132878375105446493)
      ·
        refine ⟨7513307674829390664542435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20035487132878375105446493 7513307674829390664542435)
        ·
          refine ⟨11269961512244085996813653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7513307674829390664542435 11269961512244085996813653)
          ·
            refine ⟨16508732683951297846895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 11269961512244085996813653 16508732683951297846895)
            ·
              rfl

theorem cell23_7812606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 11].length) (baseStart_7812606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7812606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7812606 prefixEnd_7812606 := by exact prefixLift 7812606
  have htrace : WordTrace (prefixWord ++ tailWord_7812606) baseStart_7812606 baseEnd_7812606 := by
    simpa [prefixWord, tailWord_7812606, baseEnd_7812606] using wordTrace_append hprefix tailTrace_7812606
  have hstable : (prefixWord ++ tailWord_7812606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7812606).length < 2 ^ (prefixWord ++ tailWord_7812606).sum := by decide
  have hdescent : baseEnd_7812606 < baseStart_7812606 := by decide
  rcases family_descends (prefixWord ++ tailWord_7812606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7812610 : List Nat := [3, 4, 1, 2, 1, 2, 2, 2, 2, 4]
def baseStart_7812610 : Nat := 118140960795 + 7812610 * 2 ^ 59
def prefixEnd_7812610 : Nat := 4983230072969 + 3 ^ 40 * 7812610 * 2
def baseEnd_7812610 : Nat := 1337208032040927787048489

theorem tailTrace_7812610 : CollatzResearch.WordTrace tailWord_7812610 prefixEnd_7812610 1337208032040927787048489 := by
  unfold tailWord_7812610
  simp only [CollatzResearch.WordTrace]
  refine ⟨71237324056563933101262821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 189966197484170488270034189 71237324056563933101262821)
  ·
    refine ⟨13356998260605737456486779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 71237324056563933101262821 13356998260605737456486779)
    ·
      refine ⟨20035497390908606184730169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13356998260605737456486779 20035497390908606184730169)
      ·
        refine ⟨15026623043181454638547627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20035497390908606184730169 15026623043181454638547627)
        ·
          refine ⟨22539934564772181957821441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15026623043181454638547627 22539934564772181957821441)
          ·
            refine ⟨16904950923579136468366081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22539934564772181957821441 16904950923579136468366081)
            ·
              refine ⟨12678713192684352351274561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16904950923579136468366081 12678713192684352351274561)
              ·
                refine ⟨9509034894513264263455921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12678713192684352351274561 9509034894513264263455921)
                ·
                  refine ⟨7131776170884948197591941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9509034894513264263455921 7131776170884948197591941)
                  ·
                    refine ⟨1337208032040927787048489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7131776170884948197591941 1337208032040927787048489)
                    ·
                      rfl

theorem cell23_7812610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 2, 2, 2, 4].length) (baseStart_7812610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7812610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7812610 prefixEnd_7812610 := by exact prefixLift 7812610
  have htrace : WordTrace (prefixWord ++ tailWord_7812610) baseStart_7812610 baseEnd_7812610 := by
    simpa [prefixWord, tailWord_7812610, baseEnd_7812610] using wordTrace_append hprefix tailTrace_7812610
  have hstable : (prefixWord ++ tailWord_7812610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7812610).length < 2 ^ (prefixWord ++ tailWord_7812610).sum := by decide
  have hdescent : baseEnd_7812610 < baseStart_7812610 := by decide
  rcases family_descends (prefixWord ++ tailWord_7812610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7812616 : List Nat := [2, 1, 3, 2, 1, 1, 2, 3, 4, 1, 3]
def baseStart_7812616 : Nat := 118140960795 + 7812616 * 2 ^ 59
def prefixEnd_7812616 : Nat := 4983230072969 + 3 ^ 40 * 7812616 * 2
def baseEnd_7812616 : Nat := 4011627177006710337670439

theorem tailTrace_7812616 : CollatzResearch.WordTrace tailWord_7812616 prefixEnd_7812616 4011627177006710337670439 := by
  unfold tailWord_7812616
  simp only [CollatzResearch.WordTrace]
  refine ⟨142474757532116997714884851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189966343376155996953179801 142474757532116997714884851)
  ·
    refine ⟨213712136298175496572327277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142474757532116997714884851 213712136298175496572327277)
    ·
      refine ⟨80142051111815811214622729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 213712136298175496572327277 80142051111815811214622729)
      ·
        refine ⟨60106538333861858410967047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80142051111815811214622729 60106538333861858410967047)
        ·
          refine ⟨90159807500792787616450571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60106538333861858410967047 90159807500792787616450571)
          ·
            refine ⟨135239711251189181424675857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90159807500792787616450571 135239711251189181424675857)
            ·
              refine ⟨101429783438391886068506893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 135239711251189181424675857 101429783438391886068506893)
              ·
                refine ⟨38036168789396957275690085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 101429783438391886068506893 38036168789396957275690085)
                ·
                  refine ⟨7131781648011929489191891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38036168789396957275690085 7131781648011929489191891)
                  ·
                    refine ⟨10697672472017894233787837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7131781648011929489191891 10697672472017894233787837)
                    ·
                      refine ⟨4011627177006710337670439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10697672472017894233787837 4011627177006710337670439)
                      ·
                        rfl

theorem cell23_7812616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 3, 4, 1, 3].length) (baseStart_7812616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7812616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7812616 prefixEnd_7812616 := by exact prefixLift 7812616
  have htrace : WordTrace (prefixWord ++ tailWord_7812616) baseStart_7812616 baseEnd_7812616 := by
    simpa [prefixWord, tailWord_7812616, baseEnd_7812616] using wordTrace_append hprefix tailTrace_7812616
  have hstable : (prefixWord ++ tailWord_7812616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7812616).length < 2 ^ (prefixWord ++ tailWord_7812616).sum := by decide
  have hdescent : baseEnd_7812616 < baseStart_7812616 := by decide
  rcases family_descends (prefixWord ++ tailWord_7812616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7812690 : List Nat := [3, 2, 2, 1, 2, 4, 1, 1, 1, 4, 2]
def baseStart_7812690 : Nat := 118140960795 + 7812690 * 2 ^ 59
def prefixEnd_7812690 : Nat := 4983230072969 + 3 ^ 40 * 7812690 * 2
def baseEnd_7812690 : Nat := 4011665174575143048145099

theorem tailTrace_7812690 : CollatzResearch.WordTrace tailWord_7812690 prefixEnd_7812690 4011665174575143048145099 := by
  unfold tailWord_7812690
  simp only [CollatzResearch.WordTrace]
  refine ⟨71238053516491476516990881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 189968142710643937378642349 71238053516491476516990881)
  ·
    refine ⟨53428540137368607387743161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71238053516491476516990881 53428540137368607387743161)
    ·
      refine ⟨40071405103026455540807371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53428540137368607387743161 40071405103026455540807371)
      ·
        refine ⟨60107107654539683311211057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40071405103026455540807371 60107107654539683311211057)
        ·
          refine ⟨45080330740904762483408293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60107107654539683311211057 45080330740904762483408293)
          ·
            refine ⟨8452562013919642965639055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45080330740904762483408293 8452562013919642965639055)
            ·
              refine ⟨12678843020879464448458583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8452562013919642965639055 12678843020879464448458583)
              ·
                refine ⟨19018264531319196672687875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12678843020879464448458583 19018264531319196672687875)
                ·
                  refine ⟨28527396796978795009031813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19018264531319196672687875 28527396796978795009031813)
                  ·
                    refine ⟨5348886899433524064193465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28527396796978795009031813 5348886899433524064193465)
                    ·
                      refine ⟨4011665174575143048145099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5348886899433524064193465 4011665174575143048145099)
                      ·
                        rfl

theorem cell23_7812690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 4, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 4, 1, 1, 1, 4, 2].length) (baseStart_7812690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7812690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7812690 prefixEnd_7812690 := by exact prefixLift 7812690
  have htrace : WordTrace (prefixWord ++ tailWord_7812690) baseStart_7812690 baseEnd_7812690 := by
    simpa [prefixWord, tailWord_7812690, baseEnd_7812690] using wordTrace_append hprefix tailTrace_7812690
  have hstable : (prefixWord ++ tailWord_7812690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7812690).length < 2 ^ (prefixWord ++ tailWord_7812690).sum := by decide
  have hdescent : baseEnd_7812690 < baseStart_7812690 := by decide
  rcases family_descends (prefixWord ++ tailWord_7812690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7812716 : List Nat := [2, 2, 1, 1, 3, 1, 1, 2, 1, 7, 2]
def baseStart_7812716 : Nat := 118140960795 + 7812716 * 2 ^ 59
def prefixEnd_7812716 : Nat := 4983230072969 + 3 ^ 40 * 7812716 * 2
def baseEnd_7812716 : Nat := 4011678525072159946419979

theorem tailTrace_7812716 : CollatzResearch.WordTrace tailWord_7812716 prefixEnd_7812716 4011678525072159946419979 := by
  unfold tailWord_7812716
  simp only [CollatzResearch.WordTrace]
  refine ⟨142476581181935856254205001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189968774909247808338940001 142476581181935856254205001)
  ·
    refine ⟨106857435886451892190653751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142476581181935856254205001 106857435886451892190653751)
    ·
      refine ⟨160286153829677838285980627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106857435886451892190653751 160286153829677838285980627)
      ·
        refine ⟨240429230744516757428970941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160286153829677838285980627 240429230744516757428970941)
        ·
          refine ⟨90160961529193784035864103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 240429230744516757428970941 90160961529193784035864103)
          ·
            refine ⟨135241442293790676053796155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90160961529193784035864103 135241442293790676053796155)
            ·
              refine ⟨202862163440686014080694233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 135241442293790676053796155 202862163440686014080694233)
              ·
                refine ⟨152146622580514510560520675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 202862163440686014080694233 152146622580514510560520675)
                ·
                  refine ⟨228219933870771765840781013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 152146622580514510560520675 228219933870771765840781013)
                  ·
                    refine ⟨5348904700096213261893305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 228219933870771765840781013 5348904700096213261893305)
                    ·
                      refine ⟨4011678525072159946419979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5348904700096213261893305 4011678525072159946419979)
                      ·
                        rfl

theorem cell23_7812716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 7, 2].length) (baseStart_7812716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7812716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7812716 prefixEnd_7812716 := by exact prefixLift 7812716
  have htrace : WordTrace (prefixWord ++ tailWord_7812716) baseStart_7812716 baseEnd_7812716 := by
    simpa [prefixWord, tailWord_7812716, baseEnd_7812716] using wordTrace_append hprefix tailTrace_7812716
  have hstable : (prefixWord ++ tailWord_7812716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7812716).length < 2 ^ (prefixWord ++ tailWord_7812716).sum := by decide
  have hdescent : baseEnd_7812716 < baseStart_7812716 := by decide
  rcases family_descends (prefixWord ++ tailWord_7812716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7812719 : List Nat := [1, 1, 2, 1, 3, 2, 1, 4, 1, 2, 5]
def baseStart_7812719 : Nat := 118140960795 + 7812719 * 2 ^ 59
def prefixEnd_7812719 : Nat := 4983230072969 + 3 ^ 40 * 7812719 * 2
def baseEnd_7812719 : Nat := 4011680065514123434682465

theorem tailTrace_7812719 : CollatzResearch.WordTrace tailWord_7812719 prefixEnd_7812719 4011680065514123434682465 := by
  unfold tailWord_7812719
  simp only [CollatzResearch.WordTrace]
  refine ⟨284953271782860844020769211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189968847855240562680512807 284953271782860844020769211)
  ·
    refine ⟨427429907674291266031153817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 284953271782860844020769211 427429907674291266031153817)
    ·
      refine ⟨320572430755718449523365363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 427429907674291266031153817 320572430755718449523365363)
      ·
        refine ⟨480858646133577674285048045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 320572430755718449523365363 480858646133577674285048045)
        ·
          refine ⟨180321992300091627856893017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 480858646133577674285048045 180321992300091627856893017)
          ·
            refine ⟨135241494225068720892669763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 180321992300091627856893017 135241494225068720892669763)
            ·
              refine ⟨202862241337603081339004645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 135241494225068720892669763 202862241337603081339004645)
              ·
                refine ⟨38036670250800577751063371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 202862241337603081339004645 38036670250800577751063371)
                ·
                  refine ⟨57055005376200866626595057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38036670250800577751063371 57055005376200866626595057)
                  ·
                    refine ⟨42791254032150649969946293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 57055005376200866626595057 42791254032150649969946293)
                    ·
                      refine ⟨4011680065514123434682465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42791254032150649969946293 4011680065514123434682465)
                      ·
                        rfl

theorem cell23_7812719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 4, 1, 2, 5].length) (baseStart_7812719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7812719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7812719 prefixEnd_7812719 := by exact prefixLift 7812719
  have htrace : WordTrace (prefixWord ++ tailWord_7812719) baseStart_7812719 baseEnd_7812719 := by
    simpa [prefixWord, tailWord_7812719, baseEnd_7812719] using wordTrace_append hprefix tailTrace_7812719
  have hstable : (prefixWord ++ tailWord_7812719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7812719).length < 2 ^ (prefixWord ++ tailWord_7812719).sum := by decide
  have hdescent : baseEnd_7812719 < baseStart_7812719 := by decide
  rcases family_descends (prefixWord ++ tailWord_7812719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7812786 : List Nat := [3, 2, 1, 1, 1, 2, 3, 4, 6]
def baseStart_7812786 : Nat := 118140960795 + 7812786 * 2 ^ 59
def prefixEnd_7812786 : Nat := 4983230072969 + 3 ^ 40 * 7812786 * 2
def baseEnd_7812786 : Nat := 445746052079774963616073

theorem tailTrace_7812786 : CollatzResearch.WordTrace tailWord_7812786 prefixEnd_7812786 445746052079774963616073 := by
  unfold tailWord_7812786
  simp only [CollatzResearch.WordTrace]
  refine ⟨71238928868404528615864553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 189970476982412076308972141 71238928868404528615864553)
  ·
    refine ⟨53429196651303396461898415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71238928868404528615864553 53429196651303396461898415)
    ·
      refine ⟨80143794976955094692847623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53429196651303396461898415 80143794976955094692847623)
      ·
        refine ⟨120215692465432642039271435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80143794976955094692847623 120215692465432642039271435)
        ·
          refine ⟨180323538698148963058907153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120215692465432642039271435 180323538698148963058907153)
          ·
            refine ⟨135242654023611722294180365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 180323538698148963058907153 135242654023611722294180365)
            ·
              refine ⟨50715995258854395860317637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 135242654023611722294180365 50715995258854395860317637)
              ·
                refine ⟨9509249111035199223809557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50715995258854395860317637 9509249111035199223809557)
                ·
                  refine ⟨445746052079774963616073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9509249111035199223809557 445746052079774963616073)
                  ·
                    rfl

theorem cell23_7812786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 3, 4, 6].length) (baseStart_7812786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7812786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7812786 prefixEnd_7812786 := by exact prefixLift 7812786
  have htrace : WordTrace (prefixWord ++ tailWord_7812786) baseStart_7812786 baseEnd_7812786 := by
    simpa [prefixWord, tailWord_7812786, baseEnd_7812786] using wordTrace_append hprefix tailTrace_7812786
  have hstable : (prefixWord ++ tailWord_7812786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7812786).length < 2 ^ (prefixWord ++ tailWord_7812786).sum := by decide
  have hdescent : baseEnd_7812786 < baseStart_7812786 := by decide
  rcases family_descends (prefixWord ++ tailWord_7812786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7812819 : List Nat := [1, 1, 1, 2, 1, 1, 1, 2, 2, 1, 10]
def baseStart_7812819 : Nat := 118140960795 + 7812819 * 2 ^ 59
def prefixEnd_7812819 : Nat := 4983230072969 + 3 ^ 40 * 7812819 * 2
def baseEnd_7812819 : Nat := 4011731413579573043432005

theorem tailTrace_7812819 : CollatzResearch.WordTrace tailWord_7812819 prefixEnd_7812819 4011731413579573043432005 := by
  unfold tailWord_7812819
  simp only [CollatzResearch.WordTrace]
  refine ⟨284956919082498561099409511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189971279388332374066273007 284956919082498561099409511)
  ·
    refine ⟨427435378623747841649114267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 284956919082498561099409511 427435378623747841649114267)
    ·
      refine ⟨641153067935621762473671401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 427435378623747841649114267 641153067935621762473671401)
      ·
        refine ⟨480864800951716321855253551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 641153067935621762473671401 480864800951716321855253551)
        ·
          refine ⟨721297201427574482782880327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 480864800951716321855253551 721297201427574482782880327)
          ·
            refine ⟨1081945802141361724174320491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 721297201427574482782880327 1081945802141361724174320491)
            ·
              refine ⟨1622918703212042586261480737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1081945802141361724174320491 1622918703212042586261480737)
              ·
                refine ⟨1217189027409031939696110553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1622918703212042586261480737 1217189027409031939696110553)
                ·
                  refine ⟨912891770556773954772082915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1217189027409031939696110553 912891770556773954772082915)
                  ·
                    refine ⟨1369337655835160932158124373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 912891770556773954772082915 1369337655835160932158124373)
                    ·
                      refine ⟨4011731413579573043432005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 10 1369337655835160932158124373 4011731413579573043432005)
                      ·
                        rfl

theorem cell23_7812819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 2, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 2, 2, 1, 10].length) (baseStart_7812819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7812819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7812819 prefixEnd_7812819 := by exact prefixLift 7812819
  have htrace : WordTrace (prefixWord ++ tailWord_7812819) baseStart_7812819 baseEnd_7812819 := by
    simpa [prefixWord, tailWord_7812819, baseEnd_7812819] using wordTrace_append hprefix tailTrace_7812819
  have hstable : (prefixWord ++ tailWord_7812819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7812819).length < 2 ^ (prefixWord ++ tailWord_7812819).sum := by decide
  have hdescent : baseEnd_7812819 < baseStart_7812819 := by decide
  rcases family_descends (prefixWord ++ tailWord_7812819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7812823 : List Nat := [1, 1, 3, 2, 1, 3, 3, 1, 1, 5, 2]
def baseStart_7812823 : Nat := 118140960795 + 7812823 * 2 ^ 59
def prefixEnd_7812823 : Nat := 4983230072969 + 3 ^ 40 * 7812823 * 2
def baseEnd_7812823 : Nat := 4011733467502191027781987

theorem tailTrace_7812823 : CollatzResearch.WordTrace tailWord_7812823 prefixEnd_7812823 4011733467502191027781987 := by
  unfold tailWord_7812823
  simp only [CollatzResearch.WordTrace]
  refine ⟨284957064974484069782555123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189971376649656046521703415 284957064974484069782555123)
  ·
    refine ⟨427435597461726104673832685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 284957064974484069782555123 427435597461726104673832685)
    ·
      refine ⟨160288349048147289252687257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 427435597461726104673832685 160288349048147289252687257)
      ·
        refine ⟨120216261786110466939515443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 160288349048147289252687257 120216261786110466939515443)
        ·
          refine ⟨180324392679165700409273165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120216261786110466939515443 180324392679165700409273165)
          ·
            refine ⟨67621647254687137653477437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 180324392679165700409273165 67621647254687137653477437)
            ·
              refine ⟨25358117720507676620054039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67621647254687137653477437 25358117720507676620054039)
              ·
                refine ⟨38037176580761514930081059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25358117720507676620054039 38037176580761514930081059)
                ·
                  refine ⟨57055764871142272395121589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38037176580761514930081059 57055764871142272395121589)
                  ·
                    refine ⟨5348977956669588037042649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 57055764871142272395121589 5348977956669588037042649)
                    ·
                      refine ⟨4011733467502191027781987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5348977956669588037042649 4011733467502191027781987)
                      ·
                        rfl

theorem cell23_7812823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 3, 1, 1, 5, 2].length) (baseStart_7812823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7812823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7812823 prefixEnd_7812823 := by exact prefixLift 7812823
  have htrace : WordTrace (prefixWord ++ tailWord_7812823) baseStart_7812823 baseEnd_7812823 := by
    simpa [prefixWord, tailWord_7812823, baseEnd_7812823] using wordTrace_append hprefix tailTrace_7812823
  have hstable : (prefixWord ++ tailWord_7812823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7812823).length < 2 ^ (prefixWord ++ tailWord_7812823).sum := by decide
  have hdescent : baseEnd_7812823 < baseStart_7812823 := by decide
  rcases family_descends (prefixWord ++ tailWord_7812823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7812856 : List Nat := [2, 1, 2, 1, 1, 2, 2, 1, 2, 6, 3]
def baseStart_7812856 : Nat := 118140960795 + 7812856 * 2 ^ 59
def prefixEnd_7812856 : Nat := 4983230072969 + 3 ^ 40 * 7812856 * 2
def baseEnd_7812856 : Nat := 4011750412363789398669335

theorem tailTrace_7812856 : CollatzResearch.WordTrace tailWord_7812856 prefixEnd_7812856 4011750412363789398669335 := by
  unfold tailWord_7812856
  simp only [CollatzResearch.WordTrace]
  refine ⟨142479134291682258209253211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189972179055576344279004281 142479134291682258209253211)
  ·
    refine ⟨213718701437523387313879817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142479134291682258209253211 213718701437523387313879817)
    ·
      refine ⟨160289026078142540485409863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 213718701437523387313879817 160289026078142540485409863)
      ·
        refine ⟨240433539117213810728114795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160289026078142540485409863 240433539117213810728114795)
        ·
          refine ⟨360650308675820716092172193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 240433539117213810728114795 360650308675820716092172193)
          ·
            refine ⟨270487731506865537069129145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 360650308675820716092172193 270487731506865537069129145)
            ·
              refine ⟨202865798630149152801846859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 270487731506865537069129145 202865798630149152801846859)
              ·
                refine ⟨304298697945223729202770289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 202865798630149152801846859 304298697945223729202770289)
                ·
                  refine ⟨228224023458917796902077717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 304298697945223729202770289 228224023458917796902077717)
                  ·
                    refine ⟨10698001099636771729784893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 228224023458917796902077717 10698001099636771729784893)
                    ·
                      refine ⟨4011750412363789398669335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10698001099636771729784893 4011750412363789398669335)
                      ·
                        rfl

theorem cell23_7812856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 1, 2, 6, 3].length) (baseStart_7812856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7812856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7812856 prefixEnd_7812856 := by exact prefixLift 7812856
  have htrace : WordTrace (prefixWord ++ tailWord_7812856) baseStart_7812856 baseEnd_7812856 := by
    simpa [prefixWord, tailWord_7812856, baseEnd_7812856] using wordTrace_append hprefix tailTrace_7812856
  have hstable : (prefixWord ++ tailWord_7812856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7812856).length < 2 ^ (prefixWord ++ tailWord_7812856).sum := by decide
  have hdescent : baseEnd_7812856 < baseStart_7812856 := by decide
  rcases family_descends (prefixWord ++ tailWord_7812856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7812863 : List Nat := [1, 1, 2, 2, 1, 3, 2, 5, 2, 4]
def baseStart_7812863 : Nat := 118140960795 + 7812863 * 2 ^ 59
def prefixEnd_7812863 : Nat := 4983230072969 + 3 ^ 40 * 7812863 * 2
def baseEnd_7812863 : Nat := 1337251335576123623760601

theorem tailTrace_7812863 : CollatzResearch.WordTrace tailWord_7812863 prefixEnd_7812863 1337251335576123623760601 := by
  unfold tailWord_7812863
  simp only [CollatzResearch.WordTrace]
  refine ⟨284958523894339156614011243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189972349262892771076007495 284958523894339156614011243)
  ·
    refine ⟨427437785841508734921016865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 284958523894339156614011243 427437785841508734921016865)
    ·
      refine ⟨320578339381131551190762649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 427437785841508734921016865 320578339381131551190762649)
      ·
        refine ⟨240433754535848663393071987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 320578339381131551190762649 240433754535848663393071987)
        ·
          refine ⟨360650631803772995089607981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 240433754535848663393071987 360650631803772995089607981)
          ·
            refine ⟨135243986926414873158602993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 360650631803772995089607981 135243986926414873158602993)
            ·
              refine ⟨101432990194811154868952245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 135243986926414873158602993 101432990194811154868952245)
              ·
                refine ⟨9509342830763545768964273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 101432990194811154868952245 9509342830763545768964273)
                ·
                  refine ⟨7132007123072659326723205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9509342830763545768964273 7132007123072659326723205)
                  ·
                    refine ⟨1337251335576123623760601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7132007123072659326723205 1337251335576123623760601)
                    ·
                      rfl

theorem cell23_7812863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 5, 2, 4].length) (baseStart_7812863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7812863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7812863 prefixEnd_7812863 := by exact prefixLift 7812863
  have htrace : WordTrace (prefixWord ++ tailWord_7812863) baseStart_7812863 baseEnd_7812863 := by
    simpa [prefixWord, tailWord_7812863, baseEnd_7812863] using wordTrace_append hprefix tailTrace_7812863
  have hstable : (prefixWord ++ tailWord_7812863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7812863).length < 2 ^ (prefixWord ++ tailWord_7812863).sum := by decide
  have hdescent : baseEnd_7812863 < baseStart_7812863 := by decide
  rcases family_descends (prefixWord ++ tailWord_7812863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7812890 : List Nat := [3, 1, 1, 3, 2, 2, 2, 3, 1, 2, 3]
def baseStart_7812890 : Nat := 118140960795 + 7812890 * 2 ^ 59
def prefixEnd_7812890 : Nat := 4983230072969 + 3 ^ 40 * 7812890 * 2
def baseEnd_7812890 : Nat := 4011767870706042265644179

theorem tailTrace_7812890 : CollatzResearch.WordTrace tailWord_7812890 prefixEnd_7812890 4011767870706042265644179 := by
  unfold tailWord_7812890
  simp only [CollatzResearch.WordTrace]
  refine ⟨71239877166310335056311031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 189973005776827560150162749 71239877166310335056311031)
  ·
    refine ⟨106859815749465502584466547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71239877166310335056311031 106859815749465502584466547)
    ·
      refine ⟨160289723624198253876699821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106859815749465502584466547 160289723624198253876699821)
      ·
        refine ⟨60108646359074345203762433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 160289723624198253876699821 60108646359074345203762433)
        ·
          refine ⟨45081484769305758902821825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60108646359074345203762433 45081484769305758902821825)
          ·
            refine ⟨33811113576979319177116369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45081484769305758902821825 33811113576979319177116369)
            ·
              refine ⟨25358335182734489382837277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33811113576979319177116369 25358335182734489382837277)
              ·
                refine ⟨9509375693525433518563979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25358335182734489382837277 9509375693525433518563979)
                ·
                  refine ⟨14264063540288150277845969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9509375693525433518563979 14264063540288150277845969)
                  ·
                    refine ⟨10698047655216112708384477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14264063540288150277845969 10698047655216112708384477)
                    ·
                      refine ⟨4011767870706042265644179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10698047655216112708384477 4011767870706042265644179)
                      ·
                        rfl

theorem cell23_7812890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 2, 3, 1, 2, 3].length) (baseStart_7812890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7812890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7812890 prefixEnd_7812890 := by exact prefixLift 7812890
  have htrace : WordTrace (prefixWord ++ tailWord_7812890) baseStart_7812890 baseEnd_7812890 := by
    simpa [prefixWord, tailWord_7812890, baseEnd_7812890] using wordTrace_append hprefix tailTrace_7812890
  have hstable : (prefixWord ++ tailWord_7812890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7812890).length < 2 ^ (prefixWord ++ tailWord_7812890).sum := by decide
  have hdescent : baseEnd_7812890 < baseStart_7812890 := by decide
  rcases family_descends (prefixWord ++ tailWord_7812890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7812904 : List Nat := [2, 1, 5, 1, 1, 4, 1, 1, 3, 2, 2]
def baseStart_7812904 : Nat := 118140960795 + 7812904 * 2 ^ 59
def prefixEnd_7812904 : Nat := 4983230072969 + 3 ^ 40 * 7812904 * 2
def baseEnd_7812904 : Nat := 4011775059435205210869115

theorem tailTrace_7812904 : CollatzResearch.WordTrace tailWord_7812904 prefixEnd_7812904 4011775059435205210869115 := by
  unfold tailWord_7812904
  simp only [CollatzResearch.WordTrace]
  refine ⟨142480009643595310308126883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189973346191460413744169177 142480009643595310308126883)
  ·
    refine ⟨213720014465392965462190325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142480009643595310308126883 213720014465392965462190325)
    ·
      refine ⟨20036251356130590512080343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 213720014465392965462190325 20036251356130590512080343)
      ·
        refine ⟨30054377034195885768120515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20036251356130590512080343 30054377034195885768120515)
        ·
          refine ⟨45081565551293828652180773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30054377034195885768120515 45081565551293828652180773)
          ·
            refine ⟨8452793540867592872283895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45081565551293828652180773 8452793540867592872283895)
            ·
              refine ⟨12679190311301389308425843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8452793540867592872283895 12679190311301389308425843)
              ·
                refine ⟨19018785466952083962638765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12679190311301389308425843 19018785466952083962638765)
                ·
                  refine ⟨7132044550107031485989537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19018785466952083962638765 7132044550107031485989537)
                  ·
                    refine ⟨5349033412580273614492153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7132044550107031485989537 5349033412580273614492153)
                    ·
                      refine ⟨4011775059435205210869115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5349033412580273614492153 4011775059435205210869115)
                      ·
                        rfl

theorem cell23_7812904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 4, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 4, 1, 1, 3, 2, 2].length) (baseStart_7812904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7812904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7812904 prefixEnd_7812904 := by exact prefixLift 7812904
  have htrace : WordTrace (prefixWord ++ tailWord_7812904) baseStart_7812904 baseEnd_7812904 := by
    simpa [prefixWord, tailWord_7812904, baseEnd_7812904] using wordTrace_append hprefix tailTrace_7812904
  have hstable : (prefixWord ++ tailWord_7812904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7812904).length < 2 ^ (prefixWord ++ tailWord_7812904).sum := by decide
  have hdescent : baseEnd_7812904 < baseStart_7812904 := by decide
  rcases family_descends (prefixWord ++ tailWord_7812904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7812910 : List Nat := [4, 1, 3, 2, 2, 1, 2, 8]
def baseStart_7812910 : Nat := 118140960795 + 7812910 * 2 ^ 59
def prefixEnd_7812910 : Nat := 4983230072969 + 3 ^ 40 * 7812910 * 2
def baseEnd_7812910 : Nat := 148584375567375266199781

theorem tailTrace_7812910 : CollatzResearch.WordTrace tailWord_7812910 prefixEnd_7812910 148584375567375266199781 := by
  unfold tailWord_7812910
  simp only [CollatzResearch.WordTrace]
  refine ⟨35620029765646110455121523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 189973492083445922427314789 35620029765646110455121523)
  ·
    refine ⟨53430044648469165682682285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35620029765646110455121523 53430044648469165682682285)
    ·
      refine ⟨20036266743175937131005857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53430044648469165682682285 20036266743175937131005857)
      ·
        refine ⟨15027200057381952848254393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20036266743175937131005857 15027200057381952848254393)
        ·
          refine ⟨11270400043036464636190795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15027200057381952848254393 11270400043036464636190795)
          ·
            refine ⟨16905600064554696954286193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11270400043036464636190795 16905600064554696954286193)
            ·
              refine ⟨12679200048416022715714645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16905600064554696954286193 12679200048416022715714645)
              ·
                refine ⟨148584375567375266199781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12679200048416022715714645 148584375567375266199781)
                ·
                  rfl

theorem cell23_7812910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 2, 8].length) (baseStart_7812910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7812910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7812910 prefixEnd_7812910 := by exact prefixLift 7812910
  have htrace : WordTrace (prefixWord ++ tailWord_7812910) baseStart_7812910 baseEnd_7812910 := by
    simpa [prefixWord, tailWord_7812910, baseEnd_7812910] using wordTrace_append hprefix tailTrace_7812910
  have hstable : (prefixWord ++ tailWord_7812910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7812910).length < 2 ^ (prefixWord ++ tailWord_7812910).sum := by decide
  have hdescent : baseEnd_7812910 < baseStart_7812910 := by decide
  rcases family_descends (prefixWord ++ tailWord_7812910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7812973 : List Nat := [1, 5, 1, 1, 1, 1, 3, 1, 1, 4, 4]
def baseStart_7812973 : Nat := 118140960795 + 7812973 * 2 ^ 59
def prefixEnd_7812973 : Nat := 4983230072969 + 3 ^ 40 * 7812973 * 2
def baseEnd_7812973 : Nat := 4011810489600365440906297

theorem tailTrace_7812973 : CollatzResearch.WordTrace tailWord_7812973 prefixEnd_7812973 4011810489600365440906297 := by
  unfold tailWord_7812973
  simp only [CollatzResearch.WordTrace]
  refine ⟨284962535923940645400515573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189975023949293763600343715 284962535923940645400515573)
  ·
    refine ⟨26715237742869435506298335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 284962535923940645400515573 26715237742869435506298335)
    ·
      refine ⟨40072856614304153259447503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26715237742869435506298335 40072856614304153259447503)
      ·
        refine ⟨60109284921456229889171255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40072856614304153259447503 60109284921456229889171255)
        ·
          refine ⟨90163927382184344833756883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60109284921456229889171255 90163927382184344833756883)
          ·
            refine ⟨135245891073276517250635325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90163927382184344833756883 135245891073276517250635325)
            ·
              refine ⟨50717209152478693968988247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 135245891073276517250635325 50717209152478693968988247)
              ·
                refine ⟨76075813728718040953482371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50717209152478693968988247 76075813728718040953482371)
                ·
                  refine ⟨114113720593077061430223557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 76075813728718040953482371 114113720593077061430223557)
                  ·
                    refine ⟨21396322611201949018166917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 114113720593077061430223557 21396322611201949018166917)
                    ·
                      refine ⟨4011810489600365440906297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21396322611201949018166917 4011810489600365440906297)
                      ·
                        rfl

theorem cell23_7812973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 3, 1, 1, 4, 4].length) (baseStart_7812973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7812973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7812973 prefixEnd_7812973 := by exact prefixLift 7812973
  have htrace : WordTrace (prefixWord ++ tailWord_7812973) baseStart_7812973 baseEnd_7812973 := by
    simpa [prefixWord, tailWord_7812973, baseEnd_7812973] using wordTrace_append hprefix tailTrace_7812973
  have hstable : (prefixWord ++ tailWord_7812973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7812973).length < 2 ^ (prefixWord ++ tailWord_7812973).sum := by decide
  have hdescent : baseEnd_7812973 < baseStart_7812973 := by decide
  rcases family_descends (prefixWord ++ tailWord_7812973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7812977 : List Nat := [1, 2, 2, 2, 1, 3, 1, 5, 2, 2, 2]
def baseStart_7812977 : Nat := 118140960795 + 7812977 * 2 ^ 59
def prefixEnd_7812977 : Nat := 4983230072969 + 3 ^ 40 * 7812977 * 2
def baseEnd_7812977 : Nat := 4011812543522983425256279

theorem tailTrace_7812977 : CollatzResearch.WordTrace tailWord_7812977 prefixEnd_7812977 4011812543522983425256279 := by
  unfold tailWord_7812977
  simp only [CollatzResearch.WordTrace]
  refine ⟨284962681815926154083661185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189975121210617436055774123 284962681815926154083661185)
  ·
    refine ⟨213722011361944615562745889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 284962681815926154083661185 213722011361944615562745889)
    ·
      refine ⟨160291508521458461672059417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 213722011361944615562745889 160291508521458461672059417)
      ·
        refine ⟨120218631391093846254044563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 160291508521458461672059417 120218631391093846254044563)
        ·
          refine ⟨180327947086640769381066845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120218631391093846254044563 180327947086640769381066845)
          ·
            refine ⟨67622980157490288517900067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 180327947086640769381066845 67622980157490288517900067)
            ·
              refine ⟨101434470236235432776850101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67622980157490288517900067 101434470236235432776850101)
              ·
                refine ⟨9509481584647071822829697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 101434470236235432776850101 9509481584647071822829697)
                ·
                  refine ⟨7132111188485303867122273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9509481584647071822829697 7132111188485303867122273)
                  ·
                    refine ⟨5349083391363977900341705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7132111188485303867122273 5349083391363977900341705)
                    ·
                      refine ⟨4011812543522983425256279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5349083391363977900341705 4011812543522983425256279)
                      ·
                        rfl

theorem cell23_7812977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 5, 2, 2, 2].length) (baseStart_7812977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7812977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7812977 prefixEnd_7812977 := by exact prefixLift 7812977
  have htrace : WordTrace (prefixWord ++ tailWord_7812977) baseStart_7812977 baseEnd_7812977 := by
    simpa [prefixWord, tailWord_7812977, baseEnd_7812977] using wordTrace_append hprefix tailTrace_7812977
  have hstable : (prefixWord ++ tailWord_7812977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7812977).length < 2 ^ (prefixWord ++ tailWord_7812977).sum := by decide
  have hdescent : baseEnd_7812977 < baseStart_7812977 := by decide
  rcases family_descends (prefixWord ++ tailWord_7812977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7813013 : List Nat := [1, 3, 2, 1, 1, 3, 2, 1, 4, 5]
def baseStart_7813013 : Nat := 118140960795 + 7813013 * 2 ^ 59
def prefixEnd_7813013 : Nat := 4983230072969 + 3 ^ 40 * 7813013 * 2
def baseEnd_7813013 : Nat := 1337277009608848428135371

theorem tailTrace_7813013 : CollatzResearch.WordTrace tailWord_7813013 prefixEnd_7813013 1337277009608848428135371 := by
  unfold tailWord_7813013
  simp only [CollatzResearch.WordTrace]
  refine ⟨284963994843795732231971693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189975996562530488154647795 284963994843795732231971693)
  ·
    refine ⟨106861498066423399586989385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 284963994843795732231971693 106861498066423399586989385)
    ·
      refine ⟨80146123549817549690242039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106861498066423399586989385 80146123549817549690242039)
      ·
        refine ⟨120219185324726324535363059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80146123549817549690242039 120219185324726324535363059)
        ·
          refine ⟨180328777987089486803044589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120219185324726324535363059 180328777987089486803044589)
          ·
            refine ⟨67623291745158557551141721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 180328777987089486803044589 67623291745158557551141721)
            ·
              refine ⟨50717468808868918163356291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67623291745158557551141721 50717468808868918163356291)
              ·
                refine ⟨76076203213303377245034437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50717468808868918163356291 76076203213303377245034437)
                ·
                  refine ⟨14264288102494383233443957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 76076203213303377245034437 14264288102494383233443957)
                  ·
                    refine ⟨1337277009608848428135371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14264288102494383233443957 1337277009608848428135371)
                    ·
                      rfl

theorem cell23_7813013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 2, 1, 4, 5].length) (baseStart_7813013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7813013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7813013 prefixEnd_7813013 := by exact prefixLift 7813013
  have htrace : WordTrace (prefixWord ++ tailWord_7813013) baseStart_7813013 baseEnd_7813013 := by
    simpa [prefixWord, tailWord_7813013, baseEnd_7813013] using wordTrace_append hprefix tailTrace_7813013
  have hstable : (prefixWord ++ tailWord_7813013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7813013).length < 2 ^ (prefixWord ++ tailWord_7813013).sum := by decide
  have hdescent : baseEnd_7813013 < baseStart_7813013 := by decide
  rcases family_descends (prefixWord ++ tailWord_7813013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7813033 : List Nat := [1, 2, 1, 1, 1, 1, 4, 1, 6, 1, 4]
def baseStart_7813033 : Nat := 118140960795 + 7813033 * 2 ^ 59
def prefixEnd_7813033 : Nat := 4983230072969 + 3 ^ 40 * 7813033 * 2
def baseEnd_7813033 : Nat := 4011841298439635206156021

theorem tailTrace_7813033 : CollatzResearch.WordTrace tailWord_7813033 prefixEnd_7813033 4011841298439635206156021 := by
  unfold tailWord_7813033
  simp only [CollatzResearch.WordTrace]
  refine ⟨284964724303723275647699753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189976482869148850431799835 284964724303723275647699753)
  ·
    refine ⟨213723543227792456735774815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 284964724303723275647699753 213723543227792456735774815)
    ·
      refine ⟨320585314841688685103662223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213723543227792456735774815 320585314841688685103662223)
      ·
        refine ⟨480877972262533027655493335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 320585314841688685103662223 480877972262533027655493335)
        ·
          refine ⟨721316958393799541483240003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 480877972262533027655493335 721316958393799541483240003)
          ·
            refine ⟨1081975437590699312224860005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 721316958393799541483240003 1081975437590699312224860005)
            ·
              refine ⟨202870394548256121042161251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1081975437590699312224860005 202870394548256121042161251)
              ·
                refine ⟨304305591822384181563241877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 202870394548256121042161251 304305591822384181563241877)
                ·
                  refine ⟨14264324616674258510776963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 304305591822384181563241877 14264324616674258510776963)
                  ·
                    refine ⟨21396486925011387766165445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14264324616674258510776963 21396486925011387766165445)
                    ·
                      refine ⟨4011841298439635206156021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21396486925011387766165445 4011841298439635206156021)
                      ·
                        rfl

theorem cell23_7813033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 1, 6, 1, 4].length) (baseStart_7813033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7813033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7813033 prefixEnd_7813033 := by exact prefixLift 7813033
  have htrace : WordTrace (prefixWord ++ tailWord_7813033) baseStart_7813033 baseEnd_7813033 := by
    simpa [prefixWord, tailWord_7813033, baseEnd_7813033] using wordTrace_append hprefix tailTrace_7813033
  have hstable : (prefixWord ++ tailWord_7813033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7813033).length < 2 ^ (prefixWord ++ tailWord_7813033).sum := by decide
  have hdescent : baseEnd_7813033 < baseStart_7813033 := by decide
  rcases family_descends (prefixWord ++ tailWord_7813033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7813050 : List Nat := [3, 1, 1, 1, 2, 1, 2, 2, 4, 4, 2]
def baseStart_7813050 : Nat := 118140960795 + 7813050 * 2 ^ 59
def prefixEnd_7813050 : Nat := 4983230072969 + 3 ^ 40 * 7813050 * 2
def baseEnd_7813050 : Nat := 4011850027610761639643443

theorem tailTrace_7813050 : CollatzResearch.WordTrace tailWord_7813050 prefixEnd_7813050 4011850027610761639643443 := by
  unfold tailWord_7813050
  simp only [CollatzResearch.WordTrace]
  refine ⟨71241336086165421887767151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 189976896229774458367379069 71241336086165421887767151)
  ·
    refine ⟨106862004129248132831650727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71241336086165421887767151 106862004129248132831650727)
    ·
      refine ⟨160293006193872199247476091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106862004129248132831650727 160293006193872199247476091)
      ·
        refine ⟨240439509290808298871214137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160293006193872199247476091 240439509290808298871214137)
        ·
          refine ⟨180329631968106224153410603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 240439509290808298871214137 180329631968106224153410603)
          ·
            refine ⟨270494447952159336230115905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 180329631968106224153410603 270494447952159336230115905)
            ·
              refine ⟨202870835964119502172586929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 270494447952159336230115905 202870835964119502172586929)
              ·
                refine ⟨152153126973089626629440197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 202870835964119502172586929 152153126973089626629440197)
                ·
                  refine ⟨28528711307454304993020037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 152153126973089626629440197 28528711307454304993020037)
                  ·
                    refine ⟨5349133370147682186191257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28528711307454304993020037 5349133370147682186191257)
                    ·
                      refine ⟨4011850027610761639643443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5349133370147682186191257 4011850027610761639643443)
                      ·
                        rfl

theorem cell23_7813050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 2, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 2, 4, 4, 2].length) (baseStart_7813050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7813050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7813050 prefixEnd_7813050 := by exact prefixLift 7813050
  have htrace : WordTrace (prefixWord ++ tailWord_7813050) baseStart_7813050 baseEnd_7813050 := by
    simpa [prefixWord, tailWord_7813050, baseEnd_7813050] using wordTrace_append hprefix tailTrace_7813050
  have hstable : (prefixWord ++ tailWord_7813050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7813050).length < 2 ^ (prefixWord ++ tailWord_7813050).sum := by decide
  have hdescent : baseEnd_7813050 < baseStart_7813050 := by decide
  rcases family_descends (prefixWord ++ tailWord_7813050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7813077 : List Nat := [1, 3, 2, 3, 2, 1, 3, 1, 3, 4]
def baseStart_7813077 : Nat := 118140960795 + 7813077 * 2 ^ 59
def prefixEnd_7813077 : Nat := 4983230072969 + 3 ^ 40 * 7813077 * 2
def baseEnd_7813077 : Nat := 1337287963862811011335273

theorem tailTrace_7813077 : CollatzResearch.WordTrace tailWord_7813077 prefixEnd_7813077 1337287963862811011335273 := by
  unfold tailWord_7813077
  simp only [CollatzResearch.WordTrace]
  refine ⟨284966329115563871162301485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189977552743709247441534323 284966329115563871162301485)
  ·
    refine ⟨106862373418336451685863057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 284966329115563871162301485 106862373418336451685863057)
    ·
      refine ⟨80146780063752338764397293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106862373418336451685863057 80146780063752338764397293)
      ·
        refine ⟨30055042523907127036648985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80146780063752338764397293 30055042523907127036648985)
        ·
          refine ⟨22541281892930345277486739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30055042523907127036648985 22541281892930345277486739)
          ·
            refine ⟨33811922839395517916230109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22541281892930345277486739 33811922839395517916230109)
            ·
              refine ⟨12679471064773319218586291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33811922839395517916230109 12679471064773319218586291)
              ·
                refine ⟨19019206597159978827879437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12679471064773319218586291 19019206597159978827879437)
                ·
                  refine ⟨7132202473934992060454789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19019206597159978827879437 7132202473934992060454789)
                  ·
                    refine ⟨1337287963862811011335273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7132202473934992060454789 1337287963862811011335273)
                    ·
                      rfl

theorem cell23_7813077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 3, 1, 3, 4].length) (baseStart_7813077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7813077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7813077 prefixEnd_7813077 := by exact prefixLift 7813077
  have htrace : WordTrace (prefixWord ++ tailWord_7813077) baseStart_7813077 baseEnd_7813077 := by
    simpa [prefixWord, tailWord_7813077, baseEnd_7813077] using wordTrace_append hprefix tailTrace_7813077
  have hstable : (prefixWord ++ tailWord_7813077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7813077).length < 2 ^ (prefixWord ++ tailWord_7813077).sum := by decide
  have hdescent : baseEnd_7813077 < baseStart_7813077 := by decide
  rcases family_descends (prefixWord ++ tailWord_7813077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7813124 : List Nat := [2, 3, 2, 4, 1, 1, 2, 2, 6]
def baseStart_7813124 : Nat := 118140960795 + 7813124 * 2 ^ 59
def prefixEnd_7813124 : Nat := 4983230072969 + 3 ^ 40 * 7813124 * 2
def baseEnd_7813124 : Nat := 445765336131021594457567

theorem tailTrace_7813124 : CollatzResearch.WordTrace tailWord_7813124 prefixEnd_7813124 445765336131021594457567 := by
  unfold tailWord_7813124
  simp only [CollatzResearch.WordTrace]
  refine ⟨142484021673196799094631213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189978695564262398792841617 142484021673196799094631213)
  ·
    refine ⟨53431508127448799660486705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 142484021673196799094631213 53431508127448799660486705)
    ·
      refine ⟨40073631095586599745365029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53431508127448799660486705 40073631095586599745365029)
      ·
        refine ⟨7513805830422487452255943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40073631095586599745365029 7513805830422487452255943)
        ·
          refine ⟨11270708745633731178383915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7513805830422487452255943 11270708745633731178383915)
          ·
            refine ⟨16906063118450596767575873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11270708745633731178383915 16906063118450596767575873)
            ·
              refine ⟨12679547338837947575681905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16906063118450596767575873 12679547338837947575681905)
              ·
                refine ⟨9509660504128460681761429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12679547338837947575681905 9509660504128460681761429)
                ·
                  refine ⟨445765336131021594457567, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9509660504128460681761429 445765336131021594457567)
                  ·
                    rfl

theorem cell23_7813124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 2, 2, 6].length) (baseStart_7813124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7813124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7813124 prefixEnd_7813124 := by exact prefixLift 7813124
  have htrace : WordTrace (prefixWord ++ tailWord_7813124) baseStart_7813124 baseEnd_7813124 := by
    simpa [prefixWord, tailWord_7813124, baseEnd_7813124] using wordTrace_append hprefix tailTrace_7813124
  have hstable : (prefixWord ++ tailWord_7813124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7813124).length < 2 ^ (prefixWord ++ tailWord_7813124).sum := by decide
  have hdescent : baseEnd_7813124 < baseStart_7813124 := by decide
  rcases family_descends (prefixWord ++ tailWord_7813124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7813174 : List Nat := [5, 1, 2, 1, 1, 1, 3, 3, 1, 1, 4]
def baseStart_7813174 : Nat := 118140960795 + 7813174 * 2 ^ 59
def prefixEnd_7813174 : Nat := 4983230072969 + 3 ^ 40 * 7813174 * 2
def baseEnd_7813174 : Nat := 4011913699211919154492873

theorem tailTrace_7813174 : CollatzResearch.WordTrace tailWord_7813174 prefixEnd_7813174 4011913699211919154492873 := by
  unfold tailWord_7813174
  simp only [CollatzResearch.WordTrace]
  refine ⟨17810616687263278545536411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 189979911330808304485721717 17810616687263278545536411)
  ·
    refine ⟨26715925030894917818304617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17810616687263278545536411 26715925030894917818304617)
    ·
      refine ⟨20036943773171188363728463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26715925030894917818304617 20036943773171188363728463)
      ·
        refine ⟨30055415659756782545592695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20036943773171188363728463 30055415659756782545592695)
        ·
          refine ⟨45083123489635173818389043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30055415659756782545592695 45083123489635173818389043)
          ·
            refine ⟨67624685234452760727583565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45083123489635173818389043 67624685234452760727583565)
            ·
              refine ⟨25359256962919785272843837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67624685234452760727583565 25359256962919785272843837)
              ·
                refine ⟨9509721361094919477316439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25359256962919785272843837 9509721361094919477316439)
                ·
                  refine ⟨14264582041642379215974659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9509721361094919477316439 14264582041642379215974659)
                  ·
                    refine ⟨21396873062463568823961989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14264582041642379215974659 21396873062463568823961989)
                    ·
                      refine ⟨4011913699211919154492873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21396873062463568823961989 4011913699211919154492873)
                      ·
                        rfl

theorem cell23_7813174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 3, 3, 1, 1, 4].length) (baseStart_7813174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7813174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7813174 prefixEnd_7813174 := by exact prefixLift 7813174
  have htrace : WordTrace (prefixWord ++ tailWord_7813174) baseStart_7813174 baseEnd_7813174 := by
    simpa [prefixWord, tailWord_7813174, baseEnd_7813174] using wordTrace_append hprefix tailTrace_7813174
  have hstable : (prefixWord ++ tailWord_7813174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7813174).length < 2 ^ (prefixWord ++ tailWord_7813174).sum := by decide
  have hdescent : baseEnd_7813174 < baseStart_7813174 := by decide
  rcases family_descends (prefixWord ++ tailWord_7813174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7813184 : List Nat := [2, 1, 1, 2, 2, 6, 1, 2, 2, 4]
def baseStart_7813184 : Nat := 118140960795 + 7813184 * 2 ^ 59
def prefixEnd_7813184 : Nat := 4983230072969 + 3 ^ 40 * 7813184 * 2
def baseEnd_7813184 : Nat := 1337306278006154705122609

theorem tailTrace_7813184 : CollatzResearch.WordTrace tailWord_7813184 prefixEnd_7813184 1337306278006154705122609 := by
  unfold tailWord_7813184
  simp only [CollatzResearch.WordTrace]
  refine ⟨142485115863088114218223303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189980154484117485624297737 142485115863088114218223303)
  ·
    refine ⟨213727673794632171327334955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142485115863088114218223303 213727673794632171327334955)
    ·
      refine ⟨320591510691948256991002433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213727673794632171327334955 320591510691948256991002433)
      ·
        refine ⟨240443633018961192743251825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 320591510691948256991002433 240443633018961192743251825)
        ·
          refine ⟨180332724764220894557438869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 240443633018961192743251825 180332724764220894557438869)
          ·
            refine ⟨8453096473322854432379947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 180332724764220894557438869 8453096473322854432379947)
            ·
              refine ⟨12679644709984281648569921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8453096473322854432379947 12679644709984281648569921)
              ·
                refine ⟨9509733532488211236427441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12679644709984281648569921 9509733532488211236427441)
                ·
                  refine ⟨7132300149366158427320581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9509733532488211236427441 7132300149366158427320581)
                  ·
                    refine ⟨1337306278006154705122609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7132300149366158427320581 1337306278006154705122609)
                    ·
                      rfl

theorem cell23_7813184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 6, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 6, 1, 2, 2, 4].length) (baseStart_7813184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7813184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7813184 prefixEnd_7813184 := by exact prefixLift 7813184
  have htrace : WordTrace (prefixWord ++ tailWord_7813184) baseStart_7813184 baseEnd_7813184 := by
    simpa [prefixWord, tailWord_7813184, baseEnd_7813184] using wordTrace_append hprefix tailTrace_7813184
  have hstable : (prefixWord ++ tailWord_7813184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7813184).length < 2 ^ (prefixWord ++ tailWord_7813184).sum := by decide
  have hdescent : baseEnd_7813184 < baseStart_7813184 := by decide
  rcases family_descends (prefixWord ++ tailWord_7813184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7813191 : List Nat := [1, 1, 4, 1, 3, 1, 1, 6, 1, 2, 2]
def baseStart_7813191 : Nat := 118140960795 + 7813191 * 2 ^ 59
def prefixEnd_7813191 : Nat := 4983230072969 + 3 ^ 40 * 7813191 * 2
def baseEnd_7813191 : Nat := 4011922428383045587980295

theorem tailTrace_7813191 : CollatzResearch.WordTrace tailWord_7813191 prefixEnd_7813191 4011922428383045587980295 := by
  unfold tailWord_7813191
  simp only [CollatzResearch.WordTrace]
  refine ⟨284970487037150868631951427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189980324691433912421300951 284970487037150868631951427)
  ·
    refine ⟨427455730555726302947927141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 284970487037150868631951427 427455730555726302947927141)
    ·
      refine ⟨80147949479198681802736339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 427455730555726302947927141 80147949479198681802736339)
      ·
        refine ⟨120221924218798022704104509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80147949479198681802736339 120221924218798022704104509)
        ·
          refine ⟨45083221582049258514039191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 120221924218798022704104509 45083221582049258514039191)
          ·
            refine ⟨67624832373073887771058787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45083221582049258514039191 67624832373073887771058787)
            ·
              refine ⟨101437248559610831656588181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67624832373073887771058787 101437248559610831656588181)
              ·
                refine ⟨4754871026231757733902571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 101437248559610831656588181 4754871026231757733902571)
                ·
                  refine ⟨7132306539347636600853857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4754871026231757733902571 7132306539347636600853857)
                  ·
                    refine ⟨5349229904510727450640393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7132306539347636600853857 5349229904510727450640393)
                    ·
                      refine ⟨4011922428383045587980295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5349229904510727450640393 4011922428383045587980295)
                      ·
                        rfl

theorem cell23_7813191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 6, 1, 2, 2].length) (baseStart_7813191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7813191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7813191 prefixEnd_7813191 := by exact prefixLift 7813191
  have htrace : WordTrace (prefixWord ++ tailWord_7813191) baseStart_7813191 baseEnd_7813191 := by
    simpa [prefixWord, tailWord_7813191, baseEnd_7813191] using wordTrace_append hprefix tailTrace_7813191
  have hstable : (prefixWord ++ tailWord_7813191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7813191).length < 2 ^ (prefixWord ++ tailWord_7813191).sum := by decide
  have hdescent : baseEnd_7813191 < baseStart_7813191 := by decide
  rcases family_descends (prefixWord ++ tailWord_7813191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7813207 : List Nat := [1, 1, 3, 2, 2, 1, 5, 1, 1, 3, 3]
def baseStart_7813207 : Nat := 118140960795 + 7813207 * 2 ^ 59
def prefixEnd_7813207 : Nat := 4983230072969 + 3 ^ 40 * 7813207 * 2
def baseEnd_7813207 : Nat := 4011930644073517525380221

theorem tailTrace_7813207 : CollatzResearch.WordTrace tailWord_7813207 prefixEnd_7813207 4011930644073517525380221 := by
  unfold tailWord_7813207
  simp only [CollatzResearch.WordTrace]
  refine ⟨284971070605092903364533875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189980713736728602243022583 284971070605092903364533875)
  ·
    refine ⟨427456605907639355046800813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 284971070605092903364533875 427456605907639355046800813)
    ·
      refine ⟨160296227215364758142550305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 427456605907639355046800813 160296227215364758142550305)
      ·
        refine ⟨120222170411523568606912729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 160296227215364758142550305 120222170411523568606912729)
        ·
          refine ⟨90166627808642676455184547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120222170411523568606912729 90166627808642676455184547)
          ·
            refine ⟨135249941712964014682776821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90166627808642676455184547 135249941712964014682776821)
            ·
              refine ⟨12679682035590376376510327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 135249941712964014682776821 12679682035590376376510327)
              ·
                refine ⟨19019523053385564564765491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12679682035590376376510327 19019523053385564564765491)
                ·
                  refine ⟨28529284580078346847148237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19019523053385564564765491 28529284580078346847148237)
                  ·
                    refine ⟨10698481717529380067680589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28529284580078346847148237 10698481717529380067680589)
                    ·
                      refine ⟨4011930644073517525380221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10698481717529380067680589 4011930644073517525380221)
                      ·
                        rfl

theorem cell23_7813207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 5, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 5, 1, 1, 3, 3].length) (baseStart_7813207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7813207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7813207 prefixEnd_7813207 := by exact prefixLift 7813207
  have htrace : WordTrace (prefixWord ++ tailWord_7813207) baseStart_7813207 baseEnd_7813207 := by
    simpa [prefixWord, tailWord_7813207, baseEnd_7813207] using wordTrace_append hprefix tailTrace_7813207
  have hstable : (prefixWord ++ tailWord_7813207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7813207).length < 2 ^ (prefixWord ++ tailWord_7813207).sum := by decide
  have hdescent : baseEnd_7813207 < baseStart_7813207 := by decide
  rcases family_descends (prefixWord ++ tailWord_7813207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7813220 : List Nat := [2, 3, 1, 1, 2, 1, 3, 1, 2, 2, 5]
def baseStart_7813220 : Nat := 118140960795 + 7813220 * 2 ^ 59
def prefixEnd_7813220 : Nat := 4983230072969 + 3 ^ 40 * 7813220 * 2
def baseEnd_7813220 : Nat := 4011937319322025974517661

theorem tailTrace_7813220 : CollatzResearch.WordTrace tailWord_7813220 prefixEnd_7813220 4011937319322025974517661 := by
  unfold tailWord_7813220
  simp only [CollatzResearch.WordTrace]
  refine ⟨142485772377022903292378557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189981029836030537723171409 142485772377022903292378557)
  ·
    refine ⟨53432164641383588734641959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 142485772377022903292378557 53432164641383588734641959)
    ·
      refine ⟨80148246962075383101962939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53432164641383588734641959 80148246962075383101962939)
      ·
        refine ⟨120222370443113074652944409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80148246962075383101962939 120222370443113074652944409)
        ·
          refine ⟨90166777832334805989708307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120222370443113074652944409 90166777832334805989708307)
          ·
            refine ⟨135250166748502208984562461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90166777832334805989708307 135250166748502208984562461)
            ·
              refine ⟨50718812530688328369210923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 135250166748502208984562461 50718812530688328369210923)
              ·
                refine ⟨76078218796032492553816385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50718812530688328369210923 76078218796032492553816385)
                ·
                  refine ⟨57058664097024369415362289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 76078218796032492553816385 57058664097024369415362289)
                  ·
                    refine ⟨42793998072768277061521717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 57058664097024369415362289 42793998072768277061521717)
                    ·
                      refine ⟨4011937319322025974517661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42793998072768277061521717 4011937319322025974517661)
                      ·
                        rfl

theorem cell23_7813220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 3, 1, 2, 2, 5].length) (baseStart_7813220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7813220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7813220 prefixEnd_7813220 := by exact prefixLift 7813220
  have htrace : WordTrace (prefixWord ++ tailWord_7813220) baseStart_7813220 baseEnd_7813220 := by
    simpa [prefixWord, tailWord_7813220, baseEnd_7813220] using wordTrace_append hprefix tailTrace_7813220
  have hstable : (prefixWord ++ tailWord_7813220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7813220).length < 2 ^ (prefixWord ++ tailWord_7813220).sum := by decide
  have hdescent : baseEnd_7813220 < baseStart_7813220 := by decide
  rcases family_descends (prefixWord ++ tailWord_7813220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7813258 : List Nat := [3, 1, 2, 3, 1, 4, 2, 1, 2, 1, 3]
def baseStart_7813258 : Nat := 118140960795 + 7813258 * 2 ^ 59
def prefixEnd_7813258 : Nat := 4983230072969 + 3 ^ 40 * 7813258 * 2
def baseEnd_7813258 : Nat := 4011956831586896825842487

theorem tailTrace_7813258 : CollatzResearch.WordTrace tailWord_7813258 prefixEnd_7813258 4011956831586896825842487 := by
  unfold tailWord_7813258
  simp only [CollatzResearch.WordTrace]
  refine ⟨71243232681977034768660107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 189981953818605426049760285 71243232681977034768660107)
  ·
    refine ⟨106864849022965552152990161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71243232681977034768660107 106864849022965552152990161)
    ·
      refine ⟨80148636767224164114742621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106864849022965552152990161 80148636767224164114742621)
      ·
        refine ⟨30055738787709061543028483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80148636767224164114742621 30055738787709061543028483)
        ·
          refine ⟨45083608181563592314542725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30055738787709061543028483 45083608181563592314542725)
          ·
            refine ⟨8453176534043173558976761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45083608181563592314542725 8453176534043173558976761)
            ·
              refine ⟨6339882400532380169232571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8453176534043173558976761 6339882400532380169232571)
              ·
                refine ⟨9509823600798570253848857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6339882400532380169232571 9509823600798570253848857)
                ·
                  refine ⟨7132367700598927690386643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9509823600798570253848857 7132367700598927690386643)
                  ·
                    refine ⟨10698551550898391535579965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7132367700598927690386643 10698551550898391535579965)
                    ·
                      refine ⟨4011956831586896825842487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10698551550898391535579965 4011956831586896825842487)
                      ·
                        rfl

theorem cell23_7813258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 4, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 4, 2, 1, 2, 1, 3].length) (baseStart_7813258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7813258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7813258 prefixEnd_7813258 := by exact prefixLift 7813258
  have htrace : WordTrace (prefixWord ++ tailWord_7813258) baseStart_7813258 baseEnd_7813258 := by
    simpa [prefixWord, tailWord_7813258, baseEnd_7813258] using wordTrace_append hprefix tailTrace_7813258
  have hstable : (prefixWord ++ tailWord_7813258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7813258).length < 2 ^ (prefixWord ++ tailWord_7813258).sum := by decide
  have hdescent : baseEnd_7813258 < baseStart_7813258 := by decide
  rcases family_descends (prefixWord ++ tailWord_7813258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7813268 : List Nat := [2, 4, 2, 3, 1, 1, 1, 1, 3, 3, 2]
def baseStart_7813268 : Nat := 118140960795 + 7813268 * 2 ^ 59
def prefixEnd_7813268 : Nat := 4983230072969 + 3 ^ 40 * 7813268 * 2
def baseEnd_7813268 : Nat := 4011961966393441786717441

theorem tailTrace_7813268 : CollatzResearch.WordTrace tailWord_7813268 prefixEnd_7813268 4011961966393441786717441 := by
  unfold tailWord_7813268
  simp only [CollatzResearch.WordTrace]
  refine ⟨142486647728935955391252229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189982196971914607188336305 142486647728935955391252229)
  ·
    refine ⟨26716246449175491635859793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 142486647728935955391252229 26716246449175491635859793)
    ·
      refine ⟨20037184836881618726894845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26716246449175491635859793 20037184836881618726894845)
      ·
        refine ⟨7513944313830607022585567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20037184836881618726894845 7513944313830607022585567)
        ·
          refine ⟨11270916470745910533878351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7513944313830607022585567 11270916470745910533878351)
          ·
            refine ⟨16906374706118865800817527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11270916470745910533878351 16906374706118865800817527)
            ·
              refine ⟨25359562059178298701226291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16906374706118865800817527 25359562059178298701226291)
              ·
                refine ⟨38039343088767448051839437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25359562059178298701226291 38039343088767448051839437)
                ·
                  refine ⟨14264753658287793019439789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38039343088767448051839437 14264753658287793019439789)
                  ·
                    refine ⟨5349282621857922382289921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14264753658287793019439789 5349282621857922382289921)
                    ·
                      refine ⟨4011961966393441786717441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5349282621857922382289921 4011961966393441786717441)
                      ·
                        rfl

theorem cell23_7813268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 1, 1, 3, 3, 2].length) (baseStart_7813268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7813268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7813268 prefixEnd_7813268 := by exact prefixLift 7813268
  have htrace : WordTrace (prefixWord ++ tailWord_7813268) baseStart_7813268 baseEnd_7813268 := by
    simpa [prefixWord, tailWord_7813268, baseEnd_7813268] using wordTrace_append hprefix tailTrace_7813268
  have hstable : (prefixWord ++ tailWord_7813268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7813268).length < 2 ^ (prefixWord ++ tailWord_7813268).sum := by decide
  have hdescent : baseEnd_7813268 < baseStart_7813268 := by decide
  rcases family_descends (prefixWord ++ tailWord_7813268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7813307 : List Nat := [1, 1, 1, 1, 1, 2, 5, 1, 1, 7, 2]
def baseStart_7813307 : Nat := 118140960795 + 7813307 * 2 ^ 59
def prefixEnd_7813307 : Nat := 4983230072969 + 3 ^ 40 * 7813307 * 2
def baseEnd_7813307 : Nat := 4011981992138967134129761

theorem tailTrace_7813307 : CollatzResearch.WordTrace tailWord_7813307 prefixEnd_7813307 4011981992138967134129761 := by
  unfold tailWord_7813307
  simp only [CollatzResearch.WordTrace]
  refine ⟨284974717904730620443174175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189983145269820413628782783 284974717904730620443174175)
  ·
    refine ⟨427462076857095930664761263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 284974717904730620443174175 427462076857095930664761263)
    ·
      refine ⟨641193115285643895997141895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 427462076857095930664761263 641193115285643895997141895)
      ·
        refine ⟨961789672928465843995712843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 641193115285643895997141895 961789672928465843995712843)
        ·
          refine ⟨1442684509392698765993569265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 961789672928465843995712843 1442684509392698765993569265)
          ·
            refine ⟨1082013382044524074495176949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1442684509392698765993569265 1082013382044524074495176949)
            ·
              refine ⟨101438754566674131983922839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1082013382044524074495176949 101438754566674131983922839)
              ·
                refine ⟨152158131850011197975884259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 101438754566674131983922839 152158131850011197975884259)
                ·
                  refine ⟨228237197775016796963826389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 152158131850011197975884259 228237197775016796963826389)
                  ·
                    refine ⟨5349309322851956178839681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 228237197775016796963826389 5349309322851956178839681)
                    ·
                      refine ⟨4011981992138967134129761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5349309322851956178839681 4011981992138967134129761)
                      ·
                        rfl

theorem cell23_7813307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 1, 1, 7, 2].length) (baseStart_7813307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7813307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7813307 prefixEnd_7813307 := by exact prefixLift 7813307
  have htrace : WordTrace (prefixWord ++ tailWord_7813307) baseStart_7813307 baseEnd_7813307 := by
    simpa [prefixWord, tailWord_7813307, baseEnd_7813307] using wordTrace_append hprefix tailTrace_7813307
  have hstable : (prefixWord ++ tailWord_7813307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7813307).length < 2 ^ (prefixWord ++ tailWord_7813307).sum := by decide
  have hdescent : baseEnd_7813307 < baseStart_7813307 := by decide
  rcases family_descends (prefixWord ++ tailWord_7813307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7813354 : List Nat := [3, 1, 3, 1, 1, 2, 1, 1, 4, 4, 2]
def baseStart_7813354 : Nat := 118140960795 + 7813354 * 2 ^ 59
def prefixEnd_7813354 : Nat := 4983230072969 + 3 ^ 40 * 7813354 * 2
def baseEnd_7813354 : Nat := 4012006125729728450242045

theorem tailTrace_7813354 : CollatzResearch.WordTrace tailWord_7813354 prefixEnd_7813354 4012006125729728450242045 := by
  unfold tailWord_7813354
  simp only [CollatzResearch.WordTrace]
  refine ⟨71244108033890086867533779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 189984288090373564980090077 71244108033890086867533779)
  ·
    refine ⟨106866162050835130301300669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71244108033890086867533779 106866162050835130301300669)
    ·
      refine ⟨40074810769063173862987751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 106866162050835130301300669 40074810769063173862987751)
      ·
        refine ⟨60112216153594760794481627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40074810769063173862987751 60112216153594760794481627)
        ·
          refine ⟨90168324230392141191722441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60112216153594760794481627 90168324230392141191722441)
          ·
            refine ⟨67626243172794105893791831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90168324230392141191722441 67626243172794105893791831)
            ·
              refine ⟨101439364759191158840687747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67626243172794105893791831 101439364759191158840687747)
              ·
                refine ⟨152159047138786738261031621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 101439364759191158840687747 152159047138786738261031621)
                ·
                  refine ⟨28529821338522513423943429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 152159047138786738261031621 28529821338522513423943429)
                  ·
                    refine ⟨5349341500972971266989393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28529821338522513423943429 5349341500972971266989393)
                    ·
                      refine ⟨4012006125729728450242045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5349341500972971266989393 4012006125729728450242045)
                      ·
                        rfl

theorem cell23_7813354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 1, 4, 4, 2].length) (baseStart_7813354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7813354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7813354 prefixEnd_7813354 := by exact prefixLift 7813354
  have htrace : WordTrace (prefixWord ++ tailWord_7813354) baseStart_7813354 baseEnd_7813354 := by
    simpa [prefixWord, tailWord_7813354, baseEnd_7813354] using wordTrace_append hprefix tailTrace_7813354
  have hstable : (prefixWord ++ tailWord_7813354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7813354).length < 2 ^ (prefixWord ++ tailWord_7813354).sum := by decide
  have hdescent : baseEnd_7813354 < baseStart_7813354 := by decide
  rcases family_descends (prefixWord ++ tailWord_7813354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7813374 : List Nat := [4, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3]
def baseStart_7813374 : Nat := 118140960795 + 7813374 * 2 ^ 59
def prefixEnd_7813374 : Nat := 4983230072969 + 3 ^ 40 * 7813374 * 2
def baseEnd_7813374 : Nat := 4012016395342818371991953

theorem tailTrace_7813374 : CollatzResearch.WordTrace tailWord_7813374 prefixEnd_7813374 4012016395342818371991953 := by
  unfold tailWord_7813374
  simp only [CollatzResearch.WordTrace]
  refine ⟨35622145199435986360732897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 189984774396991927257242117 35622145199435986360732897)
  ·
    refine ⟨26716608899576989770549673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35622145199435986360732897 26716608899576989770549673)
    ·
      refine ⟨20037456674682742327912255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26716608899576989770549673 20037456674682742327912255)
      ·
        refine ⟨30056185012024113491868383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20037456674682742327912255 30056185012024113491868383)
        ·
          refine ⟨45084277518036170237802575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30056185012024113491868383 45084277518036170237802575)
          ·
            refine ⟨67626416277054255356703863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45084277518036170237802575 67626416277054255356703863)
            ·
              refine ⟨101439624415581383035055795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67626416277054255356703863 101439624415581383035055795)
              ·
                refine ⟨152159436623372074552583693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 101439624415581383035055795 152159436623372074552583693)
                ·
                  refine ⟨57059788733764527957218885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 152159436623372074552583693 57059788733764527957218885)
                  ·
                    refine ⟨10698710387580848991978541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 57059788733764527957218885 10698710387580848991978541)
                    ·
                      refine ⟨4012016395342818371991953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10698710387580848991978541 4012016395342818371991953)
                      ·
                        rfl

theorem cell23_7813374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3].length) (baseStart_7813374 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7813374 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7813374 prefixEnd_7813374 := by exact prefixLift 7813374
  have htrace : WordTrace (prefixWord ++ tailWord_7813374) baseStart_7813374 baseEnd_7813374 := by
    simpa [prefixWord, tailWord_7813374, baseEnd_7813374] using wordTrace_append hprefix tailTrace_7813374
  have hstable : (prefixWord ++ tailWord_7813374).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7813374).length < 2 ^ (prefixWord ++ tailWord_7813374).sum := by decide
  have hdescent : baseEnd_7813374 < baseStart_7813374 := by decide
  rcases family_descends (prefixWord ++ tailWord_7813374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7813387 : List Nat := [1, 1, 1, 1, 5, 2, 1, 1, 2, 5, 3]
def baseStart_7813387 : Nat := 118140960795 + 7813387 * 2 ^ 59
def prefixEnd_7813387 : Nat := 4983230072969 + 3 ^ 40 * 7813387 * 2
def baseEnd_7813387 : Nat := 4012023070591326821129393

theorem tailTrace_7813387 : CollatzResearch.WordTrace tailWord_7813387 prefixEnd_7813387 4012023070591326821129393 := by
  unfold tailWord_7813387
  simp only [CollatzResearch.WordTrace]
  refine ⟨284977635744440794106086415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189985090496293862737390943 284977635744440794106086415)
  ·
    refine ⟨427466453616661191159129623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 284977635744440794106086415 427466453616661191159129623)
    ·
      refine ⟨641199680424991786738694435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 427466453616661191159129623 641199680424991786738694435)
      ·
        refine ⟨961799520637487680108041653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 641199680424991786738694435 961799520637487680108041653)
        ·
          refine ⟨90168705059764470010128905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 961799520637487680108041653 90168705059764470010128905)
          ·
            refine ⟨67626528794823352507596679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90168705059764470010128905 67626528794823352507596679)
            ·
              refine ⟨101439793192235028761395019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67626528794823352507596679 101439793192235028761395019)
              ·
                refine ⟨152159689788352543142092529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 101439793192235028761395019 152159689788352543142092529)
                ·
                  refine ⟨114119767341264407356569397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 152159689788352543142092529 114119767341264407356569397)
                  ·
                    refine ⟨10698728188243538189678381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 114119767341264407356569397 10698728188243538189678381)
                    ·
                      refine ⟨4012023070591326821129393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10698728188243538189678381 4012023070591326821129393)
                      ·
                        rfl

theorem cell23_7813387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 1, 2, 5, 3].length) (baseStart_7813387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7813387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7813387 prefixEnd_7813387 := by exact prefixLift 7813387
  have htrace : WordTrace (prefixWord ++ tailWord_7813387) baseStart_7813387 baseEnd_7813387 := by
    simpa [prefixWord, tailWord_7813387, baseEnd_7813387] using wordTrace_append hprefix tailTrace_7813387
  have hstable : (prefixWord ++ tailWord_7813387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7813387).length < 2 ^ (prefixWord ++ tailWord_7813387).sum := by decide
  have hdescent : baseEnd_7813387 < baseStart_7813387 := by decide
  rcases family_descends (prefixWord ++ tailWord_7813387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7813428 : List Nat := [2, 5, 1, 1, 1, 4, 2, 1, 6]
def baseStart_7813428 : Nat := 118140960795 + 7813428 * 2 ^ 59
def prefixEnd_7813428 : Nat := 4983230072969 + 3 ^ 40 * 7813428 * 2
def baseEnd_7813428 : Nat := 445782680366462351190745

theorem tailTrace_7813428 : CollatzResearch.WordTrace tailWord_7813428 prefixEnd_7813428 445782680366462351190745 := by
  unfold tailWord_7813428
  simp only [CollatzResearch.WordTrace]
  refine ⟨142489565568646129054164469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189986087424861505405552625 142489565568646129054164469)
  ·
    refine ⟨13358396772060574598827919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 142489565568646129054164469 13358396772060574598827919)
    ·
      refine ⟨20037595158090861898241879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13358396772060574598827919 20037595158090861898241879)
      ·
        refine ⟨30056392737136292847362819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20037595158090861898241879 30056392737136292847362819)
        ·
          refine ⟨45084589105704439271044229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30056392737136292847362819 45084589105704439271044229)
          ·
            refine ⟨8453360457319582363320793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45084589105704439271044229 8453360457319582363320793)
            ·
              refine ⟨6340020342989686772490595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8453360457319582363320793 6340020342989686772490595)
              ·
                refine ⟨9510030514484530158735893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6340020342989686772490595 9510030514484530158735893)
                ·
                  refine ⟨445782680366462351190745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9510030514484530158735893 445782680366462351190745)
                  ·
                    rfl

theorem cell23_7813428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 4, 2, 1, 6].length) (baseStart_7813428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7813428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7813428 prefixEnd_7813428 := by exact prefixLift 7813428
  have htrace : WordTrace (prefixWord ++ tailWord_7813428) baseStart_7813428 baseEnd_7813428 := by
    simpa [prefixWord, tailWord_7813428, baseEnd_7813428] using wordTrace_append hprefix tailTrace_7813428
  have hstable : (prefixWord ++ tailWord_7813428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7813428).length < 2 ^ (prefixWord ++ tailWord_7813428).sum := by decide
  have hdescent : baseEnd_7813428 < baseStart_7813428 := by decide
  rcases family_descends (prefixWord ++ tailWord_7813428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7813441 : List Nat := [1, 2, 5, 2, 2, 1, 1, 1, 3, 5]
def baseStart_7813441 : Nat := 118140960795 + 7813441 * 2 ^ 59
def prefixEnd_7813441 : Nat := 4983230072969 + 3 ^ 40 * 7813441 * 2
def baseEnd_7813441 : Nat := 1337350266182223203284715

theorem tailTrace_7813441 : CollatzResearch.WordTrace tailWord_7813441 prefixEnd_7813441 1337350266182223203284715 := by
  unfold tailWord_7813441
  simp only [CollatzResearch.WordTrace]
  refine ⟨284979605286245161328552177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189986403524163440885701451 284979605286245161328552177)
  ·
    refine ⟨213734703964683870996414133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 284979605286245161328552177 213734703964683870996414133)
    ·
      refine ⟨20037628496689112905913825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 213734703964683870996414133 20037628496689112905913825)
      ·
        refine ⟨15028221372516834679435369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20037628496689112905913825 15028221372516834679435369)
        ·
          refine ⟨11271166029387626009576527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15028221372516834679435369 11271166029387626009576527)
          ·
            refine ⟨16906749044081439014364791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11271166029387626009576527 16906749044081439014364791)
            ·
              refine ⟨25360123566122158521547187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16906749044081439014364791 25360123566122158521547187)
              ·
                refine ⟨38040185349183237782320781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25360123566122158521547187 38040185349183237782320781)
                ·
                  refine ⟨14265069505943714168370293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38040185349183237782320781 14265069505943714168370293)
                  ·
                    refine ⟨1337350266182223203284715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14265069505943714168370293 1337350266182223203284715)
                    ·
                      rfl

theorem cell23_7813441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 1, 1, 3, 5].length) (baseStart_7813441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7813441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7813441 prefixEnd_7813441 := by exact prefixLift 7813441
  have htrace : WordTrace (prefixWord ++ tailWord_7813441) baseStart_7813441 baseEnd_7813441 := by
    simpa [prefixWord, tailWord_7813441, baseEnd_7813441] using wordTrace_append hprefix tailTrace_7813441
  have hstable : (prefixWord ++ tailWord_7813441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7813441).length < 2 ^ (prefixWord ++ tailWord_7813441).sum := by decide
  have hdescent : baseEnd_7813441 < baseStart_7813441 := by decide
  rcases family_descends (prefixWord ++ tailWord_7813441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7813454 : List Nat := [4, 1, 1, 1, 1, 1, 2, 4, 4, 4]
def baseStart_7813454 : Nat := 118140960795 + 7813454 * 2 ^ 59
def prefixEnd_7813454 : Nat := 4983230072969 + 3 ^ 40 * 7813454 * 2
def baseEnd_7813454 : Nat := 1337352491265059352997195

theorem tailTrace_7813454 : CollatzResearch.WordTrace tailWord_7813454 prefixEnd_7813454 1337352491265059352997195 := by
  unfold tailWord_7813454
  simp only [CollatzResearch.WordTrace]
  refine ⟨35622509929399758068596927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 189986719623465376365850277 35622509929399758068596927)
  ·
    refine ⟨53433764894099637102895391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35622509929399758068596927 53433764894099637102895391)
    ·
      refine ⟨80150647341149455654343087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53433764894099637102895391 80150647341149455654343087)
      ·
        refine ⟨120225971011724183481514631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80150647341149455654343087 120225971011724183481514631)
        ·
          refine ⟨180338956517586275222271947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120225971011724183481514631 180338956517586275222271947)
          ·
            refine ⟨270508434776379412833407921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 180338956517586275222271947 270508434776379412833407921)
            ·
              refine ⟨202881326082284559625055941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 270508434776379412833407921 202881326082284559625055941)
              ·
                refine ⟨38040248640428354929697989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 202881326082284559625055941 38040248640428354929697989)
                ·
                  refine ⟨7132546620080316549318373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38040248640428354929697989 7132546620080316549318373)
                  ·
                    refine ⟨1337352491265059352997195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7132546620080316549318373 1337352491265059352997195)
                    ·
                      rfl

theorem cell23_7813454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 4, 4, 4].length) (baseStart_7813454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7813454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7813454 prefixEnd_7813454 := by exact prefixLift 7813454
  have htrace : WordTrace (prefixWord ++ tailWord_7813454) baseStart_7813454 baseEnd_7813454 := by
    simpa [prefixWord, tailWord_7813454, baseEnd_7813454] using wordTrace_append hprefix tailTrace_7813454
  have hstable : (prefixWord ++ tailWord_7813454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7813454).length < 2 ^ (prefixWord ++ tailWord_7813454).sum := by decide
  have hdescent : baseEnd_7813454 < baseStart_7813454 := by decide
  rcases family_descends (prefixWord ++ tailWord_7813454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7813472 : List Nat := [2, 1, 1, 3, 5, 2, 2, 2, 1, 1, 3]
def baseStart_7813472 : Nat := 118140960795 + 7813472 * 2 ^ 59
def prefixEnd_7813472 : Nat := 4983230072969 + 3 ^ 40 * 7813472 * 2
def baseEnd_7813472 : Nat := 4012066716446958988566503

theorem tailTrace_7813472 : CollatzResearch.WordTrace tailWord_7813472 prefixEnd_7813472 4012066716446958988566503 := by
  unfold tailWord_7813472
  simp only [CollatzResearch.WordTrace]
  refine ⟨142490367974566426811465335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189987157299421902415287113 142490367974566426811465335)
  ·
    refine ⟨213735551961849640217198003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142490367974566426811465335 213735551961849640217198003)
    ·
      refine ⟨320603327942774460325797005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213735551961849640217198003 320603327942774460325797005)
      ·
        refine ⟨120226247978540422622173877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 320603327942774460325797005 120226247978540422622173877)
        ·
          refine ⟨11271210747988164620828801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 120226247978540422622173877 11271210747988164620828801)
          ·
            refine ⟨8453408060991123465621601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11271210747988164620828801 8453408060991123465621601)
            ·
              refine ⟨6340056045743342599216201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8453408060991123465621601 6340056045743342599216201)
              ·
                refine ⟨4755042034307506949412151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6340056045743342599216201 4755042034307506949412151)
                ·
                  refine ⟨7132563051461260424118227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4755042034307506949412151 7132563051461260424118227)
                  ·
                    refine ⟨10698844577191890636177341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7132563051461260424118227 10698844577191890636177341)
                    ·
                      refine ⟨4012066716446958988566503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10698844577191890636177341 4012066716446958988566503)
                      ·
                        rfl

theorem cell23_7813472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 2, 2, 2, 1, 1, 3].length) (baseStart_7813472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7813472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7813472 prefixEnd_7813472 := by exact prefixLift 7813472
  have htrace : WordTrace (prefixWord ++ tailWord_7813472) baseStart_7813472 baseEnd_7813472 := by
    simpa [prefixWord, tailWord_7813472, baseEnd_7813472] using wordTrace_append hprefix tailTrace_7813472
  have hstable : (prefixWord ++ tailWord_7813472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7813472).length < 2 ^ (prefixWord ++ tailWord_7813472).sum := by decide
  have hdescent : baseEnd_7813472 < baseStart_7813472 := by decide
  rcases family_descends (prefixWord ++ tailWord_7813472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7813497 : List Nat := [1, 2, 1, 3, 2, 1, 1, 1, 4, 7]
def baseStart_7813497 : Nat := 118140960795 + 7813497 * 2 ^ 59
def prefixEnd_7813497 : Nat := 4983230072969 + 3 ^ 40 * 7813497 * 2
def baseEnd_7813497 : Nat := 1337359851154440463584629

theorem tailTrace_7813497 : CollatzResearch.WordTrace tailWord_7813497 prefixEnd_7813497 1337359851154440463584629 := by
  unfold tailWord_7813497
  simp only [CollatzResearch.WordTrace]
  refine ⟨284981647774042282892590745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189987765182694855261727163 284981647774042282892590745)
  ·
    refine ⟨213736235830531712169443059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 284981647774042282892590745 213736235830531712169443059)
    ·
      refine ⟨320604353745797568254164589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213736235830531712169443059 320604353745797568254164589)
      ·
        refine ⟨120226632654674088095311721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 320604353745797568254164589 120226632654674088095311721)
        ·
          refine ⟨90169974491005566071483791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120226632654674088095311721 90169974491005566071483791)
          ·
            refine ⟨135254961736508349107225687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90169974491005566071483791 135254961736508349107225687)
            ·
              refine ⟨202882442604762523660838531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 135254961736508349107225687 202882442604762523660838531)
              ·
                refine ⟨304323663907143785491257797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 202882442604762523660838531 304323663907143785491257797)
                ·
                  refine ⟨57060686982589459779610837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 304323663907143785491257797 57060686982589459779610837)
                  ·
                    refine ⟨1337359851154440463584629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 57060686982589459779610837 1337359851154440463584629)
                    ·
                      rfl

theorem cell23_7813497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 1, 4, 7].length) (baseStart_7813497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7813497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7813497 prefixEnd_7813497 := by exact prefixLift 7813497
  have htrace : WordTrace (prefixWord ++ tailWord_7813497) baseStart_7813497 baseEnd_7813497 := by
    simpa [prefixWord, tailWord_7813497, baseEnd_7813497] using wordTrace_append hprefix tailTrace_7813497
  have hstable : (prefixWord ++ tailWord_7813497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7813497).length < 2 ^ (prefixWord ++ tailWord_7813497).sum := by decide
  have hdescent : baseEnd_7813497 < baseStart_7813497 := by decide
  rcases family_descends (prefixWord ++ tailWord_7813497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7813511 : List Nat := [1, 1, 4, 2, 2, 1, 2, 2, 4, 1, 3]
def baseStart_7813511 : Nat := 118140960795 + 7813511 * 2 ^ 59
def prefixEnd_7813511 : Nat := 4983230072969 + 3 ^ 40 * 7813511 * 2
def baseEnd_7813511 : Nat := 4012086742192484335978823

theorem tailTrace_7813511 : CollatzResearch.WordTrace tailWord_7813511 prefixEnd_7813511 4012086742192484335978823 := by
  unfold tailWord_7813511
  simp only [CollatzResearch.WordTrace]
  refine ⟨284982158395991563283600387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189988105597327708855733591 284982158395991563283600387)
  ·
    refine ⟨427473237593987344925400581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 284982158395991563283600387 427473237593987344925400581)
    ·
      refine ⟨80151232048872627173512609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 427473237593987344925400581 80151232048872627173512609)
      ·
        refine ⟨60113424036654470380134457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80151232048872627173512609 60113424036654470380134457)
        ·
          refine ⟨45085068027490852785100843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60113424036654470380134457 45085068027490852785100843)
          ·
            refine ⟨67627602041236279177651265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45085068027490852785100843 67627602041236279177651265)
            ·
              refine ⟨50720701530927209383238449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67627602041236279177651265 50720701530927209383238449)
              ·
                refine ⟨38040526148195407037428837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50720701530927209383238449 38040526148195407037428837)
                ·
                  refine ⟨7132598652786638819517907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38040526148195407037428837 7132598652786638819517907)
                  ·
                    refine ⟨10698897979179958229276861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7132598652786638819517907 10698897979179958229276861)
                    ·
                      refine ⟨4012086742192484335978823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10698897979179958229276861 4012086742192484335978823)
                      ·
                        rfl

theorem cell23_7813511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 2, 2, 4, 1, 3].length) (baseStart_7813511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7813511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7813511 prefixEnd_7813511 := by exact prefixLift 7813511
  have htrace : WordTrace (prefixWord ++ tailWord_7813511) baseStart_7813511 baseEnd_7813511 := by
    simpa [prefixWord, tailWord_7813511, baseEnd_7813511] using wordTrace_append hprefix tailTrace_7813511
  have hstable : (prefixWord ++ tailWord_7813511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7813511).length < 2 ^ (prefixWord ++ tailWord_7813511).sum := by decide
  have hdescent : baseEnd_7813511 < baseStart_7813511 := by decide
  rcases family_descends (prefixWord ++ tailWord_7813511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7813528 : List Nat := [2, 1, 2, 5, 1, 2, 1, 1, 4, 1, 3]
def baseStart_7813528 : Nat := 118140960795 + 7813528 * 2 ^ 59
def prefixEnd_7813528 : Nat := 4983230072969 + 3 ^ 40 * 7813528 * 2
def baseEnd_7813528 : Nat := 4012095471363610769466245

theorem tailTrace_7813528 : CollatzResearch.WordTrace tailWord_7813528 prefixEnd_7813528 4012095471363610769466245 := by
  unfold tailWord_7813528
  simp only [CollatzResearch.WordTrace]
  refine ⟨142491389218464987593484619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189988518957953316791312825 142491389218464987593484619)
  ·
    refine ⟨213737083827697481390226929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142491389218464987593484619 213737083827697481390226929)
    ·
      refine ⟨160302812870773111042670197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 213737083827697481390226929 160302812870773111042670197)
      ·
        refine ⟨15028388706634979160250331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 160302812870773111042670197 15028388706634979160250331)
        ·
          refine ⟨22542583059952468740375497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15028388706634979160250331 22542583059952468740375497)
          ·
            refine ⟨16906937294964351555281623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22542583059952468740375497 16906937294964351555281623)
            ·
              refine ⟨25360405942446527332922435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16906937294964351555281623 25360405942446527332922435)
              ·
                refine ⟨38040608913669790999383653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25360405942446527332922435 38040608913669790999383653)
                ·
                  refine ⟨7132614171313085812384435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38040608913669790999383653 7132614171313085812384435)
                  ·
                    refine ⟨10698921256969628718576653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7132614171313085812384435 10698921256969628718576653)
                    ·
                      refine ⟨4012095471363610769466245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10698921256969628718576653 4012095471363610769466245)
                      ·
                        rfl

theorem cell23_7813528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 1, 1, 4, 1, 3].length) (baseStart_7813528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7813528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7813528 prefixEnd_7813528 := by exact prefixLift 7813528
  have htrace : WordTrace (prefixWord ++ tailWord_7813528) baseStart_7813528 baseEnd_7813528 := by
    simpa [prefixWord, tailWord_7813528, baseEnd_7813528] using wordTrace_append hprefix tailTrace_7813528
  have hstable : (prefixWord ++ tailWord_7813528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7813528).length < 2 ^ (prefixWord ++ tailWord_7813528).sum := by decide
  have hdescent : baseEnd_7813528 < baseStart_7813528 := by decide
  rcases family_descends (prefixWord ++ tailWord_7813528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7813554 : List Nat := [3, 2, 1, 1, 1, 1, 4, 2, 2, 1, 5]
def baseStart_7813554 : Nat := 118140960795 + 7813554 * 2 ^ 59
def prefixEnd_7813554 : Nat := 4983230072969 + 3 ^ 40 * 7813554 * 2
def baseEnd_7813554 : Nat := 4012108821860627667741125

theorem tailTrace_7813554 : CollatzResearch.WordTrace tailWord_7813554 prefixEnd_7813554 4012108821860627667741125 := by
  unfold tailWord_7813554
  simp only [CollatzResearch.WordTrace]
  refine ⟨71245931683708945406853929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 189989151156557187751610477 71245931683708945406853929)
  ·
    refine ⟨53434448762781709055140447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71245931683708945406853929 53434448762781709055140447)
    ·
      refine ⟨80151673144172563582710671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53434448762781709055140447 80151673144172563582710671)
      ·
        refine ⟨120227509716258845374066007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80151673144172563582710671 120227509716258845374066007)
        ·
          refine ⟨180341264574388268061099011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120227509716258845374066007 180341264574388268061099011)
          ·
            refine ⟨270511896861582402091648517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 180341264574388268061099011 270511896861582402091648517)
            ·
              refine ⟨50720980661546700392184097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 270511896861582402091648517 50720980661546700392184097)
              ·
                refine ⟨38040735496160025294138073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50720980661546700392184097 38040735496160025294138073)
                ·
                  refine ⟨28530551622120018970603555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38040735496160025294138073 28530551622120018970603555)
                  ·
                    refine ⟨42795827433180028455905333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28530551622120018970603555 42795827433180028455905333)
                    ·
                      refine ⟨4012108821860627667741125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42795827433180028455905333 4012108821860627667741125)
                      ·
                        rfl

theorem cell23_7813554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 4, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 4, 2, 2, 1, 5].length) (baseStart_7813554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7813554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7813554 prefixEnd_7813554 := by exact prefixLift 7813554
  have htrace : WordTrace (prefixWord ++ tailWord_7813554) baseStart_7813554 baseEnd_7813554 := by
    simpa [prefixWord, tailWord_7813554, baseEnd_7813554] using wordTrace_append hprefix tailTrace_7813554
  have hstable : (prefixWord ++ tailWord_7813554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7813554).length < 2 ^ (prefixWord ++ tailWord_7813554).sum := by decide
  have hdescent : baseEnd_7813554 < baseStart_7813554 := by decide
  rcases family_descends (prefixWord ++ tailWord_7813554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7813651 : List Nat := [1, 1, 1, 2, 1, 5, 2, 3, 3, 4]
def baseStart_7813651 : Nat := 118140960795 + 7813651 * 2 ^ 59
def prefixEnd_7813651 : Nat := 4983230072969 + 3 ^ 40 * 7813651 * 2
def baseEnd_7813651 : Nat := 1337386209828037929409393

theorem tailTrace_7813651 : CollatzResearch.WordTrace tailWord_7813651 prefixEnd_7813651 1337386209828037929409393 := by
  unfold tailWord_7813651
  simp only [CollatzResearch.WordTrace]
  refine ⟨284987264615484367193696807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189991509743656244795797871 284987264615484367193696807)
  ·
    refine ⟨427480896923226550790545211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 284987264615484367193696807 427480896923226550790545211)
    ·
      refine ⟨641221345384839826185817817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 427480896923226550790545211 641221345384839826185817817)
      ·
        refine ⟨480916009038629869639363363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 641221345384839826185817817 480916009038629869639363363)
        ·
          refine ⟨721374013557944804459045045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 480916009038629869639363363 721374013557944804459045045)
          ·
            refine ⟨67628813771057325418035473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 721374013557944804459045045 67628813771057325418035473)
            ·
              refine ⟨50721610328292994063526605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67628813771057325418035473 50721610328292994063526605)
              ·
                refine ⟨19020603873109872773822477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50721610328292994063526605 19020603873109872773822477)
                ·
                  refine ⟨7132726452416202290183429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19020603873109872773822477 7132726452416202290183429)
                  ·
                    refine ⟨1337386209828037929409393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7132726452416202290183429 1337386209828037929409393)
                    ·
                      rfl

theorem cell23_7813651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 2, 3, 3, 4].length) (baseStart_7813651 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7813651 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7813651 prefixEnd_7813651 := by exact prefixLift 7813651
  have htrace : WordTrace (prefixWord ++ tailWord_7813651) baseStart_7813651 baseEnd_7813651 := by
    simpa [prefixWord, tailWord_7813651, baseEnd_7813651] using wordTrace_append hprefix tailTrace_7813651
  have hstable : (prefixWord ++ tailWord_7813651).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7813651).length < 2 ^ (prefixWord ++ tailWord_7813651).sum := by decide
  have hdescent : baseEnd_7813651 < baseStart_7813651 := by decide
  rcases family_descends (prefixWord ++ tailWord_7813651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7813685 : List Nat := [1, 3, 3, 1, 1, 2, 4, 3, 1, 4]
def baseStart_7813685 : Nat := 118140960795 + 7813685 * 2 ^ 59
def prefixEnd_7813685 : Nat := 4983230072969 + 3 ^ 40 * 7813685 * 2
def baseEnd_7813685 : Nat := 1337392029275455551734341

theorem tailTrace_7813685 : CollatzResearch.WordTrace tailWord_7813685 prefixEnd_7813685 1337392029275455551734341 := by
  unfold tailWord_7813685
  simp only [CollatzResearch.WordTrace]
  refine ⟨284988504697361191000434509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189992336464907460666956339 284988504697361191000434509)
  ·
    refine ⟨106870689261510446625162941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 284988504697361191000434509 106870689261510446625162941)
    ·
      refine ⟨40076508473066417484436103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 106870689261510446625162941 40076508473066417484436103)
      ·
        refine ⟨60114762709599626226654155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40076508473066417484436103 60114762709599626226654155)
        ·
          refine ⟨90172144064399439339981233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60114762709599626226654155 90172144064399439339981233)
          ·
            refine ⟨67629108048299579504985925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90172144064399439339981233 67629108048299579504985925)
            ·
              refine ⟨12680457759056171157184861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 67629108048299579504985925 12680457759056171157184861)
              ·
                refine ⟨4755171659646064183944323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12680457759056171157184861 4755171659646064183944323)
                ·
                  refine ⟨7132757489469096275916485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4755171659646064183944323 7132757489469096275916485)
                  ·
                    refine ⟨1337392029275455551734341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7132757489469096275916485 1337392029275455551734341)
                    ·
                      rfl

theorem cell23_7813685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 4, 3, 1, 4].length) (baseStart_7813685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7813685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7813685 prefixEnd_7813685 := by exact prefixLift 7813685
  have htrace : WordTrace (prefixWord ++ tailWord_7813685) baseStart_7813685 baseEnd_7813685 := by
    simpa [prefixWord, tailWord_7813685, baseEnd_7813685] using wordTrace_append hprefix tailTrace_7813685
  have hstable : (prefixWord ++ tailWord_7813685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7813685).length < 2 ^ (prefixWord ++ tailWord_7813685).sum := by decide
  have hdescent : baseEnd_7813685 < baseStart_7813685 := by decide
  rcases family_descends (prefixWord ++ tailWord_7813685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7813702 : List Nat := [6, 1, 1, 1, 2, 2, 2, 1, 3, 4]
def baseStart_7813702 : Nat := 118140960795 + 7813702 * 2 ^ 59
def prefixEnd_7813702 : Nat := 4983230072969 + 3 ^ 40 * 7813702 * 2
def baseEnd_7813702 : Nat := 1337394938999164362896815

theorem tailTrace_7813702 : CollatzResearch.WordTrace tailWord_7813702 prefixEnd_7813702 1337394938999164362896815 := by
  unfold tailWord_7813702
  simp only [CollatzResearch.WordTrace]
  refine ⟨8905910148071862590743855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 189992749825533068602535573 8905910148071862590743855)
  ·
    refine ⟨13358865222107793886115783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8905910148071862590743855 13358865222107793886115783)
    ·
      refine ⟨20038297833161690829173675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13358865222107793886115783 20038297833161690829173675)
      ·
        refine ⟨30057446749742536243760513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20038297833161690829173675 30057446749742536243760513)
        ·
          refine ⟨22543085062306902182820385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30057446749742536243760513 22543085062306902182820385)
          ·
            refine ⟨16907313796730176637115289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22543085062306902182820385 16907313796730176637115289)
            ·
              refine ⟨12680485347547632477836467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16907313796730176637115289 12680485347547632477836467)
              ·
                refine ⟨19020728021321448716754701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12680485347547632477836467 19020728021321448716754701)
                ·
                  refine ⟨7132773007995543268783013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19020728021321448716754701 7132773007995543268783013)
                  ·
                    refine ⟨1337394938999164362896815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7132773007995543268783013 1337394938999164362896815)
                    ·
                      rfl

theorem cell23_7813702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 2, 1, 3, 4].length) (baseStart_7813702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7813702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7813702 prefixEnd_7813702 := by exact prefixLift 7813702
  have htrace : WordTrace (prefixWord ++ tailWord_7813702) baseStart_7813702 baseEnd_7813702 := by
    simpa [prefixWord, tailWord_7813702, baseEnd_7813702] using wordTrace_append hprefix tailTrace_7813702
  have hstable : (prefixWord ++ tailWord_7813702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7813702).length < 2 ^ (prefixWord ++ tailWord_7813702).sum := by decide
  have hdescent : baseEnd_7813702 < baseStart_7813702 := by decide
  rcases family_descends (prefixWord ++ tailWord_7813702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7813751 : List Nat := [1, 1, 3, 1, 1, 3, 3, 3, 1, 1, 5]
def baseStart_7813751 : Nat := 118140960795 + 7813751 * 2 ^ 59
def prefixEnd_7813751 : Nat := 4983230072969 + 3 ^ 40 * 7813751 * 2
def baseEnd_7813751 : Nat := 4012209977549563396977719

theorem tailTrace_7813751 : CollatzResearch.WordTrace tailWord_7813751 prefixEnd_7813751 4012209977549563396977719 := by
  unfold tailWord_7813751
  simp only [CollatzResearch.WordTrace]
  refine ⟨284990911915122084272337107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189993941276748056181558071 284990911915122084272337107)
  ·
    refine ⟨427486367872683126408505661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 284990911915122084272337107 427486367872683126408505661)
    ·
      refine ⟨160307387952256172403189623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 427486367872683126408505661 160307387952256172403189623)
      ·
        refine ⟨240461081928384258604784435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160307387952256172403189623 240461081928384258604784435)
        ·
          refine ⟨360691622892576387907176653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 240461081928384258604784435 360691622892576387907176653)
          ·
            refine ⟨135259358584716145465191245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 360691622892576387907176653 135259358584716145465191245)
            ·
              refine ⟨50722259469268554549446717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 135259358584716145465191245 50722259469268554549446717)
              ·
                refine ⟨19020847300975707956042519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50722259469268554549446717 19020847300975707956042519)
                ·
                  refine ⟨28531270951463561934063779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19020847300975707956042519 28531270951463561934063779)
                  ·
                    refine ⟨42796906427195342901095669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28531270951463561934063779 42796906427195342901095669)
                    ·
                      refine ⟨4012209977549563396977719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42796906427195342901095669 4012209977549563396977719)
                      ·
                        rfl

theorem cell23_7813751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 3, 3, 1, 1, 5].length) (baseStart_7813751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7813751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7813751 prefixEnd_7813751 := by exact prefixLift 7813751
  have htrace : WordTrace (prefixWord ++ tailWord_7813751) baseStart_7813751 baseEnd_7813751 := by
    simpa [prefixWord, tailWord_7813751, baseEnd_7813751] using wordTrace_append hprefix tailTrace_7813751
  have hstable : (prefixWord ++ tailWord_7813751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7813751).length < 2 ^ (prefixWord ++ tailWord_7813751).sum := by decide
  have hdescent : baseEnd_7813751 < baseStart_7813751 := by decide
  rcases family_descends (prefixWord ++ tailWord_7813751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7813761 : List Nat := [1, 2, 4, 2, 1, 1, 1, 1, 3, 1, 6]
def baseStart_7813761 : Nat := 118140960795 + 7813761 * 2 ^ 59
def prefixEnd_7813761 : Nat := 4983230072969 + 3 ^ 40 * 7813761 * 2
def baseEnd_7813761 : Nat := 4012215112356108357852673

theorem tailTrace_7813761 : CollatzResearch.WordTrace tailWord_7813761 prefixEnd_7813761 4012215112356108357852673 := by
  unfold tailWord_7813761
  simp only [CollatzResearch.WordTrace]
  refine ⟨284991276645085855980201137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189994184430057237320134091 284991276645085855980201137)
  ·
    refine ⟨213743457483814391985150853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 284991276645085855980201137 213743457483814391985150853)
    ·
      refine ⟨40076898278215198497215785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 213743457483814391985150853 40076898278215198497215785)
      ·
        refine ⟨30057673708661398872911839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40076898278215198497215785 30057673708661398872911839)
        ·
          refine ⟨45086510562992098309367759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30057673708661398872911839 45086510562992098309367759)
          ·
            refine ⟨67629765844488147464051639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45086510562992098309367759 67629765844488147464051639)
            ·
              refine ⟨101444648766732221196077459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67629765844488147464051639 101444648766732221196077459)
              ·
                refine ⟨152166973150098331794116189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 101444648766732221196077459 152166973150098331794116189)
                ·
                  refine ⟨57062614931286874422793571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 152166973150098331794116189 57062614931286874422793571)
                  ·
                    refine ⟨85593922396930311634190357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 57062614931286874422793571 85593922396930311634190357)
                    ·
                      refine ⟨4012215112356108357852673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 85593922396930311634190357 4012215112356108357852673)
                      ·
                        rfl

theorem cell23_7813761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 1, 3, 1, 6].length) (baseStart_7813761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7813761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7813761 prefixEnd_7813761 := by exact prefixLift 7813761
  have htrace : WordTrace (prefixWord ++ tailWord_7813761) baseStart_7813761 baseEnd_7813761 := by
    simpa [prefixWord, tailWord_7813761, baseEnd_7813761] using wordTrace_append hprefix tailTrace_7813761
  have hstable : (prefixWord ++ tailWord_7813761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7813761).length < 2 ^ (prefixWord ++ tailWord_7813761).sum := by decide
  have hdescent : baseEnd_7813761 < baseStart_7813761 := by decide
  rcases family_descends (prefixWord ++ tailWord_7813761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7813778 : List Nat := [3, 2, 3, 1, 2, 1, 2, 1, 1, 1, 6]
def baseStart_7813778 : Nat := 118140960795 + 7813778 * 2 ^ 59
def prefixEnd_7813778 : Nat := 4983230072969 + 3 ^ 40 * 7813778 * 2
def baseEnd_7813778 : Nat := 4012223841527234791340095

theorem tailTrace_7813778 : CollatzResearch.WordTrace tailWord_7813778 prefixEnd_7813778 4012223841527234791340095 := by
  unfold tailWord_7813778
  simp only [CollatzResearch.WordTrace]
  refine ⟨71247974171506066970892497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 189994597790682845255713325 71247974171506066970892497)
  ·
    refine ⟨53435980628629550228169373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71247974171506066970892497 53435980628629550228169373)
    ·
      refine ⟨20038492735736081335563515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53435980628629550228169373 20038492735736081335563515)
      ·
        refine ⟨30057739103604122003345273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20038492735736081335563515 30057739103604122003345273)
        ·
          refine ⟨22543304327703091502508955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30057739103604122003345273 22543304327703091502508955)
          ·
            refine ⟨33814956491554637253763433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22543304327703091502508955 33814956491554637253763433)
            ·
              refine ⟨25361217368665977940322575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33814956491554637253763433 25361217368665977940322575)
              ·
                refine ⟨38041826052998966910483863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25361217368665977940322575 38041826052998966910483863)
                ·
                  refine ⟨57062739079498450365725795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38041826052998966910483863 57062739079498450365725795)
                  ·
                    refine ⟨85594108619247675548588693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 57062739079498450365725795 85594108619247675548588693)
                    ·
                      refine ⟨4012223841527234791340095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 85594108619247675548588693 4012223841527234791340095)
                      ·
                        rfl

theorem cell23_7813778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 2, 1, 1, 1, 6].length) (baseStart_7813778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7813778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7813778 prefixEnd_7813778 := by exact prefixLift 7813778
  have htrace : WordTrace (prefixWord ++ tailWord_7813778) baseStart_7813778 baseEnd_7813778 := by
    simpa [prefixWord, tailWord_7813778, baseEnd_7813778] using wordTrace_append hprefix tailTrace_7813778
  have hstable : (prefixWord ++ tailWord_7813778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7813778).length < 2 ^ (prefixWord ++ tailWord_7813778).sum := by decide
  have hdescent : baseEnd_7813778 < baseStart_7813778 := by decide
  rcases family_descends (prefixWord ++ tailWord_7813778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7813799 : List Nat := [1, 1, 6, 3, 1, 1, 3, 1, 1, 1, 4]
def baseStart_7813799 : Nat := 118140960795 + 7813799 * 2 ^ 59
def prefixEnd_7813799 : Nat := 4983230072969 + 3 ^ 40 * 7813799 * 2
def baseEnd_7813799 : Nat := 4012234624620979209177499

theorem tailTrace_7813799 : CollatzResearch.WordTrace tailWord_7813799 prefixEnd_7813799 4012234624620979209177499 := by
  unfold tailWord_7813799
  simp only [CollatzResearch.WordTrace]
  refine ⟨284992662618948188470084451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189995108412632125646722967 284992662618948188470084451)
  ·
    refine ⟨427488993928422282705126677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 284992662618948188470084451 427488993928422282705126677)
    ·
      refine ⟨20038546590394794501802813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 427488993928422282705126677 20038546590394794501802813)
      ·
        refine ⟨7514454971398047938176055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20038546590394794501802813 7514454971398047938176055)
        ·
          refine ⟨11271682457097071907264083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7514454971398047938176055 11271682457097071907264083)
          ·
            refine ⟨16907523685645607860896125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11271682457097071907264083 16907523685645607860896125)
            ·
              refine ⟨6340321382117102947836047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16907523685645607860896125 6340321382117102947836047)
              ·
                refine ⟨9510482073175654421754071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6340321382117102947836047 9510482073175654421754071)
                ·
                  refine ⟨14265723109763481632631107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9510482073175654421754071 14265723109763481632631107)
                  ·
                    refine ⟨21398584664645222448946661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14265723109763481632631107 21398584664645222448946661)
                    ·
                      refine ⟨4012234624620979209177499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21398584664645222448946661 4012234624620979209177499)
                      ·
                        rfl

theorem cell23_7813799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 3, 1, 1, 1, 4].length) (baseStart_7813799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7813799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7813799 prefixEnd_7813799 := by exact prefixLift 7813799
  have htrace : WordTrace (prefixWord ++ tailWord_7813799) baseStart_7813799 baseEnd_7813799 := by
    simpa [prefixWord, tailWord_7813799, baseEnd_7813799] using wordTrace_append hprefix tailTrace_7813799
  have hstable : (prefixWord ++ tailWord_7813799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7813799).length < 2 ^ (prefixWord ++ tailWord_7813799).sum := by decide
  have hdescent : baseEnd_7813799 < baseStart_7813799 := by decide
  rcases family_descends (prefixWord ++ tailWord_7813799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7813855 : List Nat := [1, 1, 2, 3, 2, 3, 2, 2, 1, 4, 2]
def baseStart_7813855 : Nat := 118140960795 + 7813855 * 2 ^ 59
def prefixEnd_7813855 : Nat := 4983230072969 + 3 ^ 40 * 7813855 * 2
def baseEnd_7813855 : Nat := 4012263379537630990077241

theorem tailTrace_7813855 : CollatzResearch.WordTrace tailWord_7813855 prefixEnd_7813855 4012263379537630990077241 := by
  unfold tailWord_7813855
  simp only [CollatzResearch.WordTrace]
  refine ⟨284994705106745310034123019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189996470071163540022748679 284994705106745310034123019)
  ·
    refine ⟨427492057660117965051184529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 284994705106745310034123019 427492057660117965051184529)
    ·
      refine ⟨320619043245088473788388397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 427492057660117965051184529 320619043245088473788388397)
      ·
        refine ⟨120232141216908177670645649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 320619043245088473788388397 120232141216908177670645649)
        ·
          refine ⟨90174105912681133252984237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120232141216908177670645649 90174105912681133252984237)
          ·
            refine ⟨33815289717255424969869089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 90174105912681133252984237 33815289717255424969869089)
            ·
              refine ⟨25361467287941568727401817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33815289717255424969869089 25361467287941568727401817)
              ·
                refine ⟨19021100465956176545551363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25361467287941568727401817 19021100465956176545551363)
                ·
                  refine ⟨28531650698934264818327045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19021100465956176545551363 28531650698934264818327045)
                  ·
                    refine ⟨5349684506050174653436321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28531650698934264818327045 5349684506050174653436321)
                    ·
                      refine ⟨4012263379537630990077241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5349684506050174653436321 4012263379537630990077241)
                      ·
                        rfl

theorem cell23_7813855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 2, 2, 1, 4, 2].length) (baseStart_7813855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7813855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7813855 prefixEnd_7813855 := by exact prefixLift 7813855
  have htrace : WordTrace (prefixWord ++ tailWord_7813855) baseStart_7813855 baseEnd_7813855 := by
    simpa [prefixWord, tailWord_7813855, baseEnd_7813855] using wordTrace_append hprefix tailTrace_7813855
  have hstable : (prefixWord ++ tailWord_7813855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7813855).length < 2 ^ (prefixWord ++ tailWord_7813855).sum := by decide
  have hdescent : baseEnd_7813855 < baseStart_7813855 := by decide
  rcases family_descends (prefixWord ++ tailWord_7813855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7813859 : List Nat := [1, 1, 1, 7, 1, 1, 4, 1, 1, 3, 2]
def baseStart_7813859 : Nat := 118140960795 + 7813859 * 2 ^ 59
def prefixEnd_7813859 : Nat := 4983230072969 + 3 ^ 40 * 7813859 * 2
def baseEnd_7813859 : Nat := 4012265433460248974427223

theorem tailTrace_7813859 : CollatzResearch.WordTrace tailWord_7813859 prefixEnd_7813859 4012265433460248974427223 := by
  unfold tailWord_7813859
  simp only [CollatzResearch.WordTrace]
  refine ⟨284994850998730818717268631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189996567332487212478179087 284994850998730818717268631)
  ·
    refine ⟨427492276498096228075902947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 284994850998730818717268631 427492276498096228075902947)
    ·
      refine ⟨641238414747144342113854421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 427492276498096228075902947 641238414747144342113854421)
      ·
        refine ⟨15029025345636195518293463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 641238414747144342113854421 15029025345636195518293463)
        ·
          refine ⟨22543538018454293277440195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15029025345636195518293463 22543538018454293277440195)
          ·
            refine ⟨33815307027681439916160293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22543538018454293277440195 33815307027681439916160293)
            ·
              refine ⟨6340370067690269984280055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33815307027681439916160293 6340370067690269984280055)
              ·
                refine ⟨9510555101535404976420083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6340370067690269984280055 9510555101535404976420083)
                ·
                  refine ⟨14265832652303107464630125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9510555101535404976420083 14265832652303107464630125)
                  ·
                    refine ⟨5349687244613665299236297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14265832652303107464630125 5349687244613665299236297)
                    ·
                      refine ⟨4012265433460248974427223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5349687244613665299236297 4012265433460248974427223)
                      ·
                        rfl

theorem cell23_7813859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 4, 1, 1, 3, 2].length) (baseStart_7813859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7813859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7813859 prefixEnd_7813859 := by exact prefixLift 7813859
  have htrace : WordTrace (prefixWord ++ tailWord_7813859) baseStart_7813859 baseEnd_7813859 := by
    simpa [prefixWord, tailWord_7813859, baseEnd_7813859] using wordTrace_append hprefix tailTrace_7813859
  have hstable : (prefixWord ++ tailWord_7813859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7813859).length < 2 ^ (prefixWord ++ tailWord_7813859).sum := by decide
  have hdescent : baseEnd_7813859 < baseStart_7813859 := by decide
  rcases family_descends (prefixWord ++ tailWord_7813859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7813940 : List Nat := [2, 5, 1, 1, 4, 1, 2, 1, 2, 2, 2]
def baseStart_7813940 : Nat := 118140960795 + 7813940 * 2 ^ 59
def prefixEnd_7813940 : Nat := 4983230072969 + 3 ^ 40 * 7813940 * 2
def baseEnd_7813940 : Nat := 4012307025393263157514351

theorem tailTrace_7813940 : CollatzResearch.WordTrace tailWord_7813940 prefixEnd_7813940 4012307025393263157514351 := by
  unfold tailWord_7813940
  simp only [CollatzResearch.WordTrace]
  refine ⟨142498902655718684775483637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189998536874291579700644849 142498902655718684775483637)
  ·
    refine ⟨13359272123973626697701591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 142498902655718684775483637 13359272123973626697701591)
    ·
      refine ⟨20038908185960440046552387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13359272123973626697701591 20038908185960440046552387)
      ·
        refine ⟨30058362278940660069828581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20038908185960440046552387 30058362278940660069828581)
        ·
          refine ⟨5635942927301373763092859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30058362278940660069828581 5635942927301373763092859)
          ·
            refine ⟨8453914390952060644639289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5635942927301373763092859 8453914390952060644639289)
            ·
              refine ⟨6340435793214045483479467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8453914390952060644639289 6340435793214045483479467)
              ·
                refine ⟨9510653689821068225219201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6340435793214045483479467 9510653689821068225219201)
                ·
                  refine ⟨7132990267365801168914401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9510653689821068225219201 7132990267365801168914401)
                  ·
                    refine ⟨5349742700524350876685801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7132990267365801168914401 5349742700524350876685801)
                    ·
                      refine ⟨4012307025393263157514351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5349742700524350876685801 4012307025393263157514351)
                      ·
                        rfl

theorem cell23_7813940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 4, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 4, 1, 2, 1, 2, 2, 2].length) (baseStart_7813940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7813940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7813940 prefixEnd_7813940 := by exact prefixLift 7813940
  have htrace : WordTrace (prefixWord ++ tailWord_7813940) baseStart_7813940 baseEnd_7813940 := by
    simpa [prefixWord, tailWord_7813940, baseEnd_7813940] using wordTrace_append hprefix tailTrace_7813940
  have hstable : (prefixWord ++ tailWord_7813940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7813940).length < 2 ^ (prefixWord ++ tailWord_7813940).sum := by decide
  have hdescent : baseEnd_7813940 < baseStart_7813940 := by decide
  rcases family_descends (prefixWord ++ tailWord_7813940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7813989 : List Nat := [1, 3, 1, 3, 1, 1, 6, 2, 1, 4]
def baseStart_7813989 : Nat := 118140960795 + 7813989 * 2 ^ 59
def prefixEnd_7813989 : Nat := 4983230072969 + 3 ^ 40 * 7813989 * 2
def baseEnd_7813989 : Nat := 1337444061981777821933875

theorem tailTrace_7813989 : CollatzResearch.WordTrace tailWord_7813989 prefixEnd_7813989 1337444061981777821933875 := by
  unfold tailWord_7813989
  simp only [CollatzResearch.WordTrace]
  refine ⟨284999592488259850919501021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189999728325506567279667347 284999592488259850919501021)
  ·
    refine ⟨106874847183097444094812883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 284999592488259850919501021 106874847183097444094812883)
    ·
      refine ⟨160312270774646166142219325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106874847183097444094812883 160312270774646166142219325)
      ·
        refine ⟨60117101540492312303332247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 160312270774646166142219325 60117101540492312303332247)
        ·
          refine ⟨90175652310738468454998371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60117101540492312303332247 90175652310738468454998371)
          ·
            refine ⟨135263478466107702682497557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90175652310738468454998371 135263478466107702682497557)
            ·
              refine ⟨6340475553098798563242073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 135263478466107702682497557 6340475553098798563242073)
              ·
                refine ⟨4755356664824098922431555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6340475553098798563242073 4755356664824098922431555)
                ·
                  refine ⟨7133034997236148383647333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4755356664824098922431555 7133034997236148383647333)
                  ·
                    refine ⟨1337444061981777821933875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7133034997236148383647333 1337444061981777821933875)
                    ·
                      rfl

theorem cell23_7813989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 6, 2, 1, 4].length) (baseStart_7813989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7813989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7813989 prefixEnd_7813989 := by exact prefixLift 7813989
  have htrace : WordTrace (prefixWord ++ tailWord_7813989) baseStart_7813989 baseEnd_7813989 := by
    simpa [prefixWord, tailWord_7813989, baseEnd_7813989] using wordTrace_append hprefix tailTrace_7813989
  have hstable : (prefixWord ++ tailWord_7813989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7813989).length < 2 ^ (prefixWord ++ tailWord_7813989).sum := by decide
  have hdescent : baseEnd_7813989 < baseStart_7813989 := by decide
  rcases family_descends (prefixWord ++ tailWord_7813989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7814069 : List Nat := [1, 3, 3, 2, 1, 1, 1, 4, 3, 2, 2]
def baseStart_7814069 : Nat := 118140960795 + 7814069 * 2 ^ 59
def prefixEnd_7814069 : Nat := 4983230072969 + 3 ^ 40 * 7814069 * 2
def baseEnd_7814069 : Nat := 4012373264397693152801257

theorem tailTrace_7814069 : CollatzResearch.WordTrace tailWord_7814069 prefixEnd_7814069 4012373264397693152801257 := by
  unfold tailWord_7814069
  simp only [CollatzResearch.WordTrace]
  refine ⟨285002510327970024582413261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190001673551980016388275507 285002510327970024582413261)
  ·
    refine ⟨106875941372988759218404973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 285002510327970024582413261 106875941372988759218404973)
    ·
      refine ⟨40078478014870784706901865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 106875941372988759218404973 40078478014870784706901865)
      ·
        refine ⟨30058858511153088530176399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40078478014870784706901865 30058858511153088530176399)
        ·
          refine ⟨45088287766729632795264599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30058858511153088530176399 45088287766729632795264599)
          ·
            refine ⟨67632431650094449192896899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45088287766729632795264599 67632431650094449192896899)
            ·
              refine ⟨101448647475141673789345349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67632431650094449192896899 101448647475141673789345349)
              ·
                refine ⟨19021621401589063835502253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 101448647475141673789345349 19021621401589063835502253)
                ·
                  refine ⟨7133108025595898938313345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19021621401589063835502253 7133108025595898938313345)
                  ·
                    refine ⟨5349831019196924203735009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7133108025595898938313345 5349831019196924203735009)
                    ·
                      refine ⟨4012373264397693152801257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5349831019196924203735009 4012373264397693152801257)
                      ·
                        rfl

theorem cell23_7814069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 4, 3, 2, 2].length) (baseStart_7814069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7814069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7814069 prefixEnd_7814069 := by exact prefixLift 7814069
  have htrace : WordTrace (prefixWord ++ tailWord_7814069) baseStart_7814069 baseEnd_7814069 := by
    simpa [prefixWord, tailWord_7814069, baseEnd_7814069] using wordTrace_append hprefix tailTrace_7814069
  have hstable : (prefixWord ++ tailWord_7814069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7814069).length < 2 ^ (prefixWord ++ tailWord_7814069).sum := by decide
  have hdescent : baseEnd_7814069 < baseStart_7814069 := by decide
  rcases family_descends (prefixWord ++ tailWord_7814069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7814072 : List Nat := [2, 1, 2, 1, 2, 4, 1, 4, 1, 2, 3]
def baseStart_7814072 : Nat := 118140960795 + 7814072 * 2 ^ 59
def prefixEnd_7814072 : Nat := 4983230072969 + 3 ^ 40 * 7814072 * 2
def baseEnd_7814072 : Nat := 4012374804839656641063743

theorem tailTrace_7814072 : CollatzResearch.WordTrace tailWord_7814072 prefixEnd_7814072 4012374804839656641063743 := by
  unfold tailWord_7814072
  simp only [CollatzResearch.WordTrace]
  refine ⟨142501309873479578047386235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190001746497972770729848313 142501309873479578047386235)
  ·
    refine ⟨213751964810219367071079353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142501309873479578047386235 213751964810219367071079353)
    ·
      refine ⟨160313973607664525303309515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 213751964810219367071079353 160313973607664525303309515)
      ·
        refine ⟨240470960411496787954964273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160313973607664525303309515 240470960411496787954964273)
        ·
          refine ⟨180353220308622590966223205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 240470960411496787954964273 180353220308622590966223205)
          ·
            refine ⟨33816228807866735806166851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 180353220308622590966223205 33816228807866735806166851)
            ·
              refine ⟨50724343211800103709250277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33816228807866735806166851 50724343211800103709250277)
              ·
                refine ⟨9510814352212519445484427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50724343211800103709250277 9510814352212519445484427)
                ·
                  refine ⟨14266221528318779168226641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9510814352212519445484427 14266221528318779168226641)
                  ·
                    refine ⟨10699666146239084376169981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14266221528318779168226641 10699666146239084376169981)
                    ·
                      refine ⟨4012374804839656641063743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10699666146239084376169981 4012374804839656641063743)
                      ·
                        rfl

theorem cell23_7814072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 1, 4, 1, 2, 3].length) (baseStart_7814072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7814072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7814072 prefixEnd_7814072 := by exact prefixLift 7814072
  have htrace : WordTrace (prefixWord ++ tailWord_7814072) baseStart_7814072 baseEnd_7814072 := by
    simpa [prefixWord, tailWord_7814072, baseEnd_7814072] using wordTrace_append hprefix tailTrace_7814072
  have hstable : (prefixWord ++ tailWord_7814072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7814072).length < 2 ^ (prefixWord ++ tailWord_7814072).sum := by decide
  have hdescent : baseEnd_7814072 < baseStart_7814072 := by decide
  rcases family_descends (prefixWord ++ tailWord_7814072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7814129 : List Nat := [1, 2, 2, 2, 4, 2, 1, 1, 3, 3, 2]
def baseStart_7814129 : Nat := 118140960795 + 7814129 * 2 ^ 59
def prefixEnd_7814129 : Nat := 4983230072969 + 3 ^ 40 * 7814129 * 2
def baseEnd_7814129 : Nat := 4012404073236962918050981

theorem tailTrace_7814129 : CollatzResearch.WordTrace tailWord_7814129 prefixEnd_7814129 4012404073236962918050981 := by
  unfold tailWord_7814129
  simp only [CollatzResearch.WordTrace]
  refine ⟨285004698707752654829597441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190003132471835103219731627 285004698707752654829597441)
  ·
    refine ⟨213753524030814491122198081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 285004698707752654829597441 213753524030814491122198081)
    ·
      refine ⟨160315143023110868341648561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 213753524030814491122198081 160315143023110868341648561)
      ·
        refine ⟨120236357267333151256236421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 160315143023110868341648561 120236357267333151256236421)
        ·
          refine ⟨22544316987624965860544329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 120236357267333151256236421 22544316987624965860544329)
          ·
            refine ⟨16908237740718724395408247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22544316987624965860544329 16908237740718724395408247)
            ·
              refine ⟨25362356611078086593112371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16908237740718724395408247 25362356611078086593112371)
              ·
                refine ⟨38043534916617129889668557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25362356611078086593112371 38043534916617129889668557)
                ·
                  refine ⟨14266325593731423708625709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38043534916617129889668557 14266325593731423708625709)
                  ·
                    refine ⟨5349872097649283890734641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14266325593731423708625709 5349872097649283890734641)
                    ·
                      refine ⟨4012404073236962918050981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5349872097649283890734641 4012404073236962918050981)
                      ·
                        rfl

theorem cell23_7814129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 1, 1, 3, 3, 2].length) (baseStart_7814129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7814129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7814129 prefixEnd_7814129 := by exact prefixLift 7814129
  have htrace : WordTrace (prefixWord ++ tailWord_7814129) baseStart_7814129 baseEnd_7814129 := by
    simpa [prefixWord, tailWord_7814129, baseEnd_7814129] using wordTrace_append hprefix tailTrace_7814129
  have hstable : (prefixWord ++ tailWord_7814129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7814129).length < 2 ^ (prefixWord ++ tailWord_7814129).sum := by decide
  have hdescent : baseEnd_7814129 < baseStart_7814129 := by decide
  rcases family_descends (prefixWord ++ tailWord_7814129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7814252 : List Nat := [2, 2, 1, 1, 3, 2, 1, 3, 1, 4, 3]
def baseStart_7814252 : Nat := 118140960795 + 7814252 * 2 ^ 59
def prefixEnd_7814252 : Nat := 4983230072969 + 3 ^ 40 * 7814252 * 2
def baseEnd_7814252 : Nat := 4012467231357465936812915

theorem tailTrace_7814252 : CollatzResearch.WordTrace tailWord_7814252 prefixEnd_7814252 4012467231357465936812915 := by
  unfold tailWord_7814252
  simp only [CollatzResearch.WordTrace]
  refine ⟨142504592443153523418162505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190006123257538031224216673 142504592443153523418162505)
  ·
    refine ⟨106878444332365142563621879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142504592443153523418162505 106878444332365142563621879)
    ·
      refine ⟨160317666498547713845432819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106878444332365142563621879 160317666498547713845432819)
      ·
        refine ⟨240476499747821570768149229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160317666498547713845432819 240476499747821570768149229)
        ·
          refine ⟨90178687405433089038055961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 240476499747821570768149229 90178687405433089038055961)
          ·
            refine ⟨67634015554074816778541971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90178687405433089038055961 67634015554074816778541971)
            ·
              refine ⟨101451023331112225167812957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67634015554074816778541971 101451023331112225167812957)
              ·
                refine ⟨38044133749167084437929859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 101451023331112225167812957 38044133749167084437929859)
                ·
                  refine ⟨57066200623750626656894789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38044133749167084437929859 57066200623750626656894789)
                  ·
                    refine ⟨10699912616953242498167773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 57066200623750626656894789 10699912616953242498167773)
                    ·
                      refine ⟨4012467231357465936812915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10699912616953242498167773 4012467231357465936812915)
                      ·
                        rfl

theorem cell23_7814252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 4, 3].length) (baseStart_7814252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7814252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7814252 prefixEnd_7814252 := by exact prefixLift 7814252
  have htrace : WordTrace (prefixWord ++ tailWord_7814252) baseStart_7814252 baseEnd_7814252 := by
    simpa [prefixWord, tailWord_7814252, baseEnd_7814252] using wordTrace_append hprefix tailTrace_7814252
  have hstable : (prefixWord ++ tailWord_7814252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7814252).length < 2 ^ (prefixWord ++ tailWord_7814252).sum := by decide
  have hdescent : baseEnd_7814252 < baseStart_7814252 := by decide
  rcases family_descends (prefixWord ++ tailWord_7814252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7814255 : List Nat := [1, 1, 2, 1, 3, 3, 1, 1, 10]
def baseStart_7814255 : Nat := 118140960795 + 7814255 * 2 ^ 59
def prefixEnd_7814255 : Nat := 4983230072969 + 3 ^ 40 * 7814255 * 2
def baseEnd_7814255 : Nat := 445829863533269936119489

theorem tailTrace_7814255 : CollatzResearch.WordTrace tailWord_7814255 prefixEnd_7814255 445829863533269936119489 := by
  unfold tailWord_7814255
  simp only [CollatzResearch.WordTrace]
  refine ⟨285009294305296178348684219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190006196203530785565789479 285009294305296178348684219)
  ·
    refine ⟨427513941457944267523026329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285009294305296178348684219 427513941457944267523026329)
    ·
      refine ⟨320635456093458200642269747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 427513941457944267523026329 320635456093458200642269747)
      ·
        refine ⟨480953184140187300963404621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 320635456093458200642269747 480953184140187300963404621)
        ·
          refine ⟨180357444052570237861276733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 480953184140187300963404621 180357444052570237861276733)
          ·
            refine ⟨67634041519713839197978775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 180357444052570237861276733 67634041519713839197978775)
            ·
              refine ⟨101451062279570758796968163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67634041519713839197978775 101451062279570758796968163)
              ·
                refine ⟨152176593419356138195452245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 101451062279570758796968163 152176593419356138195452245)
                ·
                  refine ⟨445829863533269936119489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 152176593419356138195452245 445829863533269936119489)
                  ·
                    rfl

theorem cell23_7814255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 1, 10].length) (baseStart_7814255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7814255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7814255 prefixEnd_7814255 := by exact prefixLift 7814255
  have htrace : WordTrace (prefixWord ++ tailWord_7814255) baseStart_7814255 baseEnd_7814255 := by
    simpa [prefixWord, tailWord_7814255, baseEnd_7814255] using wordTrace_append hprefix tailTrace_7814255
  have hstable : (prefixWord ++ tailWord_7814255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7814255).length < 2 ^ (prefixWord ++ tailWord_7814255).sum := by decide
  have hdescent : baseEnd_7814255 < baseStart_7814255 := by decide
  rcases family_descends (prefixWord ++ tailWord_7814255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7814269 : List Nat := [1, 4, 1, 1, 3, 1, 3, 2, 2, 2, 3]
def baseStart_7814269 : Nat := 118140960795 + 7814269 * 2 ^ 59
def prefixEnd_7814269 : Nat := 4983230072969 + 3 ^ 40 * 7814269 * 2
def baseEnd_7814269 : Nat := 4012475960528592370300337

theorem tailTrace_7814269 : CollatzResearch.WordTrace tailWord_7814269 prefixEnd_7814269 4012475960528592370300337 := by
  unfold tailWord_7814269
  simp only [CollatzResearch.WordTrace]
  refine ⟨285009804927245458739693861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190006536618163639159795907 285009804927245458739693861)
  ·
    refine ⟨53439338423858523513692599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 285009804927245458739693861 53439338423858523513692599)
    ·
      refine ⟨80159007635787785270538899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53439338423858523513692599 80159007635787785270538899)
      ·
        refine ⟨120238511453681677905808349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80159007635787785270538899 120238511453681677905808349)
        ·
          refine ⟨45089441795130629214678131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 120238511453681677905808349 45089441795130629214678131)
          ·
            refine ⟨67634162692695943822017197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45089441795130629214678131 67634162692695943822017197)
            ·
              refine ⟨25362811009760978933256449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67634162692695943822017197 25362811009760978933256449)
              ·
                refine ⟨19022108257320734199942337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25362811009760978933256449 19022108257320734199942337)
                ·
                  refine ⟨14266581192990550649956753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19022108257320734199942337 14266581192990550649956753)
                  ·
                    refine ⟨10699935894742912987467565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14266581192990550649956753 10699935894742912987467565)
                    ·
                      refine ⟨4012475960528592370300337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10699935894742912987467565 4012475960528592370300337)
                      ·
                        rfl

theorem cell23_7814269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 3, 2, 2, 2, 3].length) (baseStart_7814269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7814269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7814269 prefixEnd_7814269 := by exact prefixLift 7814269
  have htrace : WordTrace (prefixWord ++ tailWord_7814269) baseStart_7814269 baseEnd_7814269 := by
    simpa [prefixWord, tailWord_7814269, baseEnd_7814269] using wordTrace_append hprefix tailTrace_7814269
  have hstable : (prefixWord ++ tailWord_7814269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7814269).length < 2 ^ (prefixWord ++ tailWord_7814269).sum := by decide
  have hdescent : baseEnd_7814269 < baseStart_7814269 := by decide
  rcases family_descends (prefixWord ++ tailWord_7814269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7814276 : List Nat := [2, 3, 2, 1, 2, 4, 1, 1, 3, 4]
def baseStart_7814276 : Nat := 118140960795 + 7814276 * 2 ^ 59
def prefixEnd_7814276 : Nat := 4983230072969 + 3 ^ 40 * 7814276 * 2
def baseEnd_7814276 : Nat := 1337493184964391280970935

theorem tailTrace_7814276 : CollatzResearch.WordTrace tailWord_7814276 prefixEnd_7814276 1337493184964391280970935 := by
  unfold tailWord_7814276
  simp only [CollatzResearch.WordTrace]
  refine ⟨142505030119110049467599341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190006706825480065956799121 142505030119110049467599341)
  ·
    refine ⟨53439386294666268550349753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 142505030119110049467599341 53439386294666268550349753)
    ·
      refine ⟨40079539720999701412762315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53439386294666268550349753 40079539720999701412762315)
      ·
        refine ⟨60119309581499552119143473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40079539720999701412762315 60119309581499552119143473)
        ·
          refine ⟨45089482186124664089357605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60119309581499552119143473 45089482186124664089357605)
          ·
            refine ⟨8454277909898374516754551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45089482186124664089357605 8454277909898374516754551)
            ·
              refine ⟨12681416864847561775131827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8454277909898374516754551 12681416864847561775131827)
              ·
                refine ⟨19022125297271342662697741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12681416864847561775131827 19022125297271342662697741)
                ·
                  refine ⟨7133296986476753498511653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19022125297271342662697741 7133296986476753498511653)
                  ·
                    refine ⟨1337493184964391280970935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7133296986476753498511653 1337493184964391280970935)
                    ·
                      rfl

theorem cell23_7814276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 4, 1, 1, 3, 4].length) (baseStart_7814276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7814276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7814276 prefixEnd_7814276 := by exact prefixLift 7814276
  have htrace : WordTrace (prefixWord ++ tailWord_7814276) baseStart_7814276 baseEnd_7814276 := by
    simpa [prefixWord, tailWord_7814276, baseEnd_7814276] using wordTrace_append hprefix tailTrace_7814276
  have hstable : (prefixWord ++ tailWord_7814276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7814276).length < 2 ^ (prefixWord ++ tailWord_7814276).sum := by decide
  have hdescent : baseEnd_7814276 < baseStart_7814276 := by decide
  rcases family_descends (prefixWord ++ tailWord_7814276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7814359 : List Nat := [1, 1, 3, 2, 1, 2, 4, 1, 3, 2, 3]
def baseStart_7814359 : Nat := 118140960795 + 7814359 * 2 ^ 59
def prefixEnd_7814359 : Nat := 4983230072969 + 3 ^ 40 * 7814359 * 2
def baseEnd_7814359 : Nat := 4012522173787497018174923

theorem tailTrace_7814359 : CollatzResearch.WordTrace tailWord_7814359 prefixEnd_7814359 4012522173787497018174923 := by
  unfold tailWord_7814359
  simp only [CollatzResearch.WordTrace]
  refine ⟨285013087496919404110470131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190008724997946269406980087 285013087496919404110470131)
  ·
    refine ⟨427519631245379106165705197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285013087496919404110470131 427519631245379106165705197)
    ·
      refine ⟨160319861717017164812139449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 427519631245379106165705197 160319861717017164812139449)
      ·
        refine ⟨120239896287762873609104587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 160319861717017164812139449 120239896287762873609104587)
        ·
          refine ⟨180359844431644310413656881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120239896287762873609104587 180359844431644310413656881)
          ·
            refine ⟨135269883323733232810242661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 180359844431644310413656881 135269883323733232810242661)
            ·
              refine ⟨25363103123199981151920499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 135269883323733232810242661 25363103123199981151920499)
              ·
                refine ⟨38044654684799971727880749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25363103123199981151920499 38044654684799971727880749)
                ·
                  refine ⟨14266745506799989397955281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38044654684799971727880749 14266745506799989397955281)
                  ·
                    refine ⟨10700059130099992048466461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14266745506799989397955281 10700059130099992048466461)
                    ·
                      refine ⟨4012522173787497018174923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10700059130099992048466461 4012522173787497018174923)
                      ·
                        rfl

theorem cell23_7814359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 4, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 4, 1, 3, 2, 3].length) (baseStart_7814359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7814359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7814359 prefixEnd_7814359 := by exact prefixLift 7814359
  have htrace : WordTrace (prefixWord ++ tailWord_7814359) baseStart_7814359 baseEnd_7814359 := by
    simpa [prefixWord, tailWord_7814359, baseEnd_7814359] using wordTrace_append hprefix tailTrace_7814359
  have hstable : (prefixWord ++ tailWord_7814359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7814359).length < 2 ^ (prefixWord ++ tailWord_7814359).sum := by decide
  have hdescent : baseEnd_7814359 < baseStart_7814359 := by decide
  rcases family_descends (prefixWord ++ tailWord_7814359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7814360 : List Nat := [2, 1, 2, 2, 6, 1, 1, 1, 2, 3, 2]
def baseStart_7814360 : Nat := 118140960795 + 7814360 * 2 ^ 59
def prefixEnd_7814360 : Nat := 4983230072969 + 3 ^ 40 * 7814360 * 2
def baseEnd_7814360 : Nat := 4012522687268151514262419

theorem tailTrace_7814360 : CollatzResearch.WordTrace tailWord_7814360 prefixEnd_7814360 4012522687268151514262419 := by
  unfold tailWord_7814360
  simp only [CollatzResearch.WordTrace]
  refine ⟨142506561984957890640628267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190008749313277187520837689 142506561984957890640628267)
  ·
    refine ⟨213759842977436835960942401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142506561984957890640628267 213759842977436835960942401)
    ·
      refine ⟨160319882233077626970706801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 213759842977436835960942401 160319882233077626970706801)
      ·
        refine ⟨120239911674808220228030101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 160319882233077626970706801 120239911674808220228030101)
        ·
          refine ⟨5636245859756635323188911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 120239911674808220228030101 5636245859756635323188911)
          ·
            refine ⟨8454368789634952984783367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5636245859756635323188911 8454368789634952984783367)
            ·
              refine ⟨12681553184452429477175051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8454368789634952984783367 12681553184452429477175051)
              ·
                refine ⟨19022329776678644215762577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12681553184452429477175051 19022329776678644215762577)
                ·
                  refine ⟨14266747332508983161821933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19022329776678644215762577 14266747332508983161821933)
                  ·
                    refine ⟨5350030249690868685683225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14266747332508983161821933 5350030249690868685683225)
                    ·
                      refine ⟨4012522687268151514262419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5350030249690868685683225 4012522687268151514262419)
                      ·
                        rfl

theorem cell23_7814360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 6, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 6, 1, 1, 1, 2, 3, 2].length) (baseStart_7814360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7814360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7814360 prefixEnd_7814360 := by exact prefixLift 7814360
  have htrace : WordTrace (prefixWord ++ tailWord_7814360) baseStart_7814360 baseEnd_7814360 := by
    simpa [prefixWord, tailWord_7814360, baseEnd_7814360] using wordTrace_append hprefix tailTrace_7814360
  have hstable : (prefixWord ++ tailWord_7814360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7814360).length < 2 ^ (prefixWord ++ tailWord_7814360).sum := by decide
  have hdescent : baseEnd_7814360 < baseStart_7814360 := by decide
  rcases family_descends (prefixWord ++ tailWord_7814360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7814369 : List Nat := [1, 2, 3, 1, 3, 2, 2, 2, 1, 2, 4]
def baseStart_7814369 : Nat := 118140960795 + 7814369 * 2 ^ 59
def prefixEnd_7814369 : Nat := 4983230072969 + 3 ^ 40 * 7814369 * 2
def baseEnd_7814369 : Nat := 4012527308594041979049877

theorem tailTrace_7814369 : CollatzResearch.WordTrace tailWord_7814369 prefixEnd_7814369 4012527308594041979049877 := by
  unfold tailWord_7814369
  simp only [CollatzResearch.WordTrace]
  refine ⟨285013452226883175818334161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190008968151255450545556107 285013452226883175818334161)
  ·
    refine ⟨213760089170162381863750621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 285013452226883175818334161 213760089170162381863750621)
    ·
      refine ⟨80160033438810893198906483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 213760089170162381863750621 80160033438810893198906483)
      ·
        refine ⟨120240050158216339798359725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80160033438810893198906483 120240050158216339798359725)
        ·
          refine ⟨45090018809331127424384897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 120240050158216339798359725 45090018809331127424384897)
          ·
            refine ⟨33817514106998345568288673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45090018809331127424384897 33817514106998345568288673)
            ·
              refine ⟨25363135580248759176216505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33817514106998345568288673 25363135580248759176216505)
              ·
                refine ⟨19022351685186569382162379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25363135580248759176216505 19022351685186569382162379)
                ·
                  refine ⟨28533527527779854073243569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19022351685186569382162379 28533527527779854073243569)
                  ·
                    refine ⟨21400145645834890554932677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28533527527779854073243569 21400145645834890554932677)
                    ·
                      refine ⟨4012527308594041979049877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21400145645834890554932677 4012527308594041979049877)
                      ·
                        rfl

theorem cell23_7814369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 2, 2, 1, 2, 4].length) (baseStart_7814369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7814369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7814369 prefixEnd_7814369 := by exact prefixLift 7814369
  have htrace : WordTrace (prefixWord ++ tailWord_7814369) baseStart_7814369 baseEnd_7814369 := by
    simpa [prefixWord, tailWord_7814369, baseEnd_7814369] using wordTrace_append hprefix tailTrace_7814369
  have hstable : (prefixWord ++ tailWord_7814369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7814369).length < 2 ^ (prefixWord ++ tailWord_7814369).sum := by decide
  have hdescent : baseEnd_7814369 < baseStart_7814369 := by decide
  rcases family_descends (prefixWord ++ tailWord_7814369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7814376 : List Nat := [2, 1, 4, 1, 2, 1, 3, 3, 1, 2, 3]
def baseStart_7814376 : Nat := 118140960795 + 7814376 * 2 ^ 59
def prefixEnd_7814376 : Nat := 4983230072969 + 3 ^ 40 * 7814376 * 2
def baseEnd_7814376 : Nat := 4012530902958623451662345

theorem tailTrace_7814376 : CollatzResearch.WordTrace tailWord_7814376 prefixEnd_7814376 4012530902958623451662345 := by
  unfold tailWord_7814376
  simp only [CollatzResearch.WordTrace]
  refine ⟨142506853768928908006919491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190009138358571877342559321 142506853768928908006919491)
  ·
    refine ⟨213760280653393362010379237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142506853768928908006919491 213760280653393362010379237)
    ·
      refine ⟨40080052622511255376946107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 213760280653393362010379237 40080052622511255376946107)
      ·
        refine ⟨60120078933766883065419161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40080052622511255376946107 60120078933766883065419161)
        ·
          refine ⟨45090059200325162299064371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60120078933766883065419161 45090059200325162299064371)
          ·
            refine ⟨67635088800487743448596557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45090059200325162299064371 67635088800487743448596557)
            ·
              refine ⟨25363158300182903793223709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67635088800487743448596557 25363158300182903793223709)
              ·
                refine ⟨9511184362568588922458891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25363158300182903793223709 9511184362568588922458891)
                ·
                  refine ⟨14266776543852883383688337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9511184362568588922458891 14266776543852883383688337)
                  ·
                    refine ⟨10700082407889662537766253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14266776543852883383688337 10700082407889662537766253)
                    ·
                      refine ⟨4012530902958623451662345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10700082407889662537766253 4012530902958623451662345)
                      ·
                        rfl

theorem cell23_7814376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 3, 3, 1, 2, 3].length) (baseStart_7814376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7814376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7814376 prefixEnd_7814376 := by exact prefixLift 7814376
  have htrace : WordTrace (prefixWord ++ tailWord_7814376) baseStart_7814376 baseEnd_7814376 := by
    simpa [prefixWord, tailWord_7814376, baseEnd_7814376] using wordTrace_append hprefix tailTrace_7814376
  have hstable : (prefixWord ++ tailWord_7814376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7814376).length < 2 ^ (prefixWord ++ tailWord_7814376).sum := by decide
  have hdescent : baseEnd_7814376 < baseStart_7814376 := by decide
  rcases family_descends (prefixWord ++ tailWord_7814376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7814383 : List Nat := [1, 1, 2, 1, 7, 2, 1, 2, 2, 4]
def baseStart_7814383 : Nat := 118140960795 + 7814383 * 2 ^ 59
def prefixEnd_7814383 : Nat := 4983230072969 + 3 ^ 40 * 7814383 * 2
def baseEnd_7814383 : Nat := 1337511499107734974758271

theorem tailTrace_7814383 : CollatzResearch.WordTrace tailWord_7814383 prefixEnd_7814383 1337511499107734974758271 := by
  unfold tailWord_7814383
  simp only [CollatzResearch.WordTrace]
  refine ⟨285013962848832456209343803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190009308565888304139562535 285013962848832456209343803)
  ·
    refine ⟨427520944273248684314015705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285013962848832456209343803 427520944273248684314015705)
    ·
      refine ⟨320640708204936513235511779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 427520944273248684314015705 320640708204936513235511779)
      ·
        refine ⟨480961062307404769853267669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 320640708204936513235511779 480961062307404769853267669)
        ·
          refine ⟨11272524897829799293435961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 480961062307404769853267669 11272524897829799293435961)
          ·
            refine ⟨8454393673372349470076971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11272524897829799293435961 8454393673372349470076971)
            ·
              refine ⟨12681590510058524205115457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8454393673372349470076971 12681590510058524205115457)
              ·
                refine ⟨9511192882543893153836593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12681590510058524205115457 9511192882543893153836593)
                ·
                  refine ⟨7133394661907919865377445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9511192882543893153836593 7133394661907919865377445)
                  ·
                    refine ⟨1337511499107734974758271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7133394661907919865377445 1337511499107734974758271)
                    ·
                      rfl

theorem cell23_7814383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 2, 1, 2, 2, 4].length) (baseStart_7814383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7814383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7814383 prefixEnd_7814383 := by exact prefixLift 7814383
  have htrace : WordTrace (prefixWord ++ tailWord_7814383) baseStart_7814383 baseEnd_7814383 := by
    simpa [prefixWord, tailWord_7814383, baseEnd_7814383] using wordTrace_append hprefix tailTrace_7814383
  have hstable : (prefixWord ++ tailWord_7814383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7814383).length < 2 ^ (prefixWord ++ tailWord_7814383).sum := by decide
  have hdescent : baseEnd_7814383 < baseStart_7814383 := by decide
  rcases family_descends (prefixWord ++ tailWord_7814383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7814457 : List Nat := [1, 2, 1, 6, 2, 2, 2, 1, 2, 1, 3]
def baseStart_7814457 : Nat := 118140960795 + 7814457 * 2 ^ 59
def prefixEnd_7814457 : Nat := 4983230072969 + 3 ^ 40 * 7814457 * 2
def baseEnd_7814457 : Nat := 4012572494891637634749473

theorem tailTrace_7814457 : CollatzResearch.WordTrace tailWord_7814457 prefixEnd_7814457 4012572494891637634749473 := by
  unfold tailWord_7814457
  simp only [CollatzResearch.WordTrace]
  refine ⟨285016661850564366847537625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190011107900376244565025083 285016661850564366847537625)
  ·
    refine ⟨213762496387923275135653219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 285016661850564366847537625 213762496387923275135653219)
    ·
      refine ⟨320643744581884912703479829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213762496387923275135653219 320643744581884912703479829)
      ·
        refine ⟨15030175527275855282975617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 320643744581884912703479829 15030175527275855282975617)
        ·
          refine ⟨11272631645456891462231713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15030175527275855282975617 11272631645456891462231713)
          ·
            refine ⟨8454473734092668596673785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11272631645456891462231713 8454473734092668596673785)
            ·
              refine ⟨6340855300569501447505339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8454473734092668596673785 6340855300569501447505339)
              ·
                refine ⟨9511282950854252171258009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6340855300569501447505339 9511282950854252171258009)
                ·
                  refine ⟨7133462213140689128443507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9511282950854252171258009 7133462213140689128443507)
                  ·
                    refine ⟨10700193319711033692665261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7133462213140689128443507 10700193319711033692665261)
                    ·
                      refine ⟨4012572494891637634749473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10700193319711033692665261 4012572494891637634749473)
                      ·
                        rfl

theorem cell23_7814457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 2, 2, 1, 2, 1, 3].length) (baseStart_7814457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7814457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7814457 prefixEnd_7814457 := by exact prefixLift 7814457
  have htrace : WordTrace (prefixWord ++ tailWord_7814457) baseStart_7814457 baseEnd_7814457 := by
    simpa [prefixWord, tailWord_7814457, baseEnd_7814457] using wordTrace_append hprefix tailTrace_7814457
  have hstable : (prefixWord ++ tailWord_7814457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7814457).length < 2 ^ (prefixWord ++ tailWord_7814457).sum := by decide
  have hdescent : baseEnd_7814457 < baseStart_7814457 := by decide
  rcases family_descends (prefixWord ++ tailWord_7814457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7814503 : List Nat := [1, 1, 5, 1, 4, 1, 1, 4, 5]
def baseStart_7814503 : Nat := 118140960795 + 7814503 * 2 ^ 59
def prefixEnd_7814503 : Nat := 4983230072969 + 3 ^ 40 * 7814503 * 2
def baseEnd_7814503 : Nat := 445844012777971606086029

theorem tailTrace_7814503 : CollatzResearch.WordTrace tailWord_7814503 prefixEnd_7814503 445844012777971606086029 := by
  unfold tailWord_7814503
  simp only [CollatzResearch.WordTrace]
  refine ⟨285018339608397716703712163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190012226405598477802474775 285018339608397716703712163)
  ·
    refine ⟨427527509412596575055568245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285018339608397716703712163 427527509412596575055568245)
    ·
      refine ⟨40080704007430928911459523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 427527509412596575055568245 40080704007430928911459523)
      ·
        refine ⟨60121056011146393367189285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40080704007430928911459523 60121056011146393367189285)
        ·
          refine ⟨11272698002089948756347991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 60121056011146393367189285 11272698002089948756347991)
          ·
            refine ⟨16909047003134923134521987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11272698002089948756347991 16909047003134923134521987)
            ·
              refine ⟨25363570504702384701782981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16909047003134923134521987 25363570504702384701782981)
              ·
                refine ⟨4755669469631697131584309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25363570504702384701782981 4755669469631697131584309)
                ·
                  refine ⟨445844012777971606086029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4755669469631697131584309 445844012777971606086029)
                  ·
                    rfl

theorem cell23_7814503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 1, 4, 5].length) (baseStart_7814503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7814503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7814503 prefixEnd_7814503 := by exact prefixLift 7814503
  have htrace : WordTrace (prefixWord ++ tailWord_7814503) baseStart_7814503 baseEnd_7814503 := by
    simpa [prefixWord, tailWord_7814503, baseEnd_7814503] using wordTrace_append hprefix tailTrace_7814503
  have hstable : (prefixWord ++ tailWord_7814503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7814503).length < 2 ^ (prefixWord ++ tailWord_7814503).sum := by decide
  have hdescent : baseEnd_7814503 < baseStart_7814503 := by decide
  rcases family_descends (prefixWord ++ tailWord_7814503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7814519 : List Nat := [1, 1, 3, 1, 1, 2, 4, 2, 1, 3, 4]
def baseStart_7814519 : Nat := 118140960795 + 7814519 * 2 ^ 59
def prefixEnd_7814519 : Nat := 4983230072969 + 3 ^ 40 * 7814519 * 2
def baseEnd_7814519 : Nat := 4012604330692216392174187

theorem tailTrace_7814519 : CollatzResearch.WordTrace tailWord_7814519 prefixEnd_7814519 4012604330692216392174187 := by
  unfold tailWord_7814519
  simp only [CollatzResearch.WordTrace]
  refine ⟨285018923176339751436294611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190012615450893167624196407 285018923176339751436294611)
  ·
    refine ⟨427528384764509627154441917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285018923176339751436294611 427528384764509627154441917)
    ·
      refine ⟨160323144286691110182915719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 427528384764509627154441917 160323144286691110182915719)
      ·
        refine ⟨240484716430036665274373579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160323144286691110182915719 240484716430036665274373579)
        ·
          refine ⟨360727074645054997911560369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 240484716430036665274373579 360727074645054997911560369)
          ·
            refine ⟨270545305983791248433670277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 360727074645054997911560369 270545305983791248433670277)
            ·
              refine ⟨50727244871960859081313177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 270545305983791248433670277 50727244871960859081313177)
              ·
                refine ⟨38045433653970644310984883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50727244871960859081313177 38045433653970644310984883)
                ·
                  refine ⟨57068150480955966466477325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38045433653970644310984883 57068150480955966466477325)
                  ·
                    refine ⟨21400556430358487424928997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 57068150480955966466477325 21400556430358487424928997)
                    ·
                      refine ⟨4012604330692216392174187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21400556430358487424928997 4012604330692216392174187)
                      ·
                        rfl

theorem cell23_7814519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 4, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 4, 2, 1, 3, 4].length) (baseStart_7814519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7814519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7814519 prefixEnd_7814519 := by exact prefixLift 7814519
  have htrace : WordTrace (prefixWord ++ tailWord_7814519) baseStart_7814519 baseEnd_7814519 := by
    simpa [prefixWord, tailWord_7814519, baseEnd_7814519] using wordTrace_append hprefix tailTrace_7814519
  have hstable : (prefixWord ++ tailWord_7814519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7814519).length < 2 ^ (prefixWord ++ tailWord_7814519).sum := by decide
  have hdescent : baseEnd_7814519 < baseStart_7814519 := by decide
  rcases family_descends (prefixWord ++ tailWord_7814519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7814536 : List Nat := [2, 1, 3, 3, 1, 3, 1, 1, 1, 3, 4]
def baseStart_7814536 : Nat := 118140960795 + 7814536 * 2 ^ 59
def prefixEnd_7814536 : Nat := 4983230072969 + 3 ^ 40 * 7814536 * 2
def baseEnd_7814536 : Nat := 4012613059863342825661609

theorem tailTrace_7814536 : CollatzResearch.WordTrace tailWord_7814536 prefixEnd_7814536 4012613059863342825661609 := by
  unfold tailWord_7814536
  simp only [CollatzResearch.WordTrace]
  refine ⟨142509771608639081669831731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190013028811518775559775641 142509771608639081669831731)
  ·
    refine ⟨213764657412958622504747597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142509771608639081669831731 213764657412958622504747597)
    ·
      refine ⟨80161746529859483439280349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 213764657412958622504747597 80161746529859483439280349)
      ·
        refine ⟨30060654948697306289730131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80161746529859483439280349 30060654948697306289730131)
        ·
          refine ⟨45090982423045959434595197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30060654948697306289730131 45090982423045959434595197)
          ·
            refine ⟨16909118408642234787973199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45090982423045959434595197 16909118408642234787973199)
            ·
              refine ⟨25363677612963352181959799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16909118408642234787973199 25363677612963352181959799)
              ·
                refine ⟨38045516419445028272939699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25363677612963352181959799 38045516419445028272939699)
                ·
                  refine ⟨57068274629167542409409549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38045516419445028272939699 57068274629167542409409549)
                  ·
                    refine ⟨21400602985937828403528581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 57068274629167542409409549 21400602985937828403528581)
                    ·
                      refine ⟨4012613059863342825661609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21400602985937828403528581 4012613059863342825661609)
                      ·
                        rfl

theorem cell23_7814536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 1, 1, 1, 3, 4].length) (baseStart_7814536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7814536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7814536 prefixEnd_7814536 := by exact prefixLift 7814536
  have htrace : WordTrace (prefixWord ++ tailWord_7814536) baseStart_7814536 baseEnd_7814536 := by
    simpa [prefixWord, tailWord_7814536, baseEnd_7814536] using wordTrace_append hprefix tailTrace_7814536
  have hstable : (prefixWord ++ tailWord_7814536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7814536).length < 2 ^ (prefixWord ++ tailWord_7814536).sum := by decide
  have hdescent : baseEnd_7814536 < baseStart_7814536 := by decide
  rcases family_descends (prefixWord ++ tailWord_7814536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7814549 : List Nat := [1, 3, 2, 1, 1, 2, 3, 1, 2, 1, 6]
def baseStart_7814549 : Nat := 118140960795 + 7814549 * 2 ^ 59
def prefixEnd_7814549 : Nat := 4983230072969 + 3 ^ 40 * 7814549 * 2
def baseEnd_7814549 : Nat := 4012619735111851274799049

theorem tailTrace_7814549 : CollatzResearch.WordTrace tailWord_7814549 prefixEnd_7814549 4012619735111851274799049 := by
  unfold tailWord_7814549
  simp only [CollatzResearch.WordTrace]
  refine ⟨285020017366231066559886701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190013344910820711039924467 285020017366231066559886701)
  ·
    refine ⟨106882506512336649959957513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 285020017366231066559886701 106882506512336649959957513)
    ·
      refine ⟨80161879884252487469968135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106882506512336649959957513 80161879884252487469968135)
      ·
        refine ⟨120242819826378731204952203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80161879884252487469968135 120242819826378731204952203)
        ·
          refine ⟨180364229739568096807428305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120242819826378731204952203 180364229739568096807428305)
          ·
            refine ⟨135273172304676072605571229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 180364229739568096807428305 135273172304676072605571229)
            ·
              refine ⟨50727439614253527227089211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 135273172304676072605571229 50727439614253527227089211)
              ·
                refine ⟨76091159421380290840633817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50727439614253527227089211 76091159421380290840633817)
                ·
                  refine ⟨57068369566035218130475363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 76091159421380290840633817 57068369566035218130475363)
                  ·
                    refine ⟨85602554349052827195713045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 57068369566035218130475363 85602554349052827195713045)
                    ·
                      refine ⟨4012619735111851274799049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 85602554349052827195713045 4012619735111851274799049)
                      ·
                        rfl

theorem cell23_7814549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 3, 1, 2, 1, 6].length) (baseStart_7814549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7814549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7814549 prefixEnd_7814549 := by exact prefixLift 7814549
  have htrace : WordTrace (prefixWord ++ tailWord_7814549) baseStart_7814549 baseEnd_7814549 := by
    simpa [prefixWord, tailWord_7814549, baseEnd_7814549] using wordTrace_append hprefix tailTrace_7814549
  have hstable : (prefixWord ++ tailWord_7814549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7814549).length < 2 ^ (prefixWord ++ tailWord_7814549).sum := by decide
  have hdescent : baseEnd_7814549 < baseStart_7814549 := by decide
  rcases family_descends (prefixWord ++ tailWord_7814549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7814563 : List Nat := [1, 1, 1, 4, 1, 3, 1, 6, 1, 4]
def baseStart_7814563 : Nat := 118140960795 + 7814563 * 2 ^ 59
def prefixEnd_7814563 : Nat := 4983230072969 + 3 ^ 40 * 7814563 * 2
def baseEnd_7814563 : Nat := 1337542307947004740007995

theorem tailTrace_7814563 : CollatzResearch.WordTrace tailWord_7814563 prefixEnd_7814563 1337542307947004740007995 := by
  unfold tailWord_7814563
  simp only [CollatzResearch.WordTrace]
  refine ⟨285020527988180346950896343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190013685325453564633930895 285020527988180346950896343)
  ·
    refine ⟨427530791982270520426344515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285020527988180346950896343 427530791982270520426344515)
    ·
      refine ⟨641296187973405780639516773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 427530791982270520426344515 641296187973405780639516773)
      ·
        refine ⟨120243035245013583869909395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 641296187973405780639516773 120243035245013583869909395)
        ·
          refine ⟨180364552867520375804864093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120243035245013583869909395 180364552867520375804864093)
          ·
            refine ⟨67636707325320140926824035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 180364552867520375804864093 67636707325320140926824035)
            ·
              refine ⟨101455060987980211390236053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67636707325320140926824035 101455060987980211390236053)
              ·
                refine ⟨4755705983811572408917315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 101455060987980211390236053 4755705983811572408917315)
                ·
                  refine ⟨7133558975717358613375973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4755705983811572408917315 7133558975717358613375973)
                  ·
                    refine ⟨1337542307947004740007995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7133558975717358613375973 1337542307947004740007995)
                    ·
                      rfl

theorem cell23_7814563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 6, 1, 4].length) (baseStart_7814563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7814563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7814563 prefixEnd_7814563 := by exact prefixLift 7814563
  have htrace : WordTrace (prefixWord ++ tailWord_7814563) baseStart_7814563 baseEnd_7814563 := by
    simpa [prefixWord, tailWord_7814563, baseEnd_7814563] using wordTrace_append hprefix tailTrace_7814563
  have hstable : (prefixWord ++ tailWord_7814563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7814563).length < 2 ^ (prefixWord ++ tailWord_7814563).sum := by decide
  have hdescent : baseEnd_7814563 < baseStart_7814563 := by decide
  rcases family_descends (prefixWord ++ tailWord_7814563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7814573 : List Nat := [1, 5, 2, 2, 1, 1, 1, 2, 1, 4, 3]
def baseStart_7814573 : Nat := 118140960795 + 7814573 * 2 ^ 59
def prefixEnd_7814573 : Nat := 4983230072969 + 3 ^ 40 * 7814573 * 2
def baseEnd_7814573 : Nat := 4012632058647559180898939

theorem tailTrace_7814573 : CollatzResearch.WordTrace tailWord_7814573 prefixEnd_7814573 4012632058647559180898939 := by
  unfold tailWord_7814573
  simp only [CollatzResearch.WordTrace]
  refine ⟨285020892718144118658760373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190013928478762745772506915 285020892718144118658760373)
  ·
    refine ⟨26720708692326011124258785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 285020892718144118658760373 26720708692326011124258785)
    ·
      refine ⟨20040531519244508343194089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26720708692326011124258785 20040531519244508343194089)
      ·
        refine ⟨15030398639433381257395567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20040531519244508343194089 15030398639433381257395567)
        ·
          refine ⟨22545597959150071886093351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15030398639433381257395567 22545597959150071886093351)
          ·
            refine ⟨33818396938725107829140027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22545597959150071886093351 33818396938725107829140027)
            ·
              refine ⟨50727595408087661743710041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33818396938725107829140027 50727595408087661743710041)
              ·
                refine ⟨38045696556065746307782531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50727595408087661743710041 38045696556065746307782531)
                ·
                  refine ⟨57068544834098619461673797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38045696556065746307782531 57068544834098619461673797)
                  ·
                    refine ⟨10700352156393491149063837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 57068544834098619461673797 10700352156393491149063837)
                    ·
                      refine ⟨4012632058647559180898939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10700352156393491149063837 4012632058647559180898939)
                      ·
                        rfl

theorem cell23_7814573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 1, 2, 1, 4, 3].length) (baseStart_7814573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7814573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7814573 prefixEnd_7814573 := by exact prefixLift 7814573
  have htrace : WordTrace (prefixWord ++ tailWord_7814573) baseStart_7814573 baseEnd_7814573 := by
    simpa [prefixWord, tailWord_7814573, baseEnd_7814573] using wordTrace_append hprefix tailTrace_7814573
  have hstable : (prefixWord ++ tailWord_7814573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7814573).length < 2 ^ (prefixWord ++ tailWord_7814573).sum := by decide
  have hdescent : baseEnd_7814573 < baseStart_7814573 := by decide
  rcases family_descends (prefixWord ++ tailWord_7814573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7814614 : List Nat := [5, 2, 1, 1, 1, 3, 3, 2, 1, 4]
def baseStart_7814614 : Nat := 118140960795 + 7814614 * 2 ^ 59
def prefixEnd_7814614 : Nat := 4983230072969 + 3 ^ 40 * 7814614 * 2
def baseEnd_7814614 : Nat := 1337551037118131173495417

theorem tailTrace_7814614 : CollatzResearch.WordTrace tailWord_7814614 prefixEnd_7814614 1337551037118131173495417 := by
  unfold tailWord_7814614
  simp only [CollatzResearch.WordTrace]
  refine ⟨17813899256937223916312681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 190014925407330388440668597 17813899256937223916312681)
  ·
    refine ⟨13360424442702917937234511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17813899256937223916312681 13360424442702917937234511)
    ·
      refine ⟨20040636664054376905851767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13360424442702917937234511 20040636664054376905851767)
      ·
        refine ⟨30060954996081565358777651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20040636664054376905851767 30060954996081565358777651)
        ·
          refine ⟨45091432494122348038166477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30060954996081565358777651 45091432494122348038166477)
          ·
            refine ⟨16909287185295880514312429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45091432494122348038166477 16909287185295880514312429)
            ·
              refine ⟨6340982694485955192867161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16909287185295880514312429 6340982694485955192867161)
              ·
                refine ⟨4755737020864466394650371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6340982694485955192867161 4755737020864466394650371)
                ·
                  refine ⟨7133605531296699591975557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4755737020864466394650371 7133605531296699591975557)
                  ·
                    refine ⟨1337551037118131173495417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7133605531296699591975557 1337551037118131173495417)
                    ·
                      rfl

theorem cell23_7814614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 3, 2, 1, 4].length) (baseStart_7814614 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7814614 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7814614 prefixEnd_7814614 := by exact prefixLift 7814614
  have htrace : WordTrace (prefixWord ++ tailWord_7814614) baseStart_7814614 baseEnd_7814614 := by
    simpa [prefixWord, tailWord_7814614, baseEnd_7814614] using wordTrace_append hprefix tailTrace_7814614
  have hstable : (prefixWord ++ tailWord_7814614).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7814614).length < 2 ^ (prefixWord ++ tailWord_7814614).sum := by decide
  have hdescent : baseEnd_7814614 < baseStart_7814614 := by decide
  rcases family_descends (prefixWord ++ tailWord_7814614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7814636 : List Nat := [2, 2, 1, 1, 2, 1, 2, 2, 6, 4]
def baseStart_7814636 : Nat := 118140960795 + 7814636 * 2 ^ 59
def prefixEnd_7814636 : Nat := 4983230072969 + 3 ^ 40 * 7814636 * 2
def baseEnd_7814636 : Nat := 1337554802642930811470383

theorem tailTrace_7814636 : CollatzResearch.WordTrace tailWord_7814636 prefixEnd_7814636 1337554802642930811470383 := by
  unfold tailWord_7814636
  simp only [CollatzResearch.WordTrace]
  refine ⟨142511595258457940209151881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190015460344610586945535841 142511595258457940209151881)
  ·
    refine ⟨106883696443843455156863911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142511595258457940209151881 106883696443843455156863911)
    ·
      refine ⟨160325544665765182735295867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106883696443843455156863911 160325544665765182735295867)
      ·
        refine ⟨240488316998647774102943801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160325544665765182735295867 240488316998647774102943801)
        ·
          refine ⟨180366237748985830577207851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 240488316998647774102943801 180366237748985830577207851)
          ·
            refine ⟨270549356623478745865811777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 180366237748985830577207851 270549356623478745865811777)
            ·
              refine ⟨202912017467609059399358833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 270549356623478745865811777 202912017467609059399358833)
              ·
                refine ⟨152184013100706794549519125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 202912017467609059399358833 152184013100706794549519125)
                ·
                  refine ⟨7133625614095630994508709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 152184013100706794549519125 7133625614095630994508709)
                  ·
                    refine ⟨1337554802642930811470383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7133625614095630994508709 1337554802642930811470383)
                    ·
                      rfl

theorem cell23_7814636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 6, 4].length) (baseStart_7814636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7814636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7814636 prefixEnd_7814636 := by exact prefixLift 7814636
  have htrace : WordTrace (prefixWord ++ tailWord_7814636) baseStart_7814636 baseEnd_7814636 := by
    simpa [prefixWord, tailWord_7814636, baseEnd_7814636] using wordTrace_append hprefix tailTrace_7814636
  have hstable : (prefixWord ++ tailWord_7814636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7814636).length < 2 ^ (prefixWord ++ tailWord_7814636).sum := by decide
  have hdescent : baseEnd_7814636 < baseStart_7814636 := by decide
  rcases family_descends (prefixWord ++ tailWord_7814636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7814663 : List Nat := [1, 1, 4, 3, 2, 1, 3, 1, 1, 1, 5]
def baseStart_7814663 : Nat := 118140960795 + 7814663 * 2 ^ 59
def prefixEnd_7814663 : Nat := 4983230072969 + 3 ^ 40 * 7814663 * 2
def baseEnd_7814663 : Nat := 4012678271906463828773525

theorem tailTrace_7814663 : CollatzResearch.WordTrace tailWord_7814663 prefixEnd_7814663 4012678271906463828773525 := by
  unfold tailWord_7814663
  simp only [CollatzResearch.WordTrace]
  refine ⟨285024175287818064029536643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190016116858545376019691095 285024175287818064029536643)
  ·
    refine ⟨427536262931727096044304965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285024175287818064029536643 427536262931727096044304965)
    ·
      refine ⟨80163049299698830508307181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 427536262931727096044304965 80163049299698830508307181)
      ·
        refine ⟨30061143487387061440615193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80163049299698830508307181 30061143487387061440615193)
        ·
          refine ⟨22545857615540296080461395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30061143487387061440615193 22545857615540296080461395)
          ·
            refine ⟨33818786423310444120692093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22545857615540296080461395 33818786423310444120692093)
            ·
              refine ⟨12682044908741416545259535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33818786423310444120692093 12682044908741416545259535)
              ·
                refine ⟨19023067363112124817889303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12682044908741416545259535 19023067363112124817889303)
                ·
                  refine ⟨28534601044668187226833955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19023067363112124817889303 28534601044668187226833955)
                  ·
                    refine ⟨42801901567002280840250933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28534601044668187226833955 42801901567002280840250933)
                    ·
                      refine ⟨4012678271906463828773525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42801901567002280840250933 4012678271906463828773525)
                      ·
                        rfl

theorem cell23_7814663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 3, 1, 1, 1, 5].length) (baseStart_7814663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7814663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7814663 prefixEnd_7814663 := by exact prefixLift 7814663
  have htrace : WordTrace (prefixWord ++ tailWord_7814663) baseStart_7814663 baseEnd_7814663 := by
    simpa [prefixWord, tailWord_7814663, baseEnd_7814663] using wordTrace_append hprefix tailTrace_7814663
  have hstable : (prefixWord ++ tailWord_7814663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7814663).length < 2 ^ (prefixWord ++ tailWord_7814663).sum := by decide
  have hdescent : baseEnd_7814663 < baseStart_7814663 := by decide
  rcases family_descends (prefixWord ++ tailWord_7814663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7814693 : List Nat := [1, 3, 1, 2, 2, 1, 1, 2, 6, 1, 3]
def baseStart_7814693 : Nat := 118140960795 + 7814693 * 2 ^ 59
def prefixEnd_7814693 : Nat := 4983230072969 + 3 ^ 40 * 7814693 * 2
def baseEnd_7814693 : Nat := 4012693676326098711398387

theorem tailTrace_7814693 : CollatzResearch.WordTrace tailWord_7814693 prefixEnd_7814693 4012693676326098711398387 := by
  unfold tailWord_7814693
  simp only [CollatzResearch.WordTrace]
  refine ⟨285025269477709379153128733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190016846318472919435419155 285025269477709379153128733)
  ·
    refine ⟨106884476054141017182423275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 285025269477709379153128733 106884476054141017182423275)
    ·
      refine ⟨160326714081211525773634913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106884476054141017182423275 160326714081211525773634913)
      ·
        refine ⟨120245035560908644330226185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 160326714081211525773634913 120245035560908644330226185)
        ·
          refine ⟨90183776670681483247669639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120245035560908644330226185 90183776670681483247669639)
          ·
            refine ⟨135275665006022224871504459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90183776670681483247669639 135275665006022224871504459)
            ·
              refine ⟨202913497509033337307256689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 135275665006022224871504459 202913497509033337307256689)
              ·
                refine ⟨152185123131775002980442517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 202913497509033337307256689 152185123131775002980442517)
                ·
                  refine ⟨7133677646801953264708243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 152185123131775002980442517 7133677646801953264708243)
                  ·
                    refine ⟨10700516470202929897062365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7133677646801953264708243 10700516470202929897062365)
                    ·
                      refine ⟨4012693676326098711398387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10700516470202929897062365 4012693676326098711398387)
                      ·
                        rfl

theorem cell23_7814693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 2, 6, 1, 3].length) (baseStart_7814693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7814693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7814693 prefixEnd_7814693 := by exact prefixLift 7814693
  have htrace : WordTrace (prefixWord ++ tailWord_7814693) baseStart_7814693 baseEnd_7814693 := by
    simpa [prefixWord, tailWord_7814693, baseEnd_7814693] using wordTrace_append hprefix tailTrace_7814693
  have hstable : (prefixWord ++ tailWord_7814693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7814693).length < 2 ^ (prefixWord ++ tailWord_7814693).sum := by decide
  have hdescent : baseEnd_7814693 < baseStart_7814693 := by decide
  rcases family_descends (prefixWord ++ tailWord_7814693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7814706 : List Nat := [3, 2, 1, 1, 2, 1, 1, 3, 2, 2, 5]
def baseStart_7814706 : Nat := 118140960795 + 7814706 * 2 ^ 59
def prefixEnd_7814706 : Nat := 4983230072969 + 3 ^ 40 * 7814706 * 2
def baseEnd_7814706 : Nat := 4012700351574607160535827

theorem tailTrace_7814706 : CollatzResearch.WordTrace tailWord_7814706 prefixEnd_7814706 4012700351574607160535827 := by
  unfold tailWord_7814706
  simp only [CollatzResearch.WordTrace]
  refine ⟨71256435906665570593337993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 190017162417774854915567981 71256435906665570593337993)
  ·
    refine ⟨53442326929999177945003495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71256435906665570593337993 53442326929999177945003495)
    ·
      refine ⟨80163490394998766917505243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53442326929999177945003495 80163490394998766917505243)
      ·
        refine ⟨120245235592498150376257865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80163490394998766917505243 120245235592498150376257865)
        ·
          refine ⟨90183926694373612782193399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120245235592498150376257865 90183926694373612782193399)
          ·
            refine ⟨135275890041560419173290099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90183926694373612782193399 135275890041560419173290099)
            ·
              refine ⟨202913835062340628759935149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 135275890041560419173290099 202913835062340628759935149)
              ·
                refine ⟨76092688148377735784975681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 202913835062340628759935149 76092688148377735784975681)
                ·
                  refine ⟨57069516111283301838731761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 76092688148377735784975681 57069516111283301838731761)
                  ·
                    refine ⟨42802137083462476379048821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 57069516111283301838731761 42802137083462476379048821)
                    ·
                      refine ⟨4012700351574607160535827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42802137083462476379048821 4012700351574607160535827)
                      ·
                        rfl

theorem cell23_7814706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 3, 2, 2, 5].length) (baseStart_7814706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7814706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7814706 prefixEnd_7814706 := by exact prefixLift 7814706
  have htrace : WordTrace (prefixWord ++ tailWord_7814706) baseStart_7814706 baseEnd_7814706 := by
    simpa [prefixWord, tailWord_7814706, baseEnd_7814706] using wordTrace_append hprefix tailTrace_7814706
  have hstable : (prefixWord ++ tailWord_7814706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7814706).length < 2 ^ (prefixWord ++ tailWord_7814706).sum := by decide
  have hdescent : baseEnd_7814706 < baseStart_7814706 := by decide
  rcases family_descends (prefixWord ++ tailWord_7814706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7814820 : List Nat := [2, 3, 1, 2, 2, 3, 2, 1, 2, 5]
def baseStart_7814820 : Nat := 118140960795 + 7814820 * 2 ^ 59
def prefixEnd_7814820 : Nat := 4983230072969 + 3 ^ 40 * 7814820 * 2
def baseEnd_7814820 : Nat := 1337586296123073238170101

theorem tailTrace_7814820 : CollatzResearch.WordTrace tailWord_7814820 prefixEnd_7814820 1337586296123073238170101 := by
  unfold tailWord_7814820
  simp only [CollatzResearch.WordTrace]
  refine ⟨142514950774124639921500957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190019934365499519895334609 142514950774124639921500957)
  ·
    refine ⟨53443106540296739970562859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 142514950774124639921500957 53443106540296739970562859)
    ·
      refine ⟨80164659810445109955844289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53443106540296739970562859 80164659810445109955844289)
      ·
        refine ⟨60123494857833832466883217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80164659810445109955844289 60123494857833832466883217)
        ·
          refine ⟨45092621143375374350162413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60123494857833832466883217 45092621143375374350162413)
          ·
            refine ⟨16909732928765765381310905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45092621143375374350162413 16909732928765765381310905)
            ·
              refine ⟨12682299696574324035983179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16909732928765765381310905 12682299696574324035983179)
              ·
                refine ⟨19023449544861486053974769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12682299696574324035983179 19023449544861486053974769)
                ·
                  refine ⟨14267587158646114540481077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19023449544861486053974769 14267587158646114540481077)
                  ·
                    refine ⟨1337586296123073238170101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14267587158646114540481077 1337586296123073238170101)
                    ·
                      rfl

theorem cell23_7814820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 2, 1, 2, 5].length) (baseStart_7814820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7814820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7814820 prefixEnd_7814820 := by exact prefixLift 7814820
  have htrace : WordTrace (prefixWord ++ tailWord_7814820) baseStart_7814820 baseEnd_7814820 := by
    simpa [prefixWord, tailWord_7814820, baseEnd_7814820] using wordTrace_append hprefix tailTrace_7814820
  have hstable : (prefixWord ++ tailWord_7814820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7814820).length < 2 ^ (prefixWord ++ tailWord_7814820).sum := by decide
  have hdescent : baseEnd_7814820 < baseStart_7814820 := by decide
  rcases family_descends (prefixWord ++ tailWord_7814820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7814940 : List Nat := [2, 2, 3, 1, 1, 2, 1, 1, 6, 4]
def baseStart_7814940 : Nat := 118140960795 + 7814940 * 2 ^ 59
def prefixEnd_7814940 : Nat := 4983230072969 + 3 ^ 40 * 7814940 * 2
def baseEnd_7814940 : Nat := 1337606835349253081669917

theorem tailTrace_7814940 : CollatzResearch.WordTrace tailWord_7814940 prefixEnd_7814940 1337606835349253081669917 := by
  unfold tailWord_7814940
  simp only [CollatzResearch.WordTrace]
  refine ⟨142517139153907270168685137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190022852205209693558246849 142517139153907270168685137)
  ·
    refine ⟨106887854365430452626513853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142517139153907270168685137 106887854365430452626513853)
    ·
      refine ⟨40082945387036419734942695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 106887854365430452626513853 40082945387036419734942695)
      ·
        refine ⟨60124418080554629602414043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40082945387036419734942695 60124418080554629602414043)
        ·
          refine ⟨90186627120831944403621065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60124418080554629602414043 90186627120831944403621065)
          ·
            refine ⟨67639970340623958302715799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90186627120831944403621065 67639970340623958302715799)
            ·
              refine ⟨101459955510935937454073699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67639970340623958302715799 101459955510935937454073699)
              ·
                refine ⟨152189933266403906181110549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 101459955510935937454073699 152189933266403906181110549)
                ·
                  refine ⟨7133903121862683102239557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 152189933266403906181110549 7133903121862683102239557)
                  ·
                    refine ⟨1337606835349253081669917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7133903121862683102239557 1337606835349253081669917)
                    ·
                      rfl

theorem cell23_7814940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 1, 6, 4].length) (baseStart_7814940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7814940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7814940 prefixEnd_7814940 := by exact prefixLift 7814940
  have htrace : WordTrace (prefixWord ++ tailWord_7814940) baseStart_7814940 baseEnd_7814940 := by
    simpa [prefixWord, tailWord_7814940, baseEnd_7814940] using wordTrace_append hprefix tailTrace_7814940
  have hstable : (prefixWord ++ tailWord_7814940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7814940).length < 2 ^ (prefixWord ++ tailWord_7814940).sum := by decide
  have hdescent : baseEnd_7814940 < baseStart_7814940 := by decide
  rcases family_descends (prefixWord ++ tailWord_7814940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7814947 : List Nat := [1, 1, 1, 4, 2, 1, 2, 2, 5, 2, 2]
def baseStart_7814947 : Nat := 118140960795 + 7814947 * 2 ^ 59
def prefixEnd_7814947 : Nat := 4983230072969 + 3 ^ 40 * 7814947 * 2
def baseEnd_7814947 : Nat := 4012824100412340717622219

theorem tailTrace_7814947 : CollatzResearch.WordTrace tailWord_7814947 prefixEnd_7814947 4012824100412340717622219 := by
  unfold tailWord_7814947
  simp only [CollatzResearch.WordTrace]
  refine ⟨285034533618789180532875095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190023022412526120355250063 285034533618789180532875095)
  ·
    refine ⟨427551800428183770799312643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285034533618789180532875095 427551800428183770799312643)
    ·
      refine ⟨641327700642275656198968965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 427551800428183770799312643 641327700642275656198968965)
      ·
        refine ⟨120248943870426685537306681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 641327700642275656198968965 120248943870426685537306681)
        ·
          refine ⟨90186707902820014152980011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120248943870426685537306681 90186707902820014152980011)
          ·
            refine ⟨135280061854230021229470017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90186707902820014152980011 135280061854230021229470017)
            ·
              refine ⟨101460046390672515922102513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 135280061854230021229470017 101460046390672515922102513)
              ·
                refine ⟨76095034793004386941576885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 101460046390672515922102513 76095034793004386941576885)
                ·
                  refine ⟨7133909511844161275772833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 76095034793004386941576885 7133909511844161275772833)
                  ·
                    refine ⟨5350432133883120956829625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7133909511844161275772833 5350432133883120956829625)
                    ·
                      refine ⟨4012824100412340717622219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5350432133883120956829625 4012824100412340717622219)
                      ·
                        rfl

theorem cell23_7814947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 2, 5, 2, 2].length) (baseStart_7814947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7814947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7814947 prefixEnd_7814947 := by exact prefixLift 7814947
  have htrace : WordTrace (prefixWord ++ tailWord_7814947) baseStart_7814947 baseEnd_7814947 := by
    simpa [prefixWord, tailWord_7814947, baseEnd_7814947] using wordTrace_append hprefix tailTrace_7814947
  have hstable : (prefixWord ++ tailWord_7814947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7814947).length < 2 ^ (prefixWord ++ tailWord_7814947).sum := by decide
  have hdescent : baseEnd_7814947 < baseStart_7814947 := by decide
  rcases family_descends (prefixWord ++ tailWord_7814947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7814958 : List Nat := [4, 1, 3, 2, 3, 1, 1, 1, 3, 1, 3]
def baseStart_7814958 : Nat := 118140960795 + 7814958 * 2 ^ 59
def prefixEnd_7814958 : Nat := 4983230072969 + 3 ^ 40 * 7814958 * 2
def baseEnd_7814958 : Nat := 4012829748699540174584669

theorem tailTrace_7814958 : CollatzResearch.WordTrace tailWord_7814958 prefixEnd_7814958 4012829748699540174584669 := by
  unfold tailWord_7814958
  simp only [CollatzResearch.WordTrace]
  refine ⟨35629366852718666176440691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 190023289881166219607683685 35629366852718666176440691)
  ·
    refine ⟨53444050279077999264661037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35629366852718666176440691 53444050279077999264661037)
    ·
      refine ⟨20041518854654249724247889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53444050279077999264661037 20041518854654249724247889)
      ·
        refine ⟨15031139140990687293185917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20041518854654249724247889 15031139140990687293185917)
        ·
          refine ⟨5636677177871507734944719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15031139140990687293185917 5636677177871507734944719)
          ·
            refine ⟨8455015766807261602417079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5636677177871507734944719 8455015766807261602417079)
            ·
              refine ⟨12682523650210892403625619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8455015766807261602417079 12682523650210892403625619)
              ·
                refine ⟨19023785475316338605438429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12682523650210892403625619 19023785475316338605438429)
                ·
                  refine ⟨7133919553243626977039411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19023785475316338605438429 7133919553243626977039411)
                  ·
                    refine ⟨10700879329865440465559117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7133919553243626977039411 10700879329865440465559117)
                    ·
                      refine ⟨4012829748699540174584669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10700879329865440465559117 4012829748699540174584669)
                      ·
                        rfl

theorem cell23_7814958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 3, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 3, 1, 1, 1, 3, 1, 3].length) (baseStart_7814958 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7814958 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7814958 prefixEnd_7814958 := by exact prefixLift 7814958
  have htrace : WordTrace (prefixWord ++ tailWord_7814958) baseStart_7814958 baseEnd_7814958 := by
    simpa [prefixWord, tailWord_7814958, baseEnd_7814958] using wordTrace_append hprefix tailTrace_7814958
  have hstable : (prefixWord ++ tailWord_7814958).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7814958).length < 2 ^ (prefixWord ++ tailWord_7814958).sum := by decide
  have hdescent : baseEnd_7814958 < baseStart_7814958 := by decide
  rcases family_descends (prefixWord ++ tailWord_7814958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7814970 : List Nat := [3, 1, 1, 1, 5, 2, 2, 8]
def baseStart_7814970 : Nat := 118140960795 + 7814970 * 2 ^ 59
def prefixEnd_7814970 : Nat := 4983230072969 + 3 ^ 40 * 7814970 * 2
def baseEnd_7814970 : Nat := 148623552239533115838319

theorem tailTrace_7814970 : CollatzResearch.WordTrace tailWord_7814970 prefixEnd_7814970 148623552239533115838319 := by
  unfold tailWord_7814970
  simp only [CollatzResearch.WordTrace]
  refine ⟨71258843124426463865240591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 190023581665137236973974909 71258843124426463865240591)
  ·
    refine ⟨106888264686639695797860887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71258843124426463865240591 106888264686639695797860887)
    ·
      refine ⟨160332397029959543696791331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106888264686639695797860887 160332397029959543696791331)
      ·
        refine ⟨240498595544939315545186997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160332397029959543696791331 240498595544939315545186997)
        ·
          refine ⟨22546743332338060832361281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 240498595544939315545186997 22546743332338060832361281)
          ·
            refine ⟨16910057499253545624270961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22546743332338060832361281 16910057499253545624270961)
            ·
              refine ⟨12682543124440159218203221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16910057499253545624270961 12682543124440159218203221)
              ·
                refine ⟨148623552239533115838319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12682543124440159218203221 148623552239533115838319)
                ·
                  rfl

theorem cell23_7814970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 2, 8].length) (baseStart_7814970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7814970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7814970 prefixEnd_7814970 := by exact prefixLift 7814970
  have htrace : WordTrace (prefixWord ++ tailWord_7814970) baseStart_7814970 baseEnd_7814970 := by
    simpa [prefixWord, tailWord_7814970, baseEnd_7814970] using wordTrace_append hprefix tailTrace_7814970
  have hstable : (prefixWord ++ tailWord_7814970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7814970).length < 2 ^ (prefixWord ++ tailWord_7814970).sum := by decide
  have hdescent : baseEnd_7814970 < baseStart_7814970 := by decide
  rcases family_descends (prefixWord ++ tailWord_7814970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7814974 : List Nat := [4, 2, 1, 2, 2, 2, 1, 3, 2, 4]
def baseStart_7814974 : Nat := 118140960795 + 7814974 * 2 ^ 59
def prefixEnd_7814974 : Nat := 4983230072969 + 3 ^ 40 * 7814974 * 2
def baseEnd_7814974 : Nat := 1337612654796670703994865

theorem tailTrace_7814974 : CollatzResearch.WordTrace tailWord_7814974 prefixEnd_7814974 1337612654796670703994865 := by
  unfold tailWord_7814974
  simp only [CollatzResearch.WordTrace]
  refine ⟨35629439798711420518013497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 190023678926460909429405317 35629439798711420518013497)
  ·
    refine ⟨26722079849033565388510123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35629439798711420518013497 26722079849033565388510123)
    ·
      refine ⟨40083119773550348082765185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26722079849033565388510123 40083119773550348082765185)
      ·
        refine ⟨30062339830162761062073889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40083119773550348082765185 30062339830162761062073889)
        ·
          refine ⟨22546754872622070796555417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30062339830162761062073889 22546754872622070796555417)
          ·
            refine ⟨16910066154466553097416563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22546754872622070796555417 16910066154466553097416563)
            ·
              refine ⟨25365099231699829646124845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16910066154466553097416563 25365099231699829646124845)
              ·
                refine ⟨9511912211887436117296817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25365099231699829646124845 9511912211887436117296817)
                ·
                  refine ⟨7133934158915577087972613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9511912211887436117296817 7133934158915577087972613)
                  ·
                    refine ⟨1337612654796670703994865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7133934158915577087972613 1337612654796670703994865)
                    ·
                      rfl

theorem cell23_7814974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 1, 3, 2, 4].length) (baseStart_7814974 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7814974 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7814974 prefixEnd_7814974 := by exact prefixLift 7814974
  have htrace : WordTrace (prefixWord ++ tailWord_7814974) baseStart_7814974 baseEnd_7814974 := by
    simpa [prefixWord, tailWord_7814974, baseEnd_7814974] using wordTrace_append hprefix tailTrace_7814974
  have hstable : (prefixWord ++ tailWord_7814974).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7814974).length < 2 ^ (prefixWord ++ tailWord_7814974).sum := by decide
  have hdescent : baseEnd_7814974 < baseStart_7814974 := by decide
  rcases family_descends (prefixWord ++ tailWord_7814974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7814984 : List Nat := [2, 1, 3, 1, 1, 6, 1, 2, 1, 2, 3]
def baseStart_7814984 : Nat := 118140960795 + 7814984 * 2 ^ 59
def prefixEnd_7814984 : Nat := 4983230072969 + 3 ^ 40 * 7814984 * 2
def baseEnd_7814984 : Nat := 4012843099196557072859549

theorem tailTrace_7814984 : CollatzResearch.WordTrace tailWord_7814984 prefixEnd_7814984 4012843099196557072859549 := by
  unfold tailWord_7814984
  simp only [CollatzResearch.WordTrace]
  refine ⟨142517941559827567925986003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190023922079770090567981337 142517941559827567925986003)
  ·
    refine ⟨213776912339741351888979005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142517941559827567925986003 213776912339741351888979005)
    ·
      refine ⟨80166342127403006958367127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 213776912339741351888979005 80166342127403006958367127)
      ·
        refine ⟨120249513191104510437550691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80166342127403006958367127 120249513191104510437550691)
        ·
          refine ⟨180374269786656765656326037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120249513191104510437550691 180374269786656765656326037)
          ·
            refine ⟨8455043896249535890140283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 180374269786656765656326037 8455043896249535890140283)
            ·
              refine ⟨12682565844374303835210425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8455043896249535890140283 12682565844374303835210425)
              ·
                refine ⟨9511924383280727876407819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12682565844374303835210425 9511924383280727876407819)
                ·
                  refine ⟨14267886574921091814611729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9511924383280727876407819 14267886574921091814611729)
                  ·
                    refine ⟨10700914931190818860958797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14267886574921091814611729 10700914931190818860958797)
                    ·
                      refine ⟨4012843099196557072859549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10700914931190818860958797 4012843099196557072859549)
                      ·
                        rfl

theorem cell23_7814984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 6, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 6, 1, 2, 1, 2, 3].length) (baseStart_7814984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7814984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7814984 prefixEnd_7814984 := by exact prefixLift 7814984
  have htrace : WordTrace (prefixWord ++ tailWord_7814984) baseStart_7814984 baseEnd_7814984 := by
    simpa [prefixWord, tailWord_7814984, baseEnd_7814984] using wordTrace_append hprefix tailTrace_7814984
  have hstable : (prefixWord ++ tailWord_7814984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7814984).length < 2 ^ (prefixWord ++ tailWord_7814984).sum := by decide
  have hdescent : baseEnd_7814984 < baseStart_7814984 := by decide
  rcases family_descends (prefixWord ++ tailWord_7814984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7814997 : List Nat := [1, 3, 2, 2, 2, 3, 1, 2, 1, 3, 3]
def baseStart_7814997 : Nat := 118140960795 + 7814997 * 2 ^ 59
def prefixEnd_7814997 : Nat := 4983230072969 + 3 ^ 40 * 7814997 * 2
def baseEnd_7814997 : Nat := 4012849774445065521996989

theorem tailTrace_7814997 : CollatzResearch.WordTrace tailWord_7814997 prefixEnd_7814997 4012849774445065521996989 := by
  unfold tailWord_7814997
  simp only [CollatzResearch.WordTrace]
  refine ⟨285036357268608039072195245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190024238179072026048130163 285036357268608039072195245)
  ·
    refine ⟨106888633975728014652073217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 285036357268608039072195245 106888633975728014652073217)
    ·
      refine ⟨80166475481796010989054913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106888633975728014652073217 80166475481796010989054913)
      ·
        refine ⟨60124856611347008241791185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80166475481796010989054913 60124856611347008241791185)
        ·
          refine ⟨45093642458510256181343389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60124856611347008241791185 45093642458510256181343389)
          ·
            refine ⟨16910115921941346068003771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45093642458510256181343389 16910115921941346068003771)
            ·
              refine ⟨25365173882912019102005657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16910115921941346068003771 25365173882912019102005657)
              ·
                refine ⟨19023880412184014326504243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25365173882912019102005657 19023880412184014326504243)
                ·
                  refine ⟨28535820618276021489756365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19023880412184014326504243 28535820618276021489756365)
                  ·
                    refine ⟨10700932731853508058658637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28535820618276021489756365 10700932731853508058658637)
                    ·
                      refine ⟨4012849774445065521996989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10700932731853508058658637 4012849774445065521996989)
                      ·
                        rfl

theorem cell23_7814997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 1, 2, 1, 3, 3].length) (baseStart_7814997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7814997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7814997 prefixEnd_7814997 := by exact prefixLift 7814997
  have htrace : WordTrace (prefixWord ++ tailWord_7814997) baseStart_7814997 baseEnd_7814997 := by
    simpa [prefixWord, tailWord_7814997, baseEnd_7814997] using wordTrace_append hprefix tailTrace_7814997
  have hstable : (prefixWord ++ tailWord_7814997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7814997).length < 2 ^ (prefixWord ++ tailWord_7814997).sum := by decide
  have hdescent : baseEnd_7814997 < baseStart_7814997 := by decide
  rcases family_descends (prefixWord ++ tailWord_7814997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7815020 : List Nat := [2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 4]
def baseStart_7815020 : Nat := 118140960795 + 7815020 * 2 ^ 59
def prefixEnd_7815020 : Nat := 4983230072969 + 3 ^ 40 * 7815020 * 2
def baseEnd_7815020 : Nat := 4012861584500118932009383

theorem tailTrace_7815020 : CollatzResearch.WordTrace tailWord_7815020 prefixEnd_7815020 4012861584500118932009383 := by
  unfold tailWord_7815020
  simp only [CollatzResearch.WordTrace]
  refine ⟨142518598073762357000141257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190024797431683142666855009 142518598073762357000141257)
  ·
    refine ⟨106888948555321767750105943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142518598073762357000141257 106888948555321767750105943)
    ·
      refine ⟨160333422832982651625158915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106888948555321767750105943 160333422832982651625158915)
      ·
        refine ⟨240500134249473977437738373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160333422832982651625158915 240500134249473977437738373)
        ·
          refine ⟨45093775171776370769575945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 240500134249473977437738373 45093775171776370769575945)
          ·
            refine ⟨33820331378832278077181959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45093775171776370769575945 33820331378832278077181959)
            ·
              refine ⟨50730497068248417115772939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33820331378832278077181959 50730497068248417115772939)
              ·
                refine ⟨76095745602372625673659409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50730497068248417115772939 76095745602372625673659409)
                ·
                  refine ⟨57071809201779469255244557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 76095745602372625673659409 57071809201779469255244557)
                  ·
                    refine ⟨21401928450667300970716709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 57071809201779469255244557 21401928450667300970716709)
                    ·
                      refine ⟨4012861584500118932009383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21401928450667300970716709 4012861584500118932009383)
                      ·
                        rfl

theorem cell23_7815020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 4].length) (baseStart_7815020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7815020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7815020 prefixEnd_7815020 := by exact prefixLift 7815020
  have htrace : WordTrace (prefixWord ++ tailWord_7815020) baseStart_7815020 baseEnd_7815020 := by
    simpa [prefixWord, tailWord_7815020, baseEnd_7815020] using wordTrace_append hprefix tailTrace_7815020
  have hstable : (prefixWord ++ tailWord_7815020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7815020).length < 2 ^ (prefixWord ++ tailWord_7815020).sum := by decide
  have hdescent : baseEnd_7815020 < baseStart_7815020 := by decide
  rcases family_descends (prefixWord ++ tailWord_7815020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7815040 : List Nat := [2, 1, 1, 2, 1, 2, 3, 2, 2, 4, 3]
def baseStart_7815040 : Nat := 118140960795 + 7815040 * 2 ^ 59
def prefixEnd_7815040 : Nat := 4983230072969 + 3 ^ 40 * 7815040 * 2
def baseEnd_7815040 : Nat := 4012871854113208853759291

theorem tailTrace_7815040 : CollatzResearch.WordTrace tailWord_7815040 prefixEnd_7815040 4012871854113208853759291 := by
  unfold tailWord_7815040
  simp only [CollatzResearch.WordTrace]
  refine ⟨142518962803726128708005287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190025283738301504944007049 142518962803726128708005287)
  ·
    refine ⟨213778444205589193062007931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142518962803726128708005287 213778444205589193062007931)
    ·
      refine ⟨320667666308383789593011897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213778444205589193062007931 320667666308383789593011897)
      ·
        refine ⟨240500749731287842194758923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 320667666308383789593011897 240500749731287842194758923)
        ·
          refine ⟨360751124596931763292138385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 240500749731287842194758923 360751124596931763292138385)
          ·
            refine ⟨270563343447698822469103789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 360751124596931763292138385 270563343447698822469103789)
            ·
              refine ⟨101461253792887058425913921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 270563343447698822469103789 101461253792887058425913921)
              ·
                refine ⟨76095940344665293819435441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 101461253792887058425913921 76095940344665293819435441)
                ·
                  refine ⟨57071955258498970364576581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 76095940344665293819435441 57071955258498970364576581)
                  ·
                    refine ⟨10700991610968556943358109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 57071955258498970364576581 10700991610968556943358109)
                    ·
                      refine ⟨4012871854113208853759291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10700991610968556943358109 4012871854113208853759291)
                      ·
                        rfl

theorem cell23_7815040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 2, 2, 4, 3].length) (baseStart_7815040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7815040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7815040 prefixEnd_7815040 := by exact prefixLift 7815040
  have htrace : WordTrace (prefixWord ++ tailWord_7815040) baseStart_7815040 baseEnd_7815040 := by
    simpa [prefixWord, tailWord_7815040, baseEnd_7815040] using wordTrace_append hprefix tailTrace_7815040
  have hstable : (prefixWord ++ tailWord_7815040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7815040).length < 2 ^ (prefixWord ++ tailWord_7815040).sum := by decide
  have hdescent : baseEnd_7815040 < baseStart_7815040 := by decide
  rcases family_descends (prefixWord ++ tailWord_7815040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7815058 : List Nat := [3, 2, 3, 2, 1, 1, 4, 1, 1, 3, 2]
def baseStart_7815058 : Nat := 118140960795 + 7815058 * 2 ^ 59
def prefixEnd_7815058 : Nat := 4983230072969 + 3 ^ 40 * 7815058 * 2
def baseEnd_7815058 : Nat := 4012881096764989783334209

theorem tailTrace_7815058 : CollatzResearch.WordTrace tailWord_7815058 prefixEnd_7815058 4012881096764989783334209 := by
  unfold tailWord_7815058
  simp only [CollatzResearch.WordTrace]
  refine ⟨71259645530346761622541457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 190025721414258030993443885 71259645530346761622541457)
  ·
    refine ⟨53444734147760071216906093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71259645530346761622541457 53444734147760071216906093)
    ·
      refine ⟨20041775305410026706339785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53444734147760071216906093 20041775305410026706339785)
      ·
        refine ⟨15031331479057520029754839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20041775305410026706339785 15031331479057520029754839)
        ·
          refine ⟨22546997218586280044632259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15031331479057520029754839 22546997218586280044632259)
          ·
            refine ⟨33820495827879420066948389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22546997218586280044632259 33820495827879420066948389)
            ·
              refine ⟨6341342967727391262552823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33820495827879420066948389 6341342967727391262552823)
              ·
                refine ⟨9512014451591086893829235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6341342967727391262552823 9512014451591086893829235)
                ·
                  refine ⟨14268021677386630340743853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9512014451591086893829235 14268021677386630340743853)
                  ·
                    refine ⟨5350508129019986377778945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14268021677386630340743853 5350508129019986377778945)
                    ·
                      refine ⟨4012881096764989783334209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5350508129019986377778945 4012881096764989783334209)
                      ·
                        rfl

theorem cell23_7815058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 4, 1, 1, 3, 2].length) (baseStart_7815058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7815058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7815058 prefixEnd_7815058 := by exact prefixLift 7815058
  have htrace : WordTrace (prefixWord ++ tailWord_7815058) baseStart_7815058 baseEnd_7815058 := by
    simpa [prefixWord, tailWord_7815058, baseEnd_7815058] using wordTrace_append hprefix tailTrace_7815058
  have hstable : (prefixWord ++ tailWord_7815058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7815058).length < 2 ^ (prefixWord ++ tailWord_7815058).sum := by decide
  have hdescent : baseEnd_7815058 < baseStart_7815058 := by decide
  rcases family_descends (prefixWord ++ tailWord_7815058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7815071 : List Nat := [1, 1, 2, 5, 3, 1, 1, 1, 4, 2, 2]
def baseStart_7815071 : Nat := 118140960795 + 7815071 * 2 ^ 59
def prefixEnd_7815071 : Nat := 4983230072969 + 3 ^ 40 * 7815071 * 2
def baseEnd_7815071 : Nat := 4012887772013498232471649

theorem tailTrace_7815071 : CollatzResearch.WordTrace tailWord_7815071 prefixEnd_7815071 4012887772013498232471649 := by
  unfold tailWord_7815071
  simp only [CollatzResearch.WordTrace]
  refine ⟨285039056270339949710389067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190026037513559966473592711 285039056270339949710389067)
  ·
    refine ⟨427558584405509924565583601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285039056270339949710389067 427558584405509924565583601)
    ·
      refine ⟨320668938304132443424187701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 427558584405509924565583601 320668938304132443424187701)
      ·
        refine ⟨30062712966012416571017597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 320668938304132443424187701 30062712966012416571017597)
        ·
          refine ⟨11273517362254656214131599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30062712966012416571017597 11273517362254656214131599)
          ·
            refine ⟨16910276043381984321197399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11273517362254656214131599 16910276043381984321197399)
            ·
              refine ⟨25365414065072976481796099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16910276043381984321197399 25365414065072976481796099)
              ·
                refine ⟨38048121097609464722694149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25365414065072976481796099 38048121097609464722694149)
                ·
                  refine ⟨7134022705801774635505153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38048121097609464722694149 7134022705801774635505153)
                  ·
                    refine ⟨5350517029351330976628865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7134022705801774635505153 5350517029351330976628865)
                    ·
                      refine ⟨4012887772013498232471649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5350517029351330976628865 4012887772013498232471649)
                      ·
                        rfl

theorem cell23_7815071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 1, 1, 4, 2, 2].length) (baseStart_7815071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7815071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7815071 prefixEnd_7815071 := by exact prefixLift 7815071
  have htrace : WordTrace (prefixWord ++ tailWord_7815071) baseStart_7815071 baseEnd_7815071 := by
    simpa [prefixWord, tailWord_7815071, baseEnd_7815071] using wordTrace_append hprefix tailTrace_7815071
  have hstable : (prefixWord ++ tailWord_7815071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7815071).length < 2 ^ (prefixWord ++ tailWord_7815071).sum := by decide
  have hdescent : baseEnd_7815071 < baseStart_7815071 := by decide
  rcases family_descends (prefixWord ++ tailWord_7815071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7815127 : List Nat := [1, 1, 3, 2, 1, 1, 5, 2, 2, 1, 4]
def baseStart_7815127 : Nat := 118140960795 + 7815127 * 2 ^ 59
def prefixEnd_7815127 : Nat := 4983230072969 + 3 ^ 40 * 7815127 * 2
def baseEnd_7815127 : Nat := 4012916526930150013371391

theorem tailTrace_7815127 : CollatzResearch.WordTrace tailWord_7815127 prefixEnd_7815127 4012916526930150013371391 := by
  unfold tailWord_7815127
  simp only [CollatzResearch.WordTrace]
  refine ⟨285041098758137071274427635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190027399172091380849618423 285041098758137071274427635)
  ·
    refine ⟨427561648137205606911641453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285041098758137071274427635 427561648137205606911641453)
    ·
      refine ⟨160335618051452102591865545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 427561648137205606911641453 160335618051452102591865545)
      ·
        refine ⟨120251713538589076943899159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 160335618051452102591865545 120251713538589076943899159)
        ·
          refine ⟨180377570307883615415848739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120251713538589076943899159 180377570307883615415848739)
          ·
            refine ⟨270566355461825423123773109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 180377570307883615415848739 270566355461825423123773109)
            ·
              refine ⟨25365595824546133417853729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 270566355461825423123773109 25365595824546133417853729)
              ·
                refine ⟨19024196868409600063390297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25365595824546133417853729 19024196868409600063390297)
                ·
                  refine ⟨14268147651307200047542723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19024196868409600063390297 14268147651307200047542723)
                  ·
                    refine ⟨21402221476960800071314085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14268147651307200047542723 21402221476960800071314085)
                    ·
                      refine ⟨4012916526930150013371391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21402221476960800071314085 4012916526930150013371391)
                      ·
                        rfl

theorem cell23_7815127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 5, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 5, 2, 2, 1, 4].length) (baseStart_7815127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7815127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7815127 prefixEnd_7815127 := by exact prefixLift 7815127
  have htrace : WordTrace (prefixWord ++ tailWord_7815127) baseStart_7815127 baseEnd_7815127 := by
    simpa [prefixWord, tailWord_7815127, baseEnd_7815127] using wordTrace_append hprefix tailTrace_7815127
  have hstable : (prefixWord ++ tailWord_7815127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7815127).length < 2 ^ (prefixWord ++ tailWord_7815127).sum := by decide
  have hdescent : baseEnd_7815127 < baseStart_7815127 := by decide
  rcases family_descends (prefixWord ++ tailWord_7815127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7815164 : List Nat := [2, 2, 2, 1, 2, 2, 4, 1, 2, 2, 3]
def baseStart_7815164 : Nat := 118140960795 + 7815164 * 2 ^ 59
def prefixEnd_7815164 : Nat := 4983230072969 + 3 ^ 40 * 7815164 * 2
def baseEnd_7815164 : Nat := 4012935525714366368608721

theorem tailTrace_7815164 : CollatzResearch.WordTrace tailWord_7815164 prefixEnd_7815164 4012935525714366368608721 := by
  unfold tailWord_7815164
  simp only [CollatzResearch.WordTrace]
  refine ⟨142521224129501513296762273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190028298839335351062349697 142521224129501513296762273)
  ·
    refine ⟨106890918097126134972571705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142521224129501513296762273 106890918097126134972571705)
    ·
      refine ⟨80168188572844601229428779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106890918097126134972571705 80168188572844601229428779)
      ·
        refine ⟨120252282859266901844143169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80168188572844601229428779 120252282859266901844143169)
        ·
          refine ⟨90189212144450176383107377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120252282859266901844143169 90189212144450176383107377)
          ·
            refine ⟨67641909108337632287330533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90189212144450176383107377 67641909108337632287330533)
            ·
              refine ⟨12682857957813306053874475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 67641909108337632287330533 12682857957813306053874475)
              ·
                refine ⟨19024286936719959080811713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12682857957813306053874475 19024286936719959080811713)
                ·
                  refine ⟨14268215202539969310608785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19024286936719959080811713 14268215202539969310608785)
                  ·
                    refine ⟨10701161401904976982956589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14268215202539969310608785 10701161401904976982956589)
                    ·
                      refine ⟨4012935525714366368608721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10701161401904976982956589 4012935525714366368608721)
                      ·
                        rfl

theorem cell23_7815164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 4, 1, 2, 2, 3].length) (baseStart_7815164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7815164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7815164 prefixEnd_7815164 := by exact prefixLift 7815164
  have htrace : WordTrace (prefixWord ++ tailWord_7815164) baseStart_7815164 baseEnd_7815164 := by
    simpa [prefixWord, tailWord_7815164, baseEnd_7815164] using wordTrace_append hprefix tailTrace_7815164
  have hstable : (prefixWord ++ tailWord_7815164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7815164).length < 2 ^ (prefixWord ++ tailWord_7815164).sum := by decide
  have hdescent : baseEnd_7815164 < baseStart_7815164 := by decide
  rcases family_descends (prefixWord ++ tailWord_7815164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7815214 : List Nat := [4, 1, 3, 1, 1, 2, 2, 1, 3, 5]
def baseStart_7815214 : Nat := 118140960795 + 7815214 * 2 ^ 59
def prefixEnd_7815214 : Nat := 4983230072969 + 3 ^ 40 * 7815214 * 2
def baseEnd_7815214 : Nat := 1337653733249030390994497

theorem tailTrace_7815214 : CollatzResearch.WordTrace tailWord_7815214 prefixEnd_7815214 1337653733249030390994497 := by
  unfold tailWord_7815214
  simp only [CollatzResearch.WordTrace]
  refine ⟨35630533988602735641605587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 190029514605881256755229797 35630533988602735641605587)
  ·
    refine ⟨53445800982904103462408381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35630533988602735641605587 53445800982904103462408381)
    ·
      refine ⟨20042175368589038798403143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53445800982904103462408381 20042175368589038798403143)
      ·
        refine ⟨30063263052883558197604715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20042175368589038798403143 30063263052883558197604715)
        ·
          refine ⟨45094894579325337296407073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30063263052883558197604715 45094894579325337296407073)
          ·
            refine ⟨33821170934494002972305305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45094894579325337296407073 33821170934494002972305305)
            ·
              refine ⟨25365878200870502229228979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33821170934494002972305305 25365878200870502229228979)
              ·
                refine ⟨38048817301305753343843469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25365878200870502229228979 38048817301305753343843469)
                ·
                  refine ⟨14268306487989657503941301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38048817301305753343843469 14268306487989657503941301)
                  ·
                    refine ⟨1337653733249030390994497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14268306487989657503941301 1337653733249030390994497)
                    ·
                      rfl

theorem cell23_7815214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 2, 1, 3, 5].length) (baseStart_7815214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7815214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7815214 prefixEnd_7815214 := by exact prefixLift 7815214
  have htrace : WordTrace (prefixWord ++ tailWord_7815214) baseStart_7815214 baseEnd_7815214 := by
    simpa [prefixWord, tailWord_7815214, baseEnd_7815214] using wordTrace_append hprefix tailTrace_7815214
  have hstable : (prefixWord ++ tailWord_7815214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7815214).length < 2 ^ (prefixWord ++ tailWord_7815214).sum := by decide
  have hdescent : baseEnd_7815214 < baseStart_7815214 := by decide
  rcases family_descends (prefixWord ++ tailWord_7815214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7815221 : List Nat := [1, 3, 3, 1, 1, 1, 5, 1, 2, 3, 2]
def baseStart_7815221 : Nat := 118140960795 + 7815221 * 2 ^ 59
def prefixEnd_7815221 : Nat := 4983230072969 + 3 ^ 40 * 7815221 * 2
def baseEnd_7815221 : Nat := 4012964794111672645595959

theorem tailTrace_7815221 : CollatzResearch.WordTrace tailWord_7815221 prefixEnd_7815221 4012964794111672645595959 := by
  unfold tailWord_7815221
  simp only [CollatzResearch.WordTrace]
  refine ⟨285044527219796525328349517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190029684813197683552233011 285044527219796525328349517)
  ·
    refine ⟨106891697707423696998131069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 285044527219796525328349517 106891697707423696998131069)
    ·
      refine ⟨40084386640283886374299151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 106891697707423696998131069 40084386640283886374299151)
      ·
        refine ⟨60126579960425829561448727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40084386640283886374299151 60126579960425829561448727)
        ·
          refine ⟨90189869940638744342173091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60126579960425829561448727 90189869940638744342173091)
          ·
            refine ⟨135284804910958116513259637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90189869940638744342173091 135284804910958116513259637)
            ·
              refine ⟨12682950460402323423118091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 135284804910958116513259637 12682950460402323423118091)
              ·
                refine ⟨19024425690603485134677137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12682950460402323423118091 19024425690603485134677137)
                ·
                  refine ⟨14268319267952613851007853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19024425690603485134677137 14268319267952613851007853)
                  ·
                    refine ⟨5350619725482230194127945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14268319267952613851007853 5350619725482230194127945)
                    ·
                      refine ⟨4012964794111672645595959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5350619725482230194127945 4012964794111672645595959)
                      ·
                        rfl

theorem cell23_7815221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 5, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 5, 1, 2, 3, 2].length) (baseStart_7815221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7815221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7815221 prefixEnd_7815221 := by exact prefixLift 7815221
  have htrace : WordTrace (prefixWord ++ tailWord_7815221) baseStart_7815221 baseEnd_7815221 := by
    simpa [prefixWord, tailWord_7815221, baseEnd_7815221] using wordTrace_append hprefix tailTrace_7815221
  have hstable : (prefixWord ++ tailWord_7815221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7815221).length < 2 ^ (prefixWord ++ tailWord_7815221).sum := by decide
  have hdescent : baseEnd_7815221 < baseStart_7815221 := by decide
  rcases family_descends (prefixWord ++ tailWord_7815221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7815227 : List Nat := [1, 1, 1, 1, 1, 2, 1, 5, 6, 4]
def baseStart_7815227 : Nat := 118140960795 + 7815227 * 2 ^ 59
def prefixEnd_7815227 : Nat := 4983230072969 + 3 ^ 40 * 7815227 * 2
def baseEnd_7815227 : Nat := 1337655958331866540706977

theorem tailTrace_7815227 : CollatzResearch.WordTrace tailWord_7815227 prefixEnd_7815227 1337655958331866540706977 := by
  unfold tailWord_7815227
  simp only [CollatzResearch.WordTrace]
  refine ⟨285044746057774788353067935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190029830705183192235378623 285044746057774788353067935)
  ·
    refine ⟨427567119086662182529601903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285044746057774788353067935 427567119086662182529601903)
    ·
      refine ⟨641350678629993273794402855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 427567119086662182529601903 641350678629993273794402855)
      ·
        refine ⟨962026017944989910691604283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 641350678629993273794402855 962026017944989910691604283)
        ·
          refine ⟨1443039026917484866037406425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 962026017944989910691604283 1443039026917484866037406425)
          ·
            refine ⟨1082279270188113649528054819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1443039026917484866037406425 1082279270188113649528054819)
            ·
              refine ⟨1623418905282170474292082229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1082279270188113649528054819 1623418905282170474292082229)
              ·
                refine ⟨152195522370203481964882709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1623418905282170474292082229 152195522370203481964882709)
                ·
                  refine ⟨7134165111103288217103877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 152195522370203481964882709 7134165111103288217103877)
                  ·
                    refine ⟨1337655958331866540706977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7134165111103288217103877 1337655958331866540706977)
                    ·
                      rfl

theorem cell23_7815227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 5, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 5, 6, 4].length) (baseStart_7815227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7815227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7815227 prefixEnd_7815227 := by exact prefixLift 7815227
  have htrace : WordTrace (prefixWord ++ tailWord_7815227) baseStart_7815227 baseEnd_7815227 := by
    simpa [prefixWord, tailWord_7815227, baseEnd_7815227] using wordTrace_append hprefix tailTrace_7815227
  have hstable : (prefixWord ++ tailWord_7815227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7815227).length < 2 ^ (prefixWord ++ tailWord_7815227).sum := by decide
  have hdescent : baseEnd_7815227 < baseStart_7815227 := by decide
  rcases family_descends (prefixWord ++ tailWord_7815227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7815228 : List Nat := [2, 2, 2, 2, 2, 1, 4, 3, 1, 1, 3]
def baseStart_7815228 : Nat := 118140960795 + 7815228 * 2 ^ 59
def prefixEnd_7815228 : Nat := 4983230072969 + 3 ^ 40 * 7815228 * 2
def baseEnd_7815228 : Nat := 4012968388476254118208427

theorem tailTrace_7815228 : CollatzResearch.WordTrace tailWord_7815228 prefixEnd_7815228 4012968388476254118208427 := by
  unfold tailWord_7815228
  simp only [CollatzResearch.WordTrace]
  refine ⟨142522391265385582761927169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190029855020514110349236225 142522391265385582761927169)
  ·
    refine ⟨106891793449039187071445377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142522391265385582761927169 106891793449039187071445377)
    ·
      refine ⟨80168845086779390303584033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106891793449039187071445377 80168845086779390303584033)
      ·
        refine ⟨60126633815084542727688025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80168845086779390303584033 60126633815084542727688025)
        ·
          refine ⟨45094975361313407045766019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60126633815084542727688025 45094975361313407045766019)
          ·
            refine ⟨67642463041970110568649029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45094975361313407045766019 67642463041970110568649029)
            ·
              refine ⟨12682961820369395731621693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 67642463041970110568649029 12682961820369395731621693)
              ·
                refine ⟨4756110682638523399358135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12682961820369395731621693 4756110682638523399358135)
                ·
                  refine ⟨7134166023957785099037203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4756110682638523399358135 7134166023957785099037203)
                  ·
                    refine ⟨10701249035936677648555805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7134166023957785099037203 10701249035936677648555805)
                    ·
                      refine ⟨4012968388476254118208427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10701249035936677648555805 4012968388476254118208427)
                      ·
                        rfl

theorem cell23_7815228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 4, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 4, 3, 1, 1, 3].length) (baseStart_7815228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7815228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7815228 prefixEnd_7815228 := by exact prefixLift 7815228
  have htrace : WordTrace (prefixWord ++ tailWord_7815228) baseStart_7815228 baseEnd_7815228 := by
    simpa [prefixWord, tailWord_7815228, baseEnd_7815228] using wordTrace_append hprefix tailTrace_7815228
  have hstable : (prefixWord ++ tailWord_7815228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7815228).length < 2 ^ (prefixWord ++ tailWord_7815228).sum := by decide
  have hdescent : baseEnd_7815228 < baseStart_7815228 := by decide
  rcases family_descends (prefixWord ++ tailWord_7815228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7815237 : List Nat := [1, 3, 1, 1, 1, 3, 1, 5, 1, 1, 5]
def baseStart_7815237 : Nat := 118140960795 + 7815237 * 2 ^ 59
def prefixEnd_7815237 : Nat := 4983230072969 + 3 ^ 40 * 7815237 * 2
def baseEnd_7815237 : Nat := 4012973009802144582995885

theorem tailTrace_7815237 : CollatzResearch.WordTrace tailWord_7815237 prefixEnd_7815237 4012973009802144582995885 := by
  unfold tailWord_7815237
  simp only [CollatzResearch.WordTrace]
  refine ⟨285045110787738560060931965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190030073858492373373954643 285045110787738560060931965)
  ·
    refine ⟨106891916545401960022849487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 285045110787738560060931965 106891916545401960022849487)
    ·
      refine ⟨160337874818102940034274231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106891916545401960022849487 160337874818102940034274231)
      ·
        refine ⟨240506812227154410051411347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160337874818102940034274231 240506812227154410051411347)
        ·
          refine ⟨360760218340731615077117021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 240506812227154410051411347 360760218340731615077117021)
          ·
            refine ⟨135285081877774355653918883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 360760218340731615077117021 135285081877774355653918883)
            ·
              refine ⟨202927622816661533480878325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 135285081877774355653918883 202927622816661533480878325)
              ·
                refine ⟨19024464639062018763832343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 202927622816661533480878325 19024464639062018763832343)
                ·
                  refine ⟨28536696958593028145748515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19024464639062018763832343 28536696958593028145748515)
                  ·
                    refine ⟨42805045437889542218622773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28536696958593028145748515 42805045437889542218622773)
                    ·
                      refine ⟨4012973009802144582995885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42805045437889542218622773 4012973009802144582995885)
                      ·
                        rfl

theorem cell23_7815237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 5, 1, 1, 5].length) (baseStart_7815237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7815237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7815237 prefixEnd_7815237 := by exact prefixLift 7815237
  have htrace : WordTrace (prefixWord ++ tailWord_7815237) baseStart_7815237 baseEnd_7815237 := by
    simpa [prefixWord, tailWord_7815237, baseEnd_7815237] using wordTrace_append hprefix tailTrace_7815237
  have hstable : (prefixWord ++ tailWord_7815237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7815237).length < 2 ^ (prefixWord ++ tailWord_7815237).sum := by decide
  have hdescent : baseEnd_7815237 < baseStart_7815237 := by decide
  rcases family_descends (prefixWord ++ tailWord_7815237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7815238 : List Nat := [6, 1, 1, 1, 1, 1, 2, 1, 4, 3, 2]
def baseStart_7815238 : Nat := 118140960795 + 7815238 * 2 ^ 59
def prefixEnd_7815238 : Nat := 4983230072969 + 3 ^ 40 * 7815238 * 2
def baseEnd_7815238 : Nat := 4012973523282799079083381

theorem tailTrace_7815238 : CollatzResearch.WordTrace tailWord_7815238 prefixEnd_7815238 4012973523282799079083381 := by
  unfold tailWord_7815238
  simp only [CollatzResearch.WordTrace]
  refine ⟨8907660851897966788491199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 190030098173823291487812245 8907660851897966788491199)
  ·
    refine ⟨13361491277846950182736799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8907660851897966788491199 13361491277846950182736799)
    ·
      refine ⟨20042236916770425274105199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13361491277846950182736799 20042236916770425274105199)
      ·
        refine ⟨30063355375155637911157799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20042236916770425274105199 30063355375155637911157799)
        ·
          refine ⟨45095033062733456866736699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30063355375155637911157799 45095033062733456866736699)
          ·
            refine ⟨67642549594100185300105049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45095033062733456866736699 67642549594100185300105049)
            ·
              refine ⟨50731912195575138975078787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67642549594100185300105049 50731912195575138975078787)
              ·
                refine ⟨76097868293362708462618181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50731912195575138975078787 76097868293362708462618181)
                ·
                  refine ⟨14268350305005507836740909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 76097868293362708462618181 14268350305005507836740909)
                  ·
                    refine ⟨5350631364377065438777841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14268350305005507836740909 5350631364377065438777841)
                    ·
                      refine ⟨4012973523282799079083381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5350631364377065438777841 4012973523282799079083381)
                      ·
                        rfl

theorem cell23_7815238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 2, 1, 4, 3, 2].length) (baseStart_7815238 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7815238 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7815238 prefixEnd_7815238 := by exact prefixLift 7815238
  have htrace : WordTrace (prefixWord ++ tailWord_7815238) baseStart_7815238 baseEnd_7815238 := by
    simpa [prefixWord, tailWord_7815238, baseEnd_7815238] using wordTrace_append hprefix tailTrace_7815238
  have hstable : (prefixWord ++ tailWord_7815238).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7815238).length < 2 ^ (prefixWord ++ tailWord_7815238).sum := by decide
  have hdescent : baseEnd_7815238 < baseStart_7815238 := by decide
  rcases family_descends (prefixWord ++ tailWord_7815238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7815261 : List Nat := [1, 4, 4, 1, 1, 1, 3, 1, 1, 6]
def baseStart_7815261 : Nat := 118140960795 + 7815261 * 2 ^ 59
def prefixEnd_7815261 : Nat := 4983230072969 + 3 ^ 40 * 7815261 * 2
def baseEnd_7815261 : Nat := 1337661777779284163031925

theorem tailTrace_7815261 : CollatzResearch.WordTrace tailWord_7815261 prefixEnd_7815261 1337661777779284163031925 := by
  unfold tailWord_7815261
  simp only [CollatzResearch.WordTrace]
  refine ⟨285045986139651612159805637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190030657426434408106537091 285045986139651612159805637)
  ·
    refine ⟨53446122401184677279963557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 285045986139651612159805637 53446122401184677279963557)
    ·
      refine ⟨10021147950222126989993167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 53446122401184677279963557 10021147950222126989993167)
      ·
        refine ⟨15031721925333190484989751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10021147950222126989993167 15031721925333190484989751)
        ·
          refine ⟨22547582887999785727484627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15031721925333190484989751 22547582887999785727484627)
          ·
            refine ⟨33821374331999678591226941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22547582887999785727484627 33821374331999678591226941)
            ·
              refine ⟨12683015374499879471710103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33821374331999678591226941 12683015374499879471710103)
              ·
                refine ⟨19024523061749819207565155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12683015374499879471710103 19024523061749819207565155)
                ·
                  refine ⟨28536784592624728811347733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19024523061749819207565155 28536784592624728811347733)
                  ·
                    refine ⟨1337661777779284163031925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28536784592624728811347733 1337661777779284163031925)
                    ·
                      rfl

theorem cell23_7815261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 3, 1, 1, 6].length) (baseStart_7815261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7815261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7815261 prefixEnd_7815261 := by exact prefixLift 7815261
  have htrace : WordTrace (prefixWord ++ tailWord_7815261) baseStart_7815261 baseEnd_7815261 := by
    simpa [prefixWord, tailWord_7815261, baseEnd_7815261] using wordTrace_append hprefix tailTrace_7815261
  have hstable : (prefixWord ++ tailWord_7815261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7815261).length < 2 ^ (prefixWord ++ tailWord_7815261).sum := by decide
  have hdescent : baseEnd_7815261 < baseStart_7815261 := by decide
  rcases family_descends (prefixWord ++ tailWord_7815261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7815264 : List Nat := [2, 1, 1, 3, 2, 3, 3, 1, 1, 2, 4]
def baseStart_7815264 : Nat := 118140960795 + 7815264 * 2 ^ 59
def prefixEnd_7815264 : Nat := 4983230072969 + 3 ^ 40 * 7815264 * 2
def baseEnd_7815264 : Nat := 4012986873779815977358261

theorem tailTrace_7815264 : CollatzResearch.WordTrace tailWord_7815264 prefixEnd_7815264 4012986873779815977358261 := by
  unfold tailWord_7815264
  simp only [CollatzResearch.WordTrace]
  refine ⟨142523047779320371836082423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190030730372427162448109897 142523047779320371836082423)
  ·
    refine ⟨213784571668980557754123635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142523047779320371836082423 213784571668980557754123635)
    ·
      refine ⟨320676857503470836631185453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213784571668980557754123635 320676857503470836631185453)
      ·
        refine ⟨120253821563801563736694545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 320676857503470836631185453 120253821563801563736694545)
        ·
          refine ⟨90190366172851172802520909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120253821563801563736694545 90190366172851172802520909)
          ·
            refine ⟨33821387314819189800945341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 90190366172851172802520909 33821387314819189800945341)
            ·
              refine ⟨12683020243057196175354503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33821387314819189800945341 12683020243057196175354503)
              ·
                refine ⟨19024530364585794263031755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12683020243057196175354503 19024530364585794263031755)
                ·
                  refine ⟨28536795546878691394547633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19024530364585794263031755 28536795546878691394547633)
                  ·
                    refine ⟨21402596660159018545910725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28536795546878691394547633 21402596660159018545910725)
                    ·
                      refine ⟨4012986873779815977358261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21402596660159018545910725 4012986873779815977358261)
                      ·
                        rfl

theorem cell23_7815264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 3, 1, 1, 2, 4].length) (baseStart_7815264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7815264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7815264 prefixEnd_7815264 := by exact prefixLift 7815264
  have htrace : WordTrace (prefixWord ++ tailWord_7815264) baseStart_7815264 baseEnd_7815264 := by
    simpa [prefixWord, tailWord_7815264, baseEnd_7815264] using wordTrace_append hprefix tailTrace_7815264
  have hstable : (prefixWord ++ tailWord_7815264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7815264).length < 2 ^ (prefixWord ++ tailWord_7815264).sum := by decide
  have hdescent : baseEnd_7815264 < baseStart_7815264 := by decide
  rcases family_descends (prefixWord ++ tailWord_7815264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7815271 : List Nat := [1, 1, 5, 1, 1, 2, 4, 2, 1, 2, 3]
def baseStart_7815271 : Nat := 118140960795 + 7815271 * 2 ^ 59
def prefixEnd_7815271 : Nat := 4983230072969 + 3 ^ 40 * 7815271 * 2
def baseEnd_7815271 : Nat := 4012990468144397449970729

theorem tailTrace_7815271 : CollatzResearch.WordTrace tailWord_7815271 prefixEnd_7815271 4012990468144397449970729 := by
  unfold tailWord_7815271
  simp only [CollatzResearch.WordTrace]
  refine ⟨285046350869615383867669667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190030900579743589245113111 285046350869615383867669667)
  ·
    refine ⟨427569526304423075801504501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285046350869615383867669667 427569526304423075801504501)
    ·
      refine ⟨40084643091039663356391047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 427569526304423075801504501 40084643091039663356391047)
      ·
        refine ⟨60126964636559495034586571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40084643091039663356391047 60126964636559495034586571)
        ·
          refine ⟨90190446954839242551879857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60126964636559495034586571 90190446954839242551879857)
          ·
            refine ⟨67642835216129431913909893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90190446954839242551879857 67642835216129431913909893)
            ·
              refine ⟨12683031603024268483858105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 67642835216129431913909893 12683031603024268483858105)
              ·
                refine ⟨9512273702268201362893579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12683031603024268483858105 9512273702268201362893579)
                ·
                  refine ⟨14268410553402302044340369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9512273702268201362893579 14268410553402302044340369)
                  ·
                    refine ⟨10701307915051726533255277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14268410553402302044340369 10701307915051726533255277)
                    ·
                      refine ⟨4012990468144397449970729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10701307915051726533255277 4012990468144397449970729)
                      ·
                        rfl

theorem cell23_7815271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 4, 2, 1, 2, 3].length) (baseStart_7815271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7815271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7815271 prefixEnd_7815271 := by exact prefixLift 7815271
  have htrace : WordTrace (prefixWord ++ tailWord_7815271) baseStart_7815271 baseEnd_7815271 := by
    simpa [prefixWord, tailWord_7815271, baseEnd_7815271] using wordTrace_append hprefix tailTrace_7815271
  have hstable : (prefixWord ++ tailWord_7815271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7815271).length < 2 ^ (prefixWord ++ tailWord_7815271).sum := by decide
  have hdescent : baseEnd_7815271 < baseStart_7815271 := by decide
  rcases family_descends (prefixWord ++ tailWord_7815271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7815274 : List Nat := [3, 1, 3, 2, 3, 1, 1, 9]
def baseStart_7815274 : Nat := 118140960795 + 7815274 * 2 ^ 59
def prefixEnd_7815274 : Nat := 4983230072969 + 3 ^ 40 * 7815274 * 2
def baseEnd_7815274 : Nat := 148629333651346701416045

theorem tailTrace_7815274 : CollatzResearch.WordTrace tailWord_7815274 prefixEnd_7815274 148629333651346701416045 := by
  unfold tailWord_7815274
  simp only [CollatzResearch.WordTrace]
  refine ⟨71261615072151128845007219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 190030973525736343586685917 71261615072151128845007219)
  ·
    refine ⟨106892422608226693267510829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71261615072151128845007219 106892422608226693267510829)
    ·
      refine ⟨40084658478085009975316561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 106892422608226693267510829 40084658478085009975316561)
      ·
        refine ⟨30063493858563757481487421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40084658478085009975316561 30063493858563757481487421)
        ·
          refine ⟨11273810196961409055557783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30063493858563757481487421 11273810196961409055557783)
          ·
            refine ⟨16910715295442113583336675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11273810196961409055557783 16910715295442113583336675)
            ·
              refine ⟨25366072943163170375005013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16910715295442113583336675 25366072943163170375005013)
              ·
                refine ⟨148629333651346701416045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 25366072943163170375005013 148629333651346701416045)
                ·
                  rfl

theorem cell23_7815274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 1, 9].length) (baseStart_7815274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7815274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7815274 prefixEnd_7815274 := by exact prefixLift 7815274
  have htrace : WordTrace (prefixWord ++ tailWord_7815274) baseStart_7815274 baseEnd_7815274 := by
    simpa [prefixWord, tailWord_7815274, baseEnd_7815274] using wordTrace_append hprefix tailTrace_7815274
  have hstable : (prefixWord ++ tailWord_7815274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7815274).length < 2 ^ (prefixWord ++ tailWord_7815274).sum := by decide
  have hdescent : baseEnd_7815274 < baseStart_7815274 := by decide
  rcases family_descends (prefixWord ++ tailWord_7815274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7815301 : List Nat := [1, 3, 1, 1, 5, 1, 2, 1, 4, 1, 3]
def baseStart_7815301 : Nat := 118140960795 + 7815301 * 2 ^ 59
def prefixEnd_7815301 : Nat := 4983230072969 + 3 ^ 40 * 7815301 * 2
def baseEnd_7815301 : Nat := 4013005872564032332595591

theorem tailTrace_7815301 : CollatzResearch.WordTrace tailWord_7815301 prefixEnd_7815301 4013005872564032332595591 := by
  unfold tailWord_7815301
  simp only [CollatzResearch.WordTrace]
  refine ⟨285047445059506698991261757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190031630039671132660841171 285047445059506698991261757)
  ·
    refine ⟨106892791897315012121723159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 285047445059506698991261757 106892791897315012121723159)
    ·
      refine ⟨160339187845972518182584739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106892791897315012121723159 160339187845972518182584739)
      ·
        refine ⟨240508781768958777273877109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160339187845972518182584739 240508781768958777273877109)
        ·
          refine ⟨22547698290839885369425979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 240508781768958777273877109 22547698290839885369425979)
          ·
            refine ⟨33821547436259828054138969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22547698290839885369425979 33821547436259828054138969)
            ·
              refine ⟨25366160577194871040604227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33821547436259828054138969 25366160577194871040604227)
              ·
                refine ⟨38049240865792306560906341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25366160577194871040604227 38049240865792306560906341)
                ·
                  refine ⟨7134232662336057480169939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38049240865792306560906341 7134232662336057480169939)
                  ·
                    refine ⟨10701348993504086220254909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7134232662336057480169939 10701348993504086220254909)
                    ·
                      refine ⟨4013005872564032332595591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10701348993504086220254909 4013005872564032332595591)
                      ·
                        rfl

theorem cell23_7815301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 2, 1, 4, 1, 3].length) (baseStart_7815301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7815301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7815301 prefixEnd_7815301 := by exact prefixLift 7815301
  have htrace : WordTrace (prefixWord ++ tailWord_7815301) baseStart_7815301 baseEnd_7815301 := by
    simpa [prefixWord, tailWord_7815301, baseEnd_7815301] using wordTrace_append hprefix tailTrace_7815301
  have hstable : (prefixWord ++ tailWord_7815301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7815301).length < 2 ^ (prefixWord ++ tailWord_7815301).sum := by decide
  have hdescent : baseEnd_7815301 < baseStart_7815301 := by decide
  rcases family_descends (prefixWord ++ tailWord_7815301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7815317 : List Nat := [1, 3, 2, 1, 1, 1, 4, 1, 1, 8]
def baseStart_7815317 : Nat := 118140960795 + 7815317 * 2 ^ 59
def prefixEnd_7815317 : Nat := 4983230072969 + 3 ^ 40 * 7815317 * 2
def baseEnd_7815317 : Nat := 1337671362751501423331839

theorem tailTrace_7815317 : CollatzResearch.WordTrace tailWord_7815317 prefixEnd_7815317 1337671362751501423331839 := by
  unfold tailWord_7815317
  simp only [CollatzResearch.WordTrace]
  refine ⟨285048028627448733723844205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190032019084965822482562803 285048028627448733723844205)
  ·
    refine ⟨106893010735293275146441577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 285048028627448733723844205 106893010735293275146441577)
    ·
      refine ⟨80169758051469956359831183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106893010735293275146441577 80169758051469956359831183)
      ·
        refine ⟨120254637077204934539746775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80169758051469956359831183 120254637077204934539746775)
        ·
          refine ⟨180381955615807401809620163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120254637077204934539746775 180381955615807401809620163)
          ·
            refine ⟨270572933423711102714430245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 180381955615807401809620163 270572933423711102714430245)
            ·
              refine ⟨50732425016945831758955671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 270572933423711102714430245 50732425016945831758955671)
              ·
                refine ⟨76098637525418747638433507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50732425016945831758955671 76098637525418747638433507)
                ·
                  refine ⟨114147956288128121457650261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 76098637525418747638433507 114147956288128121457650261)
                  ·
                    refine ⟨1337671362751501423331839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 114147956288128121457650261 1337671362751501423331839)
                    ·
                      rfl

theorem cell23_7815317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 4, 1, 1, 8].length) (baseStart_7815317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7815317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7815317 prefixEnd_7815317 := by exact prefixLift 7815317
  have htrace : WordTrace (prefixWord ++ tailWord_7815317) baseStart_7815317 baseEnd_7815317 := by
    simpa [prefixWord, tailWord_7815317, baseEnd_7815317] using wordTrace_append hprefix tailTrace_7815317
  have hstable : (prefixWord ++ tailWord_7815317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7815317).length < 2 ^ (prefixWord ++ tailWord_7815317).sum := by decide
  have hdescent : baseEnd_7815317 < baseStart_7815317 := by decide
  rcases family_descends (prefixWord ++ tailWord_7815317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7815328 : List Nat := [2, 1, 1, 4, 2, 2, 3, 2, 1, 3, 2]
def baseStart_7815328 : Nat := 118140960795 + 7815328 * 2 ^ 59
def prefixEnd_7815328 : Nat := 4983230072969 + 3 ^ 40 * 7815328 * 2
def baseEnd_7815328 : Nat := 4013019736541703726957967

theorem tailTrace_7815328 : CollatzResearch.WordTrace tailWord_7815328 prefixEnd_7815328 4013019736541703726957967 := by
  unfold tailWord_7815328
  simp only [CollatzResearch.WordTrace]
  refine ⟨142524214915204441301247319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190032286553605921734996425 142524214915204441301247319)
  ·
    refine ⟨213786322372806661951870979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142524214915204441301247319 213786322372806661951870979)
    ·
      refine ⟨320679483559209992927806469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213786322372806661951870979 320679483559209992927806469)
      ·
        refine ⟨60127403167351873673963713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 320679483559209992927806469 60127403167351873673963713)
        ·
          refine ⟨45095552375513905255472785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60127403167351873673963713 45095552375513905255472785)
          ·
            refine ⟨33821664281635428941604589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45095552375513905255472785 33821664281635428941604589)
            ·
              refine ⟨12683124105613285853101721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33821664281635428941604589 12683124105613285853101721)
              ·
                refine ⟨9512343079209964389826291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12683124105613285853101721 9512343079209964389826291)
                ·
                  refine ⟨14268514618814946584739437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9512343079209964389826291 14268514618814946584739437)
                  ·
                    refine ⟨5350692982055604969277289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14268514618814946584739437 5350692982055604969277289)
                    ·
                      refine ⟨4013019736541703726957967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5350692982055604969277289 4013019736541703726957967)
                      ·
                        rfl

theorem cell23_7815328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 3, 2, 1, 3, 2].length) (baseStart_7815328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7815328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7815328 prefixEnd_7815328 := by exact prefixLift 7815328
  have htrace : WordTrace (prefixWord ++ tailWord_7815328) baseStart_7815328 baseEnd_7815328 := by
    simpa [prefixWord, tailWord_7815328, baseEnd_7815328] using wordTrace_append hprefix tailTrace_7815328
  have hstable : (prefixWord ++ tailWord_7815328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7815328).length < 2 ^ (prefixWord ++ tailWord_7815328).sum := by decide
  have hdescent : baseEnd_7815328 < baseStart_7815328 := by decide
  rcases family_descends (prefixWord ++ tailWord_7815328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7815367 : List Nat := [1, 1, 4, 1, 1, 1, 1, 1, 1, 3, 8]
def baseStart_7815367 : Nat := 118140960795 + 7815367 * 2 ^ 59
def prefixEnd_7815367 : Nat := 4983230072969 + 3 ^ 40 * 7815367 * 2
def baseEnd_7815367 : Nat := 4013039762287229074370287

theorem tailTrace_7815367 : CollatzResearch.WordTrace tailWord_7815367 prefixEnd_7815367 4013039762287229074370287 := by
  unfold tailWord_7815367
  simp only [CollatzResearch.WordTrace]
  refine ⟨285049852277267592263164355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190033234851511728175442903 285049852277267592263164355)
  ·
    refine ⟨427574778415901388394746533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285049852277267592263164355 427574778415901388394746533)
    ·
      refine ⟨80170270952981510324014975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 427574778415901388394746533 80170270952981510324014975)
      ·
        refine ⟨120255406429472265486022463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80170270952981510324014975 120255406429472265486022463)
        ·
          refine ⟨180383109644208398229033695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120255406429472265486022463 180383109644208398229033695)
          ·
            refine ⟨270574664466312597343550543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 180383109644208398229033695 270574664466312597343550543)
            ·
              refine ⟨405861996699468896015325815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 270574664466312597343550543 405861996699468896015325815)
              ·
                refine ⟨608792995049203344022988723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 405861996699468896015325815 608792995049203344022988723)
                ·
                  refine ⟨913189492573805016034483085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 608792995049203344022988723 913189492573805016034483085)
                  ·
                    refine ⟨342446059715176881012931157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 913189492573805016034483085 342446059715176881012931157)
                    ·
                      refine ⟨4013039762287229074370287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 342446059715176881012931157 4013039762287229074370287)
                      ·
                        rfl

theorem cell23_7815367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 1, 1, 3, 8].length) (baseStart_7815367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7815367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7815367 prefixEnd_7815367 := by exact prefixLift 7815367
  have htrace : WordTrace (prefixWord ++ tailWord_7815367) baseStart_7815367 baseEnd_7815367 := by
    simpa [prefixWord, tailWord_7815367, baseEnd_7815367] using wordTrace_append hprefix tailTrace_7815367
  have hstable : (prefixWord ++ tailWord_7815367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7815367).length < 2 ^ (prefixWord ++ tailWord_7815367).sum := by decide
  have hdescent : baseEnd_7815367 < baseStart_7815367 := by decide
  rcases family_descends (prefixWord ++ tailWord_7815367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7815381 : List Nat := [1, 3, 2, 4, 2, 1, 1, 2, 7]
def baseStart_7815381 : Nat := 118140960795 + 7815381 * 2 ^ 59
def prefixEnd_7815381 : Nat := 4983230072969 + 3 ^ 40 * 7815381 * 2
def baseEnd_7815381 : Nat := 445894105668488002177247

theorem tailTrace_7815381 : CollatzResearch.WordTrace tailWord_7815381 prefixEnd_7815381 445894105668488002177247 := by
  unfold tailWord_7815381
  simp only [CollatzResearch.WordTrace]
  refine ⟨285050362899216872654173997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190033575266144581769449331 285050362899216872654173997)
  ·
    refine ⟨106893886087206327245315249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 285050362899216872654173997 106893886087206327245315249)
    ·
      refine ⟨80170414565404745433986437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106893886087206327245315249 80170414565404745433986437)
      ·
        refine ⟨15031952731013389768872457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 80170414565404745433986437 15031952731013389768872457)
        ·
          refine ⟨11273964548260042326654343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15031952731013389768872457 11273964548260042326654343)
          ·
            refine ⟨16910946822390063489981515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11273964548260042326654343 16910946822390063489981515)
            ·
              refine ⟨25366420233585095234972273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16910946822390063489981515 25366420233585095234972273)
              ·
                refine ⟨19024815175188821426229205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25366420233585095234972273 19024815175188821426229205)
                ·
                  refine ⟨445894105668488002177247, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19024815175188821426229205 445894105668488002177247)
                  ·
                    rfl

theorem cell23_7815381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 1, 2, 7].length) (baseStart_7815381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7815381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7815381 prefixEnd_7815381 := by exact prefixLift 7815381
  have htrace : WordTrace (prefixWord ++ tailWord_7815381) baseStart_7815381 baseEnd_7815381 := by
    simpa [prefixWord, tailWord_7815381, baseEnd_7815381] using wordTrace_append hprefix tailTrace_7815381
  have hstable : (prefixWord ++ tailWord_7815381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7815381).length < 2 ^ (prefixWord ++ tailWord_7815381).sum := by decide
  have hdescent : baseEnd_7815381 < baseStart_7815381 := by decide
  rcases family_descends (prefixWord ++ tailWord_7815381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7815387 : List Nat := [1, 1, 1, 1, 1, 1, 1, 5, 3, 1, 7]
def baseStart_7815387 : Nat := 118140960795 + 7815387 * 2 ^ 59
def prefixEnd_7815387 : Nat := 4983230072969 + 3 ^ 40 * 7815387 * 2
def baseEnd_7815387 : Nat := 4013050031900318996120195

theorem tailTrace_7815387 : CollatzResearch.WordTrace tailWord_7815387 prefixEnd_7815387 4013050031900318996120195 := by
  unfold tailWord_7815387
  simp only [CollatzResearch.WordTrace]
  refine ⟨285050581737195135678892415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190033721158130090452594943 285050581737195135678892415)
  ·
    refine ⟨427575872605792703518338623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285050581737195135678892415 427575872605792703518338623)
    ·
      refine ⟨641363808908689055277507935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 427575872605792703518338623 641363808908689055277507935)
      ·
        refine ⟨962045713363033582916261903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 641363808908689055277507935 962045713363033582916261903)
        ·
          refine ⟨1443068570044550374374392855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 962045713363033582916261903 1443068570044550374374392855)
          ·
            refine ⟨2164602855066825561561589283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1443068570044550374374392855 2164602855066825561561589283)
            ·
              refine ⟨3246904282600238342342383925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2164602855066825561561589283 3246904282600238342342383925)
              ·
                refine ⟨304397276493772344594598493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3246904282600238342342383925 304397276493772344594598493)
                ·
                  refine ⟨114148978685164629222974435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 304397276493772344594598493 114148978685164629222974435)
                  ·
                    refine ⟨171223468027746943834461653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 114148978685164629222974435 171223468027746943834461653)
                    ·
                      refine ⟨4013050031900318996120195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 171223468027746943834461653 4013050031900318996120195)
                      ·
                        rfl

theorem cell23_7815387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 5, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 5, 3, 1, 7].length) (baseStart_7815387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7815387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7815387 prefixEnd_7815387 := by exact prefixLift 7815387
  have htrace : WordTrace (prefixWord ++ tailWord_7815387) baseStart_7815387 baseEnd_7815387 := by
    simpa [prefixWord, tailWord_7815387, baseEnd_7815387] using wordTrace_append hprefix tailTrace_7815387
  have hstable : (prefixWord ++ tailWord_7815387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7815387).length < 2 ^ (prefixWord ++ tailWord_7815387).sum := by decide
  have hdescent : baseEnd_7815387 < baseStart_7815387 := by decide
  rcases family_descends (prefixWord ++ tailWord_7815387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7815441 : List Nat := [1, 2, 2, 1, 1, 5, 2, 2, 3, 4]
def baseStart_7815441 : Nat := 118140960795 + 7815441 * 2 ^ 59
def prefixEnd_7815441 : Nat := 4983230072969 + 3 ^ 40 * 7815441 * 2
def baseEnd_7815441 : Nat := 1337692586618553928281649

theorem tailTrace_7815441 : CollatzResearch.WordTrace tailWord_7815441 prefixEnd_7815441 1337692586618553928281649 := by
  unfold tailWord_7815441
  simp only [CollatzResearch.WordTrace]
  refine ⟨285052551278999502901358177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190035034185999668600905451 285052551278999502901358177)
  ·
    refine ⟨213789413459249627176018633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 285052551278999502901358177 213789413459249627176018633)
    ·
      refine ⟨160342060094437220382013975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 213789413459249627176018633 160342060094437220382013975)
      ·
        refine ⟨240513090141655830573020963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160342060094437220382013975 240513090141655830573020963)
        ·
          refine ⟨360769635212483745859531445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 240513090141655830573020963 360769635212483745859531445)
          ·
            refine ⟨33822153301170351174331073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 360769635212483745859531445 33822153301170351174331073)
            ·
              refine ⟨25366614975877763380748305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33822153301170351174331073 25366614975877763380748305)
              ·
                refine ⟨19024961231908322535561229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25366614975877763380748305 19024961231908322535561229)
                ·
                  refine ⟨7134360461965620950835461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19024961231908322535561229 7134360461965620950835461)
                  ·
                    refine ⟨1337692586618553928281649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7134360461965620950835461 1337692586618553928281649)
                    ·
                      rfl

theorem cell23_7815441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 2, 2, 3, 4].length) (baseStart_7815441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7815441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7815441 prefixEnd_7815441 := by exact prefixLift 7815441
  have htrace : WordTrace (prefixWord ++ tailWord_7815441) baseStart_7815441 baseEnd_7815441 := by
    simpa [prefixWord, tailWord_7815441, baseEnd_7815441] using wordTrace_append hprefix tailTrace_7815441
  have hstable : (prefixWord ++ tailWord_7815441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7815441).length < 2 ^ (prefixWord ++ tailWord_7815441).sum := by decide
  have hdescent : baseEnd_7815441 < baseStart_7815441 := by decide
  rcases family_descends (prefixWord ++ tailWord_7815441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7815475 : List Nat := [1, 1, 1, 2, 5, 1, 5, 2, 1, 4]
def baseStart_7815475 : Nat := 118140960795 + 7815475 * 2 ^ 59
def prefixEnd_7815475 : Nat := 4983230072969 + 3 ^ 40 * 7815475 * 2
def baseEnd_7815475 : Nat := 1337698406065971550606597

theorem tailTrace_7815475 : CollatzResearch.WordTrace tailWord_7815475 prefixEnd_7815475 1337698406065971550606597 := by
  unfold tailWord_7815475
  simp only [CollatzResearch.WordTrace]
  refine ⟨285053791360876326708095879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190035860907250884472063919 285053791360876326708095879)
  ·
    refine ⟨427580687041314490062143819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285053791360876326708095879 427580687041314490062143819)
    ·
      refine ⟨641371030561971735093215729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 427580687041314490062143819 641371030561971735093215729)
      ·
        refine ⟨481028272921478801319911797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 641371030561971735093215729 481028272921478801319911797)
        ·
          refine ⟨45096400586388637623741731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 481028272921478801319911797 45096400586388637623741731)
          ·
            refine ⟨67644600879582956435612597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45096400586388637623741731 67644600879582956435612597)
            ·
              refine ⟨6341681332460902165838681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 67644600879582956435612597 6341681332460902165838681)
              ·
                refine ⟨4756260999345676624379011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6341681332460902165838681 4756260999345676624379011)
                ·
                  refine ⟨7134391499018514936568517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4756260999345676624379011 7134391499018514936568517)
                  ·
                    refine ⟨1337698406065971550606597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7134391499018514936568517 1337698406065971550606597)
                    ·
                      rfl

theorem cell23_7815475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 5, 2, 1, 4].length) (baseStart_7815475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7815475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7815475 prefixEnd_7815475 := by exact prefixLift 7815475
  have htrace : WordTrace (prefixWord ++ tailWord_7815475) baseStart_7815475 baseEnd_7815475 := by
    simpa [prefixWord, tailWord_7815475, baseEnd_7815475] using wordTrace_append hprefix tailTrace_7815475
  have hstable : (prefixWord ++ tailWord_7815475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7815475).length < 2 ^ (prefixWord ++ tailWord_7815475).sum := by decide
  have hdescent : baseEnd_7815475 < baseStart_7815475 := by decide
  rcases family_descends (prefixWord ++ tailWord_7815475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7815491 : List Nat := [1, 1, 1, 3, 1, 3, 2, 1, 3, 5, 2]
def baseStart_7815491 : Nat := 118140960795 + 7815491 * 2 ^ 59
def prefixEnd_7815491 : Nat := 4983230072969 + 3 ^ 40 * 7815491 * 2
def baseEnd_7815491 : Nat := 4013103433888386589219717

theorem tailTrace_7815491 : CollatzResearch.WordTrace tailWord_7815491 prefixEnd_7815491 4013103433888386589219717 := by
  unfold tailWord_7815491
  simp only [CollatzResearch.WordTrace]
  refine ⟨285054374928818361440678327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190036249952545574293785551 285054374928818361440678327)
  ·
    refine ⟨427581562393227542161017491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285054374928818361440678327 427581562393227542161017491)
    ·
      refine ⟨641372343589841313241526237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 427581562393227542161017491 641372343589841313241526237)
      ·
        refine ⟨240514628846190492465572339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 641372343589841313241526237 240514628846190492465572339)
        ·
          refine ⟨360771943269285738698358509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 240514628846190492465572339 360771943269285738698358509)
          ·
            refine ⟨135289478725982152011884441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 360771943269285738698358509 135289478725982152011884441)
            ·
              refine ⟨101467109044486614008913331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 135289478725982152011884441 101467109044486614008913331)
              ·
                refine ⟨152200663566729921013369997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 101467109044486614008913331 152200663566729921013369997)
                ·
                  refine ⟨57075248837523720380013749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 152200663566729921013369997 57075248837523720380013749)
                  ·
                    refine ⟨5350804578517848785626289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 57075248837523720380013749 5350804578517848785626289)
                    ·
                      refine ⟨4013103433888386589219717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5350804578517848785626289 4013103433888386589219717)
                      ·
                        rfl

theorem cell23_7815491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 1, 3, 5, 2].length) (baseStart_7815491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7815491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7815491 prefixEnd_7815491 := by exact prefixLift 7815491
  have htrace : WordTrace (prefixWord ++ tailWord_7815491) baseStart_7815491 baseEnd_7815491 := by
    simpa [prefixWord, tailWord_7815491, baseEnd_7815491] using wordTrace_append hprefix tailTrace_7815491
  have hstable : (prefixWord ++ tailWord_7815491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7815491).length < 2 ^ (prefixWord ++ tailWord_7815491).sum := by decide
  have hdescent : baseEnd_7815491 < baseStart_7815491 := by decide
  rcases family_descends (prefixWord ++ tailWord_7815491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7815532 : List Nat := [2, 2, 1, 1, 6, 1, 1, 4, 1, 1, 3]
def baseStart_7815532 : Nat := 118140960795 + 7815532 * 2 ^ 59
def prefixEnd_7815532 : Nat := 4983230072969 + 3 ^ 40 * 7815532 * 2
def baseEnd_7815532 : Nat := 4013124486595220928807029

theorem tailTrace_7815532 : CollatzResearch.WordTrace tailWord_7815532 prefixEnd_7815532 4013124486595220928807029 := by
  unfold tailWord_7815532
  simp only [CollatzResearch.WordTrace]
  refine ⟨142527935160834912721460425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190037246881113216961947233 142527935160834912721460425)
  ·
    refine ⟨106895951370626184541095319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142527935160834912721460425 106895951370626184541095319)
    ·
      refine ⟨160343927055939276811642979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106895951370626184541095319 160343927055939276811642979)
      ·
        refine ⟨240515890583908915217464469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160343927055939276811642979 240515890583908915217464469)
        ·
          refine ⟨11274182371120730400818647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 240515890583908915217464469 11274182371120730400818647)
          ·
            refine ⟨16911273556681095601227971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11274182371120730400818647 16911273556681095601227971)
            ·
              refine ⟨25366910335021643401841957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16911273556681095601227971 25366910335021643401841957)
              ·
                refine ⟨4756295687816558137845367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25366910335021643401841957 4756295687816558137845367)
                ·
                  refine ⟨7134443531724837206768051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4756295687816558137845367 7134443531724837206768051)
                  ·
                    refine ⟨10701665297587255810152077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7134443531724837206768051 10701665297587255810152077)
                    ·
                      refine ⟨4013124486595220928807029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10701665297587255810152077 4013124486595220928807029)
                      ·
                        rfl

theorem cell23_7815532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 1, 4, 1, 1, 3].length) (baseStart_7815532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7815532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7815532 prefixEnd_7815532 := by exact prefixLift 7815532
  have htrace : WordTrace (prefixWord ++ tailWord_7815532) baseStart_7815532 baseEnd_7815532 := by
    simpa [prefixWord, tailWord_7815532, baseEnd_7815532] using wordTrace_append hprefix tailTrace_7815532
  have hstable : (prefixWord ++ tailWord_7815532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7815532).length < 2 ^ (prefixWord ++ tailWord_7815532).sum := by decide
  have hdescent : baseEnd_7815532 < baseStart_7815532 := by decide
  rcases family_descends (prefixWord ++ tailWord_7815532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7815575 : List Nat := [1, 1, 3, 3, 1, 1, 6, 1, 1, 2, 3]
def baseStart_7815575 : Nat := 118140960795 + 7815575 * 2 ^ 59
def prefixEnd_7815575 : Nat := 4983230072969 + 3 ^ 40 * 7815575 * 2
def baseEnd_7815575 : Nat := 4013146566263364260569331

theorem tailTrace_7815575 : CollatzResearch.WordTrace tailWord_7815575 prefixEnd_7815575 4013146566263364260569331 := by
  unfold tailWord_7815575
  simp only [CollatzResearch.WordTrace]
  refine ⟨285057438660514043786736179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190038292440342695857824119 285057438660514043786736179)
  ·
    refine ⟨427586157990771065680104269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285057438660514043786736179 427586157990771065680104269)
    ·
      refine ⟨160344809246539149630039101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 427586157990771065680104269 160344809246539149630039101)
      ·
        refine ⟨60129303467452181111264663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 160344809246539149630039101 60129303467452181111264663)
        ·
          refine ⟨90193955201178271666896995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60129303467452181111264663 90193955201178271666896995)
          ·
            refine ⟨135290932801767407500345493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90193955201178271666896995 135290932801767407500345493)
            ·
              refine ⟨6341762475082847226578695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 135290932801767407500345493 6341762475082847226578695)
              ·
                refine ⟨9512643712624270839868043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6341762475082847226578695 9512643712624270839868043)
                ·
                  refine ⟨14268965568936406259802065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9512643712624270839868043 14268965568936406259802065)
                  ·
                    refine ⟨10701724176702304694851549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14268965568936406259802065 10701724176702304694851549)
                    ·
                      refine ⟨4013146566263364260569331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10701724176702304694851549 4013146566263364260569331)
                      ·
                        rfl

theorem cell23_7815575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 6, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 6, 1, 1, 2, 3].length) (baseStart_7815575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7815575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7815575 prefixEnd_7815575 := by exact prefixLift 7815575
  have htrace : WordTrace (prefixWord ++ tailWord_7815575) baseStart_7815575 baseEnd_7815575 := by
    simpa [prefixWord, tailWord_7815575, baseEnd_7815575] using wordTrace_append hprefix tailTrace_7815575
  have hstable : (prefixWord ++ tailWord_7815575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7815575).length < 2 ^ (prefixWord ++ tailWord_7815575).sum := by decide
  have hdescent : baseEnd_7815575 < baseStart_7815575 := by decide
  rcases family_descends (prefixWord ++ tailWord_7815575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7815582 : List Nat := [4, 3, 1, 2, 1, 1, 3, 2, 2, 4]
def baseStart_7815582 : Nat := 118140960795 + 7815582 * 2 ^ 59
def prefixEnd_7815582 : Nat := 4983230072969 + 3 ^ 40 * 7815582 * 2
def baseEnd_7815582 : Nat := 1337716720209315244393933

theorem tailTrace_7815582 : CollatzResearch.WordTrace tailWord_7815582 prefixEnd_7815582 1337716720209315244393933 := by
  unfold tailWord_7815582
  simp only [CollatzResearch.WordTrace]
  refine ⟨35632211746436085497780125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 190038462647659122654827333 35632211746436085497780125)
  ·
    refine ⟨13362079404913532061667547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35632211746436085497780125 13362079404913532061667547)
    ·
      refine ⟨20043119107370298092501321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13362079404913532061667547 20043119107370298092501321)
      ·
        refine ⟨15032339330527723569375991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20043119107370298092501321 15032339330527723569375991)
        ·
          refine ⟨22548508995791585354063987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15032339330527723569375991 22548508995791585354063987)
          ·
            refine ⟨33822763493687378031095981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22548508995791585354063987 33822763493687378031095981)
            ·
              refine ⟨12683536310132766761660993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33822763493687378031095981 12683536310132766761660993)
              ·
                refine ⟨9512652232599575071245745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12683536310132766761660993 9512652232599575071245745)
                ·
                  refine ⟨7134489174449681303434309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9512652232599575071245745 7134489174449681303434309)
                  ·
                    refine ⟨1337716720209315244393933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7134489174449681303434309 1337716720209315244393933)
                    ·
                      rfl

theorem cell23_7815582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 3, 2, 2, 4].length) (baseStart_7815582 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7815582 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7815582 prefixEnd_7815582 := by exact prefixLift 7815582
  have htrace : WordTrace (prefixWord ++ tailWord_7815582) baseStart_7815582 baseEnd_7815582 := by
    simpa [prefixWord, tailWord_7815582, baseEnd_7815582] using wordTrace_append hprefix tailTrace_7815582
  have hstable : (prefixWord ++ tailWord_7815582).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7815582).length < 2 ^ (prefixWord ++ tailWord_7815582).sum := by decide
  have hdescent : baseEnd_7815582 < baseStart_7815582 := by decide
  rcases family_descends (prefixWord ++ tailWord_7815582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7815631 : List Nat := [1, 1, 2, 1, 1, 4, 1, 2, 1, 6, 3]
def baseStart_7815631 : Nat := 118140960795 + 7815631 * 2 ^ 59
def prefixEnd_7815631 : Nat := 4983230072969 + 3 ^ 40 * 7815631 * 2
def baseEnd_7815631 : Nat := 4013175321180016041469073

theorem tailTrace_7815631 : CollatzResearch.WordTrace tailWord_7815631 prefixEnd_7815631 4013175321180016041469073 := by
  unfold tailWord_7815631
  simp only [CollatzResearch.WordTrace]
  refine ⟨285059481148311165350774747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190039654098874110233849831 285059481148311165350774747)
  ·
    refine ⟨427589221722466748026162121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285059481148311165350774747 427589221722466748026162121)
    ·
      refine ⟨320691916291850061019621591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 427589221722466748026162121 320691916291850061019621591)
      ·
        refine ⟨481037874437775091529432387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 320691916291850061019621591 481037874437775091529432387)
        ·
          refine ⟨721556811656662637294148581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 481037874437775091529432387 721556811656662637294148581)
          ·
            refine ⟨135291902185624244492652859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 721556811656662637294148581 135291902185624244492652859)
            ·
              refine ⟨202937853278436366738979289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 135291902185624244492652859 202937853278436366738979289)
              ·
                refine ⟨152203389958827275054234467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 202937853278436366738979289 152203389958827275054234467)
                ·
                  refine ⟨228305084938240912581351701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 152203389958827275054234467 228305084938240912581351701)
                  ·
                    refine ⟨10701800856480042777250861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 228305084938240912581351701 10701800856480042777250861)
                    ·
                      refine ⟨4013175321180016041469073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10701800856480042777250861 4013175321180016041469073)
                      ·
                        rfl

theorem cell23_7815631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 2, 1, 6, 3].length) (baseStart_7815631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7815631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7815631 prefixEnd_7815631 := by exact prefixLift 7815631
  have htrace : WordTrace (prefixWord ++ tailWord_7815631) baseStart_7815631 baseEnd_7815631 := by
    simpa [prefixWord, tailWord_7815631, baseEnd_7815631] using wordTrace_append hprefix tailTrace_7815631
  have hstable : (prefixWord ++ tailWord_7815631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7815631).length < 2 ^ (prefixWord ++ tailWord_7815631).sum := by decide
  have hdescent : baseEnd_7815631 < baseStart_7815631 := by decide
  rcases family_descends (prefixWord ++ tailWord_7815631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7815666 : List Nat := [3, 2, 1, 4, 3, 1, 1, 2, 1, 3, 2]
def baseStart_7815666 : Nat := 118140960795 + 7815666 * 2 ^ 59
def prefixEnd_7815666 : Nat := 4983230072969 + 3 ^ 40 * 7815666 * 2
def baseEnd_7815666 : Nat := 4013193293002923404531413

theorem tailTrace_7815666 : CollatzResearch.WordTrace tailWord_7815666 prefixEnd_7815666 4013193293002923404531413 := by
  unfold tailWord_7815666
  simp only [CollatzResearch.WordTrace]
  refine ⟨71265189425796091582074713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 190040505135456244218865901 71265189425796091582074713)
  ·
    refine ⟨53448892069347068686556035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71265189425796091582074713 53448892069347068686556035)
    ·
      refine ⟨80173338104020603029834053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53448892069347068686556035 80173338104020603029834053)
      ·
        refine ⟨15032500894503863068093885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 80173338104020603029834053 15032500894503863068093885)
        ·
          refine ⟨5637187835438948650535207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15032500894503863068093885 5637187835438948650535207)
          ·
            refine ⟨8455781753158422975802811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5637187835438948650535207 8455781753158422975802811)
            ·
              refine ⟨12683672629737634463704217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8455781753158422975802811 12683672629737634463704217)
              ·
                refine ⟨9512754472303225847778163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12683672629737634463704217 9512754472303225847778163)
                ·
                  refine ⟨14269131708454838771667245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9512754472303225847778163 14269131708454838771667245)
                  ·
                    refine ⟨5350924390670564539375217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14269131708454838771667245 5350924390670564539375217)
                    ·
                      refine ⟨4013193293002923404531413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5350924390670564539375217 4013193293002923404531413)
                      ·
                        rfl

theorem cell23_7815666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 3, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 3, 1, 1, 2, 1, 3, 2].length) (baseStart_7815666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7815666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7815666 prefixEnd_7815666 := by exact prefixLift 7815666
  have htrace : WordTrace (prefixWord ++ tailWord_7815666) baseStart_7815666 baseEnd_7815666 := by
    simpa [prefixWord, tailWord_7815666, baseEnd_7815666] using wordTrace_append hprefix tailTrace_7815666
  have hstable : (prefixWord ++ tailWord_7815666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7815666).length < 2 ^ (prefixWord ++ tailWord_7815666).sum := by decide
  have hdescent : baseEnd_7815666 < baseStart_7815666 := by decide
  rcases family_descends (prefixWord ++ tailWord_7815666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7815708 : List Nat := [2, 2, 3, 1, 2, 2, 2, 1, 1, 2, 5]
def baseStart_7815708 : Nat := 118140960795 + 7815708 * 2 ^ 59
def prefixEnd_7815708 : Nat := 4983230072969 + 3 ^ 40 * 7815708 * 2
def baseEnd_7815708 : Nat := 4013214859190412240206219

theorem tailTrace_7815708 : CollatzResearch.WordTrace tailWord_7815708 prefixEnd_7815708 4013214859190412240206219 := by
  unfold tailWord_7815708
  simp only [CollatzResearch.WordTrace]
  refine ⟨142531144784516103750663889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190041526379354805000885185 142531144784516103750663889)
  ·
    refine ⟨106898358588387077812997917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142531144784516103750663889 106898358588387077812997917)
    ·
      refine ⟨40086884470645154179874219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 106898358588387077812997917 40086884470645154179874219)
      ·
        refine ⟨60130326705967731269811329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40086884470645154179874219 60130326705967731269811329)
        ·
          refine ⟨45097745029475798452358497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60130326705967731269811329 45097745029475798452358497)
          ·
            refine ⟨33823308772106848839268873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45097745029475798452358497 33823308772106848839268873)
            ·
              refine ⟨25367481579080136629451655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33823308772106848839268873 25367481579080136629451655)
              ·
                refine ⟨38051222368620204944177483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25367481579080136629451655 38051222368620204944177483)
                ·
                  refine ⟨57076833552930307416266225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38051222368620204944177483 57076833552930307416266225)
                  ·
                    refine ⟨42807625164697730562199669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 57076833552930307416266225 42807625164697730562199669)
                    ·
                      refine ⟨4013214859190412240206219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42807625164697730562199669 4013214859190412240206219)
                      ·
                        rfl

theorem cell23_7815708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 2, 1, 1, 2, 5].length) (baseStart_7815708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7815708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7815708 prefixEnd_7815708 := by exact prefixLift 7815708
  have htrace : WordTrace (prefixWord ++ tailWord_7815708) baseStart_7815708 baseEnd_7815708 := by
    simpa [prefixWord, tailWord_7815708, baseEnd_7815708] using wordTrace_append hprefix tailTrace_7815708
  have hstable : (prefixWord ++ tailWord_7815708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7815708).length < 2 ^ (prefixWord ++ tailWord_7815708).sum := by decide
  have hdescent : baseEnd_7815708 < baseStart_7815708 := by decide
  rcases family_descends (prefixWord ++ tailWord_7815708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7815711 : List Nat := [1, 1, 2, 4, 1, 1, 1, 2, 2, 8]
def baseStart_7815711 : Nat := 118140960795 + 7815711 * 2 ^ 59
def prefixEnd_7815711 : Nat := 4983230072969 + 3 ^ 40 * 7815711 * 2
def baseEnd_7815711 : Nat := 1337738799877458576156235

theorem tailTrace_7815711 : CollatzResearch.WordTrace tailWord_7815711 prefixEnd_7815711 1337738799877458576156235 := by
  unfold tailWord_7815711
  simp only [CollatzResearch.WordTrace]
  refine ⟨285062398988021339013686987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190041599325347559342457991 285062398988021339013686987)
  ·
    refine ⟨427593598482032008520530481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285062398988021339013686987 427593598482032008520530481)
    ·
      refine ⟨320695198861524006390397861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 427593598482032008520530481 320695198861524006390397861)
      ·
        refine ⟨60130349786535751198199599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 320695198861524006390397861 60130349786535751198199599)
        ·
          refine ⟨90195524679803626797299399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60130349786535751198199599 90195524679803626797299399)
          ·
            refine ⟨135293287019705440195949099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90195524679803626797299399 135293287019705440195949099)
            ·
              refine ⟨202939930529558160293923649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 135293287019705440195949099 202939930529558160293923649)
              ·
                refine ⟨152204947897168620220442737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 202939930529558160293923649 152204947897168620220442737)
                ·
                  refine ⟨114153710922876465165332053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 152204947897168620220442737 114153710922876465165332053)
                  ·
                    refine ⟨1337738799877458576156235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 114153710922876465165332053 1337738799877458576156235)
                    ·
                      rfl

theorem cell23_7815711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 2, 2, 8].length) (baseStart_7815711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7815711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7815711 prefixEnd_7815711 := by exact prefixLift 7815711
  have htrace : WordTrace (prefixWord ++ tailWord_7815711) baseStart_7815711 baseEnd_7815711 := by
    simpa [prefixWord, tailWord_7815711, baseEnd_7815711] using wordTrace_append hprefix tailTrace_7815711
  have hstable : (prefixWord ++ tailWord_7815711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7815711).length < 2 ^ (prefixWord ++ tailWord_7815711).sum := by decide
  have hdescent : baseEnd_7815711 < baseStart_7815711 := by decide
  rcases family_descends (prefixWord ++ tailWord_7815711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7815728 : List Nat := [2, 1, 1, 1, 2, 3, 3, 1, 5, 4]
def baseStart_7815728 : Nat := 118140960795 + 7815728 * 2 ^ 59
def prefixEnd_7815728 : Nat := 4983230072969 + 3 ^ 40 * 7815728 * 2
def baseEnd_7815728 : Nat := 1337741709601167387318709

theorem tailTrace_7815728 : CollatzResearch.WordTrace tailWord_7815728 prefixEnd_7815728 1337741709601167387318709 := by
  unfold tailWord_7815728
  simp only [CollatzResearch.WordTrace]
  refine ⟨142531509514479875458527919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190042012685973167278037225 142531509514479875458527919)
  ·
    refine ⟨213797264271719813187791879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142531509514479875458527919 213797264271719813187791879)
    ·
      refine ⟨320695896407579719781687819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213797264271719813187791879 320695896407579719781687819)
      ·
        refine ⟨481043844611369579672531729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 320695896407579719781687819 481043844611369579672531729)
        ·
          refine ⟨360782883458527184754398797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 481043844611369579672531729 360782883458527184754398797)
          ·
            refine ⟨135293581296947694282899549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 360782883458527184754398797 135293581296947694282899549)
            ·
              refine ⟨50735092986355385356087331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 135293581296947694282899549 50735092986355385356087331)
              ·
                refine ⟨76102639479533078034130997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50735092986355385356087331 76102639479533078034130997)
                ·
                  refine ⟨7134622451206226065699781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 76102639479533078034130997 7134622451206226065699781)
                  ·
                    refine ⟨1337741709601167387318709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7134622451206226065699781 1337741709601167387318709)
                    ·
                      rfl

theorem cell23_7815728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 3, 1, 5, 4].length) (baseStart_7815728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7815728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7815728 prefixEnd_7815728 := by exact prefixLift 7815728
  have htrace : WordTrace (prefixWord ++ tailWord_7815728) baseStart_7815728 baseEnd_7815728 := by
    simpa [prefixWord, tailWord_7815728, baseEnd_7815728] using wordTrace_append hprefix tailTrace_7815728
  have hstable : (prefixWord ++ tailWord_7815728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7815728).length < 2 ^ (prefixWord ++ tailWord_7815728).sum := by decide
  have hdescent : baseEnd_7815728 < baseStart_7815728 := by decide
  rcases family_descends (prefixWord ++ tailWord_7815728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7815732 : List Nat := [2, 5, 1, 3, 1, 1, 1, 1, 1, 7]
def baseStart_7815732 : Nat := 118140960795 + 7815732 * 2 ^ 59
def prefixEnd_7815732 : Nat := 4983230072969 + 3 ^ 40 * 7815732 * 2
def baseEnd_7815732 : Nat := 1337742394242040048768703

theorem tailTrace_7815732 : CollatzResearch.WordTrace tailWord_7815732 prefixEnd_7815732 1337742394242040048768703 := by
  unfold tailWord_7815732
  simp only [CollatzResearch.WordTrace]
  refine ⟨142531582460472629800100725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190042109947296839733467633 142531582460472629800100725)
  ·
    refine ⟨13362335855669309043759443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 142531582460472629800100725 13362335855669309043759443)
    ·
      refine ⟨20043503783503963565639165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13362335855669309043759443 20043503783503963565639165)
      ·
        refine ⟨7516313918813986337114687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20043503783503963565639165 7516313918813986337114687)
        ·
          refine ⟨11274470878220979505672031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7516313918813986337114687 11274470878220979505672031)
          ·
            refine ⟨16911706317331469258508047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11274470878220979505672031 16911706317331469258508047)
            ·
              refine ⟨25367559475997203887762071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16911706317331469258508047 25367559475997203887762071)
              ·
                refine ⟨38051339213995805831643107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25367559475997203887762071 38051339213995805831643107)
                ·
                  refine ⟨57077008820993708747464661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38051339213995805831643107 57077008820993708747464661)
                  ·
                    refine ⟨1337742394242040048768703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 57077008820993708747464661 1337742394242040048768703)
                    ·
                      rfl

theorem cell23_7815732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 1, 1, 1, 7].length) (baseStart_7815732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7815732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7815732 prefixEnd_7815732 := by exact prefixLift 7815732
  have htrace : WordTrace (prefixWord ++ tailWord_7815732) baseStart_7815732 baseEnd_7815732 := by
    simpa [prefixWord, tailWord_7815732, baseEnd_7815732] using wordTrace_append hprefix tailTrace_7815732
  have hstable : (prefixWord ++ tailWord_7815732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7815732).length < 2 ^ (prefixWord ++ tailWord_7815732).sum := by decide
  have hdescent : baseEnd_7815732 < baseStart_7815732 := by decide
  rcases family_descends (prefixWord ++ tailWord_7815732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7815762 : List Nat := [3, 2, 2, 1, 2, 1, 1, 6, 1, 4]
def baseStart_7815762 : Nat := 118140960795 + 7815762 * 2 ^ 59
def prefixEnd_7815762 : Nat := 4983230072969 + 3 ^ 40 * 7815762 * 2
def baseEnd_7815762 : Nat := 1337747529048585009643657

theorem tailTrace_7815762 : CollatzResearch.WordTrace tailWord_7815762 prefixEnd_7815762 1337747529048585009643657 := by
  unfold tailWord_7815762
  simp only [CollatzResearch.WordTrace]
  refine ⟨71266064777709143680948385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 190042839407224383149195693 71266064777709143680948385)
  ·
    refine ⟨53449548583281857760711289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71266064777709143680948385 53449548583281857760711289)
    ·
      refine ⟨40087161437461393320533467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53449548583281857760711289 40087161437461393320533467)
      ·
        refine ⟨60130742156192089980800201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40087161437461393320533467 60130742156192089980800201)
        ·
          refine ⟨45098056617144067485600151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60130742156192089980800201 45098056617144067485600151)
          ·
            refine ⟨67647084925716101228400227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45098056617144067485600151 67647084925716101228400227)
            ·
              refine ⟨101470627388574151842600341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67647084925716101228400227 101470627388574151842600341)
              ·
                refine ⟨4756435658839413367621891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 101470627388574151842600341 4756435658839413367621891)
                ·
                  refine ⟨7134653488259120051432837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4756435658839413367621891 7134653488259120051432837)
                  ·
                    refine ⟨1337747529048585009643657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7134653488259120051432837 1337747529048585009643657)
                    ·
                      rfl

theorem cell23_7815762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 6, 1, 4].length) (baseStart_7815762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7815762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7815762 prefixEnd_7815762 := by exact prefixLift 7815762
  have htrace : WordTrace (prefixWord ++ tailWord_7815762) baseStart_7815762 baseEnd_7815762 := by
    simpa [prefixWord, tailWord_7815762, baseEnd_7815762] using wordTrace_append hprefix tailTrace_7815762
  have hstable : (prefixWord ++ tailWord_7815762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7815762).length < 2 ^ (prefixWord ++ tailWord_7815762).sum := by decide
  have hdescent : baseEnd_7815762 < baseStart_7815762 := by decide
  rcases family_descends (prefixWord ++ tailWord_7815762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7815788 : List Nat := [2, 2, 1, 1, 3, 1, 2, 3, 3, 5]
def baseStart_7815788 : Nat := 118140960795 + 7815788 * 2 ^ 59
def prefixEnd_7815788 : Nat := 4983230072969 + 3 ^ 40 * 7815788 * 2
def baseEnd_7815788 : Nat := 1337751979214257309068617

theorem tailTrace_7815788 : CollatzResearch.WordTrace tailWord_7815788 prefixEnd_7815788 1337751979214257309068617 := by
  unfold tailWord_7815788
  simp only [CollatzResearch.WordTrace]
  refine ⟨142532603704371190582120009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190043471605828254109493345 142532603704371190582120009)
  ·
    refine ⟨106899452778278392936590007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142532603704371190582120009 106899452778278392936590007)
    ·
      refine ⟨160349179167417589404885011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106899452778278392936590007 160349179167417589404885011)
      ·
        refine ⟨240523768751126384107327517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160349179167417589404885011 240523768751126384107327517)
        ·
          refine ⟨90196413281672394040247819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 240523768751126384107327517 90196413281672394040247819)
          ·
            refine ⟨135294619922508591060371729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90196413281672394040247819 135294619922508591060371729)
            ·
              refine ⟨101470964941881443295278797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 135294619922508591060371729 101470964941881443295278797)
              ·
                refine ⟨38051611853205541235729549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 101470964941881443295278797 38051611853205541235729549)
                ·
                  refine ⟨14269354444952077963398581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38051611853205541235729549 14269354444952077963398581)
                  ·
                    refine ⟨1337751979214257309068617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14269354444952077963398581 1337751979214257309068617)
                    ·
                      rfl

theorem cell23_7815788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 5].length) (baseStart_7815788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7815788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7815788 prefixEnd_7815788 := by exact prefixLift 7815788
  have htrace : WordTrace (prefixWord ++ tailWord_7815788) baseStart_7815788 baseEnd_7815788 := by
    simpa [prefixWord, tailWord_7815788, baseEnd_7815788] using wordTrace_append hprefix tailTrace_7815788
  have hstable : (prefixWord ++ tailWord_7815788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7815788).length < 2 ^ (prefixWord ++ tailWord_7815788).sum := by decide
  have hdescent : baseEnd_7815788 < baseStart_7815788 := by decide
  rcases family_descends (prefixWord ++ tailWord_7815788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7815812 : List Nat := [2, 3, 2, 1, 3, 1, 1, 1, 4, 3, 2]
def baseStart_7815812 : Nat := 118140960795 + 7815812 * 2 ^ 59
def prefixEnd_7815812 : Nat := 4983230072969 + 3 ^ 40 * 7815812 * 2
def baseEnd_7815812 : Nat := 4013268261178479833305741

theorem tailTrace_7815812 : CollatzResearch.WordTrace tailWord_7815812 prefixEnd_7815812 4013268261178479833305741 := by
  unfold tailWord_7815812
  simp only [CollatzResearch.WordTrace]
  refine ⟨142533041380327716631556845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190044055173770288842075793 142533041380327716631556845)
  ·
    refine ⟨53449890517622893736833817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 142533041380327716631556845 53449890517622893736833817)
    ·
      refine ⟨40087417888217170302625363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53449890517622893736833817 40087417888217170302625363)
      ·
        refine ⟨60131126832325755453938045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40087417888217170302625363 60131126832325755453938045)
        ·
          refine ⟨22549172562122158295226767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60131126832325755453938045 22549172562122158295226767)
          ·
            refine ⟨33823758843183237442840151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22549172562122158295226767 33823758843183237442840151)
            ·
              refine ⟨50735638264774856164260227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33823758843183237442840151 50735638264774856164260227)
              ·
                refine ⟨76103457397162284246390341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50735638264774856164260227 76103457397162284246390341)
                ·
                  refine ⟨14269398261967928296198189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 76103457397162284246390341 14269398261967928296198189)
                  ·
                    refine ⟨5351024348237973111074321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14269398261967928296198189 5351024348237973111074321)
                    ·
                      refine ⟨4013268261178479833305741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5351024348237973111074321 4013268261178479833305741)
                      ·
                        rfl

theorem cell23_7815812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 1, 1, 4, 3, 2].length) (baseStart_7815812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7815812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7815812 prefixEnd_7815812 := by exact prefixLift 7815812
  have htrace : WordTrace (prefixWord ++ tailWord_7815812) baseStart_7815812 baseEnd_7815812 := by
    simpa [prefixWord, tailWord_7815812, baseEnd_7815812] using wordTrace_append hprefix tailTrace_7815812
  have hstable : (prefixWord ++ tailWord_7815812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7815812).length < 2 ^ (prefixWord ++ tailWord_7815812).sum := by decide
  have hdescent : baseEnd_7815812 < baseStart_7815812 := by decide
  rcases family_descends (prefixWord ++ tailWord_7815812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7815855 : List Nat := [1, 1, 2, 1, 2, 6, 1, 2, 1, 2, 4]
def baseStart_7815855 : Nat := 118140960795 + 7815855 * 2 ^ 59
def prefixEnd_7815855 : Nat := 4983230072969 + 3 ^ 40 * 7815855 * 2
def baseEnd_7815855 : Nat := 4013290340846623165068043

theorem tailTrace_7815855 : CollatzResearch.WordTrace tailWord_7815855 prefixEnd_7815855 4013290340846623165068043 := by
  unfold tailWord_7815855
  simp only [CollatzResearch.WordTrace]
  refine ⟨285067651099499651606929019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190045100732999767737952679 285067651099499651606929019)
  ·
    refine ⟨427601476649249477410393529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285067651099499651606929019 427601476649249477410393529)
    ·
      refine ⟨320701107486937108057795147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 427601476649249477410393529 320701107486937108057795147)
      ·
        refine ⟨481051661230405662086692721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 320701107486937108057795147 481051661230405662086692721)
        ·
          refine ⟨360788745922804246565019541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 481051661230405662086692721 360788745922804246565019541)
          ·
            refine ⟨16911972465131449057735291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 360788745922804246565019541 16911972465131449057735291)
            ·
              refine ⟨25367958697697173586602937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16911972465131449057735291 25367958697697173586602937)
              ·
                refine ⟨19025969023272880189952203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25367958697697173586602937 19025969023272880189952203)
                ·
                  refine ⟨28538953534909320284928305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19025969023272880189952203 28538953534909320284928305)
                  ·
                    refine ⟨21404215151181990213696229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28538953534909320284928305 21404215151181990213696229)
                    ·
                      refine ⟨4013290340846623165068043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21404215151181990213696229 4013290340846623165068043)
                      ·
                        rfl

theorem cell23_7815855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 1, 2, 1, 2, 4].length) (baseStart_7815855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7815855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7815855 prefixEnd_7815855 := by exact prefixLift 7815855
  have htrace : WordTrace (prefixWord ++ tailWord_7815855) baseStart_7815855 baseEnd_7815855 := by
    simpa [prefixWord, tailWord_7815855, baseEnd_7815855] using wordTrace_append hprefix tailTrace_7815855
  have hstable : (prefixWord ++ tailWord_7815855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7815855).length < 2 ^ (prefixWord ++ tailWord_7815855).sum := by decide
  have hdescent : baseEnd_7815855 < baseStart_7815855 := by decide
  rcases family_descends (prefixWord ++ tailWord_7815855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7815919 : List Nat := [1, 1, 2, 1, 5, 3, 1, 3, 1, 3, 2]
def baseStart_7815919 : Nat := 118140960795 + 7815919 * 2 ^ 59
def prefixEnd_7815919 : Nat := 4983230072969 + 3 ^ 40 * 7815919 * 2
def baseEnd_7815919 : Nat := 4013323203608510914667749

theorem tailTrace_7815919 : CollatzResearch.WordTrace tailWord_7815919 prefixEnd_7815919 4013323203608510914667749 := by
  unfold tailWord_7815919
  simp only [CollatzResearch.WordTrace]
  refine ⟨285069985371267790537258811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190046656914178527024839207 285069985371267790537258811)
  ·
    refine ⟨427604978056901685805888217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285069985371267790537258811 427604978056901685805888217)
    ·
      refine ⟨320703733542676264354416163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 427604978056901685805888217 320703733542676264354416163)
      ·
        refine ⟨481055600314014396531624245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 320703733542676264354416163 481055600314014396531624245)
        ·
          refine ⟨45098962529438849674839773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 481055600314014396531624245 45098962529438849674839773)
          ·
            refine ⟨16912110948539568628064915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45098962529438849674839773 16912110948539568628064915)
            ·
              refine ⟨25368166422809352942097373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16912110948539568628064915 25368166422809352942097373)
              ·
                refine ⟨9513062408553507353286515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25368166422809352942097373 9513062408553507353286515)
                ·
                  refine ⟨14269593612830261029929773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9513062408553507353286515 14269593612830261029929773)
                  ·
                    refine ⟨5351097604811347886223665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14269593612830261029929773 5351097604811347886223665)
                    ·
                      refine ⟨4013323203608510914667749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5351097604811347886223665 4013323203608510914667749)
                      ·
                        rfl

theorem cell23_7815919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 1, 3, 1, 3, 2].length) (baseStart_7815919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7815919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7815919 prefixEnd_7815919 := by exact prefixLift 7815919
  have htrace : WordTrace (prefixWord ++ tailWord_7815919) baseStart_7815919 baseEnd_7815919 := by
    simpa [prefixWord, tailWord_7815919, baseEnd_7815919] using wordTrace_append hprefix tailTrace_7815919
  have hstable : (prefixWord ++ tailWord_7815919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7815919).length < 2 ^ (prefixWord ++ tailWord_7815919).sum := by decide
  have hdescent : baseEnd_7815919 < baseStart_7815919 := by decide
  rcases family_descends (prefixWord ++ tailWord_7815919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7815945 : List Nat := [1, 2, 1, 1, 3, 2, 4, 1, 2, 2, 4]
def baseStart_7815945 : Nat := 118140960795 + 7815945 * 2 ^ 59
def prefixEnd_7815945 : Nat := 4983230072969 + 3 ^ 40 * 7815945 * 2
def baseEnd_7815945 : Nat := 4013336554105527812942629

theorem tailTrace_7815945 : CollatzResearch.WordTrace tailWord_7815945 prefixEnd_7815945 4013336554105527812942629 := by
  unfold tailWord_7815945
  simp only [CollatzResearch.WordTrace]
  refine ⟨285070933669173596977705289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190047289112782397985136859 285070933669173596977705289)
  ·
    refine ⟨213803200251880197733278967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 285070933669173596977705289 213803200251880197733278967)
    ·
      refine ⟨320704800377820296599918451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213803200251880197733278967 320704800377820296599918451)
      ·
        refine ⟨481057200566730444899877677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 320704800377820296599918451 481057200566730444899877677)
        ·
          refine ⟨180396450212523916837454129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 481057200566730444899877677 180396450212523916837454129)
          ·
            refine ⟨135297337659392937628090597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 180396450212523916837454129 135297337659392937628090597)
            ·
              refine ⟨25368250811136175805266987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 135297337659392937628090597 25368250811136175805266987)
              ·
                refine ⟨38052376216704263707900481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25368250811136175805266987 38052376216704263707900481)
                ·
                  refine ⟨28539282162528197780925361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38052376216704263707900481 28539282162528197780925361)
                  ·
                    refine ⟨21404461621896148335694021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28539282162528197780925361 21404461621896148335694021)
                    ·
                      refine ⟨4013336554105527812942629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21404461621896148335694021 4013336554105527812942629)
                      ·
                        rfl

theorem cell23_7815945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 4, 1, 2, 2, 4].length) (baseStart_7815945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7815945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7815945 prefixEnd_7815945 := by exact prefixLift 7815945
  have htrace : WordTrace (prefixWord ++ tailWord_7815945) baseStart_7815945 baseEnd_7815945 := by
    simpa [prefixWord, tailWord_7815945, baseEnd_7815945] using wordTrace_append hprefix tailTrace_7815945
  have hstable : (prefixWord ++ tailWord_7815945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7815945).length < 2 ^ (prefixWord ++ tailWord_7815945).sum := by decide
  have hdescent : baseEnd_7815945 < baseStart_7815945 := by decide
  rcases family_descends (prefixWord ++ tailWord_7815945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7815992 : List Nat := [2, 1, 2, 1, 3, 2, 2, 1, 2, 5, 2]
def baseStart_7815992 : Nat := 118140960795 + 7815992 * 2 ^ 59
def prefixEnd_7815992 : Nat := 4983230072969 + 3 ^ 40 * 7815992 * 2
def baseEnd_7815992 : Nat := 4013360687696289129054913

theorem tailTrace_7815992 : CollatzResearch.WordTrace tailWord_7815992 prefixEnd_7815992 4013360687696289129054913 := by
  unfold tailWord_7815992
  simp only [CollatzResearch.WordTrace]
  refine ⟨142536323950001662002333115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190048431933335549336444153 142536323950001662002333115)
  ·
    refine ⟨213804485925002493003499673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142536323950001662002333115 213804485925002493003499673)
    ·
      refine ⟨160353364443751869752624755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 213804485925002493003499673 160353364443751869752624755)
      ·
        refine ⟨240530046665627804628937133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160353364443751869752624755 240530046665627804628937133)
        ·
          refine ⟨90198767499610426735851425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 240530046665627804628937133 90198767499610426735851425)
          ·
            refine ⟨67649075624707820051888569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90198767499610426735851425 67649075624707820051888569)
            ·
              refine ⟨50736806718530865038916427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67649075624707820051888569 50736806718530865038916427)
              ·
                refine ⟨76105210077796297558374641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50736806718530865038916427 76105210077796297558374641)
                ·
                  refine ⟨57078907558347223168780981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 76105210077796297558374641 57078907558347223168780981)
                  ·
                    refine ⟨5351147583595052172073217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 57078907558347223168780981 5351147583595052172073217)
                    ·
                      refine ⟨4013360687696289129054913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5351147583595052172073217 4013360687696289129054913)
                      ·
                        rfl

theorem cell23_7815992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 2, 1, 2, 5, 2].length) (baseStart_7815992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7815992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7815992 prefixEnd_7815992 := by exact prefixLift 7815992
  have htrace : WordTrace (prefixWord ++ tailWord_7815992) baseStart_7815992 baseEnd_7815992 := by
    simpa [prefixWord, tailWord_7815992, baseEnd_7815992] using wordTrace_append hprefix tailTrace_7815992
  have hstable : (prefixWord ++ tailWord_7815992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7815992).length < 2 ^ (prefixWord ++ tailWord_7815992).sum := by decide
  have hdescent : baseEnd_7815992 < baseStart_7815992 := by decide
  rcases family_descends (prefixWord ++ tailWord_7815992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7816005 : List Nat := [1, 3, 1, 1, 1, 2, 2, 4, 1, 3, 4]
def baseStart_7816005 : Nat := 118140960795 + 7816005 * 2 ^ 59
def prefixEnd_7816005 : Nat := 4983230072969 + 3 ^ 40 * 7816005 * 2
def baseEnd_7816005 : Nat := 4013367362944797578192353

theorem tailTrace_7816005 : CollatzResearch.WordTrace tailWord_7816005 prefixEnd_7816005 4013367362944797578192353 := by
  unfold tailWord_7816005
  simp only [CollatzResearch.WordTrace]
  refine ⟨285073122048956227224889469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190048748032637484816592979 285073122048956227224889469)
  ·
    refine ⟨106902420768358585209333551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 285073122048956227224889469 106902420768358585209333551)
    ·
      refine ⟨160353631152537877814000327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106902420768358585209333551 160353631152537877814000327)
      ·
        refine ⟨240530446728806816721000491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160353631152537877814000327 240530446728806816721000491)
        ·
          refine ⟨360795670093210225081500737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 240530446728806816721000491 360795670093210225081500737)
          ·
            refine ⟨270596752569907668811125553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 360795670093210225081500737 270596752569907668811125553)
            ·
              refine ⟨202947564427430751608344165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 270596752569907668811125553 202947564427430751608344165)
              ·
                refine ⟨38052668330143265926564531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 202947564427430751608344165 38052668330143265926564531)
                ·
                  refine ⟨57079002495214898889846797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38052668330143265926564531 57079002495214898889846797)
                  ·
                    refine ⟨21404625935705587083692549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 57079002495214898889846797 21404625935705587083692549)
                    ·
                      refine ⟨4013367362944797578192353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21404625935705587083692549 4013367362944797578192353)
                      ·
                        rfl

theorem cell23_7816005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 4, 1, 3, 4].length) (baseStart_7816005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7816005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7816005 prefixEnd_7816005 := by exact prefixLift 7816005
  have htrace : WordTrace (prefixWord ++ tailWord_7816005) baseStart_7816005 baseEnd_7816005 := by
    simpa [prefixWord, tailWord_7816005, baseEnd_7816005] using wordTrace_append hprefix tailTrace_7816005
  have hstable : (prefixWord ++ tailWord_7816005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7816005).length < 2 ^ (prefixWord ++ tailWord_7816005).sum := by decide
  have hdescent : baseEnd_7816005 < baseStart_7816005 := by decide
  rcases family_descends (prefixWord ++ tailWord_7816005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7816086 : List Nat := [5, 3, 1, 1, 1, 1, 1, 1, 2, 1, 6]
def baseStart_7816086 : Nat := 118140960795 + 7816086 * 2 ^ 59
def prefixEnd_7816086 : Nat := 4983230072969 + 3 ^ 40 * 7816086 * 2
def baseEnd_7816086 : Nat := 4013408954877811761279481

theorem tailTrace_7816086 : CollatzResearch.WordTrace tailWord_7816086 prefixEnd_7816086 4013408954877811761279481 := by
  unfold tailWord_7816086
  simp only [CollatzResearch.WordTrace]
  refine ⟨17817254772603923628661757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 190050717574441852039058741 17817254772603923628661757)
  ·
    refine ⟨6681470539726471360748159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17817254772603923628661757 6681470539726471360748159)
    ·
      refine ⟨10022205809589707041122239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6681470539726471360748159 10022205809589707041122239)
      ·
        refine ⟨15033308714384560561683359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10022205809589707041122239 15033308714384560561683359)
        ·
          refine ⟨22549963071576840842525039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15033308714384560561683359 22549963071576840842525039)
          ·
            refine ⟨33824944607365261263787559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22549963071576840842525039 33824944607365261263787559)
            ·
              refine ⟨50737416911047891895681339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33824944607365261263787559 50737416911047891895681339)
              ·
                refine ⟨76106125366571837843522009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50737416911047891895681339 76106125366571837843522009)
                ·
                  refine ⟨57079594024928878382641507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 76106125366571837843522009 57079594024928878382641507)
                  ·
                    refine ⟨85619391037393317573962261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 57079594024928878382641507 85619391037393317573962261)
                    ·
                      refine ⟨4013408954877811761279481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 85619391037393317573962261 4013408954877811761279481)
                      ·
                        rfl

theorem cell23_7816086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 1, 1, 2, 1, 6].length) (baseStart_7816086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7816086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7816086 prefixEnd_7816086 := by exact prefixLift 7816086
  have htrace : WordTrace (prefixWord ++ tailWord_7816086) baseStart_7816086 baseEnd_7816086 := by
    simpa [prefixWord, tailWord_7816086, baseEnd_7816086] using wordTrace_append hprefix tailTrace_7816086
  have hstable : (prefixWord ++ tailWord_7816086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7816086).length < 2 ^ (prefixWord ++ tailWord_7816086).sum := by decide
  have hdescent : baseEnd_7816086 < baseStart_7816086 := by decide
  rcases family_descends (prefixWord ++ tailWord_7816086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7816099 : List Nat := [1, 1, 1, 4, 1, 2, 2, 4, 2, 3, 2]
def baseStart_7816099 : Nat := 118140960795 + 7816099 * 2 ^ 59
def prefixEnd_7816099 : Nat := 4983230072969 + 3 ^ 40 * 7816099 * 2
def baseEnd_7816099 : Nat := 4013415630126320210416921

theorem tailTrace_7816099 : CollatzResearch.WordTrace tailWord_7816099 prefixEnd_7816099 4013415630126320210416921 := by
  unfold tailWord_7816099
  simp only [CollatzResearch.WordTrace]
  refine ⟨285076550510615681278811351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190051033673743787519207567 285076550510615681278811351)
  ·
    refine ⟨427614825765923521918217027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285076550510615681278811351 427614825765923521918217027)
    ·
      refine ⟨641422238648885282877325541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 427614825765923521918217027 641422238648885282877325541)
      ·
        refine ⟨120266669746665990539498539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 641422238648885282877325541 120266669746665990539498539)
        ·
          refine ⟨180400004619998985809247809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120266669746665990539498539 180400004619998985809247809)
          ·
            refine ⟨135300003464999239356935857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 180400004619998985809247809 135300003464999239356935857)
            ·
              refine ⟨101475002598749429517701893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 135300003464999239356935857 101475002598749429517701893)
              ·
                refine ⟨19026562987265518034569105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 101475002598749429517701893 19026562987265518034569105)
                ·
                  refine ⟨14269922240449138525926829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19026562987265518034569105 14269922240449138525926829)
                  ·
                    refine ⟨5351220840168426947222561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14269922240449138525926829 5351220840168426947222561)
                    ·
                      refine ⟨4013415630126320210416921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5351220840168426947222561 4013415630126320210416921)
                      ·
                        rfl

theorem cell23_7816099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 4, 2, 3, 2].length) (baseStart_7816099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7816099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7816099 prefixEnd_7816099 := by exact prefixLift 7816099
  have htrace : WordTrace (prefixWord ++ tailWord_7816099) baseStart_7816099 baseEnd_7816099 := by
    simpa [prefixWord, tailWord_7816099, baseEnd_7816099] using wordTrace_append hprefix tailTrace_7816099
  have hstable : (prefixWord ++ tailWord_7816099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7816099).length < 2 ^ (prefixWord ++ tailWord_7816099).sum := by decide
  have hdescent : baseEnd_7816099 < baseStart_7816099 := by decide
  rcases family_descends (prefixWord ++ tailWord_7816099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7816146 : List Nat := [3, 2, 2, 3, 1, 1, 2, 3, 1, 1, 4]
def baseStart_7816146 : Nat := 118140960795 + 7816146 * 2 ^ 59
def prefixEnd_7816146 : Nat := 4983230072969 + 3 ^ 40 * 7816146 * 2
def baseEnd_7816146 : Nat := 4013439763717081526529205

theorem tailTrace_7816146 : CollatzResearch.WordTrace tailWord_7816146 prefixEnd_7816146 4013439763717081526529205 := by
  unfold tailWord_7816146
  simp only [CollatzResearch.WordTrace]
  refine ⟨71269566185361352076443073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 190052176494296938870514861 71269566185361352076443073)
  ·
    refine ⟨53452174639021014057332305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71269566185361352076443073 53452174639021014057332305)
    ·
      refine ⟨40089130979265760542999229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53452174639021014057332305 40089130979265760542999229)
      ·
        refine ⟨15033424117224660203624711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40089130979265760542999229 15033424117224660203624711)
        ·
          refine ⟨22550136175836990305437067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15033424117224660203624711 22550136175836990305437067)
          ·
            refine ⟨33825204263755485458155601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22550136175836990305437067 33825204263755485458155601)
            ·
              refine ⟨25368903197816614093616701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33825204263755485458155601 25368903197816614093616701)
              ·
                refine ⟨9513338699181230285106263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25368903197816614093616701 9513338699181230285106263)
                ·
                  refine ⟨14270008048771845427659395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9513338699181230285106263 14270008048771845427659395)
                  ·
                    refine ⟨21405012073157768141489093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14270008048771845427659395 21405012073157768141489093)
                    ·
                      refine ⟨4013439763717081526529205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21405012073157768141489093 4013439763717081526529205)
                      ·
                        rfl

theorem cell23_7816146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 2, 3, 1, 1, 4].length) (baseStart_7816146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7816146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7816146 prefixEnd_7816146 := by exact prefixLift 7816146
  have htrace : WordTrace (prefixWord ++ tailWord_7816146) baseStart_7816146 baseEnd_7816146 := by
    simpa [prefixWord, tailWord_7816146, baseEnd_7816146] using wordTrace_append hprefix tailTrace_7816146
  have hstable : (prefixWord ++ tailWord_7816146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7816146).length < 2 ^ (prefixWord ++ tailWord_7816146).sum := by decide
  have hdescent : baseEnd_7816146 < baseStart_7816146 := by decide
  rcases family_descends (prefixWord ++ tailWord_7816146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7816152 : List Nat := [2, 1, 2, 2, 2, 5, 9]
def baseStart_7816152 : Nat := 118140960795 + 7816152 * 2 ^ 59
def prefixEnd_7816152 : Nat := 4983230072969 + 3 ^ 40 * 7816152 * 2
def baseEnd_7816152 : Nat := 49548677093839611148817

theorem tailTrace_7816152 : CollatzResearch.WordTrace tailWord_7816152 prefixEnd_7816152 49548677093839611148817 := by
  unfold tailWord_7816152
  simp only [CollatzResearch.WordTrace]
  refine ⟨142539241789711835665245355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190052322386282447553660473 142539241789711835665245355)
  ·
    refine ⟨213808862684567753497868033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142539241789711835665245355 213808862684567753497868033)
    ·
      refine ⟨160356647013425815123401025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 213808862684567753497868033 160356647013425815123401025)
      ·
        refine ⟨120267485260069361342550769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 160356647013425815123401025 120267485260069361342550769)
        ·
          refine ⟨90200613945052021006913077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120267485260069361342550769 90200613945052021006913077)
          ·
            refine ⟨8456307557348626969398101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 90200613945052021006913077 8456307557348626969398101)
            ·
              refine ⟨49548677093839611148817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8456307557348626969398101 49548677093839611148817)
              ·
                rfl

theorem cell23_7816152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 5, 9].length) (baseStart_7816152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7816152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7816152 prefixEnd_7816152 := by exact prefixLift 7816152
  have htrace : WordTrace (prefixWord ++ tailWord_7816152) baseStart_7816152 baseEnd_7816152 := by
    simpa [prefixWord, tailWord_7816152, baseEnd_7816152] using wordTrace_append hprefix tailTrace_7816152
  have hstable : (prefixWord ++ tailWord_7816152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7816152).length < 2 ^ (prefixWord ++ tailWord_7816152).sum := by decide
  have hdescent : baseEnd_7816152 < baseStart_7816152 := by decide
  rcases family_descends (prefixWord ++ tailWord_7816152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7816213 : List Nat := [1, 3, 2, 1, 4, 2, 2, 2, 2, 1, 3]
def baseStart_7816213 : Nat := 118140960795 + 7816213 * 2 ^ 59
def prefixEnd_7816213 : Nat := 4983230072969 + 3 ^ 40 * 7816213 * 2
def baseEnd_7816213 : Nat := 4013474166920932764391397

theorem tailTrace_7816213 : CollatzResearch.WordTrace tailWord_7816213 prefixEnd_7816213 4013474166920932764391397 := by
  unfold tailWord_7816213
  simp only [CollatzResearch.WordTrace]
  refine ⟨285080708432202678748461293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190053805621468452498974195 285080708432202678748461293)
  ·
    refine ⟨106905265662076004530672985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 285080708432202678748461293 106905265662076004530672985)
    ·
      refine ⟨80178949246557003398004739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106905265662076004530672985 80178949246557003398004739)
      ·
        refine ⟨120268423869835505097007109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80178949246557003398004739 120268423869835505097007109)
        ·
          refine ⟨22550329475594157205688833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 120268423869835505097007109 22550329475594157205688833)
          ·
            refine ⟨16912747106695617904266625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22550329475594157205688833 16912747106695617904266625)
            ·
              refine ⟨12684560330021713428199969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16912747106695617904266625 12684560330021713428199969)
              ·
                refine ⟨9513420247516285071149977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12684560330021713428199969 9513420247516285071149977)
                ·
                  refine ⟨7135065185637213803362483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9513420247516285071149977 7135065185637213803362483)
                  ·
                    refine ⟨10702597778455820705043725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7135065185637213803362483 10702597778455820705043725)
                    ·
                      refine ⟨4013474166920932764391397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10702597778455820705043725 4013474166920932764391397)
                      ·
                        rfl

theorem cell23_7816213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 2, 2, 2, 1, 3].length) (baseStart_7816213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7816213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7816213 prefixEnd_7816213 := by exact prefixLift 7816213
  have htrace : WordTrace (prefixWord ++ tailWord_7816213) baseStart_7816213 baseEnd_7816213 := by
    simpa [prefixWord, tailWord_7816213, baseEnd_7816213] using wordTrace_append hprefix tailTrace_7816213
  have hstable : (prefixWord ++ tailWord_7816213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7816213).length < 2 ^ (prefixWord ++ tailWord_7816213).sum := by decide
  have hdescent : baseEnd_7816213 < baseStart_7816213 := by decide
  rcases family_descends (prefixWord ++ tailWord_7816213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7816236 : List Nat := [2, 2, 1, 1, 1, 2, 6, 1, 1, 4, 2]
def baseStart_7816236 : Nat := 118140960795 + 7816236 * 2 ^ 59
def prefixEnd_7816236 : Nat := 4983230072969 + 3 ^ 40 * 7816236 * 2
def baseEnd_7816236 : Nat := 4013485976975986174403791

theorem tailTrace_7816236 : CollatzResearch.WordTrace tailWord_7816236 prefixEnd_7816236 4013485976975986174403791 := by
  unfold tailWord_7816236
  simp only [CollatzResearch.WordTrace]
  refine ⟨142540773655559676838274281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190054364874079569117699041 142540773655559676838274281)
  ·
    refine ⟨106905580241669757628705711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142540773655559676838274281 106905580241669757628705711)
    ·
      refine ⟨160358370362504636443058567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106905580241669757628705711 160358370362504636443058567)
      ·
        refine ⟨240537555543756954664587851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160358370362504636443058567 240537555543756954664587851)
        ·
          refine ⟨360806333315635431996881777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 240537555543756954664587851 360806333315635431996881777)
          ·
            refine ⟨270604749986726573997661333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 360806333315635431996881777 270604749986726573997661333)
            ·
              refine ⟨12684597655627808156140375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 270604749986726573997661333 12684597655627808156140375)
              ·
                refine ⟨19026896483441712234210563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12684597655627808156140375 19026896483441712234210563)
                ·
                  refine ⟨28540344725162568351315845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19026896483441712234210563 28540344725162568351315845)
                  ·
                    refine ⟨5351314635967981565871721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28540344725162568351315845 5351314635967981565871721)
                    ·
                      refine ⟨4013485976975986174403791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5351314635967981565871721 4013485976975986174403791)
                      ·
                        rfl

theorem cell23_7816236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 4, 2].length) (baseStart_7816236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7816236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7816236 prefixEnd_7816236 := by exact prefixLift 7816236
  have htrace : WordTrace (prefixWord ++ tailWord_7816236) baseStart_7816236 baseEnd_7816236 := by
    simpa [prefixWord, tailWord_7816236, baseEnd_7816236] using wordTrace_append hprefix tailTrace_7816236
  have hstable : (prefixWord ++ tailWord_7816236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7816236).length < 2 ^ (prefixWord ++ tailWord_7816236).sum := by decide
  have hdescent : baseEnd_7816236 < baseStart_7816236 := by decide
  rcases family_descends (prefixWord ++ tailWord_7816236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7816257 : List Nat := [1, 2, 5, 1, 3, 2, 2, 1, 1, 3, 2]
def baseStart_7816257 : Nat := 118140960795 + 7816257 * 2 ^ 59
def prefixEnd_7816257 : Nat := 4983230072969 + 3 ^ 40 * 7816257 * 2
def baseEnd_7816257 : Nat := 4013496760069730592241195

theorem tailTrace_7816257 : CollatzResearch.WordTrace tailWord_7816257 prefixEnd_7816257 4013496760069730592241195 := by
  unfold tailWord_7816257
  simp only [CollatzResearch.WordTrace]
  refine ⟨285082313244043274263063025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190054875496028849508708683 285082313244043274263063025)
  ·
    refine ⟨213811734933032455697297269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 285082313244043274263063025 213811734933032455697297269)
    ·
      refine ⟨20044850149971792721621619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 213811734933032455697297269 20044850149971792721621619)
      ·
        refine ⟨30067275224957689082432429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20044850149971792721621619 30067275224957689082432429)
        ·
          refine ⟨11275228209359133405912161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30067275224957689082432429 11275228209359133405912161)
          ·
            refine ⟨8456421157019350054434121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11275228209359133405912161 8456421157019350054434121)
            ·
              refine ⟨6342315867764512540825591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8456421157019350054434121 6342315867764512540825591)
              ·
                refine ⟨9513473801646768811238387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6342315867764512540825591 9513473801646768811238387)
                ·
                  refine ⟨14270210702470153216857581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9513473801646768811238387 14270210702470153216857581)
                  ·
                    refine ⟨5351329013426307456321593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14270210702470153216857581 5351329013426307456321593)
                    ·
                      refine ⟨4013496760069730592241195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5351329013426307456321593 4013496760069730592241195)
                      ·
                        rfl

theorem cell23_7816257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 2, 2, 1, 1, 3, 2].length) (baseStart_7816257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7816257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7816257 prefixEnd_7816257 := by exact prefixLift 7816257
  have htrace : WordTrace (prefixWord ++ tailWord_7816257) baseStart_7816257 baseEnd_7816257 := by
    simpa [prefixWord, tailWord_7816257, baseEnd_7816257] using wordTrace_append hprefix tailTrace_7816257
  have hstable : (prefixWord ++ tailWord_7816257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7816257).length < 2 ^ (prefixWord ++ tailWord_7816257).sum := by decide
  have hdescent : baseEnd_7816257 < baseStart_7816257 := by decide
  rcases family_descends (prefixWord ++ tailWord_7816257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7816276 : List Nat := [2, 4, 1, 1, 1, 1, 4, 4, 5]
def baseStart_7816276 : Nat := 118140960795 + 7816276 * 2 ^ 59
def prefixEnd_7816276 : Nat := 4983230072969 + 3 ^ 40 * 7816276 * 2
def baseEnd_7816276 : Nat := 445945168466907335322623

theorem tailTrace_7816276 : CollatzResearch.WordTrace tailWord_7816276 prefixEnd_7816276 445945168466907335322623 := by
  unfold tailWord_7816276
  simp only [CollatzResearch.WordTrace]
  refine ⟨142541503115487220254002341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190055337487316293672003121 142541503115487220254002341)
  ·
    refine ⟨26726531834153853797625439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 142541503115487220254002341 26726531834153853797625439)
    ·
      refine ⟨40089797751230780696438159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26726531834153853797625439 40089797751230780696438159)
      ·
        refine ⟨60134696626846171044657239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40089797751230780696438159 60134696626846171044657239)
        ·
          refine ⟨90202044940269256566985859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60134696626846171044657239 90202044940269256566985859)
          ·
            refine ⟨135303067410403884850478789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90202044940269256566985859 135303067410403884850478789)
            ·
              refine ⟨25369325139450728409464773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 135303067410403884850478789 25369325139450728409464773)
              ·
                refine ⟨4756748463647011576774645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25369325139450728409464773 4756748463647011576774645)
                ·
                  refine ⟨445945168466907335322623, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4756748463647011576774645 445945168466907335322623)
                  ·
                    rfl

theorem cell23_7816276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 4, 4, 5].length) (baseStart_7816276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7816276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7816276 prefixEnd_7816276 := by exact prefixLift 7816276
  have htrace : WordTrace (prefixWord ++ tailWord_7816276) baseStart_7816276 baseEnd_7816276 := by
    simpa [prefixWord, tailWord_7816276, baseEnd_7816276] using wordTrace_append hprefix tailTrace_7816276
  have hstable : (prefixWord ++ tailWord_7816276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7816276).length < 2 ^ (prefixWord ++ tailWord_7816276).sum := by decide
  have hdescent : baseEnd_7816276 < baseStart_7816276 := by decide
  rcases family_descends (prefixWord ++ tailWord_7816276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7816376 : List Nat := [2, 1, 2, 1, 2, 1, 2, 1, 7, 1, 3]
def baseStart_7816376 : Nat := 118140960795 + 7816376 * 2 ^ 59
def prefixEnd_7816376 : Nat := 4983230072969 + 3 ^ 40 * 7816376 * 2
def baseEnd_7816376 : Nat := 4013557864267615626653147

theorem tailTrace_7816376 : CollatzResearch.WordTrace tailWord_7816376 prefixEnd_7816376 4013557864267615626653147 := by
  unfold tailWord_7816376
  simp only [CollatzResearch.WordTrace]
  refine ⟨142543326765306078793322491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190057769020408105057763321 142543326765306078793322491)
  ·
    refine ⟨213814990147959118189983737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142543326765306078793322491 213814990147959118189983737)
    ·
      refine ⟨160361242610969338642487803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 213814990147959118189983737 160361242610969338642487803)
      ·
        refine ⟨240541863916454007963731705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160361242610969338642487803 240541863916454007963731705)
        ·
          refine ⟨180406397937340505972798779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 240541863916454007963731705 180406397937340505972798779)
          ·
            refine ⟨270609596906010758959198169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 180406397937340505972798779 270609596906010758959198169)
            ·
              refine ⟨202957197679508069219398627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 270609596906010758959198169 202957197679508069219398627)
              ·
                refine ⟨304435796519262103829097941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 202957197679508069219398627 304435796519262103829097941)
                ·
                  refine ⟨7135213980920205558494483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 304435796519262103829097941 7135213980920205558494483)
                  ·
                    refine ⟨10702820971380308337741725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7135213980920205558494483 10702820971380308337741725)
                    ·
                      refine ⟨4013557864267615626653147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10702820971380308337741725 4013557864267615626653147)
                      ·
                        rfl

theorem cell23_7816376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 1, 7, 1, 3].length) (baseStart_7816376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7816376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7816376 prefixEnd_7816376 := by exact prefixLift 7816376
  have htrace : WordTrace (prefixWord ++ tailWord_7816376) baseStart_7816376 baseEnd_7816376 := by
    simpa [prefixWord, tailWord_7816376, baseEnd_7816376] using wordTrace_append hprefix tailTrace_7816376
  have hstable : (prefixWord ++ tailWord_7816376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7816376).length < 2 ^ (prefixWord ++ tailWord_7816376).sum := by decide
  have hdescent : baseEnd_7816376 < baseStart_7816376 := by decide
  rcases family_descends (prefixWord ++ tailWord_7816376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7816416 : List Nat := [2, 1, 1, 3, 1, 4, 2, 1, 3, 1, 4]
def baseStart_7816416 : Nat := 118140960795 + 7816416 * 2 ^ 59
def prefixEnd_7816416 : Nat := 4983230072969 + 3 ^ 40 * 7816416 * 2
def baseEnd_7816416 : Nat := 4013578403493795470152963

theorem tailTrace_7816416 : CollatzResearch.WordTrace tailWord_7816416 prefixEnd_7816416 4013578403493795470152963 := by
  unfold tailWord_7816416
  simp only [CollatzResearch.WordTrace]
  refine ⟨142544056225233622209050551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190058741633644829612067401 142544056225233622209050551)
  ·
    refine ⟨213816084337850433313575827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142544056225233622209050551 213816084337850433313575827)
    ·
      refine ⟨320724126506775649970363741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213816084337850433313575827 320724126506775649970363741)
      ·
        refine ⟨120271547440040868738886403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 320724126506775649970363741 120271547440040868738886403)
        ·
          refine ⟨180407321160061303108329605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120271547440040868738886403 180407321160061303108329605)
          ·
            refine ⟨33826372717511494332811801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 180407321160061303108329605 33826372717511494332811801)
            ·
              refine ⟨25369779538133620749608851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33826372717511494332811801 25369779538133620749608851)
              ·
                refine ⟨38054669307200431124413277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25369779538133620749608851 38054669307200431124413277)
                ·
                  refine ⟨14270500990200161671654979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38054669307200431124413277 14270500990200161671654979)
                  ·
                    refine ⟨21405751485300242507482469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14270500990200161671654979 21405751485300242507482469)
                    ·
                      refine ⟨4013578403493795470152963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21405751485300242507482469 4013578403493795470152963)
                      ·
                        rfl

theorem cell23_7816416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 2, 1, 3, 1, 4].length) (baseStart_7816416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7816416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7816416 prefixEnd_7816416 := by exact prefixLift 7816416
  have htrace : WordTrace (prefixWord ++ tailWord_7816416) baseStart_7816416 baseEnd_7816416 := by
    simpa [prefixWord, tailWord_7816416, baseEnd_7816416] using wordTrace_append hprefix tailTrace_7816416
  have hstable : (prefixWord ++ tailWord_7816416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7816416).length < 2 ^ (prefixWord ++ tailWord_7816416).sum := by decide
  have hdescent : baseEnd_7816416 < baseStart_7816416 := by decide
  rcases family_descends (prefixWord ++ tailWord_7816416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7816426 : List Nat := [3, 1, 3, 1, 1, 3, 2, 2, 1, 6]
def baseStart_7816426 : Nat := 118140960795 + 7816426 * 2 ^ 59
def prefixEnd_7816426 : Nat := 4983230072969 + 3 ^ 40 * 7816426 * 2
def baseEnd_7816426 : Nat := 1337861179433446810342639

theorem tailTrace_7816426 : CollatzResearch.WordTrace tailWord_7816426 prefixEnd_7816426 1337861179433446810342639 := by
  unfold tailWord_7816426
  simp only [CollatzResearch.WordTrace]
  refine ⟨71272119295107754031491283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 190058984786954010750643421 71272119295107754031491283)
  ·
    refine ⟨106908178942661631047236925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71272119295107754031491283 106908178942661631047236925)
    ·
      refine ⟨40090567103498111642713847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 106908178942661631047236925 40090567103498111642713847)
      ·
        refine ⟨60135850655247167464070771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40090567103498111642713847 60135850655247167464070771)
        ·
          refine ⟨90203775982870751196106157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60135850655247167464070771 90203775982870751196106157)
          ·
            refine ⟨33826415993576531698539809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 90203775982870751196106157 33826415993576531698539809)
            ·
              refine ⟨25369811995182398773904857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33826415993576531698539809 25369811995182398773904857)
              ·
                refine ⟨19027358996386799080428643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25369811995182398773904857 19027358996386799080428643)
                ·
                  refine ⟨28541038494580198620642965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19027358996386799080428643 28541038494580198620642965)
                  ·
                    refine ⟨1337861179433446810342639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28541038494580198620642965 1337861179433446810342639)
                    ·
                      rfl

theorem cell23_7816426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 2, 2, 1, 6].length) (baseStart_7816426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7816426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7816426 prefixEnd_7816426 := by exact prefixLift 7816426
  have htrace : WordTrace (prefixWord ++ tailWord_7816426) baseStart_7816426 baseEnd_7816426 := by
    simpa [prefixWord, tailWord_7816426, baseEnd_7816426] using wordTrace_append hprefix tailTrace_7816426
  have hstable : (prefixWord ++ tailWord_7816426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7816426).length < 2 ^ (prefixWord ++ tailWord_7816426).sum := by decide
  have hdescent : baseEnd_7816426 < baseStart_7816426 := by decide
  rcases family_descends (prefixWord ++ tailWord_7816426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7816433 : List Nat := [1, 2, 2, 2, 2, 1, 1, 1, 7, 2, 2]
def baseStart_7816433 : Nat := 118140960795 + 7816433 * 2 ^ 59
def prefixEnd_7816433 : Nat := 4983230072969 + 3 ^ 40 * 7816433 * 2
def baseEnd_7816433 : Nat := 4013587132664921903640385

theorem tailTrace_7816433 : CollatzResearch.WordTrace tailWord_7816433 prefixEnd_7816433 4013587132664921903640385 := by
  unfold tailWord_7816433
  simp only [CollatzResearch.WordTrace]
  refine ⟨285088732491405656321469953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190059154994270437547646635 285088732491405656321469953)
  ·
    refine ⟨213816549368554242241102465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 285088732491405656321469953 213816549368554242241102465)
    ·
      refine ⟨160362412026415681680826849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 213816549368554242241102465 160362412026415681680826849)
      ·
        refine ⟨120271809019811761260620137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 160362412026415681680826849 120271809019811761260620137)
        ·
          refine ⟨90203856764858820945465103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120271809019811761260620137 90203856764858820945465103)
          ·
            refine ⟨135305785147288231418197655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90203856764858820945465103 135305785147288231418197655)
            ·
              refine ⟨202958677720932347127296483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 135305785147288231418197655 202958677720932347127296483)
              ·
                refine ⟨304438016581398520690944725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 202958677720932347127296483 304438016581398520690944725)
                ·
                  refine ⟨7135266013626527828694017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 304438016581398520690944725 7135266013626527828694017)
                  ·
                    refine ⟨5351449510219895871520513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7135266013626527828694017 5351449510219895871520513)
                    ·
                      refine ⟨4013587132664921903640385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5351449510219895871520513 4013587132664921903640385)
                      ·
                        rfl

theorem cell23_7816433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 1, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 1, 7, 2, 2].length) (baseStart_7816433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7816433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7816433 prefixEnd_7816433 := by exact prefixLift 7816433
  have htrace : WordTrace (prefixWord ++ tailWord_7816433) baseStart_7816433 baseEnd_7816433 := by
    simpa [prefixWord, tailWord_7816433, baseEnd_7816433] using wordTrace_append hprefix tailTrace_7816433
  have hstable : (prefixWord ++ tailWord_7816433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7816433).length < 2 ^ (prefixWord ++ tailWord_7816433).sum := by decide
  have hdescent : baseEnd_7816433 < baseStart_7816433 := by decide
  rcases family_descends (prefixWord ++ tailWord_7816433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7816460 : List Nat := [2, 2, 1, 2, 2, 4, 3, 1, 2, 4]
def baseStart_7816460 : Nat := 118140960795 + 7816460 * 2 ^ 59
def prefixEnd_7816460 : Nat := 4983230072969 + 3 ^ 40 * 7816460 * 2
def baseEnd_7816460 : Nat := 1337866998880864432667587

theorem tailTrace_7816460 : CollatzResearch.WordTrace tailWord_7816460 prefixEnd_7816460 1337866998880864432667587 := by
  unfold tailWord_7816460
  simp only [CollatzResearch.WordTrace]
  refine ⟨142544858631153919966351417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190059811508205226621801889 142544858631153919966351417)
  ·
    refine ⟨106908643973365439974763563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142544858631153919966351417 106908643973365439974763563)
    ·
      refine ⟨160362965960048159962145345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106908643973365439974763563 160362965960048159962145345)
      ·
        refine ⟨120272224470036119971609009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 160362965960048159962145345 120272224470036119971609009)
        ·
          refine ⟨90204168352527089978706757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120272224470036119971609009 90204168352527089978706757)
          ·
            refine ⟨16913281566098829371007517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 90204168352527089978706757 16913281566098829371007517)
            ·
              refine ⟨6342480587287061014127819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16913281566098829371007517 6342480587287061014127819)
              ·
                refine ⟨9513720880930591521191729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6342480587287061014127819 9513720880930591521191729)
                ·
                  refine ⟨7135290660697943640893797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9513720880930591521191729 7135290660697943640893797)
                  ·
                    refine ⟨1337866998880864432667587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7135290660697943640893797 1337866998880864432667587)
                    ·
                      rfl

theorem cell23_7816460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 3, 1, 2, 4].length) (baseStart_7816460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7816460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7816460 prefixEnd_7816460 := by exact prefixLift 7816460
  have htrace : WordTrace (prefixWord ++ tailWord_7816460) baseStart_7816460 baseEnd_7816460 := by
    simpa [prefixWord, tailWord_7816460, baseEnd_7816460] using wordTrace_append hprefix tailTrace_7816460
  have hstable : (prefixWord ++ tailWord_7816460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7816460).length < 2 ^ (prefixWord ++ tailWord_7816460).sum := by decide
  have hdescent : baseEnd_7816460 < baseStart_7816460 := by decide
  rcases family_descends (prefixWord ++ tailWord_7816460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7816478 : List Nat := [4, 3, 2, 1, 3, 1, 1, 3, 1, 1, 3]
def baseStart_7816478 : Nat := 118140960795 + 7816478 * 2 ^ 59
def prefixEnd_7816478 : Nat := 4983230072969 + 3 ^ 40 * 7816478 * 2
def baseEnd_7816478 : Nat := 4013610239294374227577679

theorem tailTrace_7816478 : CollatzResearch.WordTrace tailWord_7816478 prefixEnd_7816478 4013610239294374227577679 := by
  unfold tailWord_7816478
  simp only [CollatzResearch.WordTrace]
  refine ⟨35636296722030328625857261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 190060249184161752671238725 35636296722030328625857261)
  ·
    refine ⟨13363611270761373234696473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35636296722030328625857261 13363611270761373234696473)
    ·
      refine ⟨10022708453071029926022355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13363611270761373234696473 10022708453071029926022355)
      ·
        refine ⟨15034062679606544889033533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10022708453071029926022355 15034062679606544889033533)
        ·
          refine ⟨5637773504852454333387575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15034062679606544889033533 5637773504852454333387575)
          ·
            refine ⟨8456660257278681500081363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5637773504852454333387575 8456660257278681500081363)
            ·
              refine ⟨12684990385918022250122045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8456660257278681500081363 12684990385918022250122045)
              ·
                refine ⟨4756871394719258343795767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12684990385918022250122045 4756871394719258343795767)
                ·
                  refine ⟨7135307092078887515693651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4756871394719258343795767 7135307092078887515693651)
                  ·
                    refine ⟨10702960638118331273540477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7135307092078887515693651 10702960638118331273540477)
                    ·
                      refine ⟨4013610239294374227577679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10702960638118331273540477 4013610239294374227577679)
                      ·
                        rfl

theorem cell23_7816478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 3, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 3, 1, 1, 3, 1, 1, 3].length) (baseStart_7816478 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7816478 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7816478 prefixEnd_7816478 := by exact prefixLift 7816478
  have htrace : WordTrace (prefixWord ++ tailWord_7816478) baseStart_7816478 baseEnd_7816478 := by
    simpa [prefixWord, tailWord_7816478, baseEnd_7816478] using wordTrace_append hprefix tailTrace_7816478
  have hstable : (prefixWord ++ tailWord_7816478).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7816478).length < 2 ^ (prefixWord ++ tailWord_7816478).sum := by decide
  have hdescent : baseEnd_7816478 < baseStart_7816478 := by decide
  rcases family_descends (prefixWord ++ tailWord_7816478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7816483 : List Nat := [1, 1, 1, 4, 2, 3, 1, 2, 4, 1, 3]
def baseStart_7816483 : Nat := 118140960795 + 7816483 * 2 ^ 59
def prefixEnd_7816483 : Nat := 4983230072969 + 3 ^ 40 * 7816483 * 2
def baseEnd_7816483 : Nat := 4013612806697646708015155

theorem tailTrace_7816483 : CollatzResearch.WordTrace tailWord_7816483 prefixEnd_7816483 4013612806697646708015155 := by
  unfold tailWord_7816483
  simp only [CollatzResearch.WordTrace]
  refine ⟨285090556141224514860790103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190060370760816343240526735 285090556141224514860790103)
  ·
    refine ⟨427635834211836772291185155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285090556141224514860790103 427635834211836772291185155)
    ·
      refine ⟨641453751317755158436777733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 427635834211836772291185155 641453751317755158436777733)
      ·
        refine ⟨120272578372079092206895825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 641453751317755158436777733 120272578372079092206895825)
        ·
          refine ⟨90204433779059319155171869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120272578372079092206895825 90204433779059319155171869)
          ·
            refine ⟨33826662667147244683189451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 90204433779059319155171869 33826662667147244683189451)
            ·
              refine ⟨50739994000720867024784177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33826662667147244683189451 50739994000720867024784177)
              ·
                refine ⟨38054995500540650268588133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50739994000720867024784177 38054995500540650268588133)
                ·
                  refine ⟨7135311656351371925360275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38054995500540650268588133 7135311656351371925360275)
                  ·
                    refine ⟨10702967484527057888040413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7135311656351371925360275 10702967484527057888040413)
                    ·
                      refine ⟨4013612806697646708015155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10702967484527057888040413 4013612806697646708015155)
                      ·
                        rfl

theorem cell23_7816483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 1, 2, 4, 1, 3].length) (baseStart_7816483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7816483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7816483 prefixEnd_7816483 := by exact prefixLift 7816483
  have htrace : WordTrace (prefixWord ++ tailWord_7816483) baseStart_7816483 baseEnd_7816483 := by
    simpa [prefixWord, tailWord_7816483, baseEnd_7816483] using wordTrace_append hprefix tailTrace_7816483
  have hstable : (prefixWord ++ tailWord_7816483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7816483).length < 2 ^ (prefixWord ++ tailWord_7816483).sum := by decide
  have hdescent : baseEnd_7816483 < baseStart_7816483 := by decide
  rcases family_descends (prefixWord ++ tailWord_7816483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7816500 : List Nat := [2, 5, 1, 1, 1, 1, 1, 3, 4, 1, 3]
def baseStart_7816500 : Nat := 118140960795 + 7816500 * 2 ^ 59
def prefixEnd_7816500 : Nat := 4983230072969 + 3 ^ 40 * 7816500 * 2
def baseEnd_7816500 : Nat := 4013621535868773141502577

theorem tailTrace_7816500 : CollatzResearch.WordTrace tailWord_7816500 prefixEnd_7816500 4013621535868773141502577 := by
  unfold tailWord_7816500
  simp only [CollatzResearch.WordTrace]
  refine ⟨142545588091081463382079477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190060784121441951176105969 142545588091081463382079477)
  ·
    refine ⟨13363648883538887192069951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 142545588091081463382079477 13363648883538887192069951)
    ·
      refine ⟨20045473325308330788104927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13363648883538887192069951 20045473325308330788104927)
      ·
        refine ⟨30068209987962496182157391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20045473325308330788104927 30068209987962496182157391)
        ·
          refine ⟨45102314981943744273236087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30068209987962496182157391 45102314981943744273236087)
          ·
            refine ⟨67653472472915616409854131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45102314981943744273236087 67653472472915616409854131)
            ·
              refine ⟨101480208709373424614781197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67653472472915616409854131 101480208709373424614781197)
              ·
                refine ⟨38055078266015034230542949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 101480208709373424614781197 38055078266015034230542949)
                ·
                  refine ⟨7135327174877818918226803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38055078266015034230542949 7135327174877818918226803)
                  ·
                    refine ⟨10702990762316728377340205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7135327174877818918226803 10702990762316728377340205)
                    ·
                      refine ⟨4013621535868773141502577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10702990762316728377340205 4013621535868773141502577)
                      ·
                        rfl

theorem cell23_7816500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 3, 4, 1, 3].length) (baseStart_7816500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7816500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7816500 prefixEnd_7816500 := by exact prefixLift 7816500
  have htrace : WordTrace (prefixWord ++ tailWord_7816500) baseStart_7816500 baseEnd_7816500 := by
    simpa [prefixWord, tailWord_7816500, baseEnd_7816500] using wordTrace_append hprefix tailTrace_7816500
  have hstable : (prefixWord ++ tailWord_7816500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7816500).length < 2 ^ (prefixWord ++ tailWord_7816500).sum := by decide
  have hdescent : baseEnd_7816500 < baseStart_7816500 := by decide
  rcases family_descends (prefixWord ++ tailWord_7816500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7816506 : List Nat := [3, 1, 1, 1, 4, 1, 2, 1, 2, 3, 4]
def baseStart_7816506 : Nat := 118140960795 + 7816506 * 2 ^ 59
def prefixEnd_7816506 : Nat := 4983230072969 + 3 ^ 40 * 7816506 * 2
def baseEnd_7816506 : Nat := 4013624616752700118027549

theorem tailTrace_7816506 : CollatzResearch.WordTrace tailWord_7816506 prefixEnd_7816506 4013624616752700118027549 := by
  unfold tailWord_7816506
  simp only [CollatzResearch.WordTrace]
  refine ⟨71272848755035297447219343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 190060930013427459859251581 71272848755035297447219343)
  ·
    refine ⟨106909273132552946170829015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71272848755035297447219343 106909273132552946170829015)
    ·
      refine ⟨160363909698829419256243523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106909273132552946170829015 160363909698829419256243523)
      ·
        refine ⟨240545864548244128884365285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160363909698829419256243523 240545864548244128884365285)
        ·
          refine ⟨45102349602795774165818491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 240545864548244128884365285 45102349602795774165818491)
          ·
            refine ⟨67653524404193661248727737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45102349602795774165818491 67653524404193661248727737)
            ·
              refine ⟨50740143303145245936545803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67653524404193661248727737 50740143303145245936545803)
              ·
                refine ⟨76110214954717868904818705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50740143303145245936545803 76110214954717868904818705)
                ·
                  refine ⟨57082661216038401678614029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 76110214954717868904818705 57082661216038401678614029)
                  ·
                    refine ⟨21405997956014400629480261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 57082661216038401678614029 21405997956014400629480261)
                    ·
                      refine ⟨4013624616752700118027549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21405997956014400629480261 4013624616752700118027549)
                      ·
                        rfl

theorem cell23_7816506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 2, 1, 2, 3, 4].length) (baseStart_7816506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7816506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7816506 prefixEnd_7816506 := by exact prefixLift 7816506
  have htrace : WordTrace (prefixWord ++ tailWord_7816506) baseStart_7816506 baseEnd_7816506 := by
    simpa [prefixWord, tailWord_7816506, baseEnd_7816506] using wordTrace_append hprefix tailTrace_7816506
  have hstable : (prefixWord ++ tailWord_7816506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7816506).length < 2 ^ (prefixWord ++ tailWord_7816506).sum := by decide
  have hdescent : baseEnd_7816506 < baseStart_7816506 := by decide
  rcases family_descends (prefixWord ++ tailWord_7816506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7816510 : List Nat := [4, 2, 1, 2, 1, 1, 2, 2, 3, 3, 2]
def baseStart_7816510 : Nat := 118140960795 + 7816510 * 2 ^ 59
def prefixEnd_7816510 : Nat := 4983230072969 + 3 ^ 40 * 7816510 * 2
def baseEnd_7816510 : Nat := 4013626670675318102377531

theorem tailTrace_7816510 : CollatzResearch.WordTrace tailWord_7816510 prefixEnd_7816510 4013626670675318102377531 := by
  unfold tailWord_7816510
  simp only [CollatzResearch.WordTrace]
  refine ⟨35636442614015837309002873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 190061027274751132314681989 35636442614015837309002873)
  ·
    refine ⟨26727331960511877981752155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35636442614015837309002873 26727331960511877981752155)
    ·
      refine ⟨40090997940767816972628233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26727331960511877981752155 40090997940767816972628233)
      ·
        refine ⟨30068248455575862729471175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40090997940767816972628233 30068248455575862729471175)
        ·
          refine ⟨45102372683363794094206763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30068248455575862729471175 45102372683363794094206763)
          ·
            refine ⟨67653559025045691141310145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45102372683363794094206763 67653559025045691141310145)
            ·
              refine ⟨50740169268784268355982609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67653559025045691141310145 50740169268784268355982609)
              ·
                refine ⟨38055126951588201266986957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50740169268784268355982609 38055126951588201266986957)
                ·
                  refine ⟨14270672606845575475120109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38055126951588201266986957 14270672606845575475120109)
                  ·
                    refine ⟨5351502227567090803170041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14270672606845575475120109 5351502227567090803170041)
                    ·
                      refine ⟨4013626670675318102377531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5351502227567090803170041 4013626670675318102377531)
                      ·
                        rfl

theorem cell23_7816510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 2, 2, 3, 3, 2].length) (baseStart_7816510 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7816510 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7816510 prefixEnd_7816510 := by exact prefixLift 7816510
  have htrace : WordTrace (prefixWord ++ tailWord_7816510) baseStart_7816510 baseEnd_7816510 := by
    simpa [prefixWord, tailWord_7816510, baseEnd_7816510] using wordTrace_append hprefix tailTrace_7816510
  have hstable : (prefixWord ++ tailWord_7816510).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7816510).length < 2 ^ (prefixWord ++ tailWord_7816510).sum := by decide
  have hdescent : baseEnd_7816510 < baseStart_7816510 := by decide
  rcases family_descends (prefixWord ++ tailWord_7816510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7816526 : List Nat := [4, 1, 1, 1, 1, 1, 3, 1, 4, 1, 5]
def baseStart_7816526 : Nat := 118140960795 + 7816526 * 2 ^ 59
def prefixEnd_7816526 : Nat := 4983230072969 + 3 ^ 40 * 7816526 * 2
def baseEnd_7816526 : Nat := 4013634886365790039777457

theorem tailTrace_7816526 : CollatzResearch.WordTrace tailWord_7816526 prefixEnd_7816526 4013634886365790039777457 := by
  unfold tailWord_7816526
  simp only [CollatzResearch.WordTrace]
  refine ⟨35636515560008591650575679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 190061416320045822136403621 35636515560008591650575679)
  ·
    refine ⟨53454773340012887475863519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35636515560008591650575679 53454773340012887475863519)
    ·
      refine ⟨80182160010019331213795279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53454773340012887475863519 80182160010019331213795279)
      ·
        refine ⟨120273240015028996820692919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80182160010019331213795279 120273240015028996820692919)
        ·
          refine ⟨180409860022543495231039379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120273240015028996820692919 180409860022543495231039379)
          ·
            refine ⟨270614790033815242846559069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 180409860022543495231039379 270614790033815242846559069)
            ·
              refine ⟨101480546262680716067459651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 270614790033815242846559069 101480546262680716067459651)
              ·
                refine ⟨152220819394021074101189477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 101480546262680716067459651 152220819394021074101189477)
                ·
                  refine ⟨28541403636378951393973027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 152220819394021074101189477 28541403636378951393973027)
                  ·
                    refine ⟨42812105454568427090959541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28541403636378951393973027 42812105454568427090959541)
                    ·
                      refine ⟨4013634886365790039777457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42812105454568427090959541 4013634886365790039777457)
                      ·
                        rfl

theorem cell23_7816526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 1, 4, 1, 5].length) (baseStart_7816526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7816526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7816526 prefixEnd_7816526 := by exact prefixLift 7816526
  have htrace : WordTrace (prefixWord ++ tailWord_7816526) baseStart_7816526 baseEnd_7816526 := by
    simpa [prefixWord, tailWord_7816526, baseEnd_7816526] using wordTrace_append hprefix tailTrace_7816526
  have hstable : (prefixWord ++ tailWord_7816526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7816526).length < 2 ^ (prefixWord ++ tailWord_7816526).sum := by decide
  have hdescent : baseEnd_7816526 < baseStart_7816526 := by decide
  rcases family_descends (prefixWord ++ tailWord_7816526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7816557 : List Nat := [1, 5, 1, 1, 1, 3, 1, 4, 2, 2, 2]
def baseStart_7816557 : Nat := 118140960795 + 7816557 * 2 ^ 59
def prefixEnd_7816557 : Nat := 4983230072969 + 3 ^ 40 * 7816557 * 2
def baseEnd_7816557 : Nat := 4013650804266079418489815

theorem tailTrace_7816557 : CollatzResearch.WordTrace tailWord_7816557 prefixEnd_7816557 4013650804266079418489815 := by
  unfold tailWord_7816557
  simp only [CollatzResearch.WordTrace]
  refine ⟨285093255142956425498983925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190062170095304283665989283 285093255142956425498983925)
  ·
    refine ⟨26727492669652164890529743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 285093255142956425498983925 26727492669652164890529743)
    ·
      refine ⟨40091239004478247335794615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26727492669652164890529743 40091239004478247335794615)
      ·
        refine ⟨60136858506717371003691923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40091239004478247335794615 60136858506717371003691923)
        ·
          refine ⟨90205287760076056505537885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60136858506717371003691923 90205287760076056505537885)
          ·
            refine ⟨33826982910028521189576707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 90205287760076056505537885 33826982910028521189576707)
            ·
              refine ⟨50740474365042781784365061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33826982910028521189576707 50740474365042781784365061)
              ·
                refine ⟨9513838943445521584568449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50740474365042781784365061 9513838943445521584568449)
                ·
                  refine ⟨7135379207584141188426337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9513838943445521584568449 7135379207584141188426337)
                  ·
                    refine ⟨5351534405688105891319753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7135379207584141188426337 5351534405688105891319753)
                    ·
                      refine ⟨4013650804266079418489815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5351534405688105891319753 4013650804266079418489815)
                      ·
                        rfl

theorem cell23_7816557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 1, 4, 2, 2, 2].length) (baseStart_7816557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7816557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7816557 prefixEnd_7816557 := by exact prefixLift 7816557
  have htrace : WordTrace (prefixWord ++ tailWord_7816557) baseStart_7816557 baseEnd_7816557 := by
    simpa [prefixWord, tailWord_7816557, baseEnd_7816557] using wordTrace_append hprefix tailTrace_7816557
  have hstable : (prefixWord ++ tailWord_7816557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7816557).length < 2 ^ (prefixWord ++ tailWord_7816557).sum := by decide
  have hdescent : baseEnd_7816557 < baseStart_7816557 := by decide
  rcases family_descends (prefixWord ++ tailWord_7816557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7816573 : List Nat := [1, 4, 1, 1, 2, 2, 3, 1, 2, 3, 3]
def baseStart_7816573 : Nat := 118140960795 + 7816573 * 2 ^ 59
def prefixEnd_7816573 : Nat := 4983230072969 + 3 ^ 40 * 7816573 * 2
def baseEnd_7816573 : Nat := 4013659019956551355889741

theorem tailTrace_7816573 : CollatzResearch.WordTrace tailWord_7816573 prefixEnd_7816573 4013659019956551355889741 := by
  unfold tailWord_7816573
  simp only [CollatzResearch.WordTrace]
  refine ⟨285093838710898460231566373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190062559140598973487710915 285093838710898460231566373)
  ·
    refine ⟨53455094758293461293418695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 285093838710898460231566373 53455094758293461293418695)
    ·
      refine ⟨80182642137440191940128043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53455094758293461293418695 80182642137440191940128043)
      ·
        refine ⟨120273963206160287910192065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80182642137440191940128043 120273963206160287910192065)
        ·
          refine ⟨90205472404620215932644049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120273963206160287910192065 90205472404620215932644049)
          ·
            refine ⟨67654104303465161949483037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90205472404620215932644049 67654104303465161949483037)
            ·
              refine ⟨25370289113799435731056139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67654104303465161949483037 25370289113799435731056139)
              ·
                refine ⟨38055433670699153596584209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25370289113799435731056139 38055433670699153596584209)
                ·
                  refine ⟨28541575253024365197438157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38055433670699153596584209 28541575253024365197438157)
                  ·
                    refine ⟨10703090719884136949039309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28541575253024365197438157 10703090719884136949039309)
                    ·
                      refine ⟨4013659019956551355889741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10703090719884136949039309 4013659019956551355889741)
                      ·
                        rfl

theorem cell23_7816573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 3, 1, 2, 3, 3].length) (baseStart_7816573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7816573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7816573 prefixEnd_7816573 := by exact prefixLift 7816573
  have htrace : WordTrace (prefixWord ++ tailWord_7816573) baseStart_7816573 baseEnd_7816573 := by
    simpa [prefixWord, tailWord_7816573, baseEnd_7816573] using wordTrace_append hprefix tailTrace_7816573
  have hstable : (prefixWord ++ tailWord_7816573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7816573).length < 2 ^ (prefixWord ++ tailWord_7816573).sum := by decide
  have hdescent : baseEnd_7816573 < baseStart_7816573 := by decide
  rcases family_descends (prefixWord ++ tailWord_7816573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7816576 : List Nat := [2, 1, 1, 2, 1, 2, 1, 4, 4, 5]
def baseStart_7816576 : Nat := 118140960795 + 7816576 * 2 ^ 59
def prefixEnd_7816576 : Nat := 4983230072969 + 3 ^ 40 * 7816576 * 2
def baseEnd_7816576 : Nat := 1337886853466171614717409

theorem tailTrace_7816576 : CollatzResearch.WordTrace tailWord_7816576 prefixEnd_7816576 1337886853466171614717409 := by
  unfold tailWord_7816576
  simp only [CollatzResearch.WordTrace]
  refine ⟨142546974064943795871962791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190062632086591727829283721 142546974064943795871962791)
  ·
    refine ⟨213820461097415693807944187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142546974064943795871962791 213820461097415693807944187)
    ·
      refine ⟨320730691646123540711916281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213820461097415693807944187 320730691646123540711916281)
      ·
        refine ⟨240548018734592655533937211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 320730691646123540711916281 240548018734592655533937211)
        ·
          refine ⟨360822028101888983300905817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 240548018734592655533937211 360822028101888983300905817)
          ·
            refine ⟨270616521076416737475679363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 360822028101888983300905817 270616521076416737475679363)
            ·
              refine ⟨405924781614625106213519045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 270616521076416737475679363 405924781614625106213519045)
              ·
                refine ⟨76110896552742207415034821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 405924781614625106213519045 76110896552742207415034821)
                ·
                  refine ⟨14270793103639163890319029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 76110896552742207415034821 14270793103639163890319029)
                  ·
                    refine ⟨1337886853466171614717409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14270793103639163890319029 1337886853466171614717409)
                    ·
                      rfl

theorem cell23_7816576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 4, 4, 5].length) (baseStart_7816576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7816576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7816576 prefixEnd_7816576 := by exact prefixLift 7816576
  have htrace : WordTrace (prefixWord ++ tailWord_7816576) baseStart_7816576 baseEnd_7816576 := by
    simpa [prefixWord, tailWord_7816576, baseEnd_7816576] using wordTrace_append hprefix tailTrace_7816576
  have hstable : (prefixWord ++ tailWord_7816576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7816576).length < 2 ^ (prefixWord ++ tailWord_7816576).sum := by decide
  have hdescent : baseEnd_7816576 < baseStart_7816576 := by decide
  rcases family_descends (prefixWord ++ tailWord_7816576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7816656 : List Nat := [2, 1, 1, 1, 1, 2, 2, 2, 3, 2, 6]
def baseStart_7816656 : Nat := 118140960795 + 7816656 * 2 ^ 59
def prefixEnd_7816656 : Nat := 4983230072969 + 3 ^ 40 * 7816656 * 2
def baseEnd_7816656 : Nat := 4013701638850874531151859

theorem tailTrace_7816656 : CollatzResearch.WordTrace tailWord_7816656 prefixEnd_7816656 4013701638850874531151859 := by
  unfold tailWord_7816656
  simp only [CollatzResearch.WordTrace]
  refine ⟨142548432984798882703418911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190064577313065176937891881 142548432984798882703418911)
  ·
    refine ⟨213822649477198324055128367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142548432984798882703418911 213822649477198324055128367)
    ·
      refine ⟨320733974215797486082692551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213822649477198324055128367 320733974215797486082692551)
      ·
        refine ⟨481100961323696229124038827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 320733974215797486082692551 481100961323696229124038827)
        ·
          refine ⟨721651441985544343686058241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 481100961323696229124038827 721651441985544343686058241)
          ·
            refine ⟨541238581489158257764543681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 721651441985544343686058241 541238581489158257764543681)
            ·
              refine ⟨405928936116868693323407761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 541238581489158257764543681 405928936116868693323407761)
              ·
                refine ⟨304446702087651519992555821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 405928936116868693323407761 304446702087651519992555821)
                ·
                  refine ⟨114167513282869319997208433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 304446702087651519992555821 114167513282869319997208433)
                  ·
                    refine ⟨85625634962151989997906325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 114167513282869319997208433 85625634962151989997906325)
                    ·
                      refine ⟨4013701638850874531151859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 85625634962151989997906325 4013701638850874531151859)
                      ·
                        rfl

theorem cell23_7816656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 2, 3, 2, 6].length) (baseStart_7816656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7816656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7816656 prefixEnd_7816656 := by exact prefixLift 7816656
  have htrace : WordTrace (prefixWord ++ tailWord_7816656) baseStart_7816656 baseEnd_7816656 := by
    simpa [prefixWord, tailWord_7816656, baseEnd_7816656] using wordTrace_append hprefix tailTrace_7816656
  have hstable : (prefixWord ++ tailWord_7816656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7816656).length < 2 ^ (prefixWord ++ tailWord_7816656).sum := by decide
  have hdescent : baseEnd_7816656 < baseStart_7816656 := by decide
  rcases family_descends (prefixWord ++ tailWord_7816656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7816700 : List Nat := [2, 2, 2, 1, 2, 1, 5, 2, 1, 5]
def baseStart_7816700 : Nat := 118140960795 + 7816700 * 2 ^ 59
def prefixEnd_7816700 : Nat := 4983230072969 + 3 ^ 40 * 7816700 * 2
def baseEnd_7816700 : Nat := 1337908077333224119667219

theorem tailTrace_7816700 : CollatzResearch.WordTrace tailWord_7816700 prefixEnd_7816700 1337908077333224119667219 := by
  unfold tailWord_7816700
  simp only [CollatzResearch.WordTrace]
  refine ⟨142549235390719180460719777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190065647187625573947626369 142549235390719180460719777)
  ·
    refine ⟨106911926543039385345539833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142549235390719180460719777 106911926543039385345539833)
    ·
      refine ⟨80183944907279539009154875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106911926543039385345539833 80183944907279539009154875)
      ·
        refine ⟨120275917360919308513732313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80183944907279539009154875 120275917360919308513732313)
        ·
          refine ⟨90206938020689481385299235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120275917360919308513732313 90206938020689481385299235)
          ·
            refine ⟨135310407031034222077948853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90206938020689481385299235 135310407031034222077948853)
            ·
              refine ⟨12685350659159458319807705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 135310407031034222077948853 12685350659159458319807705)
              ·
                refine ⟨9514012994369593739855779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12685350659159458319807705 9514012994369593739855779)
                ·
                  refine ⟨14271019491554390609783669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9514012994369593739855779 14271019491554390609783669)
                  ·
                    refine ⟨1337908077333224119667219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14271019491554390609783669 1337908077333224119667219)
                    ·
                      rfl

theorem cell23_7816700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 5, 2, 1, 5].length) (baseStart_7816700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7816700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7816700 prefixEnd_7816700 := by exact prefixLift 7816700
  have htrace : WordTrace (prefixWord ++ tailWord_7816700) baseStart_7816700 baseEnd_7816700 := by
    simpa [prefixWord, tailWord_7816700, baseEnd_7816700] using wordTrace_append hprefix tailTrace_7816700
  have hstable : (prefixWord ++ tailWord_7816700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7816700).length < 2 ^ (prefixWord ++ tailWord_7816700).sum := by decide
  have hdescent : baseEnd_7816700 < baseStart_7816700 := by decide
  rcases family_descends (prefixWord ++ tailWord_7816700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7816713 : List Nat := [1, 2, 1, 1, 3, 1, 5, 2, 1, 6]
def baseStart_7816713 : Nat := 118140960795 + 7816713 * 2 ^ 59
def prefixEnd_7816713 : Nat := 4983230072969 + 3 ^ 40 * 7816713 * 2
def baseEnd_7816713 : Nat := 1337910302416060269379699

theorem tailTrace_7816713 : CollatzResearch.WordTrace tailWord_7816713 prefixEnd_7816713 1337910302416060269379699 := by
  unfold tailWord_7816713
  simp only [CollatzResearch.WordTrace]
  refine ⟨285098944930391264141662793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190065963286927509427775195 285098944930391264141662793)
  ·
    refine ⟨213824208697793448106247095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 285098944930391264141662793 213824208697793448106247095)
    ·
      refine ⟨320736313046690172159370643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213824208697793448106247095 320736313046690172159370643)
      ·
        refine ⟨481104469570035258239055965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 320736313046690172159370643 481104469570035258239055965)
        ·
          refine ⟨180414176088763221839645987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 481104469570035258239055965 180414176088763221839645987)
          ·
            refine ⟨270621264133144832759468981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 180414176088763221839645987 270621264133144832759468981)
            ·
              refine ⟨25370743512482328071200217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 270621264133144832759468981 25370743512482328071200217)
              ·
                refine ⟨19028057634361746053400163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25370743512482328071200217 19028057634361746053400163)
                ·
                  refine ⟨28542086451542619080100245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19028057634361746053400163 28542086451542619080100245)
                  ·
                    refine ⟨1337910302416060269379699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28542086451542619080100245 1337910302416060269379699)
                    ·
                      rfl

theorem cell23_7816713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 5, 2, 1, 6].length) (baseStart_7816713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7816713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7816713 prefixEnd_7816713 := by exact prefixLift 7816713
  have htrace : WordTrace (prefixWord ++ tailWord_7816713) baseStart_7816713 baseEnd_7816713 := by
    simpa [prefixWord, tailWord_7816713, baseEnd_7816713] using wordTrace_append hprefix tailTrace_7816713
  have hstable : (prefixWord ++ tailWord_7816713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7816713).length < 2 ^ (prefixWord ++ tailWord_7816713).sum := by decide
  have hdescent : baseEnd_7816713 < baseStart_7816713 := by decide
  rcases family_descends (prefixWord ++ tailWord_7816713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7816758 : List Nat := [5, 1, 2, 1, 4, 1, 1, 1, 2, 3, 2]
def baseStart_7816758 : Nat := 118140960795 + 7816758 * 2 ^ 59
def prefixEnd_7816758 : Nat := 4983230072969 + 3 ^ 40 * 7816758 * 2
def baseEnd_7816758 : Nat := 4013754013877633132076391

theorem tailTrace_7816758 : CollatzResearch.WordTrace tailWord_7816758 prefixEnd_7816758 4013754013877633132076391 := by
  unfold tailWord_7816758
  simp only [CollatzResearch.WordTrace]
  refine ⟨17818786638451764801690683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 190067057476818824551367285 17818786638451764801690683)
  ·
    refine ⟨26728179957677647202536025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17818786638451764801690683 26728179957677647202536025)
    ·
      refine ⟨20046134968258235401902019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26728179957677647202536025 20046134968258235401902019)
      ·
        refine ⟨30069202452387353102853029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20046134968258235401902019 30069202452387353102853029)
        ·
          refine ⟨5637975459822628706784943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30069202452387353102853029 5637975459822628706784943)
          ·
            refine ⟨8456963189733943060177415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5637975459822628706784943 8456963189733943060177415)
            ·
              refine ⟨12685444784600914590266123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8456963189733943060177415 12685444784600914590266123)
              ·
                refine ⟨19028167176901371885399185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12685444784600914590266123 19028167176901371885399185)
                ·
                  refine ⟨14271125382676028914049389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19028167176901371885399185 14271125382676028914049389)
                  ·
                    refine ⟨5351672018503510842768521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14271125382676028914049389 5351672018503510842768521)
                    ·
                      refine ⟨4013754013877633132076391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5351672018503510842768521 4013754013877633132076391)
                      ·
                        rfl

theorem cell23_7816758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 4, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 4, 1, 1, 1, 2, 3, 2].length) (baseStart_7816758 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7816758 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7816758 prefixEnd_7816758 := by exact prefixLift 7816758
  have htrace : WordTrace (prefixWord ++ tailWord_7816758) baseStart_7816758 baseEnd_7816758 := by
    simpa [prefixWord, tailWord_7816758, baseEnd_7816758] using wordTrace_append hprefix tailTrace_7816758
  have hstable : (prefixWord ++ tailWord_7816758).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7816758).length < 2 ^ (prefixWord ++ tailWord_7816758).sum := by decide
  have hdescent : baseEnd_7816758 < baseStart_7816758 := by decide
  rcases family_descends (prefixWord ++ tailWord_7816758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7816760 : List Nat := [2, 1, 2, 1, 4, 3, 3, 7]
def baseStart_7816760 : Nat := 118140960795 + 7816760 * 2 ^ 59
def prefixEnd_7816760 : Nat := 4983230072969 + 3 ^ 40 * 7816760 * 2
def baseEnd_7816760 : Nat := 148657594105146004601903

theorem tailTrace_7816760 : CollatzResearch.WordTrace tailWord_7816760 prefixEnd_7816760 148657594105146004601903 := by
  unfold tailWord_7816760
  simp only [CollatzResearch.WordTrace]
  refine ⟨142550329580610495584311867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190067106107480660779082489 142550329580610495584311867)
  ·
    refine ⟨213825494370915743376467801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142550329580610495584311867 213825494370915743376467801)
    ·
      refine ⟨160369120778186807532350851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 213825494370915743376467801 160369120778186807532350851)
      ·
        refine ⟨240553681167280211298526277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160369120778186807532350851 240553681167280211298526277)
        ·
          refine ⟨45103815218865039618473677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 240553681167280211298526277 45103815218865039618473677)
          ·
            refine ⟨16913930707074389856927629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45103815218865039618473677 16913930707074389856927629)
            ·
              refine ⟨6342724015152896196347861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16913930707074389856927629 6342724015152896196347861)
              ·
                refine ⟨148657594105146004601903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6342724015152896196347861 148657594105146004601903)
                ·
                  rfl

theorem cell23_7816760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 3, 7].length) (baseStart_7816760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7816760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7816760 prefixEnd_7816760 := by exact prefixLift 7816760
  have htrace : WordTrace (prefixWord ++ tailWord_7816760) baseStart_7816760 baseEnd_7816760 := by
    simpa [prefixWord, tailWord_7816760, baseEnd_7816760] using wordTrace_append hprefix tailTrace_7816760
  have hstable : (prefixWord ++ tailWord_7816760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7816760).length < 2 ^ (prefixWord ++ tailWord_7816760).sum := by decide
  have hdescent : baseEnd_7816760 < baseStart_7816760 := by decide
  rcases family_descends (prefixWord ++ tailWord_7816760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7816781 : List Nat := [1, 6, 1, 1, 3, 2, 1, 2, 2, 4]
def baseStart_7816781 : Nat := 118140960795 + 7816781 * 2 ^ 59
def prefixEnd_7816781 : Nat := 4983230072969 + 3 ^ 40 * 7816781 * 2
def baseEnd_7816781 : Nat := 1337921941310895514029595

theorem tailTrace_7816781 : CollatzResearch.WordTrace tailWord_7816781 prefixEnd_7816781 1337921941310895514029595 := by
  unfold tailWord_7816781
  simp only [CollatzResearch.WordTrace]
  refine ⟨285101425094144911755138197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190067616729429941170092131 285101425094144911755138197)
  ·
    refine ⟨13364129301288042738522103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 285101425094144911755138197 13364129301288042738522103)
    ·
      refine ⟨20046193951932064107783155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13364129301288042738522103 20046193951932064107783155)
      ·
        refine ⟨30069290927898096161674733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20046193951932064107783155 30069290927898096161674733)
        ·
          refine ⟨11275984097961786060628025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30069290927898096161674733 11275984097961786060628025)
          ·
            refine ⟨8456988073471339545471019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11275984097961786060628025 8456988073471339545471019)
            ·
              refine ⟨12685482110207009318206529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8456988073471339545471019 12685482110207009318206529)
              ·
                refine ⟨9514111582655256988654897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12685482110207009318206529 9514111582655256988654897)
                ·
                  refine ⟨7135583686991442741491173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9514111582655256988654897 7135583686991442741491173)
                  ·
                    refine ⟨1337921941310895514029595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7135583686991442741491173 1337921941310895514029595)
                    ·
                      rfl

theorem cell23_7816781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 2, 1, 2, 2, 4].length) (baseStart_7816781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7816781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7816781 prefixEnd_7816781 := by exact prefixLift 7816781
  have htrace : WordTrace (prefixWord ++ tailWord_7816781) baseStart_7816781 baseEnd_7816781 := by
    simpa [prefixWord, tailWord_7816781, baseEnd_7816781] using wordTrace_append hprefix tailTrace_7816781
  have hstable : (prefixWord ++ tailWord_7816781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7816781).length < 2 ^ (prefixWord ++ tailWord_7816781).sum := by decide
  have hdescent : baseEnd_7816781 < baseStart_7816781 := by decide
  rcases family_descends (prefixWord ++ tailWord_7816781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7816793 : List Nat := [1, 2, 1, 2, 2, 1, 1, 3, 1, 5, 4]
def baseStart_7816793 : Nat := 118140960795 + 7816793 * 2 ^ 59
def prefixEnd_7816793 : Nat := 4983230072969 + 3 ^ 40 * 7816793 * 2
def baseEnd_7816793 : Nat := 4013771985700540495138729

theorem tailTrace_7816793 : CollatzResearch.WordTrace tailWord_7816793 prefixEnd_7816793 4013771985700540495138729 := by
  unfold tailWord_7816793
  simp only [CollatzResearch.WordTrace]
  refine ⟨285101862770101437804575033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190067908513400958536383355 285101862770101437804575033)
  ·
    refine ⟨213826397077576078353431275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 285101862770101437804575033 213826397077576078353431275)
    ·
      refine ⟨320739595616364117530146913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213826397077576078353431275 320739595616364117530146913)
      ·
        refine ⟨240554696712273088147610185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 320739595616364117530146913 240554696712273088147610185)
        ·
          refine ⟨180416022534204816110707639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 240554696712273088147610185 180416022534204816110707639)
          ·
            refine ⟨270624033801307224166061459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 180416022534204816110707639 270624033801307224166061459)
            ·
              refine ⟨405936050701960836249092189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 270624033801307224166061459 405936050701960836249092189)
              ·
                refine ⟨152226019013235313593409571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 405936050701960836249092189 152226019013235313593409571)
                ·
                  refine ⟨228339028519852970390114357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 152226019013235313593409571 228339028519852970390114357)
                  ·
                    refine ⟨21406783923736215974073221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 228339028519852970390114357 21406783923736215974073221)
                    ·
                      refine ⟨4013771985700540495138729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21406783923736215974073221 4013771985700540495138729)
                      ·
                        rfl

theorem cell23_7816793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 3, 1, 5, 4].length) (baseStart_7816793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7816793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7816793 prefixEnd_7816793 := by exact prefixLift 7816793
  have htrace : WordTrace (prefixWord ++ tailWord_7816793) baseStart_7816793 baseEnd_7816793 := by
    simpa [prefixWord, tailWord_7816793, baseEnd_7816793] using wordTrace_append hprefix tailTrace_7816793
  have hstable : (prefixWord ++ tailWord_7816793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7816793).length < 2 ^ (prefixWord ++ tailWord_7816793).sum := by decide
  have hdescent : baseEnd_7816793 < baseStart_7816793 := by decide
  rcases family_descends (prefixWord ++ tailWord_7816793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7816827 : List Nat := [1, 1, 1, 1, 1, 4, 3, 1, 6, 2, 2]
def baseStart_7816827 : Nat := 118140960795 + 7816827 * 2 ^ 59
def prefixEnd_7816827 : Nat := 4983230072969 + 3 ^ 40 * 7816827 * 2
def baseEnd_7816827 : Nat := 4013789444042793362113573

theorem tailTrace_7816827 : CollatzResearch.WordTrace tailWord_7816827 prefixEnd_7816827 4013789444042793362113573 := by
  unfold tailWord_7816827
  simp only [CollatzResearch.WordTrace]
  refine ⟨285103102851978261611312735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190068735234652174407541823 285103102851978261611312735)
  ·
    refine ⟨427654654277967392416969103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285103102851978261611312735 427654654277967392416969103)
    ·
      refine ⟨641481981416951088625453655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 427654654277967392416969103 641481981416951088625453655)
      ·
        refine ⟨962222972125426632938180483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 641481981416951088625453655 962222972125426632938180483)
        ·
          refine ⟨1443334458188139949407270725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 962222972125426632938180483 1443334458188139949407270725)
          ·
            refine ⟨270625210910276240513863261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1443334458188139949407270725 270625210910276240513863261)
            ·
              refine ⟨101484454091353590192698723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 270625210910276240513863261 101484454091353590192698723)
              ·
                refine ⟨152226681137030385289048085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 101484454091353590192698723 152226681137030385289048085)
                ·
                  refine ⟨7135625678298299310424129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 152226681137030385289048085 7135625678298299310424129)
                  ·
                    refine ⟨5351719258723724482818097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7135625678298299310424129 5351719258723724482818097)
                    ·
                      refine ⟨4013789444042793362113573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5351719258723724482818097 4013789444042793362113573)
                      ·
                        rfl

theorem cell23_7816827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 1, 6, 2, 2].length) (baseStart_7816827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7816827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7816827 prefixEnd_7816827 := by exact prefixLift 7816827
  have htrace : WordTrace (prefixWord ++ tailWord_7816827) baseStart_7816827 baseEnd_7816827 := by
    simpa [prefixWord, tailWord_7816827, baseEnd_7816827] using wordTrace_append hprefix tailTrace_7816827
  have hstable : (prefixWord ++ tailWord_7816827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7816827).length < 2 ^ (prefixWord ++ tailWord_7816827).sum := by decide
  have hdescent : baseEnd_7816827 < baseStart_7816827 := by decide
  rcases family_descends (prefixWord ++ tailWord_7816827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7816843 : List Nat := [1, 1, 1, 1, 4, 1, 3, 1, 1, 2, 7]
def baseStart_7816843 : Nat := 118140960795 + 7816843 * 2 ^ 59
def prefixEnd_7816843 : Nat := 4983230072969 + 3 ^ 40 * 7816843 * 2
def baseEnd_7816843 : Nat := 4013797659733265299513499

theorem tailTrace_7816843 : CollatzResearch.WordTrace tailWord_7816843 prefixEnd_7816843 4013797659733265299513499 := by
  unfold tailWord_7816843
  simp only [CollatzResearch.WordTrace]
  refine ⟨285103686419920296343895183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190069124279946864229263455 285103686419920296343895183)
  ·
    refine ⟨427655529629880444515842775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285103686419920296343895183 427655529629880444515842775)
    ·
      refine ⟨641483294444820666773764163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 427655529629880444515842775 641483294444820666773764163)
      ·
        refine ⟨962224941667231000160646245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 641483294444820666773764163 962224941667231000160646245)
        ·
          refine ⟨180417176562605812530121171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 962224941667231000160646245 180417176562605812530121171)
          ·
            refine ⟨270625764843908718795181757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 180417176562605812530121171 270625764843908718795181757)
            ·
              refine ⟨101484661816465769548193159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 270625764843908718795181757 101484661816465769548193159)
              ·
                refine ⟨152226992724698654322289739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 101484661816465769548193159 152226992724698654322289739)
                ·
                  refine ⟨228340489087047981483434609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 152226992724698654322289739 228340489087047981483434609)
                  ·
                    refine ⟨171255366815285986112575957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 228340489087047981483434609 171255366815285986112575957)
                    ·
                      refine ⟨4013797659733265299513499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 171255366815285986112575957 4013797659733265299513499)
                      ·
                        rfl

theorem cell23_7816843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 1, 1, 2, 7].length) (baseStart_7816843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7816843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7816843 prefixEnd_7816843 := by exact prefixLift 7816843
  have htrace : WordTrace (prefixWord ++ tailWord_7816843) baseStart_7816843 baseEnd_7816843 := by
    simpa [prefixWord, tailWord_7816843, baseEnd_7816843] using wordTrace_append hprefix tailTrace_7816843
  have hstable : (prefixWord ++ tailWord_7816843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7816843).length < 2 ^ (prefixWord ++ tailWord_7816843).sum := by decide
  have hdescent : baseEnd_7816843 < baseStart_7816843 := by decide
  rcases family_descends (prefixWord ++ tailWord_7816843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7816844 : List Nat := [2, 2, 1, 2, 1, 1, 4, 4, 2, 2, 2]
def baseStart_7816844 : Nat := 118140960795 + 7816844 * 2 ^ 59
def prefixEnd_7816844 : Nat := 4983230072969 + 3 ^ 40 * 7816844 * 2
def baseEnd_7816844 : Nat := 4013798173213919795600995

theorem tailTrace_7816844 : CollatzResearch.WordTrace tailWord_7816844 prefixEnd_7816844 4013798173213919795600995 := by
  unfold tailWord_7816844
  simp only [CollatzResearch.WordTrace]
  refine ⟨142551861446458336757340793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190069148595277782343121057 142551861446458336757340793)
  ·
    refine ⟨106913896084843752568005595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142551861446458336757340793 106913896084843752568005595)
    ·
      refine ⟨160370844127265628852008393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106913896084843752568005595 160370844127265628852008393)
      ·
        refine ⟨120278133095449221639006295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 160370844127265628852008393 120278133095449221639006295)
        ·
          refine ⟨180417199643173832458509443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120278133095449221639006295 180417199643173832458509443)
          ·
            refine ⟨270625799464760748687764165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 180417199643173832458509443 270625799464760748687764165)
            ·
              refine ⟨50742337399642640378955781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 270625799464760748687764165 50742337399642640378955781)
              ·
                refine ⟨9514188262432995071054209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50742337399642640378955781 9514188262432995071054209)
                ·
                  refine ⟨7135641196824746303290657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9514188262432995071054209 7135641196824746303290657)
                  ·
                    refine ⟨5351730897618559727467993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7135641196824746303290657 5351730897618559727467993)
                    ·
                      refine ⟨4013798173213919795600995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5351730897618559727467993 4013798173213919795600995)
                      ·
                        rfl

theorem cell23_7816844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 4, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 4, 4, 2, 2, 2].length) (baseStart_7816844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7816844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7816844 prefixEnd_7816844 := by exact prefixLift 7816844
  have htrace : WordTrace (prefixWord ++ tailWord_7816844) baseStart_7816844 baseEnd_7816844 := by
    simpa [prefixWord, tailWord_7816844, baseEnd_7816844] using wordTrace_append hprefix tailTrace_7816844
  have hstable : (prefixWord ++ tailWord_7816844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7816844).length < 2 ^ (prefixWord ++ tailWord_7816844).sum := by decide
  have hdescent : baseEnd_7816844 < baseStart_7816844 := by decide
  rcases family_descends (prefixWord ++ tailWord_7816844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7816880 : List Nat := [2, 1, 1, 1, 2, 1, 5, 3, 2, 5]
def baseStart_7816880 : Nat := 118140960795 + 7816880 * 2 ^ 59
def prefixEnd_7816880 : Nat := 4983230072969 + 3 ^ 40 * 7816880 * 2
def baseEnd_7816880 : Nat := 1337938886172493884916943

theorem tailTrace_7816880 : CollatzResearch.WordTrace tailWord_7816880 prefixEnd_7816880 1337938886172493884916943 := by
  unfold tailWord_7816880
  simp only [CollatzResearch.WordTrace]
  refine ⟨142552517960393125831496047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190070023947190834441994729 142552517960393125831496047)
  ·
    refine ⟨213828776940589688747244071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142552517960393125831496047 213828776940589688747244071)
    ·
      refine ⟨320743165410884533120866107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213828776940589688747244071 320743165410884533120866107)
      ·
        refine ⟨481114748116326799681299161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 320743165410884533120866107 481114748116326799681299161)
        ·
          refine ⟨360836061087245099760974371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 481114748116326799681299161 360836061087245099760974371)
          ·
            refine ⟨541254091630867649641461557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 360836061087245099760974371 541254091630867649641461557)
            ·
              refine ⟨50742571090393842153887021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 541254091630867649641461557 50742571090393842153887021)
              ·
                refine ⟨19028464158897690807707633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50742571090393842153887021 19028464158897690807707633)
                ·
                  refine ⟨14271348119173268105780725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19028464158897690807707633 14271348119173268105780725)
                  ·
                    refine ⟨1337938886172493884916943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14271348119173268105780725 1337938886172493884916943)
                    ·
                      rfl

theorem cell23_7816880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 5, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 5, 3, 2, 5].length) (baseStart_7816880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7816880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7816880 prefixEnd_7816880 := by exact prefixLift 7816880
  have htrace : WordTrace (prefixWord ++ tailWord_7816880) baseStart_7816880 baseEnd_7816880 := by
    simpa [prefixWord, tailWord_7816880, baseEnd_7816880] using wordTrace_append hprefix tailTrace_7816880
  have hstable : (prefixWord ++ tailWord_7816880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7816880).length < 2 ^ (prefixWord ++ tailWord_7816880).sum := by decide
  have hdescent : baseEnd_7816880 < baseStart_7816880 := by decide
  rcases family_descends (prefixWord ++ tailWord_7816880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7816890 : List Nat := [3, 1, 1, 1, 2, 4, 1, 2, 1, 2, 5]
def baseStart_7816890 : Nat := 118140960795 + 7816890 * 2 ^ 59
def prefixEnd_7816890 : Nat := 4983230072969 + 3 ^ 40 * 7816890 * 2
def baseEnd_7816890 : Nat := 4013821793324026615625783

theorem tailTrace_7816890 : CollatzResearch.WordTrace tailWord_7816890 prefixEnd_7816890 4013821793324026615625783 := by
  unfold tailWord_7816890
  simp only [CollatzResearch.WordTrace]
  refine ⟨71276350162687505842714031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 190070267100500015580570749 71276350162687505842714031)
  ·
    refine ⟨106914525244031258764071047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71276350162687505842714031 106914525244031258764071047)
    ·
      refine ⟨160371787866046888146106571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106914525244031258764071047 160371787866046888146106571)
      ·
        refine ⟨240557681799070332219159857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160371787866046888146106571 240557681799070332219159857)
        ·
          refine ⟨180418261349302749164369893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 240557681799070332219159857 180418261349302749164369893)
          ·
            refine ⟨33828424002994265468319355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 180418261349302749164369893 33828424002994265468319355)
            ·
              refine ⟨50742636004491398202479033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33828424002994265468319355 50742636004491398202479033)
              ·
                refine ⟨38056977003368548651859275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50742636004491398202479033 38056977003368548651859275)
                ·
                  refine ⟨57085465505052822977788913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38056977003368548651859275 57085465505052822977788913)
                  ·
                    refine ⟨42814099128789617233341685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 57085465505052822977788913 42814099128789617233341685)
                    ·
                      refine ⟨4013821793324026615625783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42814099128789617233341685 4013821793324026615625783)
                      ·
                        rfl

theorem cell23_7816890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 1, 2, 1, 2, 5].length) (baseStart_7816890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7816890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7816890 prefixEnd_7816890 := by exact prefixLift 7816890
  have htrace : WordTrace (prefixWord ++ tailWord_7816890) baseStart_7816890 baseEnd_7816890 := by
    simpa [prefixWord, tailWord_7816890, baseEnd_7816890] using wordTrace_append hprefix tailTrace_7816890
  have hstable : (prefixWord ++ tailWord_7816890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7816890).length < 2 ^ (prefixWord ++ tailWord_7816890).sum := by decide
  have hdescent : baseEnd_7816890 < baseStart_7816890 := by decide
  rcases family_descends (prefixWord ++ tailWord_7816890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7816927 : List Nat := [1, 1, 2, 3, 2, 2, 3, 2, 3, 4]
def baseStart_7816927 : Nat := 118140960795 + 7816927 * 2 ^ 59
def prefixEnd_7816927 : Nat := 4983230072969 + 3 ^ 40 * 7816927 * 2
def baseEnd_7816927 : Nat := 1337946930702747656954371

theorem tailTrace_7816927 : CollatzResearch.WordTrace tailWord_7816927 prefixEnd_7816927 1337946930702747656954371 := by
  unfold tailWord_7816927
  simp only [CollatzResearch.WordTrace]
  refine ⟨285106750151615978689953035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190071166767743985793302023 285106750151615978689953035)
  ·
    refine ⟨427660125227423968034929553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285106750151615978689953035 427660125227423968034929553)
    ·
      refine ⟨320745093920567976026197165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 427660125227423968034929553 320745093920567976026197165)
      ·
        refine ⟨120279410220212991009823937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 320745093920567976026197165 120279410220212991009823937)
        ·
          refine ⟨90209557665159743257367953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120279410220212991009823937 90209557665159743257367953)
          ·
            refine ⟨67657168248869807443025965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90209557665159743257367953 67657168248869807443025965)
            ·
              refine ⟨25371438093326177791134737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67657168248869807443025965 25371438093326177791134737)
              ·
                refine ⟨19028578569994633343351053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25371438093326177791134737 19028578569994633343351053)
                ·
                  refine ⟨7135716963747987503756645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19028578569994633343351053 7135716963747987503756645)
                  ·
                    refine ⟨1337946930702747656954371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7135716963747987503756645 1337946930702747656954371)
                    ·
                      rfl

theorem cell23_7816927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 3, 2, 3, 4].length) (baseStart_7816927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7816927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7816927 prefixEnd_7816927 := by exact prefixLift 7816927
  have htrace : WordTrace (prefixWord ++ tailWord_7816927) baseStart_7816927 baseEnd_7816927 := by
    simpa [prefixWord, tailWord_7816927, baseEnd_7816927] using wordTrace_append hprefix tailTrace_7816927
  have hstable : (prefixWord ++ tailWord_7816927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7816927).length < 2 ^ (prefixWord ++ tailWord_7816927).sum := by decide
  have hdescent : baseEnd_7816927 < baseStart_7816927 := by decide
  rcases family_descends (prefixWord ++ tailWord_7816927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7816931 : List Nat := [1, 1, 1, 7, 3, 1, 1, 1, 2, 5]
def baseStart_7816931 : Nat := 118140960795 + 7816931 * 2 ^ 59
def prefixEnd_7816931 : Nat := 4983230072969 + 3 ^ 40 * 7816931 * 2
def baseEnd_7816931 : Nat := 1337947615343620318404365

theorem tailTrace_7816931 : CollatzResearch.WordTrace tailWord_7816931 prefixEnd_7816931 1337947615343620318404365 := by
  unfold tailWord_7816931
  simp only [CollatzResearch.WordTrace]
  refine ⟨285106896043601487373098647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190071264029067658248732431 285106896043601487373098647)
  ·
    refine ⟨427660344065402231059647971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285106896043601487373098647 427660344065402231059647971)
    ·
      refine ⟨641490516098103346589471957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 427660344065402231059647971 641490516098103346589471957)
      ·
        refine ⟨15034933971049297185690749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 641490516098103346589471957 15034933971049297185690749)
        ·
          refine ⟨5638100239143486444634031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15034933971049297185690749 5638100239143486444634031)
          ·
            refine ⟨8457150358715229666951047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5638100239143486444634031 8457150358715229666951047)
            ·
              refine ⟨12685725538072844500426571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8457150358715229666951047 12685725538072844500426571)
              ·
                refine ⟨19028588307109266750639857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12685725538072844500426571 19028588307109266750639857)
                ·
                  refine ⟨14271441230331950062979893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19028588307109266750639857 14271441230331950062979893)
                  ·
                    refine ⟨1337947615343620318404365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14271441230331950062979893 1337947615343620318404365)
                    ·
                      rfl

theorem cell23_7816931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 3, 1, 1, 1, 2, 5].length) (baseStart_7816931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7816931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7816931 prefixEnd_7816931 := by exact prefixLift 7816931
  have htrace : WordTrace (prefixWord ++ tailWord_7816931) baseStart_7816931 baseEnd_7816931 := by
    simpa [prefixWord, tailWord_7816931, baseEnd_7816931] using wordTrace_append hprefix tailTrace_7816931
  have hstable : (prefixWord ++ tailWord_7816931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7816931).length < 2 ^ (prefixWord ++ tailWord_7816931).sum := by decide
  have hdescent : baseEnd_7816931 < baseStart_7816931 := by decide
  rcases family_descends (prefixWord ++ tailWord_7816931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7816984 : List Nat := [2, 1, 2, 3, 1, 1, 4, 2, 3, 1, 3]
def baseStart_7816984 : Nat := 118140960795 + 7816984 * 2 ^ 59
def prefixEnd_7816984 : Nat := 4983230072969 + 3 ^ 40 * 7816984 * 2
def baseEnd_7816984 : Nat := 4013870060505549247850351

theorem tailTrace_7816984 : CollatzResearch.WordTrace tailWord_7816984 prefixEnd_7816984 4013870060505549247850351 := by
  unfold tailWord_7816984
  simp only [CollatzResearch.WordTrace]
  refine ⟨142554414556204738712389003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190072552741606318283185337 142554414556204738712389003)
  ·
    refine ⟨213831621834307108068583505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142554414556204738712389003 213831621834307108068583505)
    ·
      refine ⟨160373716375730331051437629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 213831621834307108068583505 160373716375730331051437629)
      ·
        refine ⟨60140143640898874144289111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 160373716375730331051437629 60140143640898874144289111)
        ·
          refine ⟨90210215461348311216433667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60140143640898874144289111 90210215461348311216433667)
          ·
            refine ⟨135315323192022466824650501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90210215461348311216433667 135315323192022466824650501)
            ·
              refine ⟨25371623098504212529621969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 135315323192022466824650501 25371623098504212529621969)
              ·
                refine ⟨19028717323878159397216477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25371623098504212529621969 19028717323878159397216477)
                ·
                  refine ⟨7135768996454309773956179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19028717323878159397216477 7135768996454309773956179)
                  ·
                    refine ⟨10703653494681464660934269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7135768996454309773956179 10703653494681464660934269)
                    ·
                      refine ⟨4013870060505549247850351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10703653494681464660934269 4013870060505549247850351)
                      ·
                        rfl

theorem cell23_7816984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 4, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 4, 2, 3, 1, 3].length) (baseStart_7816984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7816984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7816984 prefixEnd_7816984 := by exact prefixLift 7816984
  have htrace : WordTrace (prefixWord ++ tailWord_7816984) baseStart_7816984 baseEnd_7816984 := by
    simpa [prefixWord, tailWord_7816984, baseEnd_7816984] using wordTrace_append hprefix tailTrace_7816984
  have hstable : (prefixWord ++ tailWord_7816984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7816984).length < 2 ^ (prefixWord ++ tailWord_7816984).sum := by decide
  have hdescent : baseEnd_7816984 < baseStart_7816984 := by decide
  rcases family_descends (prefixWord ++ tailWord_7816984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7816994 : List Nat := [3, 3, 1, 1, 2, 1, 1, 3, 1, 5, 2]
def baseStart_7816994 : Nat := 118140960795 + 7816994 * 2 ^ 59
def prefixEnd_7816994 : Nat := 4983230072969 + 3 ^ 40 * 7816994 * 2
def baseEnd_7816994 : Nat := 4013875195312094208725305

theorem tailTrace_7816994 : CollatzResearch.WordTrace tailWord_7816994 prefixEnd_7816994 4013875195312094208725305 := by
  unfold tailWord_7816994
  simp only [CollatzResearch.WordTrace]
  refine ⟨71277298460593312283160509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 190072795894915499421761357 71277298460593312283160509)
  ·
    refine ⟨26728986922722492106185191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71277298460593312283160509 26728986922722492106185191)
    ·
      refine ⟨40093480384083738159277787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26728986922722492106185191 40093480384083738159277787)
      ·
        refine ⟨60140220576125607238916681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40093480384083738159277787 60140220576125607238916681)
        ·
          refine ⟨45105165432094205429187511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60140220576125607238916681 45105165432094205429187511)
          ·
            refine ⟨67657748148141308143781267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45105165432094205429187511 67657748148141308143781267)
            ·
              refine ⟨101486622222211962215671901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67657748148141308143781267 101486622222211962215671901)
              ·
                refine ⟨38057483333329485830876963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 101486622222211962215671901 38057483333329485830876963)
                ·
                  refine ⟨57086224999994228746315445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38057483333329485830876963 57086224999994228746315445)
                  ·
                    refine ⟨5351833593749458944967073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 57086224999994228746315445 5351833593749458944967073)
                    ·
                      refine ⟨4013875195312094208725305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5351833593749458944967073 4013875195312094208725305)
                      ·
                        rfl

theorem cell23_7816994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 3, 1, 5, 2].length) (baseStart_7816994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7816994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7816994 prefixEnd_7816994 := by exact prefixLift 7816994
  have htrace : WordTrace (prefixWord ++ tailWord_7816994) baseStart_7816994 baseEnd_7816994 := by
    simpa [prefixWord, tailWord_7816994, baseEnd_7816994] using wordTrace_append hprefix tailTrace_7816994
  have hstable : (prefixWord ++ tailWord_7816994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7816994).length < 2 ^ (prefixWord ++ tailWord_7816994).sum := by decide
  have hdescent : baseEnd_7816994 < baseStart_7816994 := by decide
  rcases family_descends (prefixWord ++ tailWord_7816994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7817007 : List Nat := [1, 1, 2, 1, 2, 1, 2, 2, 1, 8, 2]
def baseStart_7817007 : Nat := 118140960795 + 7817007 * 2 ^ 59
def prefixEnd_7817007 : Nat := 4983230072969 + 3 ^ 40 * 7817007 * 2
def baseEnd_7817007 : Nat := 4013881870560602657862745

theorem tailTrace_7817007 : CollatzResearch.WordTrace tailWord_7817007 prefixEnd_7817007 4013881870560602657862745 := by
  unfold tailWord_7817007
  simp only [CollatzResearch.WordTrace]
  refine ⟨285109667991326152352865275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190073111994217434901910183 285109667991326152352865275)
  ·
    refine ⟨427664501986989228529297913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285109667991326152352865275 427664501986989228529297913)
    ·
      refine ⟨320748376490241921396973435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 427664501986989228529297913 320748376490241921396973435)
      ·
        refine ⟨481122564735362882095460153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 320748376490241921396973435 481122564735362882095460153)
        ·
          refine ⟨360841923551522161571595115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 481122564735362882095460153 360841923551522161571595115)
          ·
            refine ⟨541262885327283242357392673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 360841923551522161571595115 541262885327283242357392673)
            ·
              refine ⟨405947163995462431768044505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 541262885327283242357392673 405947163995462431768044505)
              ·
                refine ⟨304460372996596823826033379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 405947163995462431768044505 304460372996596823826033379)
                ·
                  refine ⟨456690559494895235739050069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 304460372996596823826033379 456690559494895235739050069)
                  ·
                    refine ⟨5351842494080803543816993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 456690559494895235739050069 5351842494080803543816993)
                    ·
                      refine ⟨4013881870560602657862745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5351842494080803543816993 4013881870560602657862745)
                      ·
                        rfl

theorem cell23_7817007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 2, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 2, 1, 8, 2].length) (baseStart_7817007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7817007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7817007 prefixEnd_7817007 := by exact prefixLift 7817007
  have htrace : WordTrace (prefixWord ++ tailWord_7817007) baseStart_7817007 baseEnd_7817007 := by
    simpa [prefixWord, tailWord_7817007, baseEnd_7817007] using wordTrace_append hprefix tailTrace_7817007
  have hstable : (prefixWord ++ tailWord_7817007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7817007).length < 2 ^ (prefixWord ++ tailWord_7817007).sum := by decide
  have hdescent : baseEnd_7817007 < baseStart_7817007 := by decide
  rcases family_descends (prefixWord ++ tailWord_7817007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7817011 : List Nat := [1, 1, 1, 2, 7, 1, 1, 2, 2, 3, 2]
def baseStart_7817011 : Nat := 118140960795 + 7817011 * 2 ^ 59
def prefixEnd_7817011 : Nat := 4983230072969 + 3 ^ 40 * 7817011 * 2
def baseEnd_7817011 : Nat := 4013883924483220642212727

theorem tailTrace_7817011 : CollatzResearch.WordTrace tailWord_7817011 prefixEnd_7817011 4013883924483220642212727 := by
  unfold tailWord_7817011
  simp only [CollatzResearch.WordTrace]
  refine ⟨285109813883311661036010887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190073209255541107357340591 285109813883311661036010887)
  ·
    refine ⟨427664720824967491554016331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285109813883311661036010887 427664720824967491554016331)
    ·
      refine ⟨641497081237451237331024497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 427664720824967491554016331 641497081237451237331024497)
      ·
        refine ⟨481122810928088427998268373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 641497081237451237331024497 481122810928088427998268373)
        ·
          refine ⟨11276315881127072531209415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 481122810928088427998268373 11276315881127072531209415)
          ·
            refine ⟨16914473821690608796814123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11276315881127072531209415 16914473821690608796814123)
            ·
              refine ⟨25371710732535913195221185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16914473821690608796814123 25371710732535913195221185)
              ·
                refine ⟨19028783049401934896415889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25371710732535913195221185 19028783049401934896415889)
                ·
                  refine ⟨14271587287051451172311917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19028783049401934896415889 14271587287051451172311917)
                  ·
                    refine ⟨5351845232644294189616969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14271587287051451172311917 5351845232644294189616969)
                    ·
                      refine ⟨4013883924483220642212727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5351845232644294189616969 4013883924483220642212727)
                      ·
                        rfl

theorem cell23_7817011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 1, 2, 2, 3, 2].length) (baseStart_7817011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7817011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7817011 prefixEnd_7817011 := by exact prefixLift 7817011
  have htrace : WordTrace (prefixWord ++ tailWord_7817011) baseStart_7817011 baseEnd_7817011 := by
    simpa [prefixWord, tailWord_7817011, baseEnd_7817011] using wordTrace_append hprefix tailTrace_7817011
  have hstable : (prefixWord ++ tailWord_7817011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7817011).length < 2 ^ (prefixWord ++ tailWord_7817011).sum := by decide
  have hdescent : baseEnd_7817011 < baseStart_7817011 := by decide
  rcases family_descends (prefixWord ++ tailWord_7817011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7817027 : List Nat := [1, 1, 1, 3, 1, 5, 2, 2, 1, 1, 5]
def baseStart_7817027 : Nat := 118140960795 + 7817027 * 2 ^ 59
def prefixEnd_7817027 : Nat := 4983230072969 + 3 ^ 40 * 7817027 * 2
def baseEnd_7817027 : Nat := 4013892140173692579612653

theorem tailTrace_7817027 : CollatzResearch.WordTrace tailWord_7817027 prefixEnd_7817027 4013892140173692579612653 := by
  unfold tailWord_7817027
  simp only [CollatzResearch.WordTrace]
  refine ⟨285110397451253695768593335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190073598300835797179062223 285110397451253695768593335)
  ·
    refine ⟨427665596176880543652890003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285110397451253695768593335 427665596176880543652890003)
    ·
      refine ⟨641498394265320815479335005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 427665596176880543652890003 641498394265320815479335005)
      ·
        refine ⟨240561897849495305804750627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 641498394265320815479335005 240561897849495305804750627)
        ·
          refine ⟨360842846774242958707125941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 240561897849495305804750627 360842846774242958707125941)
          ·
            refine ⟨33829016885085277378793057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 360842846774242958707125941 33829016885085277378793057)
            ·
              refine ⟨25371762663813958034094793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33829016885085277378793057 25371762663813958034094793)
              ·
                refine ⟨19028821997860468525571095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25371762663813958034094793 19028821997860468525571095)
                ·
                  refine ⟨28543232996790702788356643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19028821997860468525571095 28543232996790702788356643)
                  ·
                    refine ⟨42814849495186054182534965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28543232996790702788356643 42814849495186054182534965)
                    ·
                      refine ⟨4013892140173692579612653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42814849495186054182534965 4013892140173692579612653)
                      ·
                        rfl

theorem cell23_7817027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 2, 2, 1, 1, 5].length) (baseStart_7817027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7817027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7817027 prefixEnd_7817027 := by exact prefixLift 7817027
  have htrace : WordTrace (prefixWord ++ tailWord_7817027) baseStart_7817027 baseEnd_7817027 := by
    simpa [prefixWord, tailWord_7817027, baseEnd_7817027] using wordTrace_append hprefix tailTrace_7817027
  have hstable : (prefixWord ++ tailWord_7817027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7817027).length < 2 ^ (prefixWord ++ tailWord_7817027).sum := by decide
  have hdescent : baseEnd_7817027 < baseStart_7817027 := by decide
  rcases family_descends (prefixWord ++ tailWord_7817027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7817034 : List Nat := [3, 1, 2, 1, 1, 1, 5, 3, 2, 4]
def baseStart_7817034 : Nat := 118140960795 + 7817034 * 2 ^ 59
def prefixEnd_7817034 : Nat := 4983230072969 + 3 ^ 40 * 7817034 * 2
def baseEnd_7817034 : Nat := 1337965244846091350741707

theorem tailTrace_7817034 : CollatzResearch.WordTrace tailWord_7817034 prefixEnd_7817034 1337965244846091350741707 := by
  unfold tailWord_7817034
  simp only [CollatzResearch.WordTrace]
  refine ⟨71277663190557083991024539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 190073768508152223976065437 71277663190557083991024539)
  ·
    refine ⟨106916494785835625986536809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71277663190557083991024539 106916494785835625986536809)
    ·
      refine ⟨80187371089376719489902607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106916494785835625986536809 80187371089376719489902607)
      ·
        refine ⟨120281056634065079234853911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80187371089376719489902607 120281056634065079234853911)
        ·
          refine ⟨180421584951097618852280867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120281056634065079234853911 180421584951097618852280867)
          ·
            refine ⟨270632377426646428278421301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 180421584951097618852280867 270632377426646428278421301)
            ·
              refine ⟨25371785383748102651101997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 270632377426646428278421301 25371785383748102651101997)
              ·
                refine ⟨9514419518905538494163249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25371785383748102651101997 9514419518905538494163249)
                ·
                  refine ⟨7135814639179153870622437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9514419518905538494163249 7135814639179153870622437)
                  ·
                    refine ⟨1337965244846091350741707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7135814639179153870622437 1337965244846091350741707)
                    ·
                      rfl

theorem cell23_7817034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 5, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 5, 3, 2, 4].length) (baseStart_7817034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7817034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7817034 prefixEnd_7817034 := by exact prefixLift 7817034
  have htrace : WordTrace (prefixWord ++ tailWord_7817034) baseStart_7817034 baseEnd_7817034 := by
    simpa [prefixWord, tailWord_7817034, baseEnd_7817034] using wordTrace_append hprefix tailTrace_7817034
  have hstable : (prefixWord ++ tailWord_7817034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7817034).length < 2 ^ (prefixWord ++ tailWord_7817034).sum := by decide
  have hdescent : baseEnd_7817034 < baseStart_7817034 := by decide
  rcases family_descends (prefixWord ++ tailWord_7817034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7817041 : List Nat := [1, 2, 2, 1, 5, 3, 1, 2, 1, 1, 4]
def baseStart_7817041 : Nat := 118140960795 + 7817041 * 2 ^ 59
def prefixEnd_7817041 : Nat := 4983230072969 + 3 ^ 40 * 7817041 * 2
def baseEnd_7817041 : Nat := 4013899328902855524837589

theorem tailTrace_7817041 : CollatzResearch.WordTrace tailWord_7817041 prefixEnd_7817041 4013899328902855524837589 := by
  unfold tailWord_7817041
  simp only [CollatzResearch.WordTrace]
  refine ⟨285110908073202976159602977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190073938715468650773068651 285110908073202976159602977)
  ·
    refine ⟨213833181054902232119702233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 285110908073202976159602977 213833181054902232119702233)
    ·
      refine ⟨160374885791176674089776675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 213833181054902232119702233 160374885791176674089776675)
      ·
        refine ⟨240562328686765011134665013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160374885791176674089776675 240562328686765011134665013)
        ·
          refine ⟨22552718314384219793874845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 240562328686765011134665013 22552718314384219793874845)
          ·
            refine ⟨8457269367894082422703067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22552718314384219793874845 8457269367894082422703067)
            ·
              refine ⟨12685904051841123634054601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8457269367894082422703067 12685904051841123634054601)
              ·
                refine ⟨9514428038880842725540951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12685904051841123634054601 9514428038880842725540951)
                ·
                  refine ⟨14271642058321264088311427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9514428038880842725540951 14271642058321264088311427)
                  ·
                    refine ⟨21407463087481896132467141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14271642058321264088311427 21407463087481896132467141)
                    ·
                      refine ⟨4013899328902855524837589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21407463087481896132467141 4013899328902855524837589)
                      ·
                        rfl

theorem cell23_7817041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 3, 1, 2, 1, 1, 4].length) (baseStart_7817041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7817041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7817041 prefixEnd_7817041 := by exact prefixLift 7817041
  have htrace : WordTrace (prefixWord ++ tailWord_7817041) baseStart_7817041 baseEnd_7817041 := by
    simpa [prefixWord, tailWord_7817041, baseEnd_7817041] using wordTrace_append hprefix tailTrace_7817041
  have hstable : (prefixWord ++ tailWord_7817041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7817041).length < 2 ^ (prefixWord ++ tailWord_7817041).sum := by decide
  have hdescent : baseEnd_7817041 < baseStart_7817041 := by decide
  rcases family_descends (prefixWord ++ tailWord_7817041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7817058 : List Nat := [3, 3, 2, 1, 2, 2, 3, 1, 1, 1, 4]
def baseStart_7817058 : Nat := 118140960795 + 7817058 * 2 ^ 59
def prefixEnd_7817058 : Nat := 4983230072969 + 3 ^ 40 * 7817058 * 2
def baseEnd_7817058 : Nat := 4013908058073981958325011

theorem tailTrace_7817058 : CollatzResearch.WordTrace tailWord_7817058 prefixEnd_7817058 4013908058073981958325011 := by
  unfold tailWord_7817058
  simp only [CollatzResearch.WordTrace]
  refine ⟨71277882028535347015742957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 190074352076094258708647885 71277882028535347015742957)
  ·
    refine ⟨26729205760700755130903609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71277882028535347015742957 26729205760700755130903609)
    ·
      refine ⟨20046904320525566348177707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26729205760700755130903609 20046904320525566348177707)
      ·
        refine ⟨30070356480788349522266561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20046904320525566348177707 30070356480788349522266561)
        ·
          refine ⟨22552767360591262141699921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30070356480788349522266561 22552767360591262141699921)
          ·
            refine ⟨16914575520443446606274941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22552767360591262141699921 16914575520443446606274941)
            ·
              refine ⟨6342965820166292477353103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16914575520443446606274941 6342965820166292477353103)
              ·
                refine ⟨9514448730249438716029655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6342965820166292477353103 9514448730249438716029655)
                ·
                  refine ⟨14271673095374158074044483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9514448730249438716029655 14271673095374158074044483)
                  ·
                    refine ⟨21407509643061237111066725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14271673095374158074044483 21407509643061237111066725)
                    ·
                      refine ⟨4013908058073981958325011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21407509643061237111066725 4013908058073981958325011)
                      ·
                        rfl

theorem cell23_7817058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 3, 1, 1, 1, 4].length) (baseStart_7817058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7817058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7817058 prefixEnd_7817058 := by exact prefixLift 7817058
  have htrace : WordTrace (prefixWord ++ tailWord_7817058) baseStart_7817058 baseEnd_7817058 := by
    simpa [prefixWord, tailWord_7817058, baseEnd_7817058] using wordTrace_append hprefix tailTrace_7817058
  have hstable : (prefixWord ++ tailWord_7817058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7817058).length < 2 ^ (prefixWord ++ tailWord_7817058).sum := by decide
  have hdescent : baseEnd_7817058 < baseStart_7817058 := by decide
  rcases family_descends (prefixWord ++ tailWord_7817058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7817077 : List Nat := [1, 3, 4, 1, 1, 1, 1, 1, 1, 9]
def baseStart_7817077 : Nat := 118140960795 + 7817077 * 2 ^ 59
def prefixEnd_7817077 : Nat := 4983230072969 + 3 ^ 40 * 7817077 * 2
def baseEnd_7817077 : Nat := 1337972604735472461329141

theorem tailTrace_7817077 : CollatzResearch.WordTrace tailWord_7817077 prefixEnd_7817077 1337972604735472461329141 := by
  unfold tailWord_7817077
  simp only [CollatzResearch.WordTrace]
  refine ⟨285112221101072554307913485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190074814067381702871942323 285112221101072554307913485)
  ·
    refine ⟨106917082912902207865467557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 285112221101072554307913485 106917082912902207865467557)
    ·
      refine ⟨20046953046169163974775167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 106917082912902207865467557 20046953046169163974775167)
      ·
        refine ⟨30070429569253745962162751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20046953046169163974775167 30070429569253745962162751)
        ·
          refine ⟨45105644353880618943244127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30070429569253745962162751 45105644353880618943244127)
          ·
            refine ⟨67658466530820928414866191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45105644353880618943244127 67658466530820928414866191)
            ·
              refine ⟨101487699796231392622299287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67658466530820928414866191 101487699796231392622299287)
              ·
                refine ⟨152231549694347088933448931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 101487699796231392622299287 152231549694347088933448931)
                ·
                  refine ⟨228347324541520633400173397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 152231549694347088933448931 228347324541520633400173397)
                  ·
                    refine ⟨1337972604735472461329141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 228347324541520633400173397 1337972604735472461329141)
                    ·
                      rfl

theorem cell23_7817077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 1, 1, 9].length) (baseStart_7817077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7817077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7817077 prefixEnd_7817077 := by exact prefixLift 7817077
  have htrace : WordTrace (prefixWord ++ tailWord_7817077) baseStart_7817077 baseEnd_7817077 := by
    simpa [prefixWord, tailWord_7817077, baseEnd_7817077] using wordTrace_append hprefix tailTrace_7817077
  have hstable : (prefixWord ++ tailWord_7817077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7817077).length < 2 ^ (prefixWord ++ tailWord_7817077).sum := by decide
  have hdescent : baseEnd_7817077 < baseStart_7817077 := by decide
  rcases family_descends (prefixWord ++ tailWord_7817077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7817091 : List Nat := [1, 1, 1, 3, 4, 2, 2, 3, 2, 1, 3]
def baseStart_7817091 : Nat := 118140960795 + 7817091 * 2 ^ 59
def prefixEnd_7817091 : Nat := 4983230072969 + 3 ^ 40 * 7817091 * 2
def baseEnd_7817091 : Nat := 4013925002935580329212359

theorem tailTrace_7817091 : CollatzResearch.WordTrace tailWord_7817091 prefixEnd_7817091 4013925002935580329212359 := by
  unfold tailWord_7817091
  simp only [CollatzResearch.WordTrace]
  refine ⟨285112731723021834698923127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190075154482014556465948751 285112731723021834698923127)
  ·
    refine ⟨427669097584532752048384691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285112731723021834698923127 427669097584532752048384691)
    ·
      refine ⟨641503646376799128072577037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 427669097584532752048384691 641503646376799128072577037)
      ·
        refine ⟨240563867391299673027216389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 641503646376799128072577037 240563867391299673027216389)
        ·
          refine ⟨45105725135868688692603073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 240563867391299673027216389 45105725135868688692603073)
          ·
            refine ⟨33829293851901516519452305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45105725135868688692603073 33829293851901516519452305)
            ·
              refine ⟨25371970388926137389589229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33829293851901516519452305 25371970388926137389589229)
              ·
                refine ⟨9514488895847301521095961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25371970388926137389589229 9514488895847301521095961)
                ·
                  refine ⟨7135866671885476140821971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9514488895847301521095961 7135866671885476140821971)
                  ·
                    refine ⟨10703800007828214211232957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7135866671885476140821971 10703800007828214211232957)
                    ·
                      refine ⟨4013925002935580329212359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10703800007828214211232957 4013925002935580329212359)
                      ·
                        rfl

theorem cell23_7817091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 2, 3, 2, 1, 3].length) (baseStart_7817091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7817091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7817091 prefixEnd_7817091 := by exact prefixLift 7817091
  have htrace : WordTrace (prefixWord ++ tailWord_7817091) baseStart_7817091 baseEnd_7817091 := by
    simpa [prefixWord, tailWord_7817091, baseEnd_7817091] using wordTrace_append hprefix tailTrace_7817091
  have hstable : (prefixWord ++ tailWord_7817091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7817091).length < 2 ^ (prefixWord ++ tailWord_7817091).sum := by decide
  have hdescent : baseEnd_7817091 < baseStart_7817091 := by decide
  rcases family_descends (prefixWord ++ tailWord_7817091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7817097 : List Nat := [1, 2, 1, 1, 5, 1, 1, 2, 2, 3, 4]
def baseStart_7817097 : Nat := 118140960795 + 7817097 * 2 ^ 59
def prefixEnd_7817097 : Nat := 4983230072969 + 3 ^ 40 * 7817097 * 2
def baseEnd_7817097 : Nat := 4013928083819507305737331

theorem tailTrace_7817097 : CollatzResearch.WordTrace tailWord_7817097 prefixEnd_7817097 4013928083819507305737331 := by
  unfold tailWord_7817097
  simp only [CollatzResearch.WordTrace]
  refine ⟨285112950561000097723641545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190075300374000065149094363 285112950561000097723641545)
  ·
    refine ⟨213834712920750073292731159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 285112950561000097723641545 213834712920750073292731159)
    ·
      refine ⟨320752069381125109939096739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213834712920750073292731159 320752069381125109939096739)
      ·
        refine ⟨481128104071687664908645109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 320752069381125109939096739 481128104071687664908645109)
        ·
          refine ⟨45105759756720718585185479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 481128104071687664908645109 45105759756720718585185479)
          ·
            refine ⟨67658639635081077877778219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45105759756720718585185479 67658639635081077877778219)
            ·
              refine ⟨101487959452621616816667329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67658639635081077877778219 101487959452621616816667329)
              ·
                refine ⟨76115969589466212612500497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 101487959452621616816667329 76115969589466212612500497)
                ·
                  refine ⟨57086977192099659459375373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 76115969589466212612500497 57086977192099659459375373)
                  ·
                    refine ⟨21407616447037372297265765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 57086977192099659459375373 21407616447037372297265765)
                    ·
                      refine ⟨4013928083819507305737331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21407616447037372297265765 4013928083819507305737331)
                      ·
                        rfl

theorem cell23_7817097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 2, 2, 3, 4].length) (baseStart_7817097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7817097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7817097 prefixEnd_7817097 := by exact prefixLift 7817097
  have htrace : WordTrace (prefixWord ++ tailWord_7817097) baseStart_7817097 baseEnd_7817097 := by
    simpa [prefixWord, tailWord_7817097, baseEnd_7817097] using wordTrace_append hprefix tailTrace_7817097
  have hstable : (prefixWord ++ tailWord_7817097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7817097).length < 2 ^ (prefixWord ++ tailWord_7817097).sum := by decide
  have hdescent : baseEnd_7817097 < baseStart_7817097 := by decide
  rcases family_descends (prefixWord ++ tailWord_7817097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7817112 : List Nat := [2, 1, 2, 6, 2, 1, 2, 1, 1, 2, 3]
def baseStart_7817112 : Nat := 118140960795 + 7817112 * 2 ^ 59
def prefixEnd_7817112 : Nat := 4983230072969 + 3 ^ 40 * 7817112 * 2
def baseEnd_7817112 : Nat := 4013935786029324747049763

theorem tailTrace_7817112 : CollatzResearch.WordTrace tailWord_7817112 prefixEnd_7817112 4013935786029324747049763 := by
  unfold tailWord_7817112
  simp only [CollatzResearch.WordTrace]
  refine ⟨142556748827972877642718795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190075665103963836856958393 142556748827972877642718795)
  ·
    refine ⟨213835123241959316464078193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142556748827972877642718795 213835123241959316464078193)
    ·
      refine ⟨160376342431469487348058645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 213835123241959316464078193 160376342431469487348058645)
      ·
        refine ⟨7517641051475132219440249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 160376342431469487348058645 7517641051475132219440249)
        ·
          refine ⟨5638230788606349164580187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7517641051475132219440249 5638230788606349164580187)
          ·
            refine ⟨8457346182909523746870281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5638230788606349164580187 8457346182909523746870281)
            ·
              refine ⟨6343009637182142810152711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8457346182909523746870281 6343009637182142810152711)
              ·
                refine ⟨9514514455773214215229067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6343009637182142810152711 9514514455773214215229067)
                ·
                  refine ⟨14271771683659821322843601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9514514455773214215229067 14271771683659821322843601)
                  ·
                    refine ⟨10703828762744865992132701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14271771683659821322843601 10703828762744865992132701)
                    ·
                      refine ⟨4013935786029324747049763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10703828762744865992132701 4013935786029324747049763)
                      ·
                        rfl

theorem cell23_7817112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 2, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 2, 1, 2, 1, 1, 2, 3].length) (baseStart_7817112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7817112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7817112 prefixEnd_7817112 := by exact prefixLift 7817112
  have htrace : WordTrace (prefixWord ++ tailWord_7817112) baseStart_7817112 baseEnd_7817112 := by
    simpa [prefixWord, tailWord_7817112, baseEnd_7817112] using wordTrace_append hprefix tailTrace_7817112
  have hstable : (prefixWord ++ tailWord_7817112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7817112).length < 2 ^ (prefixWord ++ tailWord_7817112).sum := by decide
  have hdescent : baseEnd_7817112 < baseStart_7817112 := by decide
  rcases family_descends (prefixWord ++ tailWord_7817112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7817167 : List Nat := [1, 1, 2, 1, 1, 5, 1, 3, 1, 7]
def baseStart_7817167 : Nat := 118140960795 + 7817167 * 2 ^ 59
def prefixEnd_7817167 : Nat := 4983230072969 + 3 ^ 40 * 7817167 * 2
def baseEnd_7817167 : Nat := 1337988009155107343954003

theorem tailTrace_7817167 : CollatzResearch.WordTrace tailWord_7817167 prefixEnd_7817167 1337988009155107343954003 := by
  unfold tailWord_7817167
  simp only [CollatzResearch.WordTrace]
  refine ⟨285115503670746499678689755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190077002447164333119126503 285115503670746499678689755)
  ·
    refine ⟨427673255506119749518034633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285115503670746499678689755 427673255506119749518034633)
    ·
      refine ⟨320754941629589812138525975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 427673255506119749518034633 320754941629589812138525975)
      ·
        refine ⟨481132412444384718207788963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 320754941629589812138525975 481132412444384718207788963)
        ·
          refine ⟨721698618666577077311683445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 481132412444384718207788963 721698618666577077311683445)
          ·
            refine ⟨67659245499991600997970323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 721698618666577077311683445 67659245499991600997970323)
            ·
              refine ⟨101488868249987401496955485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67659245499991600997970323 101488868249987401496955485)
              ·
                refine ⟨38058325593745275561358307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 101488868249987401496955485 38058325593745275561358307)
                ·
                  refine ⟨57087488390617913342037461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38058325593745275561358307 57087488390617913342037461)
                  ·
                    refine ⟨1337988009155107343954003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 57087488390617913342037461 1337988009155107343954003)
                    ·
                      rfl

theorem cell23_7817167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 3, 1, 7].length) (baseStart_7817167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7817167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7817167 prefixEnd_7817167 := by exact prefixLift 7817167
  have htrace : WordTrace (prefixWord ++ tailWord_7817167) baseStart_7817167 baseEnd_7817167 := by
    simpa [prefixWord, tailWord_7817167, baseEnd_7817167] using wordTrace_append hprefix tailTrace_7817167
  have hstable : (prefixWord ++ tailWord_7817167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7817167).length < 2 ^ (prefixWord ++ tailWord_7817167).sum := by decide
  have hdescent : baseEnd_7817167 < baseStart_7817167 := by decide
  rcases family_descends (prefixWord ++ tailWord_7817167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7817194 : List Nat := [3, 1, 3, 1, 2, 1, 3, 1, 1, 2, 5]
def baseStart_7817194 : Nat := 118140960795 + 7817194 * 2 ^ 59
def prefixEnd_7817194 : Nat := 4983230072969 + 3 ^ 40 * 7817194 * 2
def baseEnd_7817194 : Nat := 4013977891442993426224385

theorem tailTrace_7817194 : CollatzResearch.WordTrace tailWord_7817194 prefixEnd_7817194 4013977891442993426224385 := by
  unfold tailWord_7817194
  simp only [CollatzResearch.WordTrace]
  refine ⟨71279122110412170822480659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 190077658961099122193281757 71279122110412170822480659)
  ·
    refine ⟨106918683165618256233720989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71279122110412170822480659 106918683165618256233720989)
    ·
      refine ⟨40094506187106846087645371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 106918683165618256233720989 40094506187106846087645371)
      ·
        refine ⟨60141759280660269131468057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40094506187106846087645371 60141759280660269131468057)
        ·
          refine ⟨45106319460495201848601043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60141759280660269131468057 45106319460495201848601043)
          ·
            refine ⟨67659479190742802772901565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45106319460495201848601043 67659479190742802772901565)
            ·
              refine ⟨25372304696528551039838087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67659479190742802772901565 25372304696528551039838087)
              ·
                refine ⟨38058457044792826559757131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25372304696528551039838087 38058457044792826559757131)
                ·
                  refine ⟨57087685567189239839635697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38058457044792826559757131 57087685567189239839635697)
                  ·
                    refine ⟨42815764175391929879726773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 57087685567189239839635697 42815764175391929879726773)
                    ·
                      refine ⟨4013977891442993426224385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42815764175391929879726773 4013977891442993426224385)
                      ·
                        rfl

theorem cell23_7817194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 3, 1, 1, 2, 5].length) (baseStart_7817194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7817194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7817194 prefixEnd_7817194 := by exact prefixLift 7817194
  have htrace : WordTrace (prefixWord ++ tailWord_7817194) baseStart_7817194 baseEnd_7817194 := by
    simpa [prefixWord, tailWord_7817194, baseEnd_7817194] using wordTrace_append hprefix tailTrace_7817194
  have hstable : (prefixWord ++ tailWord_7817194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7817194).length < 2 ^ (prefixWord ++ tailWord_7817194).sum := by decide
  have hdescent : baseEnd_7817194 < baseStart_7817194 := by decide
  rcases family_descends (prefixWord ++ tailWord_7817194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7817207 : List Nat := [1, 1, 3, 1, 1, 1, 1, 1, 3, 5, 5]
def baseStart_7817207 : Nat := 118140960795 + 7817207 * 2 ^ 59
def prefixEnd_7817207 : Nat := 4983230072969 + 3 ^ 40 * 7817207 * 2
def baseEnd_7817207 : Nat := 4013984566691501875361825

theorem tailTrace_7817207 : CollatzResearch.WordTrace tailWord_7817207 prefixEnd_7817207 4013984566691501875361825 := by
  unfold tailWord_7817207
  simp only [CollatzResearch.WordTrace]
  refine ⟨285116962590601586510145875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190077975060401057673430583 285116962590601586510145875)
  ·
    refine ⟨427675443885902379765218813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285116962590601586510145875 427675443885902379765218813)
    ·
      refine ⟨160378291457213392411957055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 427675443885902379765218813 160378291457213392411957055)
      ·
        refine ⟨240567437185820088617935583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160378291457213392411957055 240567437185820088617935583)
        ·
          refine ⟨360851155778730132926903375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 240567437185820088617935583 360851155778730132926903375)
          ·
            refine ⟨541276733668095199390355063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 360851155778730132926903375 541276733668095199390355063)
            ·
              refine ⟨811915100502142799085532595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 541276733668095199390355063 811915100502142799085532595)
              ·
                refine ⟨1217872650753214198628298893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 811915100502142799085532595 1217872650753214198628298893)
                ·
                  refine ⟨456702244032455324485612085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1217872650753214198628298893 456702244032455324485612085)
                  ·
                    refine ⟨42815835378042686670526133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 456702244032455324485612085 42815835378042686670526133)
                    ·
                      refine ⟨4013984566691501875361825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42815835378042686670526133 4013984566691501875361825)
                      ·
                        rfl

theorem cell23_7817207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 3, 5, 5].length) (baseStart_7817207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7817207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7817207 prefixEnd_7817207 := by exact prefixLift 7817207
  have htrace : WordTrace (prefixWord ++ tailWord_7817207) baseStart_7817207 baseEnd_7817207 := by
    simpa [prefixWord, tailWord_7817207, baseEnd_7817207] using wordTrace_append hprefix tailTrace_7817207
  have hstable : (prefixWord ++ tailWord_7817207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7817207).length < 2 ^ (prefixWord ++ tailWord_7817207).sum := by decide
  have hdescent : baseEnd_7817207 < baseStart_7817207 := by decide
  rcases family_descends (prefixWord ++ tailWord_7817207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7817221 : List Nat := [1, 3, 1, 1, 2, 5, 2, 1, 2, 1, 4]
def baseStart_7817221 : Nat := 118140960795 + 7817221 * 2 ^ 59
def prefixEnd_7817221 : Nat := 4983230072969 + 3 ^ 40 * 7817221 * 2
def baseEnd_7817221 : Nat := 4013991755420664820586761

theorem tailTrace_7817221 : CollatzResearch.WordTrace tailWord_7817221 prefixEnd_7817221 4013991755420664820586761 := by
  unfold tailWord_7817221
  simp only [CollatzResearch.WordTrace]
  refine ⟨285117473212550866901155517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190078315475033911267437011 285117473212550866901155517)
  ·
    refine ⟨106919052454706575087933319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 285117473212550866901155517 106919052454706575087933319)
    ·
      refine ⟨160378578682059862631899979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106919052454706575087933319 160378578682059862631899979)
      ·
        refine ⟨240567868023089793947849969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160378578682059862631899979 240567868023089793947849969)
        ·
          refine ⟨180425901017317345460887477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 240567868023089793947849969 180425901017317345460887477)
          ·
            refine ⟨16914928220373501136958201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 180425901017317345460887477 16914928220373501136958201)
            ·
              refine ⟨12686196165280125852718651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16914928220373501136958201 12686196165280125852718651)
              ·
                refine ⟨19029294247920188779077977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12686196165280125852718651 19029294247920188779077977)
                ·
                  refine ⟨14271970685940141584308483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19029294247920188779077977 14271970685940141584308483)
                  ·
                    refine ⟨21407956028910212376462725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14271970685940141584308483 21407956028910212376462725)
                    ·
                      refine ⟨4013991755420664820586761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21407956028910212376462725 4013991755420664820586761)
                      ·
                        rfl

theorem cell23_7817221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 2, 1, 2, 1, 4].length) (baseStart_7817221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7817221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7817221 prefixEnd_7817221 := by exact prefixLift 7817221
  have htrace : WordTrace (prefixWord ++ tailWord_7817221) baseStart_7817221 baseEnd_7817221 := by
    simpa [prefixWord, tailWord_7817221, baseEnd_7817221] using wordTrace_append hprefix tailTrace_7817221
  have hstable : (prefixWord ++ tailWord_7817221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7817221).length < 2 ^ (prefixWord ++ tailWord_7817221).sum := by decide
  have hdescent : baseEnd_7817221 < baseStart_7817221 := by decide
  rcases family_descends (prefixWord ++ tailWord_7817221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7817255 : List Nat := [1, 1, 7, 1, 2, 1, 1, 1, 2, 4, 2]
def baseStart_7817255 : Nat := 118140960795 + 7817255 * 2 ^ 59
def prefixEnd_7817255 : Nat := 4983230072969 + 3 ^ 40 * 7817255 * 2
def baseEnd_7817255 : Nat := 4014009213762917687561605

theorem tailTrace_7817255 : CollatzResearch.WordTrace tailWord_7817255 prefixEnd_7817255 4014009213762917687561605 := by
  unfold tailWord_7817255
  simp only [CollatzResearch.WordTrace]
  refine ⟨285118713294427690707893219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190079142196285127138595479 285118713294427690707893219)
  ·
    refine ⟨427678069941641536061839829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285118713294427690707893219 427678069941641536061839829)
    ·
      refine ⟨10023704764257223501449371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 427678069941641536061839829 10023704764257223501449371)
      ·
        refine ⟨15035557146385835252174057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10023704764257223501449371 15035557146385835252174057)
        ·
          refine ⟨11276667859789376439130543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15035557146385835252174057 11276667859789376439130543)
          ·
            refine ⟨16915001789684064658695815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11276667859789376439130543 16915001789684064658695815)
            ·
              refine ⟨25372502684526096988043723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16915001789684064658695815 25372502684526096988043723)
              ·
                refine ⟨38058754026789145482065585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25372502684526096988043723 38058754026789145482065585)
                ·
                  refine ⟨28544065520091859111549189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38058754026789145482065585 28544065520091859111549189)
                  ·
                    refine ⟨5352012285017223583415473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28544065520091859111549189 5352012285017223583415473)
                    ·
                      refine ⟨4014009213762917687561605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5352012285017223583415473 4014009213762917687561605)
                      ·
                        rfl

theorem cell23_7817255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 1, 1, 2, 4, 2].length) (baseStart_7817255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7817255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7817255 prefixEnd_7817255 := by exact prefixLift 7817255
  have htrace : WordTrace (prefixWord ++ tailWord_7817255) baseStart_7817255 baseEnd_7817255 := by
    simpa [prefixWord, tailWord_7817255, baseEnd_7817255] using wordTrace_append hprefix tailTrace_7817255
  have hstable : (prefixWord ++ tailWord_7817255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7817255).length < 2 ^ (prefixWord ++ tailWord_7817255).sum := by decide
  have hdescent : baseEnd_7817255 < baseStart_7817255 := by decide
  rcases family_descends (prefixWord ++ tailWord_7817255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7817271 : List Nat := [1, 1, 3, 1, 2, 2, 3, 1, 5, 1, 3]
def baseStart_7817271 : Nat := 118140960795 + 7817271 * 2 ^ 59
def prefixEnd_7817271 : Nat := 4983230072969 + 3 ^ 40 * 7817271 * 2
def baseEnd_7817271 : Nat := 4014017429453389624961531

theorem tailTrace_7817271 : CollatzResearch.WordTrace tailWord_7817271 prefixEnd_7817271 4014017429453389624961531 := by
  unfold tailWord_7817271
  simp only [CollatzResearch.WordTrace]
  refine ⟨285119296862369725440475667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190079531241579816960317111 285119296862369725440475667)
  ·
    refine ⟨427678945293554588160713501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285119296862369725440475667 427678945293554588160713501)
    ·
      refine ⟨160379604485082970560267563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 427678945293554588160713501 160379604485082970560267563)
      ·
        refine ⟨240569406727624455840401345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160379604485082970560267563 240569406727624455840401345)
        ·
          refine ⟨180427055045718341880301009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 240569406727624455840401345 180427055045718341880301009)
          ·
            refine ⟨135320291284288756410225757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 180427055045718341880301009 135320291284288756410225757)
            ·
              refine ⟨50745109231608283653834659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 135320291284288756410225757 50745109231608283653834659)
              ·
                refine ⟨76117663847412425480751989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50745109231608283653834659 76117663847412425480751989)
                ·
                  refine ⟨7136030985694914888820499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 76117663847412425480751989 7136030985694914888820499)
                  ·
                    refine ⟨10704046478542372333230749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7136030985694914888820499 10704046478542372333230749)
                    ·
                      refine ⟨4014017429453389624961531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10704046478542372333230749 4014017429453389624961531)
                      ·
                        rfl

theorem cell23_7817271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 3, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 3, 1, 5, 1, 3].length) (baseStart_7817271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7817271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7817271 prefixEnd_7817271 := by exact prefixLift 7817271
  have htrace : WordTrace (prefixWord ++ tailWord_7817271) baseStart_7817271 baseEnd_7817271 := by
    simpa [prefixWord, tailWord_7817271, baseEnd_7817271] using wordTrace_append hprefix tailTrace_7817271
  have hstable : (prefixWord ++ tailWord_7817271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7817271).length < 2 ^ (prefixWord ++ tailWord_7817271).sum := by decide
  have hdescent : baseEnd_7817271 < baseStart_7817271 := by decide
  rcases family_descends (prefixWord ++ tailWord_7817271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7817328 : List Nat := [2, 1, 1, 1, 5, 3, 2, 2, 1, 1, 4]
def baseStart_7817328 : Nat := 118140960795 + 7817328 * 2 ^ 59
def prefixEnd_7817328 : Nat := 4983230072969 + 3 ^ 40 * 7817328 * 2
def baseEnd_7817328 : Nat := 4014046697850695901948769

theorem tailTrace_7817328 : CollatzResearch.WordTrace tailWord_7817328 prefixEnd_7817328 4014046697850695901948769 := by
  unfold tailWord_7817328
  simp only [CollatzResearch.WordTrace]
  refine ⟨142560687911581612087650319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190080917215442149450200425 142560687911581612087650319)
  ·
    refine ⟨213841031867372418131475479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142560687911581612087650319 213841031867372418131475479)
    ·
      refine ⟨320761547801058627197213219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213841031867372418131475479 320761547801058627197213219)
      ·
        refine ⟨481142321701587940795819829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 320761547801058627197213219 481142321701587940795819829)
        ·
          refine ⟨45107092659523869449608109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 481142321701587940795819829 45107092659523869449608109)
          ·
            refine ⟨16915159747321451043603041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45107092659523869449608109 16915159747321451043603041)
            ·
              refine ⟨12686369810491088282702281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16915159747321451043603041 12686369810491088282702281)
              ·
                refine ⟨9514777357868316212026711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12686369810491088282702281 9514777357868316212026711)
                ·
                  refine ⟨14272166036802474318040067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9514777357868316212026711 14272166036802474318040067)
                  ·
                    refine ⟨21408249055203711477060101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14272166036802474318040067 21408249055203711477060101)
                    ·
                      refine ⟨4014046697850695901948769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21408249055203711477060101 4014046697850695901948769)
                      ·
                        rfl

theorem cell23_7817328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 2, 2, 1, 1, 4].length) (baseStart_7817328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7817328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7817328 prefixEnd_7817328 := by exact prefixLift 7817328
  have htrace : WordTrace (prefixWord ++ tailWord_7817328) baseStart_7817328 baseEnd_7817328 := by
    simpa [prefixWord, tailWord_7817328, baseEnd_7817328] using wordTrace_append hprefix tailTrace_7817328
  have hstable : (prefixWord ++ tailWord_7817328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7817328).length < 2 ^ (prefixWord ++ tailWord_7817328).sum := by decide
  have hdescent : baseEnd_7817328 < baseStart_7817328 := by decide
  rcases family_descends (prefixWord ++ tailWord_7817328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7817348 : List Nat := [2, 3, 2, 1, 2, 1, 1, 5, 1, 2, 3]
def baseStart_7817348 : Nat := 118140960795 + 7817348 * 2 ^ 59
def prefixEnd_7817348 : Nat := 4983230072969 + 3 ^ 40 * 7817348 * 2
def baseEnd_7817348 : Nat := 4014056967463785823698677

theorem tailTrace_7817348 : CollatzResearch.WordTrace tailWord_7817348 prefixEnd_7817348 4014056967463785823698677 := by
  unfold tailWord_7817348
  simp only [CollatzResearch.WordTrace]
  refine ⟨142561052641545383795514349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190081403522060511727352465 142561052641545383795514349)
  ·
    refine ⟨53460394740579518923317881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 142561052641545383795514349 53460394740579518923317881)
    ·
      refine ⟨40095296055434639192488411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53460394740579518923317881 40095296055434639192488411)
      ·
        refine ⟨60142944083151958788732617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40095296055434639192488411 60142944083151958788732617)
        ·
          refine ⟨45107208062363969091549463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60142944083151958788732617 45107208062363969091549463)
          ·
            refine ⟨67660812093545953637324195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45107208062363969091549463 67660812093545953637324195)
            ·
              refine ⟨101491218140318930455986293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67660812093545953637324195 101491218140318930455986293)
              ·
                refine ⟨9514801700654899730248715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 101491218140318930455986293 9514801700654899730248715)
                ·
                  refine ⟨14272202550982349595373073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9514801700654899730248715 14272202550982349595373073)
                  ·
                    refine ⟨10704151913236762196529805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14272202550982349595373073 10704151913236762196529805)
                    ·
                      refine ⟨4014056967463785823698677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10704151913236762196529805 4014056967463785823698677)
                      ·
                        rfl

theorem cell23_7817348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 5, 1, 2, 3].length) (baseStart_7817348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7817348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7817348 prefixEnd_7817348 := by exact prefixLift 7817348
  have htrace : WordTrace (prefixWord ++ tailWord_7817348) baseStart_7817348 baseEnd_7817348 := by
    simpa [prefixWord, tailWord_7817348, baseEnd_7817348] using wordTrace_append hprefix tailTrace_7817348
  have hstable : (prefixWord ++ tailWord_7817348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7817348).length < 2 ^ (prefixWord ++ tailWord_7817348).sum := by decide
  have hdescent : baseEnd_7817348 < baseStart_7817348 := by decide
  rcases family_descends (prefixWord ++ tailWord_7817348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7817396 : List Nat := [2, 5, 3, 1, 1, 1, 3, 1, 1, 1, 4]
def baseStart_7817396 : Nat := 118140960795 + 7817396 * 2 ^ 59
def prefixEnd_7817396 : Nat := 4983230072969 + 3 ^ 40 * 7817396 * 2
def baseEnd_7817396 : Nat := 4014081614535201635898457

theorem tailTrace_7817396 : CollatzResearch.WordTrace tailWord_7817396 prefixEnd_7817396 4014081614535201635898457 := by
  unfold tailWord_7817396
  simp only [CollatzResearch.WordTrace]
  refine ⟨142561927993458435894388021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190082570657944581192517361 142561927993458435894388021)
  ·
    refine ⟨13365180749386728365098877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 142561927993458435894388021 13365180749386728365098877)
    ·
      refine ⟨5011942781020023136912079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13365180749386728365098877 5011942781020023136912079)
      ·
        refine ⟨7517914171530034705368119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5011942781020023136912079 7517914171530034705368119)
        ·
          refine ⟨11276871257295052058052179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7517914171530034705368119 11276871257295052058052179)
          ·
            refine ⟨16915306885942578087078269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11276871257295052058052179 16915306885942578087078269)
            ·
              refine ⟨6343240082228466782654351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16915306885942578087078269 6343240082228466782654351)
              ·
                refine ⟨9514860123342700173981527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6343240082228466782654351 9514860123342700173981527)
                ·
                  refine ⟨14272290185014050260972291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9514860123342700173981527 14272290185014050260972291)
                  ·
                    refine ⟨21408435277521075391458437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14272290185014050260972291 21408435277521075391458437)
                    ·
                      refine ⟨4014081614535201635898457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21408435277521075391458437 4014081614535201635898457)
                      ·
                        rfl

theorem cell23_7817396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 3, 1, 1, 1, 4].length) (baseStart_7817396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7817396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7817396 prefixEnd_7817396 := by exact prefixLift 7817396
  have htrace : WordTrace (prefixWord ++ tailWord_7817396) baseStart_7817396 baseEnd_7817396 := by
    simpa [prefixWord, tailWord_7817396, baseEnd_7817396] using wordTrace_append hprefix tailTrace_7817396
  have hstable : (prefixWord ++ tailWord_7817396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7817396).length < 2 ^ (prefixWord ++ tailWord_7817396).sum := by decide
  have hdescent : baseEnd_7817396 < baseStart_7817396 := by decide
  rcases family_descends (prefixWord ++ tailWord_7817396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7817412 : List Nat := [2, 3, 3, 1, 2, 2, 2, 2, 2, 1, 3]
def baseStart_7817412 : Nat := 118140960795 + 7817412 * 2 ^ 59
def prefixEnd_7817412 : Nat := 4983230072969 + 3 ^ 40 * 7817412 * 2
def baseEnd_7817412 : Nat := 4014089830225673573298383

theorem tailTrace_7817412 : CollatzResearch.WordTrace tailWord_7817412 prefixEnd_7817412 4014089830225673573298383 := by
  unfold tailWord_7817412
  simp only [CollatzResearch.WordTrace]
  refine ⟨142562219777429453260679245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190082959703239271014238993 142562219777429453260679245)
  ·
    refine ⟨53460832416536044972754717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 142562219777429453260679245 53460832416536044972754717)
    ·
      refine ⟨20047812156201016864783019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53460832416536044972754717 20047812156201016864783019)
      ·
        refine ⟨30071718234301525297174529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20047812156201016864783019 30071718234301525297174529)
        ·
          refine ⟨22553788675726143972880897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30071718234301525297174529 22553788675726143972880897)
          ·
            refine ⟨16915341506794607979660673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22553788675726143972880897 16915341506794607979660673)
            ·
              refine ⟨12686506130095955984745505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16915341506794607979660673 12686506130095955984745505)
              ·
                refine ⟨9514879597571966988559129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12686506130095955984745505 9514879597571966988559129)
                ·
                  refine ⟨7136159698178975241419347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9514879597571966988559129 7136159698178975241419347)
                  ·
                    refine ⟨10704239547268462862129021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7136159698178975241419347 10704239547268462862129021)
                    ·
                      refine ⟨4014089830225673573298383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10704239547268462862129021 4014089830225673573298383)
                      ·
                        rfl

theorem cell23_7817412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 2, 2, 2, 1, 3].length) (baseStart_7817412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7817412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7817412 prefixEnd_7817412 := by exact prefixLift 7817412
  have htrace : WordTrace (prefixWord ++ tailWord_7817412) baseStart_7817412 baseEnd_7817412 := by
    simpa [prefixWord, tailWord_7817412, baseEnd_7817412] using wordTrace_append hprefix tailTrace_7817412
  have hstable : (prefixWord ++ tailWord_7817412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7817412).length < 2 ^ (prefixWord ++ tailWord_7817412).sum := by decide
  have hdescent : baseEnd_7817412 < baseStart_7817412 := by decide
  rcases family_descends (prefixWord ++ tailWord_7817412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7817418 : List Nat := [3, 1, 2, 1, 3, 1, 1, 2, 3, 4, 2]
def baseStart_7817418 : Nat := 118140960795 + 7817418 * 2 ^ 59
def prefixEnd_7817418 : Nat := 4983230072969 + 3 ^ 40 * 7817418 * 2
def baseEnd_7817418 : Nat := 4014092911109600549823355

theorem tailTrace_7817418 : CollatzResearch.WordTrace tailWord_7817418 prefixEnd_7817418 4014092911109600549823355 := by
  unfold tailWord_7817418
  simp only [CollatzResearch.WordTrace]
  refine ⟨71281164598209292386519227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 190083105595224779697384605 71281164598209292386519227)
  ·
    refine ⟨106921746897313938579778841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71281164598209292386519227 106921746897313938579778841)
    ·
      refine ⟨80191310172985453934834131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106921746897313938579778841 80191310172985453934834131)
      ·
        refine ⟨120286965259478180902251197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80191310172985453934834131 120286965259478180902251197)
        ·
          refine ⟨45107611972304317838344199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 120286965259478180902251197 45107611972304317838344199)
          ·
            refine ⟨67661417958456476757516299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45107611972304317838344199 67661417958456476757516299)
            ·
              refine ⟨101492126937684715136274449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67661417958456476757516299 101492126937684715136274449)
              ·
                refine ⟨76119095203263536352205837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 101492126937684715136274449 76119095203263536352205837)
                ·
                  refine ⟨28544660701223826132077189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 76119095203263536352205837 28544660701223826132077189)
                  ·
                    refine ⟨5352123881479467399764473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28544660701223826132077189 5352123881479467399764473)
                    ·
                      refine ⟨4014092911109600549823355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5352123881479467399764473 4014092911109600549823355)
                      ·
                        rfl

theorem cell23_7817418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 2, 3, 4, 2].length) (baseStart_7817418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7817418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7817418 prefixEnd_7817418 := by exact prefixLift 7817418
  have htrace : WordTrace (prefixWord ++ tailWord_7817418) baseStart_7817418 baseEnd_7817418 := by
    simpa [prefixWord, tailWord_7817418, baseEnd_7817418] using wordTrace_append hprefix tailTrace_7817418
  have hstable : (prefixWord ++ tailWord_7817418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7817418).length < 2 ^ (prefixWord ++ tailWord_7817418).sum := by decide
  have hdescent : baseEnd_7817418 < baseStart_7817418 := by decide
  rcases family_descends (prefixWord ++ tailWord_7817418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7817424 : List Nat := [2, 1, 1, 1, 1, 2, 1, 1, 13]
def baseStart_7817424 : Nat := 118140960795 + 7817424 * 2 ^ 59
def prefixEnd_7817424 : Nat := 4983230072969 + 3 ^ 40 * 7817424 * 2
def baseEnd_7817424 : Nat := 446010665777058614038703

theorem tailTrace_7817424 : CollatzResearch.WordTrace tailWord_7817424 prefixEnd_7817424 446010665777058614038703 := by
  unfold tailWord_7817424
  simp only [CollatzResearch.WordTrace]
  refine ⟨142562438615407716285397663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190083251487210288380530217 142562438615407716285397663)
  ·
    refine ⟨213843657923111574428096495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142562438615407716285397663 213843657923111574428096495)
    ·
      refine ⟨320765486884667361642144743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213843657923111574428096495 320765486884667361642144743)
      ·
        refine ⟨481148230327001042463217115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 320765486884667361642144743 481148230327001042463217115)
        ·
          refine ⟨721722345490501563694825673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 481148230327001042463217115 721722345490501563694825673)
          ·
            refine ⟨541291759117876172771119255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 721722345490501563694825673 541291759117876172771119255)
            ·
              refine ⟨811937638676814259156678883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 541291759117876172771119255 811937638676814259156678883)
              ·
                refine ⟨1217906458015221388735018325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 811937638676814259156678883 1217906458015221388735018325)
                ·
                  refine ⟨446010665777058614038703, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 13 1217906458015221388735018325 446010665777058614038703)
                  ·
                    rfl

theorem cell23_7817424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 13].length) (baseStart_7817424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7817424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7817424 prefixEnd_7817424 := by exact prefixLift 7817424
  have htrace : WordTrace (prefixWord ++ tailWord_7817424) baseStart_7817424 baseEnd_7817424 := by
    simpa [prefixWord, tailWord_7817424, baseEnd_7817424] using wordTrace_append hprefix tailTrace_7817424
  have hstable : (prefixWord ++ tailWord_7817424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7817424).length < 2 ^ (prefixWord ++ tailWord_7817424).sum := by decide
  have hdescent : baseEnd_7817424 < baseStart_7817424 := by decide
  rcases family_descends (prefixWord ++ tailWord_7817424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7817441 : List Nat := [1, 2, 3, 1, 3, 1, 3, 2, 7]
def baseStart_7817441 : Nat := 118140960795 + 7817441 * 2 ^ 59
def prefixEnd_7817441 : Nat := 4983230072969 + 3 ^ 40 * 7817441 * 2
def baseEnd_7817441 : Nat := 446011635684961551092861

theorem tailTrace_7817441 : CollatzResearch.WordTrace tailWord_7817441 prefixEnd_7817441 446011635684961551092861 := by
  unfold tailWord_7817441
  simp only [CollatzResearch.WordTrace]
  refine ⟨285125497271753844474164177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190083664847835896316109451 285125497271753844474164177)
  ·
    refine ⟨213844122953815383355623133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 285125497271753844474164177 213844122953815383355623133)
    ·
      refine ⟨80191546107680768758358675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 213844122953815383355623133 80191546107680768758358675)
      ·
        refine ⟨120287319161521153137538013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80191546107680768758358675 120287319161521153137538013)
        ·
          refine ⟨45107744685570432426576755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 120287319161521153137538013 45107744685570432426576755)
          ·
            refine ⟨67661617028355648639865133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45107744685570432426576755 67661617028355648639865133)
            ·
              refine ⟨25373106385633368239949425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67661617028355648639865133 25373106385633368239949425)
              ·
                refine ⟨19029829789225026179962069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25373106385633368239949425 19029829789225026179962069)
                ·
                  refine ⟨446011635684961551092861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19029829789225026179962069 446011635684961551092861)
                  ·
                    rfl

theorem cell23_7817441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 3, 2, 7].length) (baseStart_7817441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7817441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7817441 prefixEnd_7817441 := by exact prefixLift 7817441
  have htrace : WordTrace (prefixWord ++ tailWord_7817441) baseStart_7817441 baseEnd_7817441 := by
    simpa [prefixWord, tailWord_7817441, baseEnd_7817441] using wordTrace_append hprefix tailTrace_7817441
  have hstable : (prefixWord ++ tailWord_7817441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7817441).length < 2 ^ (prefixWord ++ tailWord_7817441).sum := by decide
  have hdescent : baseEnd_7817441 < baseStart_7817441 := by decide
  rcases family_descends (prefixWord ++ tailWord_7817441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7817451 : List Nat := [1, 1, 1, 1, 2, 5, 1, 2, 1, 5, 3]
def baseStart_7817451 : Nat := 118140960795 + 7817451 * 2 ^ 59
def prefixEnd_7817451 : Nat := 4983230072969 + 3 ^ 40 * 7817451 * 2
def baseEnd_7817451 : Nat := 4014109855971198920710703

theorem tailTrace_7817451 : CollatzResearch.WordTrace tailWord_7817451 prefixEnd_7817451 4014109855971198920710703 := by
  unfold tailWord_7817451
  simp only [CollatzResearch.WordTrace]
  refine ⟨285125862001717616182028207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190083908001145077454685471 285125862001717616182028207)
  ·
    refine ⟨427688793002576424273042311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285125862001717616182028207 427688793002576424273042311)
    ·
      refine ⟨641533189503864636409563467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 427688793002576424273042311 641533189503864636409563467)
      ·
        refine ⟨962299784255796954614345201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 641533189503864636409563467 962299784255796954614345201)
        ·
          refine ⟨721724838191847715960758901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 962299784255796954614345201 721724838191847715960758901)
          ·
            refine ⟨67661703580485723371321147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 721724838191847715960758901 67661703580485723371321147)
            ·
              refine ⟨101492555370728585056981721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67661703580485723371321147 101492555370728585056981721)
              ·
                refine ⟨76119416528046438792736291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 101492555370728585056981721 76119416528046438792736291)
                ·
                  refine ⟨114179124792069658189104437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 76119416528046438792736291 114179124792069658189104437)
                  ·
                    refine ⟨10704292949256530455228541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 114179124792069658189104437 10704292949256530455228541)
                    ·
                      refine ⟨4014109855971198920710703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10704292949256530455228541 4014109855971198920710703)
                      ·
                        rfl

theorem cell23_7817451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 2, 1, 5, 3].length) (baseStart_7817451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7817451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7817451 prefixEnd_7817451 := by exact prefixLift 7817451
  have htrace : WordTrace (prefixWord ++ tailWord_7817451) baseStart_7817451 baseEnd_7817451 := by
    simpa [prefixWord, tailWord_7817451, baseEnd_7817451] using wordTrace_append hprefix tailTrace_7817451
  have hstable : (prefixWord ++ tailWord_7817451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7817451).length < 2 ^ (prefixWord ++ tailWord_7817451).sum := by decide
  have hdescent : baseEnd_7817451 < baseStart_7817451 := by decide
  rcases family_descends (prefixWord ++ tailWord_7817451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7817468 : List Nat := [2, 2, 2, 1, 4, 1, 1, 2, 2, 3, 3]
def baseStart_7817468 : Nat := 118140960795 + 7817468 * 2 ^ 59
def prefixEnd_7817468 : Nat := 4983230072969 + 3 ^ 40 * 7817468 * 2
def baseEnd_7817468 : Nat := 4014118585142325354198125

theorem tailTrace_7817468 : CollatzResearch.WordTrace tailWord_7817468 prefixEnd_7817468 4014118585142325354198125 := by
  unfold tailWord_7817468
  simp only [CollatzResearch.WordTrace]
  refine ⟨142563241021328014042698529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190084321361770685390264705 142563241021328014042698529)
  ·
    refine ⟨106922430765996010532023897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142563241021328014042698529 106922430765996010532023897)
    ·
      refine ⟨80191823074497007899017923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106922430765996010532023897 80191823074497007899017923)
      ·
        refine ⟨120287734611745511848526885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80191823074497007899017923 120287734611745511848526885)
        ·
          refine ⟨22553950239702283471598791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 120287734611745511848526885 22553950239702283471598791)
          ·
            refine ⟨33830925359553425207398187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22553950239702283471598791 33830925359553425207398187)
            ·
              refine ⟨50746388039330137811097281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33830925359553425207398187 50746388039330137811097281)
              ·
                refine ⟨38059791029497603358322961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50746388039330137811097281 38059791029497603358322961)
                ·
                  refine ⟨28544843272123202518742221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38059791029497603358322961 28544843272123202518742221)
                  ·
                    refine ⟨10704316227046200944528333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28544843272123202518742221 10704316227046200944528333)
                    ·
                      refine ⟨4014118585142325354198125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10704316227046200944528333 4014118585142325354198125)
                      ·
                        rfl

theorem cell23_7817468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 1, 2, 2, 3, 3].length) (baseStart_7817468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7817468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7817468 prefixEnd_7817468 := by exact prefixLift 7817468
  have htrace : WordTrace (prefixWord ++ tailWord_7817468) baseStart_7817468 baseEnd_7817468 := by
    simpa [prefixWord, tailWord_7817468, baseEnd_7817468] using wordTrace_append hprefix tailTrace_7817468
  have hstable : (prefixWord ++ tailWord_7817468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7817468).length < 2 ^ (prefixWord ++ tailWord_7817468).sum := by decide
  have hdescent : baseEnd_7817468 < baseStart_7817468 := by decide
  rcases family_descends (prefixWord ++ tailWord_7817468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7817471 : List Nat := [1, 1, 2, 2, 1, 4, 2, 1, 4, 5]
def baseStart_7817471 : Nat := 118140960795 + 7817471 * 2 ^ 59
def prefixEnd_7817471 : Nat := 4983230072969 + 3 ^ 40 * 7817471 * 2
def baseEnd_7817471 : Nat := 1338040041861429614153537

theorem tailTrace_7817471 : CollatzResearch.WordTrace tailWord_7817471 prefixEnd_7817471 1338040041861429614153537 := by
  unfold tailWord_7817471
  simp only [CollatzResearch.WordTrace]
  refine ⟨285126591461645159597756267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190084394307763439731837511 285126591461645159597756267)
  ·
    refine ⟨427689887192467739396634401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285126591461645159597756267 427689887192467739396634401)
    ·
      refine ⟨320767415394350804547475801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 427689887192467739396634401 320767415394350804547475801)
      ·
        refine ⟨240575561545763103410606851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 320767415394350804547475801 240575561545763103410606851)
        ·
          refine ⟨360863342318644655115910277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 240575561545763103410606851 360863342318644655115910277)
          ·
            refine ⟨67661876684745872834233177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 360863342318644655115910277 67661876684745872834233177)
            ·
              refine ⟨50746407513559404625674883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67661876684745872834233177 50746407513559404625674883)
              ·
                refine ⟨76119611270339106938512325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50746407513559404625674883 76119611270339106938512325)
                ·
                  refine ⟨14272427113188582550971061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 76119611270339106938512325 14272427113188582550971061)
                  ·
                    refine ⟨1338040041861429614153537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14272427113188582550971061 1338040041861429614153537)
                    ·
                      rfl

theorem cell23_7817471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 2, 1, 4, 5].length) (baseStart_7817471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7817471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7817471 prefixEnd_7817471 := by exact prefixLift 7817471
  have htrace : WordTrace (prefixWord ++ tailWord_7817471) baseStart_7817471 baseEnd_7817471 := by
    simpa [prefixWord, tailWord_7817471, baseEnd_7817471] using wordTrace_append hprefix tailTrace_7817471
  have hstable : (prefixWord ++ tailWord_7817471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7817471).length < 2 ^ (prefixWord ++ tailWord_7817471).sum := by decide
  have hdescent : baseEnd_7817471 < baseStart_7817471 := by decide
  rcases family_descends (prefixWord ++ tailWord_7817471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7817508 : List Nat := [2, 3, 1, 3, 1, 2, 2, 1, 1, 3, 4]
def baseStart_7817508 : Nat := 118140960795 + 7817508 * 2 ^ 59
def prefixEnd_7817508 : Nat := 4983230072969 + 3 ^ 40 * 7817508 * 2
def baseEnd_7817508 : Nat := 4014139124368505197697941

theorem tailTrace_7817508 : CollatzResearch.WordTrace tailWord_7817508 prefixEnd_7817508 4014139124368505197697941 := by
  unfold tailWord_7817508
  simp only [CollatzResearch.WordTrace]
  refine ⟨142563970481255557458426589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190085293975007409944568785 142563970481255557458426589)
  ·
    refine ⟨53461488930470834046909971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 142563970481255557458426589 53461488930470834046909971)
    ·
      refine ⟨80192233395706251070364957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53461488930470834046909971 80192233395706251070364957)
      ·
        refine ⟨30072087523389844151386859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80192233395706251070364957 30072087523389844151386859)
        ·
          refine ⟨45108131285084766227080289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30072087523389844151386859 45108131285084766227080289)
          ·
            refine ⟨33831098463813574670310217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45108131285084766227080289 33831098463813574670310217)
            ·
              refine ⟨25373323847860181002732663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33831098463813574670310217 25373323847860181002732663)
              ·
                refine ⟨38059985771790271504098995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25373323847860181002732663 38059985771790271504098995)
                ·
                  refine ⟨57089978657685407256148493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38059985771790271504098995 57089978657685407256148493)
                  ·
                    refine ⟨21408741996632027721055685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 57089978657685407256148493 21408741996632027721055685)
                    ·
                      refine ⟨4014139124368505197697941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21408741996632027721055685 4014139124368505197697941)
                      ·
                        rfl

theorem cell23_7817508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 2, 1, 1, 3, 4].length) (baseStart_7817508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7817508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7817508 prefixEnd_7817508 := by exact prefixLift 7817508
  have htrace : WordTrace (prefixWord ++ tailWord_7817508) baseStart_7817508 baseEnd_7817508 := by
    simpa [prefixWord, tailWord_7817508, baseEnd_7817508] using wordTrace_append hprefix tailTrace_7817508
  have hstable : (prefixWord ++ tailWord_7817508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7817508).length < 2 ^ (prefixWord ++ tailWord_7817508).sum := by decide
  have hdescent : baseEnd_7817508 < baseStart_7817508 := by decide
  rcases family_descends (prefixWord ++ tailWord_7817508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7817528 : List Nat := [2, 1, 2, 1, 3, 1, 3, 1, 4, 2, 3]
def baseStart_7817528 : Nat := 118140960795 + 7817528 * 2 ^ 59
def prefixEnd_7817528 : Nat := 4983230072969 + 3 ^ 40 * 7817528 * 2
def baseEnd_7817528 : Nat := 4014149393981595119447849

theorem tailTrace_7817528 : CollatzResearch.WordTrace tailWord_7817528 prefixEnd_7817528 4014149393981595119447849 := by
  unfold tailWord_7817528
  simp only [CollatzResearch.WordTrace]
  refine ⟨142564335211219329166290619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190085780281625772221720825 142564335211219329166290619)
  ·
    refine ⟨213846502816828993749435929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142564335211219329166290619 213846502816828993749435929)
    ·
      refine ⟨160384877112621745312076947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 213846502816828993749435929 160384877112621745312076947)
      ·
        refine ⟨240577315668932617968115421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160384877112621745312076947 240577315668932617968115421)
        ·
          refine ⟨90216493375849731738043283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 240577315668932617968115421 90216493375849731738043283)
          ·
            refine ⟨135324740063774597607064925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90216493375849731738043283 135324740063774597607064925)
            ·
              refine ⟨50746777523915474102649347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 135324740063774597607064925 50746777523915474102649347)
              ·
                refine ⟨76120166285873211153974021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50746777523915474102649347 76120166285873211153974021)
                ·
                  refine ⟨14272531178601227091370129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 76120166285873211153974021 14272531178601227091370129)
                  ·
                    refine ⟨10704398383950920318527597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14272531178601227091370129 10704398383950920318527597)
                    ·
                      refine ⟨4014149393981595119447849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10704398383950920318527597 4014149393981595119447849)
                      ·
                        rfl

theorem cell23_7817528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 3, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 3, 1, 4, 2, 3].length) (baseStart_7817528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7817528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7817528 prefixEnd_7817528 := by exact prefixLift 7817528
  have htrace : WordTrace (prefixWord ++ tailWord_7817528) baseStart_7817528 baseEnd_7817528 := by
    simpa [prefixWord, tailWord_7817528, baseEnd_7817528] using wordTrace_append hprefix tailTrace_7817528
  have hstable : (prefixWord ++ tailWord_7817528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7817528).length < 2 ^ (prefixWord ++ tailWord_7817528).sum := by decide
  have hdescent : baseEnd_7817528 < baseStart_7817528 := by decide
  rcases family_descends (prefixWord ++ tailWord_7817528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7817548 : List Nat := [2, 2, 1, 3, 2, 1, 3, 3, 6]
def baseStart_7817548 : Nat := 118140960795 + 7817548 * 2 ^ 59
def prefixEnd_7817548 : Nat := 4983230072969 + 3 ^ 40 * 7817548 * 2
def baseEnd_7817548 : Nat := 446017740399409449021973

theorem tailTrace_7817548 : CollatzResearch.WordTrace tailWord_7817548 prefixEnd_7817548 446017740399409449021973 := by
  unfold tailWord_7817548
  simp only [CollatzResearch.WordTrace]
  refine ⟨142564699941183100874154649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190086266588244134498872865 142564699941183100874154649)
  ·
    refine ⟨106923524955887325655615987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142564699941183100874154649 106923524955887325655615987)
    ·
      refine ⟨160385287433830988483423981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106923524955887325655615987 160385287433830988483423981)
      ·
        refine ⟨60144482787686620681283993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 160385287433830988483423981 60144482787686620681283993)
        ·
          refine ⟨45108362090764965510962995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60144482787686620681283993 45108362090764965510962995)
          ·
            refine ⟨67662543136147448266444493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45108362090764965510962995 67662543136147448266444493)
            ·
              refine ⟨25373453676055293099916685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67662543136147448266444493 25373453676055293099916685)
              ·
                refine ⟨9515045128520734912468757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25373453676055293099916685 9515045128520734912468757)
                ·
                  refine ⟨446017740399409449021973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9515045128520734912468757 446017740399409449021973)
                  ·
                    rfl

theorem cell23_7817548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 3, 3, 6].length) (baseStart_7817548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7817548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7817548 prefixEnd_7817548 := by exact prefixLift 7817548
  have htrace : WordTrace (prefixWord ++ tailWord_7817548) baseStart_7817548 baseEnd_7817548 := by
    simpa [prefixWord, tailWord_7817548, baseEnd_7817548] using wordTrace_append hprefix tailTrace_7817548
  have hstable : (prefixWord ++ tailWord_7817548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7817548).length < 2 ^ (prefixWord ++ tailWord_7817548).sum := by decide
  have hdescent : baseEnd_7817548 < baseStart_7817548 := by decide
  rcases family_descends (prefixWord ++ tailWord_7817548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7817629 : List Nat := [1, 4, 2, 1, 4, 2, 2, 1, 1, 5]
def baseStart_7817629 : Nat := 118140960795 + 7817629 * 2 ^ 59
def prefixEnd_7817629 : Nat := 4983230072969 + 3 ^ 40 * 7817629 * 2
def baseEnd_7817629 : Nat := 1338067085175899741428295

theorem tailTrace_7817629 : CollatzResearch.WordTrace tailWord_7817629 prefixEnd_7817629 1338067085175899741428295 := by
  unfold tailWord_7817629
  simp only [CollatzResearch.WordTrace]
  refine ⟨285132354195072752582007941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190088236130048501721338627 285132354195072752582007941)
  ·
    refine ⟨53462316411576141109126489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 285132354195072752582007941 53462316411576141109126489)
    ·
      refine ⟨40096737308682105831844867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53462316411576141109126489 40096737308682105831844867)
      ·
        refine ⟨60145105963023158747767301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40096737308682105831844867 60145105963023158747767301)
        ·
          refine ⟨11277207368066842265206369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 60145105963023158747767301 11277207368066842265206369)
          ·
            refine ⟨8457905526050131698904777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11277207368066842265206369 8457905526050131698904777)
            ·
              refine ⟨6343429144537598774178583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8457905526050131698904777 6343429144537598774178583)
              ·
                refine ⟨9515143716806398161267875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6343429144537598774178583 9515143716806398161267875)
                ·
                  refine ⟨14272715575209597241901813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9515143716806398161267875 14272715575209597241901813)
                  ·
                    refine ⟨1338067085175899741428295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14272715575209597241901813 1338067085175899741428295)
                    ·
                      rfl

theorem cell23_7817629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 2, 2, 1, 1, 5].length) (baseStart_7817629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7817629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7817629 prefixEnd_7817629 := by exact prefixLift 7817629
  have htrace : WordTrace (prefixWord ++ tailWord_7817629) baseStart_7817629 baseEnd_7817629 := by
    simpa [prefixWord, tailWord_7817629, baseEnd_7817629] using wordTrace_append hprefix tailTrace_7817629
  have hstable : (prefixWord ++ tailWord_7817629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7817629).length < 2 ^ (prefixWord ++ tailWord_7817629).sum := by decide
  have hdescent : baseEnd_7817629 < baseStart_7817629 := by decide
  rcases family_descends (prefixWord ++ tailWord_7817629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7817632 : List Nat := [2, 1, 1, 4, 1, 3, 4, 1, 1, 1, 4]
def baseStart_7817632 : Nat := 118140960795 + 7817632 * 2 ^ 59
def prefixEnd_7817632 : Nat := 4983230072969 + 3 ^ 40 * 7817632 * 2
def baseEnd_7817632 : Nat := 4014202795969662712547371

theorem tailTrace_7817632 : CollatzResearch.WordTrace tailWord_7817632 prefixEnd_7817632 4014202795969662712547371 := by
  unfold tailWord_7817632
  simp only [CollatzResearch.WordTrace]
  refine ⟨142566231807030942047183575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190088309076041256062911433 142566231807030942047183575)
  ·
    refine ⟨213849347710546413070775363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142566231807030942047183575 213849347710546413070775363)
    ·
      refine ⟨320774021565819619606163045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213849347710546413070775363 320774021565819619606163045)
      ·
        refine ⟨60145129043591178676155571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 320774021565819619606163045 60145129043591178676155571)
        ·
          refine ⟨90217693565386768014233357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60145129043591178676155571 90217693565386768014233357)
          ·
            refine ⟨33831635087020038005337509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 90217693565386768014233357 33831635087020038005337509)
            ·
              refine ⟨6343431578816257126000783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33831635087020038005337509 6343431578816257126000783)
              ·
                refine ⟨9515147368224385689001175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6343431578816257126000783 9515147368224385689001175)
                ·
                  refine ⟨14272721052336578533501763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9515147368224385689001175 14272721052336578533501763)
                  ·
                    refine ⟨21409081578504867800252645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14272721052336578533501763 21409081578504867800252645)
                    ·
                      refine ⟨4014202795969662712547371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21409081578504867800252645 4014202795969662712547371)
                      ·
                        rfl

theorem cell23_7817632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 4, 1, 1, 1, 4].length) (baseStart_7817632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7817632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7817632 prefixEnd_7817632 := by exact prefixLift 7817632
  have htrace : WordTrace (prefixWord ++ tailWord_7817632) baseStart_7817632 baseEnd_7817632 := by
    simpa [prefixWord, tailWord_7817632, baseEnd_7817632] using wordTrace_append hprefix tailTrace_7817632
  have hstable : (prefixWord ++ tailWord_7817632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7817632).length < 2 ^ (prefixWord ++ tailWord_7817632).sum := by decide
  have hdescent : baseEnd_7817632 < baseStart_7817632 := by decide
  rcases family_descends (prefixWord ++ tailWord_7817632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7817649 : List Nat := [1, 2, 2, 4, 1, 3, 2, 1, 3, 2, 2]
def baseStart_7817649 : Nat := 118140960795 + 7817649 * 2 ^ 59
def prefixEnd_7817649 : Nat := 4983230072969 + 3 ^ 40 * 7817649 * 2
def baseEnd_7817649 : Nat := 4014211525140789146034793

theorem tailTrace_7817649 : CollatzResearch.WordTrace tailWord_7817649 prefixEnd_7817649 4014211525140789146034793 := by
  unfold tailWord_7817649
  simp only [CollatzResearch.WordTrace]
  refine ⟨285133083655000295997736001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190088722436666863998490667 285133083655000295997736001)
  ·
    refine ⟨213849812741250221998302001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 285133083655000295997736001 213849812741250221998302001)
    ·
      refine ⟨160387359555937666498726501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 213849812741250221998302001 160387359555937666498726501)
      ·
        refine ⟨30072629916738312468511219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 160387359555937666498726501 30072629916738312468511219)
        ·
          refine ⟨45108944875107468702766829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30072629916738312468511219 45108944875107468702766829)
          ·
            refine ⟨16915854328165300763537561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45108944875107468702766829 16915854328165300763537561)
            ·
              refine ⟨12686890746123975572653171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16915854328165300763537561 12686890746123975572653171)
              ·
                refine ⟨19030336119185963358979757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12686890746123975572653171 19030336119185963358979757)
                ·
                  refine ⟨7136376044694736259617409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19030336119185963358979757 7136376044694736259617409)
                  ·
                    refine ⟨5352282033521052194713057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7136376044694736259617409 5352282033521052194713057)
                    ·
                      refine ⟨4014211525140789146034793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5352282033521052194713057 4014211525140789146034793)
                      ·
                        rfl

theorem cell23_7817649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 2, 1, 3, 2, 2].length) (baseStart_7817649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7817649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7817649 prefixEnd_7817649 := by exact prefixLift 7817649
  have htrace : WordTrace (prefixWord ++ tailWord_7817649) baseStart_7817649 baseEnd_7817649 := by
    simpa [prefixWord, tailWord_7817649, baseEnd_7817649] using wordTrace_append hprefix tailTrace_7817649
  have hstable : (prefixWord ++ tailWord_7817649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7817649).length < 2 ^ (prefixWord ++ tailWord_7817649).sum := by decide
  have hdescent : baseEnd_7817649 < baseStart_7817649 := by decide
  rcases family_descends (prefixWord ++ tailWord_7817649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7817688 : List Nat := [2, 1, 2, 2, 2, 1, 1, 2, 1, 5, 4]
def baseStart_7817688 : Nat := 118140960795 + 7817688 * 2 ^ 59
def prefixEnd_7817688 : Nat := 4983230072969 + 3 ^ 40 * 7817688 * 2
def baseEnd_7817688 : Nat := 4014231550886314493447113

theorem tailTrace_7817688 : CollatzResearch.WordTrace tailWord_7817688 prefixEnd_7817688 4014231550886314493447113 := by
  unfold tailWord_7817688
  simp only [CollatzResearch.WordTrace]
  refine ⟨142567253050929502829202859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190089670734572670438937145 142567253050929502829202859)
  ·
    refine ⟨213850879576394254243804289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142567253050929502829202859 213850879576394254243804289)
    ·
      refine ⟨160388159682295690682853217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 213850879576394254243804289 160388159682295690682853217)
      ·
        refine ⟨120291119761721768012139913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 160388159682295690682853217 120291119761721768012139913)
        ·
          refine ⟨90218339821291326009104935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120291119761721768012139913 90218339821291326009104935)
          ·
            refine ⟨135327509731936989013657403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90218339821291326009104935 135327509731936989013657403)
            ·
              refine ⟨202991264597905483520486105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 135327509731936989013657403 202991264597905483520486105)
              ·
                refine ⟨152243448448429112640364579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 202991264597905483520486105 152243448448429112640364579)
                ·
                  refine ⟨228365172672643668960546869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 152243448448429112640364579 228365172672643668960546869)
                  ·
                    refine ⟨21409234938060343965051269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 228365172672643668960546869 21409234938060343965051269)
                    ·
                      refine ⟨4014231550886314493447113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21409234938060343965051269 4014231550886314493447113)
                      ·
                        rfl

theorem cell23_7817688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 2, 1, 5, 4].length) (baseStart_7817688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7817688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7817688 prefixEnd_7817688 := by exact prefixLift 7817688
  have htrace : WordTrace (prefixWord ++ tailWord_7817688) baseStart_7817688 baseEnd_7817688 := by
    simpa [prefixWord, tailWord_7817688, baseEnd_7817688] using wordTrace_append hprefix tailTrace_7817688
  have hstable : (prefixWord ++ tailWord_7817688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7817688).length < 2 ^ (prefixWord ++ tailWord_7817688).sum := by decide
  have hdescent : baseEnd_7817688 < baseStart_7817688 := by decide
  rcases family_descends (prefixWord ++ tailWord_7817688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7817705 : List Nat := [1, 2, 1, 1, 1, 2, 1, 3, 5, 4, 2]
def baseStart_7817705 : Nat := 118140960795 + 7817705 * 2 ^ 59
def prefixEnd_7817705 : Nat := 4983230072969 + 3 ^ 40 * 7817705 * 2
def baseEnd_7817705 : Nat := 4014240280057440926934535

theorem tailTrace_7817705 : CollatzResearch.WordTrace tailWord_7817705 prefixEnd_7817705 4014240280057440926934535 := by
  unfold tailWord_7817705
  simp only [CollatzResearch.WordTrace]
  refine ⟨285135126142797417561774569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190090084095198278374516379 285135126142797417561774569)
  ·
    refine ⟨213851344607098063171330927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 285135126142797417561774569 213851344607098063171330927)
    ·
      refine ⟨320777016910647094756996391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213851344607098063171330927 320777016910647094756996391)
      ·
        refine ⟨481165525365970642135494587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 320777016910647094756996391 481165525365970642135494587)
        ·
          refine ⟨721748288048955963203241881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 481165525365970642135494587 721748288048955963203241881)
          ·
            refine ⟨541311216036716972402431411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 721748288048955963203241881 541311216036716972402431411)
            ·
              refine ⟨811966824055075458603647117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 541311216036716972402431411 811966824055075458603647117)
              ·
                refine ⟨304487559020653296976367669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 811966824055075458603647117 304487559020653296976367669)
                ·
                  refine ⟨28545708658186246591534469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 304487559020653296976367669 28545708658186246591534469)
                  ·
                    refine ⟨5352320373409921235912713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28545708658186246591534469 5352320373409921235912713)
                    ·
                      refine ⟨4014240280057440926934535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5352320373409921235912713 4014240280057440926934535)
                      ·
                        rfl

theorem cell23_7817705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 3, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 3, 5, 4, 2].length) (baseStart_7817705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7817705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7817705 prefixEnd_7817705 := by exact prefixLift 7817705
  have htrace : WordTrace (prefixWord ++ tailWord_7817705) baseStart_7817705 baseEnd_7817705 := by
    simpa [prefixWord, tailWord_7817705, baseEnd_7817705] using wordTrace_append hprefix tailTrace_7817705
  have hstable : (prefixWord ++ tailWord_7817705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7817705).length < 2 ^ (prefixWord ++ tailWord_7817705).sum := by decide
  have hdescent : baseEnd_7817705 < baseStart_7817705 := by decide
  rcases family_descends (prefixWord ++ tailWord_7817705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7817708 : List Nat := [2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 5]
def baseStart_7817708 : Nat := 118140960795 + 7817708 * 2 ^ 59
def prefixEnd_7817708 : Nat := 4983230072969 + 3 ^ 40 * 7817708 * 2
def baseEnd_7817708 : Nat := 4014241820499404415197021

theorem tailTrace_7817708 : CollatzResearch.WordTrace tailWord_7817708 prefixEnd_7817708 4014241820499404415197021 := by
  unfold tailWord_7817708
  simp only [CollatzResearch.WordTrace]
  refine ⟨142567617780893274537066889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190090157041191032716089185 142567617780893274537066889)
  ·
    refine ⟨106925713335669955902800167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142567617780893274537066889 106925713335669955902800167)
    ·
      refine ⟨160388570003504933854200251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106925713335669955902800167 160388570003504933854200251)
      ·
        refine ⟨240582855005257400781300377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160388570003504933854200251 240582855005257400781300377)
        ·
          refine ⟨180437141253943050585975283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 240582855005257400781300377 180437141253943050585975283)
          ·
            refine ⟨270655711880914575878962925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 180437141253943050585975283 270655711880914575878962925)
            ·
              refine ⟨101495891955342965954611097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 270655711880914575878962925 101495891955342965954611097)
              ·
                refine ⟨76121918966507224465958323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 101495891955342965954611097 76121918966507224465958323)
                ·
                  refine ⟨114182878449760836698937485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 76121918966507224465958323 114182878449760836698937485)
                  ·
                    refine ⟨42818579418660313762101557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 114182878449760836698937485 42818579418660313762101557)
                    ·
                      refine ⟨4014241820499404415197021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42818579418660313762101557 4014241820499404415197021)
                      ·
                        rfl

theorem cell23_7817708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 5].length) (baseStart_7817708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7817708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7817708 prefixEnd_7817708 := by exact prefixLift 7817708
  have htrace : WordTrace (prefixWord ++ tailWord_7817708) baseStart_7817708 baseEnd_7817708 := by
    simpa [prefixWord, tailWord_7817708, baseEnd_7817708] using wordTrace_append hprefix tailTrace_7817708
  have hstable : (prefixWord ++ tailWord_7817708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7817708).length < 2 ^ (prefixWord ++ tailWord_7817708).sum := by decide
  have hdescent : baseEnd_7817708 < baseStart_7817708 := by decide
  rcases family_descends (prefixWord ++ tailWord_7817708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7817722 : List Nat := [3, 1, 1, 1, 1, 2, 2, 2, 6, 2, 2]
def baseStart_7817722 : Nat := 118140960795 + 7817722 * 2 ^ 59
def prefixEnd_7817722 : Nat := 4983230072969 + 3 ^ 40 * 7817722 * 2
def baseEnd_7817722 : Nat := 4014249009228567360421957

theorem tailTrace_7817722 : CollatzResearch.WordTrace tailWord_7817722 prefixEnd_7817722 4014249009228567360421957 := by
  unfold tailWord_7817722
  simp only [CollatzResearch.WordTrace]
  refine ⟨71283936545933957366285855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 190090497455823886310095613 71283936545933957366285855)
  ·
    refine ⟨106925904818900936049428783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71283936545933957366285855 106925904818900936049428783)
    ·
      refine ⟨160388857228351404074143175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106925904818900936049428783 160388857228351404074143175)
      ·
        refine ⟨240583285842527106111214763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160388857228351404074143175 240583285842527106111214763)
        ·
          refine ⟨360874928763790659166822145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 240583285842527106111214763 360874928763790659166822145)
          ·
            refine ⟨270656196572842994375116609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 360874928763790659166822145 270656196572842994375116609)
            ·
              refine ⟨202992147429632245781337457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 270656196572842994375116609 202992147429632245781337457)
              ·
                refine ⟨152244110572224184336003093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 202992147429632245781337457 152244110572224184336003093)
                ·
                  refine ⟨7136442683073008640750145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 152244110572224184336003093 7136442683073008640750145)
                  ·
                    refine ⟨5352332012304756480562609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7136442683073008640750145 5352332012304756480562609)
                    ·
                      refine ⟨4014249009228567360421957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5352332012304756480562609 4014249009228567360421957)
                      ·
                        rfl

theorem cell23_7817722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 2, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 2, 6, 2, 2].length) (baseStart_7817722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7817722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7817722 prefixEnd_7817722 := by exact prefixLift 7817722
  have htrace : WordTrace (prefixWord ++ tailWord_7817722) baseStart_7817722 baseEnd_7817722 := by
    simpa [prefixWord, tailWord_7817722, baseEnd_7817722] using wordTrace_append hprefix tailTrace_7817722
  have hstable : (prefixWord ++ tailWord_7817722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7817722).length < 2 ^ (prefixWord ++ tailWord_7817722).sum := by decide
  have hdescent : baseEnd_7817722 < baseStart_7817722 := by decide
  rcases family_descends (prefixWord ++ tailWord_7817722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7817756 : List Nat := [2, 2, 3, 1, 2, 3, 2, 2, 2, 2, 2]
def baseStart_7817756 : Nat := 118140960795 + 7817756 * 2 ^ 59
def prefixEnd_7817756 : Nat := 4983230072969 + 3 ^ 40 * 7817756 * 2
def baseEnd_7817756 : Nat := 4014266467570820227396801

theorem tailTrace_7817756 : CollatzResearch.WordTrace tailWord_7817756 prefixEnd_7817756 4014266467570820227396801 := by
  unfold tailWord_7817756
  simp only [CollatzResearch.WordTrace]
  refine ⟨142568493132806326635940561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190091324177075102181254081 142568493132806326635940561)
  ·
    refine ⟨106926369849604744976955421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142568493132806326635940561 106926369849604744976955421)
    ·
      refine ⟨40097388693601779366358283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 106926369849604744976955421 40097388693601779366358283)
      ·
        refine ⟨60146083040402669049537425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40097388693601779366358283 60146083040402669049537425)
        ·
          refine ⟨45109562280302001787153069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60146083040402669049537425 45109562280302001787153069)
          ·
            refine ⟨16916085855113250670182401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45109562280302001787153069 16916085855113250670182401)
            ·
              refine ⟨12687064391334938002636801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16916085855113250670182401 12687064391334938002636801)
              ·
                refine ⟨9515298293501203501977601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12687064391334938002636801 9515298293501203501977601)
                ·
                  refine ⟨7136473720125902626483201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9515298293501203501977601 7136473720125902626483201)
                  ·
                    refine ⟨5352355290094426969862401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7136473720125902626483201 5352355290094426969862401)
                    ·
                      refine ⟨4014266467570820227396801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5352355290094426969862401 4014266467570820227396801)
                      ·
                        rfl

theorem cell23_7817756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 2, 2, 2, 2, 2].length) (baseStart_7817756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7817756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7817756 prefixEnd_7817756 := by exact prefixLift 7817756
  have htrace : WordTrace (prefixWord ++ tailWord_7817756) baseStart_7817756 baseEnd_7817756 := by
    simpa [prefixWord, tailWord_7817756, baseEnd_7817756] using wordTrace_append hprefix tailTrace_7817756
  have hstable : (prefixWord ++ tailWord_7817756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7817756).length < 2 ^ (prefixWord ++ tailWord_7817756).sum := by decide
  have hdescent : baseEnd_7817756 < baseStart_7817756 := by decide
  rcases family_descends (prefixWord ++ tailWord_7817756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7817856 : List Nat := [2, 1, 1, 2, 1, 7, 1, 3, 1, 4]
def baseStart_7817856 : Nat := 118140960795 + 7817856 * 2 ^ 59
def prefixEnd_7817856 : Nat := 4983230072969 + 3 ^ 40 * 7817856 * 2
def baseEnd_7817856 : Nat := 1338105938545423278715447

theorem tailTrace_7817856 : CollatzResearch.WordTrace tailWord_7817856 prefixEnd_7817856 1338105938545423278715447 := by
  unfold tailWord_7817856
  simp only [CollatzResearch.WordTrace]
  refine ⟨142570316782625185175260711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190093755710166913567014281 142570316782625185175260711)
  ·
    refine ⟨213855475173937777762891067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142570316782625185175260711 213855475173937777762891067)
    ·
      refine ⟨320783212760906666644336601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213855475173937777762891067 320783212760906666644336601)
      ·
        refine ⟨240587409570679999983252451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 320783212760906666644336601 240587409570679999983252451)
        ·
          refine ⟨360881114356019999974878677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 240587409570679999983252451 360881114356019999974878677)
          ·
            refine ⟨8458151117719218749411219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 360881114356019999974878677 8458151117719218749411219)
            ·
              refine ⟨12687226676578828124116829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8458151117719218749411219 12687226676578828124116829)
              ·
                refine ⟨4757710003717060546543811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12687226676578828124116829 4757710003717060546543811)
                ·
                  refine ⟨7136565005575590819815717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4757710003717060546543811 7136565005575590819815717)
                  ·
                    refine ⟨1338105938545423278715447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7136565005575590819815717 1338105938545423278715447)
                    ·
                      rfl

theorem cell23_7817856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 7, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 7, 1, 3, 1, 4].length) (baseStart_7817856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7817856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7817856 prefixEnd_7817856 := by exact prefixLift 7817856
  have htrace : WordTrace (prefixWord ++ tailWord_7817856) baseStart_7817856 baseEnd_7817856 := by
    simpa [prefixWord, tailWord_7817856, baseEnd_7817856] using wordTrace_append hprefix tailTrace_7817856
  have hstable : (prefixWord ++ tailWord_7817856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7817856).length < 2 ^ (prefixWord ++ tailWord_7817856).sum := by decide
  have hdescent : baseEnd_7817856 < baseStart_7817856 := by decide
  rcases family_descends (prefixWord ++ tailWord_7817856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7817865 : List Nat := [1, 2, 1, 1, 4, 1, 1, 2, 5, 5]
def baseStart_7817865 : Nat := 118140960795 + 7817865 * 2 ^ 59
def prefixEnd_7817865 : Nat := 4983230072969 + 3 ^ 40 * 7817865 * 2
def baseEnd_7817865 : Nat := 1338107478987386766977933

theorem tailTrace_7817865 : CollatzResearch.WordTrace tailWord_7817865 prefixEnd_7817865 1338107478987386766977933 := by
  unfold tailWord_7817865
  simp only [CollatzResearch.WordTrace]
  refine ⟨285140961822217764887599049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190093974548145176591732699 285140961822217764887599049)
  ·
    refine ⟨213855721366663323665699287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 285140961822217764887599049 213855721366663323665699287)
    ·
      refine ⟨320783582049994985498548931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213855721366663323665699287 320783582049994985498548931)
      ·
        refine ⟨481175373074992478247823397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 320783582049994985498548931 481175373074992478247823397)
        ·
          refine ⟨90220382451561089671466887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 481175373074992478247823397 90220382451561089671466887)
          ·
            refine ⟨135330573677341634507200331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90220382451561089671466887 135330573677341634507200331)
            ·
              refine ⟨202995860516012451760800497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 135330573677341634507200331 202995860516012451760800497)
              ·
                refine ⟨152246895387009338820600373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 202995860516012451760800497 152246895387009338820600373)
                ·
                  refine ⟨14273146442532125514431285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 152246895387009338820600373 14273146442532125514431285)
                  ·
                    refine ⟨1338107478987386766977933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14273146442532125514431285 1338107478987386766977933)
                    ·
                      rfl

theorem cell23_7817865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 2, 5, 5].length) (baseStart_7817865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7817865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7817865 prefixEnd_7817865 := by exact prefixLift 7817865
  have htrace : WordTrace (prefixWord ++ tailWord_7817865) baseStart_7817865 baseEnd_7817865 := by
    simpa [prefixWord, tailWord_7817865, baseEnd_7817865] using wordTrace_append hprefix tailTrace_7817865
  have hstable : (prefixWord ++ tailWord_7817865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7817865).length < 2 ^ (prefixWord ++ tailWord_7817865).sum := by decide
  have hdescent : baseEnd_7817865 < baseStart_7817865 := by decide
  rcases family_descends (prefixWord ++ tailWord_7817865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7817930 : List Nat := [3, 1, 2, 1, 4, 3, 2, 2, 1, 1, 3]
def baseStart_7817930 : Nat := 118140960795 + 7817930 * 2 ^ 59
def prefixEnd_7817930 : Nat := 4983230072969 + 3 ^ 40 * 7817930 * 2
def baseEnd_7817930 : Nat := 4014355813204702546621001

theorem tailTrace_7817930 : CollatzResearch.WordTrace tailWord_7817930 prefixEnd_7817930 4014355813204702546621001 := by
  unfold tailWord_7817930
  simp only [CollatzResearch.WordTrace]
  refine ⟨71285833141745570247178811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 190095555044654853992476829 71285833141745570247178811)
  ·
    refine ⟨106928749712618355370768217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71285833141745570247178811 106928749712618355370768217)
    ·
      refine ⟨80196562284463766528076163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106928749712618355370768217 80196562284463766528076163)
      ·
        refine ⟨120294843426695649792114245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80196562284463766528076163 120294843426695649792114245)
        ·
          refine ⟨22555283142505434336021421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 120294843426695649792114245 22555283142505434336021421)
          ·
            refine ⟨8458231178439537876008033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22555283142505434336021421 8458231178439537876008033)
            ·
              refine ⟨6343673383829653407006025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8458231178439537876008033 6343673383829653407006025)
              ·
                refine ⟨4757755037872240055254519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6343673383829653407006025 4757755037872240055254519)
                ·
                  refine ⟨7136632556808360082881779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4757755037872240055254519 7136632556808360082881779)
                  ·
                    refine ⟨10704948835212540124322669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7136632556808360082881779 10704948835212540124322669)
                    ·
                      refine ⟨4014355813204702546621001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10704948835212540124322669 4014355813204702546621001)
                      ·
                        rfl

theorem cell23_7817930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 3, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 3, 2, 2, 1, 1, 3].length) (baseStart_7817930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7817930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7817930 prefixEnd_7817930 := by exact prefixLift 7817930
  have htrace : WordTrace (prefixWord ++ tailWord_7817930) baseStart_7817930 baseEnd_7817930 := by
    simpa [prefixWord, tailWord_7817930, baseEnd_7817930] using wordTrace_append hprefix tailTrace_7817930
  have hstable : (prefixWord ++ tailWord_7817930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7817930).length < 2 ^ (prefixWord ++ tailWord_7817930).sum := by decide
  have hdescent : baseEnd_7817930 < baseStart_7817930 := by decide
  rcases family_descends (prefixWord ++ tailWord_7817930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7817969 : List Nat := [1, 2, 2, 2, 2, 2, 2, 2, 4, 1, 3]
def baseStart_7817969 : Nat := 118140960795 + 7817969 * 2 ^ 59
def prefixEnd_7817969 : Nat := 4983230072969 + 3 ^ 40 * 7817969 * 2
def baseEnd_7817969 : Nat := 4014375838950227894033321

theorem tailTrace_7817969 : CollatzResearch.WordTrace tailWord_7817969 prefixEnd_7817969 4014375838950227894033321 := by
  unfold tailWord_7817969
  simp only [CollatzResearch.WordTrace]
  refine ⟨285144755013840990649384961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190096503342560660432923307 285144755013840990649384961)
  ·
    refine ⟨213858566260380742987038721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 285144755013840990649384961 213858566260380742987038721)
    ·
      refine ⟨160393924695285557240279041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 213858566260380742987038721 160393924695285557240279041)
      ·
        refine ⟨120295443521464167930209281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 160393924695285557240279041 120295443521464167930209281)
        ·
          refine ⟨90221582641098125947656961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120295443521464167930209281 90221582641098125947656961)
          ·
            refine ⟨67666186980823594460742721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90221582641098125947656961 67666186980823594460742721)
            ·
              refine ⟨50749640235617695845557041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67666186980823594460742721 50749640235617695845557041)
              ·
                refine ⟨38062230176713271884167781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50749640235617695845557041 38062230176713271884167781)
                ·
                  refine ⟨7136668158133738478281459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38062230176713271884167781 7136668158133738478281459)
                  ·
                    refine ⟨10705002237200607717422189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7136668158133738478281459 10705002237200607717422189)
                    ·
                      refine ⟨4014375838950227894033321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10705002237200607717422189 4014375838950227894033321)
                      ·
                        rfl

theorem cell23_7817969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 4, 1, 3].length) (baseStart_7817969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7817969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7817969 prefixEnd_7817969 := by exact prefixLift 7817969
  have htrace : WordTrace (prefixWord ++ tailWord_7817969) baseStart_7817969 baseEnd_7817969 := by
    simpa [prefixWord, tailWord_7817969, baseEnd_7817969] using wordTrace_append hprefix tailTrace_7817969
  have hstable : (prefixWord ++ tailWord_7817969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7817969).length < 2 ^ (prefixWord ++ tailWord_7817969).sum := by decide
  have hdescent : baseEnd_7817969 < baseStart_7817969 := by decide
  rcases family_descends (prefixWord ++ tailWord_7817969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7817970 : List Nat := [3, 2, 1, 3, 1, 3, 2, 3, 1, 2, 2]
def baseStart_7817970 : Nat := 118140960795 + 7817970 * 2 ^ 59
def prefixEnd_7817970 : Nat := 4983230072969 + 3 ^ 40 * 7817970 * 2
def baseEnd_7817970 : Nat := 4014376352430882390120817

theorem tailTrace_7817970 : CollatzResearch.WordTrace tailWord_7817970 prefixEnd_7817970 4014376352430882390120817 := by
  unfold tailWord_7817970
  simp only [CollatzResearch.WordTrace]
  refine ⟨71286197871709341955042841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 190096527657891578546780909 71286197871709341955042841)
  ·
    refine ⟨53464648403782006466282131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71286197871709341955042841 53464648403782006466282131)
    ·
      refine ⟨80196972605673009699423197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53464648403782006466282131 80196972605673009699423197)
      ·
        refine ⟨30073864727127378637283699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80196972605673009699423197 30073864727127378637283699)
        ·
          refine ⟨45110797090691067955925549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30073864727127378637283699 45110797090691067955925549)
          ·
            refine ⟨16916548909009150483472081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45110797090691067955925549 16916548909009150483472081)
            ·
              refine ⟨12687411681756862862604061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16916548909009150483472081 12687411681756862862604061)
              ·
                refine ⟨4757779380658823573476523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12687411681756862862604061 4757779380658823573476523)
                ·
                  refine ⟨7136669070988235360214785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4757779380658823573476523 7136669070988235360214785)
                  ·
                    refine ⟨5352501803241176520161089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7136669070988235360214785 5352501803241176520161089)
                    ·
                      refine ⟨4014376352430882390120817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5352501803241176520161089 4014376352430882390120817)
                      ·
                        rfl

theorem cell23_7817970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 2, 3, 1, 2, 2].length) (baseStart_7817970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7817970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7817970 prefixEnd_7817970 := by exact prefixLift 7817970
  have htrace : WordTrace (prefixWord ++ tailWord_7817970) baseStart_7817970 baseEnd_7817970 := by
    simpa [prefixWord, tailWord_7817970, baseEnd_7817970] using wordTrace_append hprefix tailTrace_7817970
  have hstable : (prefixWord ++ tailWord_7817970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7817970).length < 2 ^ (prefixWord ++ tailWord_7817970).sum := by decide
  have hdescent : baseEnd_7817970 < baseStart_7817970 := by decide
  rcases family_descends (prefixWord ++ tailWord_7817970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7818009 : List Nat := [1, 2, 1, 2, 1, 1, 1, 7, 1, 4, 2]
def baseStart_7818009 : Nat := 118140960795 + 7818009 * 2 ^ 59
def prefixEnd_7818009 : Nat := 4983230072969 + 3 ^ 40 * 7818009 * 2
def baseEnd_7818009 : Nat := 4014396378176407737533137

theorem tailTrace_7818009 : CollatzResearch.WordTrace tailWord_7818009 prefixEnd_7818009 4014396378176407737533137 := by
  unfold tailWord_7818009
  simp only [CollatzResearch.WordTrace]
  refine ⟨285146213933696077480841081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190097475955797384987227387 285146213933696077480841081)
  ·
    refine ⟨213859660450272058110630811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 285146213933696077480841081 213859660450272058110630811)
    ·
      refine ⟨320789490675408087165946217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213859660450272058110630811 320789490675408087165946217)
      ·
        refine ⟨240592118006556065374459663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 320789490675408087165946217 240592118006556065374459663)
        ·
          refine ⟨360888177009834098061689495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 240592118006556065374459663 360888177009834098061689495)
          ·
            refine ⟨541332265514751147092534243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 360888177009834098061689495 541332265514751147092534243)
            ·
              refine ⟨811998398272126720638801365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 541332265514751147092534243 811998398272126720638801365)
              ·
                refine ⟨19031212459502970014971907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 811998398272126720638801365 19031212459502970014971907)
                ·
                  refine ⟨28546818689254455022457861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19031212459502970014971907 28546818689254455022457861)
                  ·
                    refine ⟨5352528504235210316710849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28546818689254455022457861 5352528504235210316710849)
                    ·
                      refine ⟨4014396378176407737533137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5352528504235210316710849 4014396378176407737533137)
                      ·
                        rfl

theorem cell23_7818009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 7, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 7, 1, 4, 2].length) (baseStart_7818009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7818009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7818009 prefixEnd_7818009 := by exact prefixLift 7818009
  have htrace : WordTrace (prefixWord ++ tailWord_7818009) baseStart_7818009 baseEnd_7818009 := by
    simpa [prefixWord, tailWord_7818009, baseEnd_7818009] using wordTrace_append hprefix tailTrace_7818009
  have hstable : (prefixWord ++ tailWord_7818009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7818009).length < 2 ^ (prefixWord ++ tailWord_7818009).sum := by decide
  have hdescent : baseEnd_7818009 < baseStart_7818009 := by decide
  rcases family_descends (prefixWord ++ tailWord_7818009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7818054 : List Nat := [6, 1, 1, 2, 2, 2, 2, 1, 2, 1, 3]
def baseStart_7818054 : Nat := 118140960795 + 7818054 * 2 ^ 59
def prefixEnd_7818054 : Nat := 4983230072969 + 3 ^ 40 * 7818054 * 2
def baseEnd_7818054 : Nat := 4014419484805860061470431

theorem tailTrace_7818054 : CollatzResearch.WordTrace tailWord_7818054 prefixEnd_7818054 4014419484805860061470431 := by
  unfold tailWord_7818054
  simp only [CollatzResearch.WordTrace]
  refine ⟨8910870475579157817694663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 190098570145688700110819477 8910870475579157817694663)
  ·
    refine ⟨13366305713368736726541995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8910870475579157817694663 13366305713368736726541995)
    ·
      refine ⟨20049458570053105089812993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13366305713368736726541995 20049458570053105089812993)
      ·
        refine ⟨15037093927539828817359745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20049458570053105089812993 15037093927539828817359745)
        ·
          refine ⟨11277820445654871613019809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15037093927539828817359745 11277820445654871613019809)
          ·
            refine ⟨8458365334241153709764857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11277820445654871613019809 8458365334241153709764857)
            ·
              refine ⟨6343774000680865282323643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8458365334241153709764857 6343774000680865282323643)
              ·
                refine ⟨9515661001021297923485465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6343774000680865282323643 9515661001021297923485465)
                ·
                  refine ⟨7136745750765973442614099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9515661001021297923485465 7136745750765973442614099)
                  ·
                    refine ⟨10705118626148960163921149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7136745750765973442614099 10705118626148960163921149)
                    ·
                      refine ⟨4014419484805860061470431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10705118626148960163921149 4014419484805860061470431)
                      ·
                        rfl

theorem cell23_7818054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 2, 2, 1, 2, 1, 3].length) (baseStart_7818054 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7818054 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7818054 prefixEnd_7818054 := by exact prefixLift 7818054
  have htrace : WordTrace (prefixWord ++ tailWord_7818054) baseStart_7818054 baseEnd_7818054 := by
    simpa [prefixWord, tailWord_7818054, baseEnd_7818054] using wordTrace_append hprefix tailTrace_7818054
  have hstable : (prefixWord ++ tailWord_7818054).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7818054).length < 2 ^ (prefixWord ++ tailWord_7818054).sum := by decide
  have hdescent : baseEnd_7818054 < baseStart_7818054 := by decide
  rcases family_descends (prefixWord ++ tailWord_7818054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7818060 : List Nat := [2, 2, 1, 3, 3, 1, 4, 1, 2, 2, 2]
def baseStart_7818060 : Nat := 118140960795 + 7818060 * 2 ^ 59
def prefixEnd_7818060 : Nat := 4983230072969 + 3 ^ 40 * 7818060 * 2
def baseEnd_7818060 : Nat := 4014422565689787037995403

theorem tailTrace_7818060 : CollatzResearch.WordTrace tailWord_7818060 prefixEnd_7818060 4014422565689787037995403 := by
  unfold tailWord_7818060
  simp only [CollatzResearch.WordTrace]
  refine ⟨142574037028255656595473817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190098716037674208793965089 142574037028255656595473817)
  ·
    refine ⟨106930527771191742446605363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142574037028255656595473817 106930527771191742446605363)
    ·
      refine ⟨160395791656787613669908045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106930527771191742446605363 160395791656787613669908045)
      ·
        refine ⟨60148421871295355126215517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 160395791656787613669908045 60148421871295355126215517)
        ·
          refine ⟨22555658201735758172330819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60148421871295355126215517 22555658201735758172330819)
          ·
            refine ⟨33833487302603637258496229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22555658201735758172330819 33833487302603637258496229)
            ·
              refine ⟨6343778869238181985968043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33833487302603637258496229 6343778869238181985968043)
              ·
                refine ⟨9515668303857272978952065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6343778869238181985968043 9515668303857272978952065)
                ·
                  refine ⟨7136751227892954734214049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9515668303857272978952065 7136751227892954734214049)
                  ·
                    refine ⟨5352563420919716050660537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7136751227892954734214049 5352563420919716050660537)
                    ·
                      refine ⟨4014422565689787037995403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5352563420919716050660537 4014422565689787037995403)
                      ·
                        rfl

theorem cell23_7818060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 4, 1, 2, 2, 2].length) (baseStart_7818060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7818060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7818060 prefixEnd_7818060 := by exact prefixLift 7818060
  have htrace : WordTrace (prefixWord ++ tailWord_7818060) baseStart_7818060 baseEnd_7818060 := by
    simpa [prefixWord, tailWord_7818060, baseEnd_7818060] using wordTrace_append hprefix tailTrace_7818060
  have hstable : (prefixWord ++ tailWord_7818060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7818060).length < 2 ^ (prefixWord ++ tailWord_7818060).sum := by decide
  have hdescent : baseEnd_7818060 < baseStart_7818060 := by decide
  rcases family_descends (prefixWord ++ tailWord_7818060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7818062 : List Nat := [4, 1, 1, 1, 1, 1, 1, 3, 3, 7]
def baseStart_7818062 : Nat := 118140960795 + 7818062 * 2 ^ 59
def prefixEnd_7818062 : Nat := 4983230072969 + 3 ^ 40 * 7818062 * 2
def baseEnd_7818062 : Nat := 1338141197550365343390131

theorem tailTrace_7818062 : CollatzResearch.WordTrace tailWord_7818062 prefixEnd_7818062 1338141197550365343390131 := by
  unfold tailWord_7818062
  simp only [CollatzResearch.WordTrace]
  refine ⟨35643518375313008441565055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 190098764668336045021680293 35643518375313008441565055)
  ·
    refine ⟨53465277562969512662347583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35643518375313008441565055 53465277562969512662347583)
    ·
      refine ⟨80197916344454268993521375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53465277562969512662347583 80197916344454268993521375)
      ·
        refine ⟨120296874516681403490282063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80197916344454268993521375 120296874516681403490282063)
        ·
          refine ⟨180445311775022105235423095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120296874516681403490282063 180445311775022105235423095)
          ·
            refine ⟨270667967662533157853134643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 180445311775022105235423095 270667967662533157853134643)
            ·
              refine ⟨406001951493799736779701965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 270667967662533157853134643 406001951493799736779701965)
              ·
                refine ⟨152250731810174901292388237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 406001951493799736779701965 152250731810174901292388237)
                ·
                  refine ⟨57094024428815587984645589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 152250731810174901292388237 57094024428815587984645589)
                  ·
                    refine ⟨1338141197550365343390131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 57094024428815587984645589 1338141197550365343390131)
                    ·
                      rfl

theorem cell23_7818062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 3, 3, 7].length) (baseStart_7818062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7818062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7818062 prefixEnd_7818062 := by exact prefixLift 7818062
  have htrace : WordTrace (prefixWord ++ tailWord_7818062) baseStart_7818062 baseEnd_7818062 := by
    simpa [prefixWord, tailWord_7818062, baseEnd_7818062] using wordTrace_append hprefix tailTrace_7818062
  have hstable : (prefixWord ++ tailWord_7818062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7818062).length < 2 ^ (prefixWord ++ tailWord_7818062).sum := by decide
  have hdescent : baseEnd_7818062 < baseStart_7818062 := by decide
  rcases family_descends (prefixWord ++ tailWord_7818062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7818079 : List Nat := [1, 1, 2, 3, 1, 3, 4, 1, 2, 5]
def baseStart_7818079 : Nat := 118140960795 + 7818079 * 2 ^ 59
def prefixEnd_7818079 : Nat := 4983230072969 + 3 ^ 40 * 7818079 * 2
def baseEnd_7818079 : Nat := 1338144107274074154552605

theorem tailTrace_7818079 : CollatzResearch.WordTrace tailWord_7818079 prefixEnd_7818079 1338144107274074154552605 := by
  unfold tailWord_7818079
  simp only [CollatzResearch.WordTrace]
  refine ⟨285148767043442479435889291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190099178028961652957259527 285148767043442479435889291)
  ·
    refine ⟨427723150565163719153833937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285148767043442479435889291 427723150565163719153833937)
    ·
      refine ⟨320792362923872789365375453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 427723150565163719153833937 320792362923872789365375453)
      ·
        refine ⟨120297136096452296012015795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 320792362923872789365375453 120297136096452296012015795)
        ·
          refine ⟨180445704144678444018023693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120297136096452296012015795 180445704144678444018023693)
          ·
            refine ⟨67667139054254416506758885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 180445704144678444018023693 67667139054254416506758885)
            ·
              refine ⟨12687588572672703095017291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 67667139054254416506758885 12687588572672703095017291)
              ·
                refine ⟨19031382859009054642525937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12687588572672703095017291 19031382859009054642525937)
                ·
                  refine ⟨14273537144256790981894453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19031382859009054642525937 14273537144256790981894453)
                  ·
                    refine ⟨1338144107274074154552605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14273537144256790981894453 1338144107274074154552605)
                    ·
                      rfl

theorem cell23_7818079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 4, 1, 2, 5].length) (baseStart_7818079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7818079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7818079 prefixEnd_7818079 := by exact prefixLift 7818079
  have htrace : WordTrace (prefixWord ++ tailWord_7818079) baseStart_7818079 baseEnd_7818079 := by
    simpa [prefixWord, tailWord_7818079, baseEnd_7818079] using wordTrace_append hprefix tailTrace_7818079
  have hstable : (prefixWord ++ tailWord_7818079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7818079).length < 2 ^ (prefixWord ++ tailWord_7818079).sum := by decide
  have hdescent : baseEnd_7818079 < baseStart_7818079 := by decide
  rcases family_descends (prefixWord ++ tailWord_7818079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7818099 : List Nat := [1, 1, 1, 2, 2, 1, 6, 2, 2, 1, 4]
def baseStart_7818099 : Nat := 118140960795 + 7818099 * 2 ^ 59
def prefixEnd_7818099 : Nat := 4983230072969 + 3 ^ 40 * 7818099 * 2
def baseEnd_7818099 : Nat := 4014442591435312385407723

theorem tailTrace_7818099 : CollatzResearch.WordTrace tailWord_7818099 prefixEnd_7818099 4014442591435312385407723 := by
  unfold tailWord_7818099
  simp only [CollatzResearch.WordTrace]
  refine ⟨285149496503370022851617351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190099664335580015234411567 285149496503370022851617351)
  ·
    refine ⟨427724244755055034277426027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285149496503370022851617351 427724244755055034277426027)
    ·
      refine ⟨641586367132582551416139041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 427724244755055034277426027 641586367132582551416139041)
      ·
        refine ⟨481189775349436913562104281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 641586367132582551416139041 481189775349436913562104281)
        ·
          refine ⟨360892331512077685171578211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 481189775349436913562104281 360892331512077685171578211)
          ·
            refine ⟨541338497268116527757367317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 360892331512077685171578211 541338497268116527757367317)
            ·
              refine ⟨25375242059442962238626593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 541338497268116527757367317 25375242059442962238626593)
              ·
                refine ⟨19031431544582221678969945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25375242059442962238626593 19031431544582221678969945)
                ·
                  refine ⟨14273573658436666259227459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19031431544582221678969945 14273573658436666259227459)
                  ·
                    refine ⟨21410360487654999388841189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14273573658436666259227459 21410360487654999388841189)
                    ·
                      refine ⟨4014442591435312385407723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21410360487654999388841189 4014442591435312385407723)
                      ·
                        rfl

theorem cell23_7818099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 6, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 6, 2, 2, 1, 4].length) (baseStart_7818099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7818099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7818099 prefixEnd_7818099 := by exact prefixLift 7818099
  have htrace : WordTrace (prefixWord ++ tailWord_7818099) baseStart_7818099 baseEnd_7818099 := by
    simpa [prefixWord, tailWord_7818099, baseEnd_7818099] using wordTrace_append hprefix tailTrace_7818099
  have hstable : (prefixWord ++ tailWord_7818099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7818099).length < 2 ^ (prefixWord ++ tailWord_7818099).sum := by decide
  have hdescent : baseEnd_7818099 < baseStart_7818099 := by decide
  rcases family_descends (prefixWord ++ tailWord_7818099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7818112 : List Nat := [2, 1, 1, 2, 1, 2, 2, 1, 4, 1, 6]
def baseStart_7818112 : Nat := 118140960795 + 7818112 * 2 ^ 59
def prefixEnd_7818112 : Nat := 4983230072969 + 3 ^ 40 * 7818112 * 2
def baseEnd_7818112 : Nat := 4014449266683820834545163

theorem tailTrace_7818112 : CollatzResearch.WordTrace tailWord_7818112 prefixEnd_7818112 4014449266683820834545163 := by
  unfold tailWord_7818112
  simp only [CollatzResearch.WordTrace]
  refine ⟨142574985326161463035920295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190099980434881950714560393 142574985326161463035920295)
  ·
    refine ⟨213862477989242194553880443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142574985326161463035920295 213862477989242194553880443)
    ·
      refine ⟨320793716983863291830820665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213862477989242194553880443 320793716983863291830820665)
      ·
        refine ⟨240595287737897468873115499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 320793716983863291830820665 240595287737897468873115499)
        ·
          refine ⟨360892931606846203309673249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 240595287737897468873115499 360892931606846203309673249)
          ·
            refine ⟨270669698705134652482254937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 360892931606846203309673249 270669698705134652482254937)
            ·
              refine ⟨203002274028850989361691203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 270669698705134652482254937 203002274028850989361691203)
              ·
                refine ⟨304503411043276484042536805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 203002274028850989361691203 304503411043276484042536805)
                ·
                  refine ⟨57094389570614340757975651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 304503411043276484042536805 57094389570614340757975651)
                  ·
                    refine ⟨85641584355921511136963477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 57094389570614340757975651 85641584355921511136963477)
                    ·
                      refine ⟨4014449266683820834545163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 85641584355921511136963477 4014449266683820834545163)
                      ·
                        rfl

theorem cell23_7818112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 1, 4, 1, 6].length) (baseStart_7818112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7818112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7818112 prefixEnd_7818112 := by exact prefixLift 7818112
  have htrace : WordTrace (prefixWord ++ tailWord_7818112) baseStart_7818112 baseEnd_7818112 := by
    simpa [prefixWord, tailWord_7818112, baseEnd_7818112] using wordTrace_append hprefix tailTrace_7818112
  have hstable : (prefixWord ++ tailWord_7818112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7818112).length < 2 ^ (prefixWord ++ tailWord_7818112).sum := by decide
  have hdescent : baseEnd_7818112 < baseStart_7818112 := by decide
  rcases family_descends (prefixWord ++ tailWord_7818112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7818130 : List Nat := [3, 2, 3, 2, 3, 1, 1, 1, 2, 5]
def baseStart_7818130 : Nat := 118140960795 + 7818130 * 2 ^ 59
def prefixEnd_7818130 : Nat := 4983230072969 + 3 ^ 40 * 7818130 * 2
def baseEnd_7818130 : Nat := 1338152836445200588040027

theorem tailTrace_7818130 : CollatzResearch.WordTrace tailWord_7818130 prefixEnd_7818130 1338152836445200588040027 := by
  unfold tailWord_7818130
  simp only [CollatzResearch.WordTrace]
  refine ⟨71287656791564428786498961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 190100418110838476763997229 71287656791564428786498961)
  ·
    refine ⟨53465742593673321589874221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71287656791564428786498961 53465742593673321589874221)
    ·
      refine ⟨20049653472627495596202833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53465742593673321589874221 20049653472627495596202833)
      ·
        refine ⟨15037240104470621697152125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20049653472627495596202833 15037240104470621697152125)
        ·
          refine ⟨5638965039176483136432047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15037240104470621697152125 5638965039176483136432047)
          ·
            refine ⟨8458447558764724704648071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5638965039176483136432047 8458447558764724704648071)
            ·
              refine ⟨12687671338147087056972107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8458447558764724704648071 12687671338147087056972107)
              ·
                refine ⟨19031507007220630585458161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12687671338147087056972107 19031507007220630585458161)
                ·
                  refine ⟨14273630255415472939093621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19031507007220630585458161 14273630255415472939093621)
                  ·
                    refine ⟨1338152836445200588040027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14273630255415472939093621 1338152836445200588040027)
                    ·
                      rfl

theorem cell23_7818130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 3, 1, 1, 1, 2, 5].length) (baseStart_7818130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7818130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7818130 prefixEnd_7818130 := by exact prefixLift 7818130
  have htrace : WordTrace (prefixWord ++ tailWord_7818130) baseStart_7818130 baseEnd_7818130 := by
    simpa [prefixWord, tailWord_7818130, baseEnd_7818130] using wordTrace_append hprefix tailTrace_7818130
  have hstable : (prefixWord ++ tailWord_7818130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7818130).length < 2 ^ (prefixWord ++ tailWord_7818130).sum := by decide
  have hdescent : baseEnd_7818130 < baseStart_7818130 := by decide
  rcases family_descends (prefixWord ++ tailWord_7818130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7818143 : List Nat := [1, 1, 2, 5, 2, 1, 1, 5, 1, 4]
def baseStart_7818143 : Nat := 118140960795 + 7818143 * 2 ^ 59
def prefixEnd_7818143 : Nat := 4983230072969 + 3 ^ 40 * 7818143 * 2
def baseEnd_7818143 : Nat := 1338155061528036737752507

theorem tailTrace_7818143 : CollatzResearch.WordTrace tailWord_7818143 prefixEnd_7818143 1338155061528036737752507 := by
  unfold tailWord_7818143
  simp only [CollatzResearch.WordTrace]
  refine ⟨285151101315210618366219083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190100734210140412244146055 285151101315210618366219083)
  ·
    refine ⟨427726651972815927549328625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285151101315210618366219083 427726651972815927549328625)
    ·
      refine ⟨320794988979611945661996469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 427726651972815927549328625 320794988979611945661996469)
      ·
        refine ⟨30074530216838619905812169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 320794988979611945661996469 30074530216838619905812169)
        ·
          refine ⟨22555897662628964929359127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30074530216838619905812169 22555897662628964929359127)
          ·
            refine ⟨33833846493943447394038691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22555897662628964929359127 33833846493943447394038691)
            ·
              refine ⟨50750769740915171091058037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33833846493943447394038691 50750769740915171091058037)
              ·
                refine ⟨4757884663210797289786691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 50750769740915171091058037 4757884663210797289786691)
                ·
                  refine ⟨7136826994816195934680037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4757884663210797289786691 7136826994816195934680037)
                  ·
                    refine ⟨1338155061528036737752507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7136826994816195934680037 1338155061528036737752507)
                    ·
                      rfl

theorem cell23_7818143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 1, 5, 1, 4].length) (baseStart_7818143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7818143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7818143 prefixEnd_7818143 := by exact prefixLift 7818143
  have htrace : WordTrace (prefixWord ++ tailWord_7818143) baseStart_7818143 baseEnd_7818143 := by
    simpa [prefixWord, tailWord_7818143, baseEnd_7818143] using wordTrace_append hprefix tailTrace_7818143
  have hstable : (prefixWord ++ tailWord_7818143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7818143).length < 2 ^ (prefixWord ++ tailWord_7818143).sum := by decide
  have hdescent : baseEnd_7818143 < baseStart_7818143 := by decide
  rcases family_descends (prefixWord ++ tailWord_7818143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7818173 : List Nat := [1, 4, 1, 2, 4, 1, 3, 1, 6]
def baseStart_7818173 : Nat := 118140960795 + 7818173 * 2 ^ 59
def prefixEnd_7818173 : Nat := 4983230072969 + 3 ^ 40 * 7818173 * 2
def baseEnd_7818173 : Nat := 446053398778193899542487

theorem tailTrace_7818173 : CollatzResearch.WordTrace tailWord_7818173 prefixEnd_7818173 446053398778193899542487 := by
  unfold tailWord_7818173
  simp only [CollatzResearch.WordTrace]
  refine ⟨285152195505101933489811173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190101463670067955659874115 285152195505101933489811173)
  ·
    refine ⟨53466036657206612529339595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 285152195505101933489811173 53466036657206612529339595)
    ·
      refine ⟨80199054985809918794009393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53466036657206612529339595 80199054985809918794009393)
      ·
        refine ⟨60149291239357439095507045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80199054985809918794009393 60149291239357439095507045)
        ·
          refine ⟨11277992107379519830407571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 60149291239357439095507045 11277992107379519830407571)
          ·
            refine ⟨16916988161069279745611357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11277992107379519830407571 16916988161069279745611357)
            ·
              refine ⟨6343870560400979904604259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16916988161069279745611357 6343870560400979904604259)
              ·
                refine ⟨9515805840601469856906389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6343870560400979904604259 9515805840601469856906389)
                ·
                  refine ⟨446053398778193899542487, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9515805840601469856906389 446053398778193899542487)
                  ·
                    rfl

theorem cell23_7818173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 3, 1, 6].length) (baseStart_7818173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7818173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7818173 prefixEnd_7818173 := by exact prefixLift 7818173
  have htrace : WordTrace (prefixWord ++ tailWord_7818173) baseStart_7818173 baseEnd_7818173 := by
    simpa [prefixWord, tailWord_7818173, baseEnd_7818173] using wordTrace_append hprefix tailTrace_7818173
  have hstable : (prefixWord ++ tailWord_7818173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7818173).length < 2 ^ (prefixWord ++ tailWord_7818173).sum := by decide
  have hdescent : baseEnd_7818173 < baseStart_7818173 := by decide
  rcases family_descends (prefixWord ++ tailWord_7818173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7818176 : List Nat := [2, 1, 1, 2, 3, 3, 1, 2, 1, 5, 2]
def baseStart_7818176 : Nat := 118140960795 + 7818176 * 2 ^ 59
def prefixEnd_7818176 : Nat := 4983230072969 + 3 ^ 40 * 7818176 * 2
def baseEnd_7818176 : Nat := 4014482129445708584144869

theorem tailTrace_7818176 : CollatzResearch.WordTrace tailWord_7818176 prefixEnd_7818176 4014482129445708584144869 := by
  unfold tailWord_7818176
  simp only [CollatzResearch.WordTrace]
  refine ⟨142576152462045532501085191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190101536616060710001446921 142576152462045532501085191)
  ·
    refine ⟨213864228693068298751627787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142576152462045532501085191 213864228693068298751627787)
    ·
      refine ⟨320796343039602448127441681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213864228693068298751627787 320796343039602448127441681)
      ·
        refine ⟨240597257279701836095581261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 320796343039602448127441681 240597257279701836095581261)
        ·
          refine ⟨90223971479888188535842973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 240597257279701836095581261 90223971479888188535842973)
          ·
            refine ⟨33833989304958070700941115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 90223971479888188535842973 33833989304958070700941115)
            ·
              refine ⟨50750983957437106051411673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33833989304958070700941115 50750983957437106051411673)
              ·
                refine ⟨38063237968077829538558755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50750983957437106051411673 38063237968077829538558755)
                ·
                  refine ⟨57094856952116744307838133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38063237968077829538558755 57094856952116744307838133)
                  ·
                    refine ⟨5352642839260944778859825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 57094856952116744307838133 5352642839260944778859825)
                    ·
                      refine ⟨4014482129445708584144869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5352642839260944778859825 4014482129445708584144869)
                      ·
                        rfl

theorem cell23_7818176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 1, 2, 1, 5, 2].length) (baseStart_7818176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7818176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7818176 prefixEnd_7818176 := by exact prefixLift 7818176
  have htrace : WordTrace (prefixWord ++ tailWord_7818176) baseStart_7818176 baseEnd_7818176 := by
    simpa [prefixWord, tailWord_7818176, baseEnd_7818176] using wordTrace_append hprefix tailTrace_7818176
  have hstable : (prefixWord ++ tailWord_7818176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7818176).length < 2 ^ (prefixWord ++ tailWord_7818176).sum := by decide
  have hdescent : baseEnd_7818176 < baseStart_7818176 := by decide
  rcases family_descends (prefixWord ++ tailWord_7818176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7818200 : List Nat := [2, 1, 2, 2, 2, 3, 3, 3, 1, 1, 3]
def baseStart_7818200 : Nat := 118140960795 + 7818200 * 2 ^ 59
def prefixEnd_7818200 : Nat := 4983230072969 + 3 ^ 40 * 7818200 * 2
def baseEnd_7818200 : Nat := 4014494452981416490244759

theorem tailTrace_7818200 : CollatzResearch.WordTrace tailWord_7818200 prefixEnd_7818200 4014494452981416490244759 := by
  unfold tailWord_7818200
  simp only [CollatzResearch.WordTrace]
  refine ⟨142576590138002058550522027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190102120184002744734029369 142576590138002058550522027)
  ·
    refine ⟨213864885207003087825783041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142576590138002058550522027 213864885207003087825783041)
    ·
      refine ⟨160398663905252315869337281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 213864885207003087825783041 160398663905252315869337281)
      ·
        refine ⟨120298997928939236902002961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 160398663905252315869337281 120298997928939236902002961)
        ·
          refine ⟨90224248446704427676502221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120298997928939236902002961 90224248446704427676502221)
          ·
            refine ⟨33834093167514160378688333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 90224248446704427676502221 33834093167514160378688333)
            ·
              refine ⟨12687784937817810142008125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33834093167514160378688333 12687784937817810142008125)
              ·
                refine ⟨4757919351681678803253047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12687784937817810142008125 4757919351681678803253047)
                ·
                  refine ⟨7136879027522518204879571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4757919351681678803253047 7136879027522518204879571)
                  ·
                    refine ⟨10705318541283777307319357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7136879027522518204879571 10705318541283777307319357)
                    ·
                      refine ⟨4014494452981416490244759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10705318541283777307319357 4014494452981416490244759)
                      ·
                        rfl

theorem cell23_7818200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 3, 3, 1, 1, 3].length) (baseStart_7818200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7818200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7818200 prefixEnd_7818200 := by exact prefixLift 7818200
  have htrace : WordTrace (prefixWord ++ tailWord_7818200) baseStart_7818200 baseEnd_7818200 := by
    simpa [prefixWord, tailWord_7818200, baseEnd_7818200] using wordTrace_append hprefix tailTrace_7818200
  have hstable : (prefixWord ++ tailWord_7818200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7818200).length < 2 ^ (prefixWord ++ tailWord_7818200).sum := by decide
  have hdescent : baseEnd_7818200 < baseStart_7818200 := by decide
  rcases family_descends (prefixWord ++ tailWord_7818200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7818210 : List Nat := [3, 3, 3, 1, 1, 1, 1, 1, 4, 3, 2]
def baseStart_7818210 : Nat := 118140960795 + 7818210 * 2 ^ 59
def prefixEnd_7818210 : Nat := 4983230072969 + 3 ^ 40 * 7818210 * 2
def baseEnd_7818210 : Nat := 4014499587787961451119713

theorem tailTrace_7818210 : CollatzResearch.WordTrace tailWord_7818210 prefixEnd_7818210 4014499587787961451119713 := by
  unfold tailWord_7818210
  simp only [CollatzResearch.WordTrace]
  refine ⟨71288386251491972202227021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 190102363337311925872605389 71288386251491972202227021)
  ·
    refine ⟨26733144844309489575835133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71288386251491972202227021 26733144844309489575835133)
    ·
      refine ⟨10024929316616058590938175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26733144844309489575835133 10024929316616058590938175)
      ·
        refine ⟨15037393974924087886407263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10024929316616058590938175 15037393974924087886407263)
        ·
          refine ⟨22556090962386131829610895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15037393974924087886407263 22556090962386131829610895)
          ·
            refine ⟨33834136443579197744416343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22556090962386131829610895 33834136443579197744416343)
            ·
              refine ⟨50751204665368796616624515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33834136443579197744416343 50751204665368796616624515)
              ·
                refine ⟨76126806998053194924936773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50751204665368796616624515 76126806998053194924936773)
                ·
                  refine ⟨14273776312134974048425645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 76126806998053194924936773 14273776312134974048425645)
                  ·
                    refine ⟨5352666117050615268159617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14273776312134974048425645 5352666117050615268159617)
                    ·
                      refine ⟨4014499587787961451119713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5352666117050615268159617 4014499587787961451119713)
                      ·
                        rfl

theorem cell23_7818210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 1, 1, 4, 3, 2].length) (baseStart_7818210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7818210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7818210 prefixEnd_7818210 := by exact prefixLift 7818210
  have htrace : WordTrace (prefixWord ++ tailWord_7818210) baseStart_7818210 baseEnd_7818210 := by
    simpa [prefixWord, tailWord_7818210, baseEnd_7818210] using wordTrace_append hprefix tailTrace_7818210
  have hstable : (prefixWord ++ tailWord_7818210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7818210).length < 2 ^ (prefixWord ++ tailWord_7818210).sum := by decide
  have hdescent : baseEnd_7818210 < baseStart_7818210 := by decide
  rcases family_descends (prefixWord ++ tailWord_7818210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7818216 : List Nat := [2, 1, 4, 1, 1, 1, 4, 1, 4, 4]
def baseStart_7818216 : Nat := 118140960795 + 7818216 * 2 ^ 59
def prefixEnd_7818216 : Nat := 4983230072969 + 3 ^ 40 * 7818216 * 2
def baseEnd_7818216 : Nat := 1338167556223962809214895

theorem tailTrace_7818216 : CollatzResearch.WordTrace tailWord_7818216 prefixEnd_7818216 1338167556223962809214895 := by
  unfold tailWord_7818216
  simp only [CollatzResearch.WordTrace]
  refine ⟨142576881921973075916813251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190102509229297434555751001 142576881921973075916813251)
  ·
    refine ⟨213865322882959613875219877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142576881921973075916813251 213865322882959613875219877)
    ·
      refine ⟨40099748040554927601603727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 213865322882959613875219877 40099748040554927601603727)
      ·
        refine ⟨60149622060832391402405591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40099748040554927601603727 60149622060832391402405591)
        ·
          refine ⟨90224433091248587103608387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60149622060832391402405591 90224433091248587103608387)
          ·
            refine ⟨135336649636872880655412581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90224433091248587103608387 135336649636872880655412581)
            ·
              refine ⟨25375621806913665122889859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 135336649636872880655412581 25375621806913665122889859)
              ·
                refine ⟨38063432710370497684334789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25375621806913665122889859 38063432710370497684334789)
                ·
                  refine ⟨7136893633194468315812773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38063432710370497684334789 7136893633194468315812773)
                  ·
                    refine ⟨1338167556223962809214895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7136893633194468315812773 1338167556223962809214895)
                    ·
                      rfl

theorem cell23_7818216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 4, 1, 4, 4].length) (baseStart_7818216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7818216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7818216 prefixEnd_7818216 := by exact prefixLift 7818216
  have htrace : WordTrace (prefixWord ++ tailWord_7818216) baseStart_7818216 baseEnd_7818216 := by
    simpa [prefixWord, tailWord_7818216, baseEnd_7818216] using wordTrace_append hprefix tailTrace_7818216
  have hstable : (prefixWord ++ tailWord_7818216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7818216).length < 2 ^ (prefixWord ++ tailWord_7818216).sum := by decide
  have hdescent : baseEnd_7818216 < baseStart_7818216 := by decide
  rcases family_descends (prefixWord ++ tailWord_7818216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7818274 : List Nat := [3, 3, 1, 1, 1, 3, 4, 2, 1, 2, 2]
def baseStart_7818274 : Nat := 118140960795 + 7818274 * 2 ^ 59
def prefixEnd_7818274 : Nat := 4983230072969 + 3 ^ 40 * 7818274 * 2
def baseEnd_7818274 : Nat := 4014532450549849200719419

theorem tailTrace_7818274 : CollatzResearch.WordTrace tailWord_7818274 prefixEnd_7818274 4014532450549849200719419 := by
  unfold tailWord_7818274
  simp only [CollatzResearch.WordTrace]
  refine ⟨71288969819434006934809469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 190103919518490685159491917 71288969819434006934809469)
  ·
    refine ⟨26733363682287752600553551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71288969819434006934809469 26733363682287752600553551)
    ·
      refine ⟨40100045523431628900830327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26733363682287752600553551 40100045523431628900830327)
      ·
        refine ⟨60150068285147443351245491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40100045523431628900830327 60150068285147443351245491)
        ·
          refine ⟨90225102427721165026868237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60150068285147443351245491 90225102427721165026868237)
          ·
            refine ⟨33834413410395436885075589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 90225102427721165026868237 33834413410395436885075589)
            ·
              refine ⟨6343952514449144415951673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33834413410395436885075589 6343952514449144415951673)
              ·
                refine ⟨4757964385836858311963755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6343952514449144415951673 4757964385836858311963755)
                ·
                  refine ⟨7136946578755287467945633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4757964385836858311963755 7136946578755287467945633)
                  ·
                    refine ⟨5352709934066465600959225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7136946578755287467945633 5352709934066465600959225)
                    ·
                      refine ⟨4014532450549849200719419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5352709934066465600959225 4014532450549849200719419)
                      ·
                        rfl

theorem cell23_7818274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 4, 2, 1, 2, 2].length) (baseStart_7818274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7818274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7818274 prefixEnd_7818274 := by exact prefixLift 7818274
  have htrace : WordTrace (prefixWord ++ tailWord_7818274) baseStart_7818274 baseEnd_7818274 := by
    simpa [prefixWord, tailWord_7818274, baseEnd_7818274] using wordTrace_append hprefix tailTrace_7818274
  have hstable : (prefixWord ++ tailWord_7818274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7818274).length < 2 ^ (prefixWord ++ tailWord_7818274).sum := by decide
  have hdescent : baseEnd_7818274 < baseStart_7818274 := by decide
  rcases family_descends (prefixWord ++ tailWord_7818274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7818276 : List Nat := [2, 3, 1, 4, 1, 1, 1, 1, 2, 7]
def baseStart_7818276 : Nat := 118140960795 + 7818276 * 2 ^ 59
def prefixEnd_7818276 : Nat := 4983230072969 + 3 ^ 40 * 7818276 * 2
def baseEnd_7818276 : Nat := 1338177825837052730964803

theorem tailTrace_7818276 : CollatzResearch.WordTrace tailWord_7818276 prefixEnd_7818276 1338177825837052730964803 := by
  unfold tailWord_7818276
  simp only [CollatzResearch.WordTrace]
  refine ⟨142577976111864391040405341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190103968149152521387207121 142577976111864391040405341)
  ·
    refine ⟨53466741041949146640152003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 142577976111864391040405341 53466741041949146640152003)
    ·
      refine ⟨80200111562923719960228005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53466741041949146640152003 80200111562923719960228005)
      ·
        refine ⟨15037520918048197492542751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 80200111562923719960228005 15037520918048197492542751)
        ·
          refine ⟨22556281377072296238814127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15037520918048197492542751 22556281377072296238814127)
          ·
            refine ⟨33834422065608444358221191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22556281377072296238814127 33834422065608444358221191)
            ·
              refine ⟨50751633098412666537331787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33834422065608444358221191 50751633098412666537331787)
              ·
                refine ⟨76127449647618999805997681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50751633098412666537331787 76127449647618999805997681)
                ·
                  refine ⟨57095587235714249854498261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 76127449647618999805997681 57095587235714249854498261)
                  ·
                    refine ⟨1338177825837052730964803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 57095587235714249854498261 1338177825837052730964803)
                    ·
                      rfl

theorem cell23_7818276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 1, 1, 2, 7].length) (baseStart_7818276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7818276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7818276 prefixEnd_7818276 := by exact prefixLift 7818276
  have htrace : WordTrace (prefixWord ++ tailWord_7818276) baseStart_7818276 baseEnd_7818276 := by
    simpa [prefixWord, tailWord_7818276, baseEnd_7818276] using wordTrace_append hprefix tailTrace_7818276
  have hstable : (prefixWord ++ tailWord_7818276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7818276).length < 2 ^ (prefixWord ++ tailWord_7818276).sum := by decide
  have hdescent : baseEnd_7818276 < baseStart_7818276 := by decide
  rcases family_descends (prefixWord ++ tailWord_7818276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7818317 : List Nat := [1, 6, 1, 1, 1, 3, 1, 3, 1, 3, 2]
def baseStart_7818317 : Nat := 118140960795 + 7818317 * 2 ^ 59
def prefixEnd_7818317 : Nat := 4983230072969 + 3 ^ 40 * 7818317 * 2
def baseEnd_7818317 : Nat := 4014554530217992532481721

theorem tailTrace_7818317 : CollatzResearch.WordTrace tailWord_7818317 prefixEnd_7818317 4014554530217992532481721 := by
  unfold tailWord_7818317
  simp only [CollatzResearch.WordTrace]
  refine ⟨285157447616580246083053205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190104965077720164055368803 285157447616580246083053205)
  ·
    refine ⟨13366755357027199035143119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 285157447616580246083053205 13366755357027199035143119)
    ·
      refine ⟨20050133035540798552714679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13366755357027199035143119 20050133035540798552714679)
      ·
        refine ⟨30075199553311197829072019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20050133035540798552714679 30075199553311197829072019)
        ·
          refine ⟨45112799329966796743608029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30075199553311197829072019 45112799329966796743608029)
          ·
            refine ⟨16917299748737548778853011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45112799329966796743608029 16917299748737548778853011)
            ·
              refine ⟨25375949623106323168279517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16917299748737548778853011 25375949623106323168279517)
              ·
                refine ⟨9515981108664871188104819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25375949623106323168279517 9515981108664871188104819)
                ·
                  refine ⟨14273971662997306782157229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9515981108664871188104819 14273971662997306782157229)
                  ·
                    refine ⟨5352739373623990043308961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14273971662997306782157229 5352739373623990043308961)
                    ·
                      refine ⟨4014554530217992532481721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5352739373623990043308961 4014554530217992532481721)
                      ·
                        rfl

theorem cell23_7818317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 1, 3, 1, 3, 2].length) (baseStart_7818317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7818317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7818317 prefixEnd_7818317 := by exact prefixLift 7818317
  have htrace : WordTrace (prefixWord ++ tailWord_7818317) baseStart_7818317 baseEnd_7818317 := by
    simpa [prefixWord, tailWord_7818317, baseEnd_7818317] using wordTrace_append hprefix tailTrace_7818317
  have hstable : (prefixWord ++ tailWord_7818317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7818317).length < 2 ^ (prefixWord ++ tailWord_7818317).sum := by decide
  have hdescent : baseEnd_7818317 < baseStart_7818317 := by decide
  rcases family_descends (prefixWord ++ tailWord_7818317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7818329 : List Nat := [1, 2, 1, 2, 2, 1, 2, 1, 1, 1, 9]
def baseStart_7818329 : Nat := 118140960795 + 7818329 * 2 ^ 59
def prefixEnd_7818329 : Nat := 4983230072969 + 3 ^ 40 * 7818329 * 2
def baseEnd_7818329 : Nat := 4014560691985846485531665

theorem tailTrace_7818329 : CollatzResearch.WordTrace tailWord_7818329 prefixEnd_7818329 4014560691985846485531665 := by
  unfold tailWord_7818329
  simp only [CollatzResearch.WordTrace]
  refine ⟨285157885292536772132490041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190105256861691181421660027 285157885292536772132490041)
  ·
    refine ⟨213868413969402579099367531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 285157885292536772132490041 213868413969402579099367531)
    ·
      refine ⟨320802620954103868649051297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213868413969402579099367531 320802620954103868649051297)
      ·
        refine ⟨240601965715577901486788473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 320802620954103868649051297 240601965715577901486788473)
        ·
          refine ⟨180451474286683426115091355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 240601965715577901486788473 180451474286683426115091355)
          ·
            refine ⟨270677211430025139172637033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 180451474286683426115091355 270677211430025139172637033)
            ·
              refine ⟨203007908572518854379477775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 270677211430025139172637033 203007908572518854379477775)
              ·
                refine ⟨304511862858778281569216663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 203007908572518854379477775 304511862858778281569216663)
                ·
                  refine ⟨456767794288167422353824995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 304511862858778281569216663 456767794288167422353824995)
                  ·
                    refine ⟨685151691432251133530737493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 456767794288167422353824995 685151691432251133530737493)
                    ·
                      refine ⟨4014560691985846485531665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 685151691432251133530737493 4014560691985846485531665)
                      ·
                        rfl

theorem cell23_7818329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 1, 1, 1, 9].length) (baseStart_7818329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7818329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7818329 prefixEnd_7818329 := by exact prefixLift 7818329
  have htrace : WordTrace (prefixWord ++ tailWord_7818329) baseStart_7818329 baseEnd_7818329 := by
    simpa [prefixWord, tailWord_7818329, baseEnd_7818329] using wordTrace_append hprefix tailTrace_7818329
  have hstable : (prefixWord ++ tailWord_7818329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7818329).length < 2 ^ (prefixWord ++ tailWord_7818329).sum := by decide
  have hdescent : baseEnd_7818329 < baseStart_7818329 := by decide
  rcases family_descends (prefixWord ++ tailWord_7818329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7818330 : List Nat := [3, 1, 1, 2, 1, 1, 2, 6, 2, 2, 2]
def baseStart_7818330 : Nat := 118140960795 + 7818330 * 2 ^ 59
def prefixEnd_7818330 : Nat := 4983230072969 + 3 ^ 40 * 7818330 * 2
def baseEnd_7818330 : Nat := 4014561205466500981619161

theorem tailTrace_7818330 : CollatzResearch.WordTrace tailWord_7818330 prefixEnd_7818330 4014561205466500981619161 := by
  unfold tailWord_7818330
  simp only [CollatzResearch.WordTrace]
  refine ⟨71289480441383287325819111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 190105281177022099535517629 71289480441383287325819111)
  ·
    refine ⟨106934220662074930988728667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71289480441383287325819111 106934220662074930988728667)
    ·
      refine ⟨160401330993112396483093001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106934220662074930988728667 160401330993112396483093001)
      ·
        refine ⟨120300998244834297362319751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 160401330993112396483093001 120300998244834297362319751)
        ·
          refine ⟨180451497367251446043479627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120300998244834297362319751 180451497367251446043479627)
          ·
            refine ⟨270677246050877169065219441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 180451497367251446043479627 270677246050877169065219441)
            ·
              refine ⟨203007934538157876798914581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 270677246050877169065219441 203007934538157876798914581)
              ·
                refine ⟨9515996931476150474949121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 203007934538157876798914581 9515996931476150474949121)
                ·
                  refine ⟨7136997698607112856211841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9515996931476150474949121 7136997698607112856211841)
                  ·
                    refine ⟨5352748273955334642158881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7136997698607112856211841 5352748273955334642158881)
                    ·
                      refine ⟨4014561205466500981619161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5352748273955334642158881 4014561205466500981619161)
                      ·
                        rfl

theorem cell23_7818330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 6, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 6, 2, 2, 2].length) (baseStart_7818330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7818330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7818330 prefixEnd_7818330 := by exact prefixLift 7818330
  have htrace : WordTrace (prefixWord ++ tailWord_7818330) baseStart_7818330 baseEnd_7818330 := by
    simpa [prefixWord, tailWord_7818330, baseEnd_7818330] using wordTrace_append hprefix tailTrace_7818330
  have hstable : (prefixWord ++ tailWord_7818330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7818330).length < 2 ^ (prefixWord ++ tailWord_7818330).sum := by decide
  have hdescent : baseEnd_7818330 < baseStart_7818330 := by decide
  rcases family_descends (prefixWord ++ tailWord_7818330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7818336 : List Nat := [2, 1, 1, 3, 2, 2, 4, 1, 7]
def baseStart_7818336 : Nat := 118140960795 + 7818336 * 2 ^ 59
def prefixEnd_7818336 : Nat := 4983230072969 + 3 ^ 40 * 7818336 * 2
def baseEnd_7818336 : Nat := 446062698483380884238237

theorem tailTrace_7818336 : CollatzResearch.WordTrace tailWord_7818336 prefixEnd_7818336 446062698483380884238237 := by
  unfold tailWord_7818336
  simp only [CollatzResearch.WordTrace]
  refine ⟨142579070301755706163997431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190105427069007608218663241 142579070301755706163997431)
  ·
    refine ⟨213868605452633559245996147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142579070301755706163997431 213868605452633559245996147)
    ·
      refine ⟨320802908178950338868994221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213868605452633559245996147 320802908178950338868994221)
      ·
        refine ⟨120301090567106377075872833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 320802908178950338868994221 120301090567106377075872833)
        ·
          refine ⟨90225817925329782806904625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120301090567106377075872833 90225817925329782806904625)
          ·
            refine ⟨67669363443997337105178469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90225817925329782806904625 67669363443997337105178469)
            ·
              refine ⟨12688005645749500707220963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 67669363443997337105178469 12688005645749500707220963)
              ·
                refine ⟨19032008468624251060831445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12688005645749500707220963 19032008468624251060831445)
                ·
                  refine ⟨446062698483380884238237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19032008468624251060831445 446062698483380884238237)
                  ·
                    rfl

theorem cell23_7818336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 4, 1, 7].length) (baseStart_7818336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7818336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7818336 prefixEnd_7818336 := by exact prefixLift 7818336
  have htrace : WordTrace (prefixWord ++ tailWord_7818336) baseStart_7818336 baseEnd_7818336 := by
    simpa [prefixWord, tailWord_7818336, baseEnd_7818336] using wordTrace_append hprefix tailTrace_7818336
  have hstable : (prefixWord ++ tailWord_7818336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7818336).length < 2 ^ (prefixWord ++ tailWord_7818336).sum := by decide
  have hdescent : baseEnd_7818336 < baseStart_7818336 := by decide
  rcases family_descends (prefixWord ++ tailWord_7818336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7818403 : List Nat := [1, 1, 1, 4, 1, 1, 1, 5, 2, 4, 2]
def baseStart_7818403 : Nat := 118140960795 + 7818403 * 2 ^ 59
def prefixEnd_7818403 : Nat := 4983230072969 + 3 ^ 40 * 7818403 * 2
def baseEnd_7818403 : Nat := 4014598689554279196006325

theorem tailTrace_7818403 : CollatzResearch.WordTrace tailWord_7818403 prefixEnd_7818403 4014598689554279196006325 := by
  unfold tailWord_7818403
  simp only [CollatzResearch.WordTrace]
  refine ⟨285160584294268682770683863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190107056196179121847122575 285160584294268682770683863)
  ·
    refine ⟨427740876441403024156025795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285160584294268682770683863 427740876441403024156025795)
    ·
      refine ⟨641611314662104536234038693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 427740876441403024156025795 641611314662104536234038693)
      ·
        refine ⟨120302121499144600543882255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 641611314662104536234038693 120302121499144600543882255)
        ·
          refine ⟨180453182248716900815823383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120302121499144600543882255 180453182248716900815823383)
          ·
            refine ⟨270679773373075351223735075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 180453182248716900815823383 270679773373075351223735075)
            ·
              refine ⟨406019660059613026835602613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 270679773373075351223735075 406019660059613026835602613)
              ·
                refine ⟨38064343130588721265837745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 406019660059613026835602613 38064343130588721265837745)
                ·
                  refine ⟨28548257347941540949378309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38064343130588721265837745 28548257347941540949378309)
                  ·
                    refine ⟨5352798252739038928008433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28548257347941540949378309 5352798252739038928008433)
                    ·
                      refine ⟨4014598689554279196006325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5352798252739038928008433 4014598689554279196006325)
                      ·
                        rfl

theorem cell23_7818403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 5, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 5, 2, 4, 2].length) (baseStart_7818403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7818403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7818403 prefixEnd_7818403 := by exact prefixLift 7818403
  have htrace : WordTrace (prefixWord ++ tailWord_7818403) baseStart_7818403 baseEnd_7818403 := by
    simpa [prefixWord, tailWord_7818403, baseEnd_7818403] using wordTrace_append hprefix tailTrace_7818403
  have hstable : (prefixWord ++ tailWord_7818403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7818403).length < 2 ^ (prefixWord ++ tailWord_7818403).sum := by decide
  have hdescent : baseEnd_7818403 < baseStart_7818403 := by decide
  rcases family_descends (prefixWord ++ tailWord_7818403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7818438 : List Nat := [6, 1, 2, 2, 1, 2, 2, 2, 5]
def baseStart_7818438 : Nat := 118140960795 + 7818438 * 2 ^ 59
def prefixEnd_7818438 : Nat := 4983230072969 + 3 ^ 40 * 7818438 * 2
def baseEnd_7818438 : Nat := 446068517930798506563185

theorem tailTrace_7818438 : CollatzResearch.WordTrace tailWord_7818438 prefixEnd_7818438 446068517930798506563185 := by
  unfold tailWord_7818438
  simp only [CollatzResearch.WordTrace]
  refine ⟨8911308151535683867131499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 190107907232761255832138645 8911308151535683867131499)
  ·
    refine ⟨13366962227303525800697249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8911308151535683867131499 13366962227303525800697249)
    ·
      refine ⟨10025221670477644350522937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13366962227303525800697249 10025221670477644350522937)
      ·
        refine ⟨7518916252858233262892203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10025221670477644350522937 7518916252858233262892203)
        ·
          refine ⟨11278374379287349894338305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7518916252858233262892203 11278374379287349894338305)
          ·
            refine ⟨8458780784465512420753729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11278374379287349894338305 8458780784465512420753729)
            ·
              refine ⟨6344085588349134315565297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8458780784465512420753729 6344085588349134315565297)
              ·
                refine ⟨4758064191261850736673973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6344085588349134315565297 4758064191261850736673973)
                ·
                  refine ⟨446068517930798506563185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4758064191261850736673973 446068517930798506563185)
                  ·
                    rfl

theorem cell23_7818438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 2, 2, 2, 5].length) (baseStart_7818438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7818438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7818438 prefixEnd_7818438 := by exact prefixLift 7818438
  have htrace : WordTrace (prefixWord ++ tailWord_7818438) baseStart_7818438 baseEnd_7818438 := by
    simpa [prefixWord, tailWord_7818438, baseEnd_7818438] using wordTrace_append hprefix tailTrace_7818438
  have hstable : (prefixWord ++ tailWord_7818438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7818438).length < 2 ^ (prefixWord ++ tailWord_7818438).sum := by decide
  have hdescent : baseEnd_7818438 < baseStart_7818438 := by decide
  rcases family_descends (prefixWord ++ tailWord_7818438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7818454 : List Nat := [5, 2, 1, 2, 2, 1, 1, 1, 2, 4, 2]
def baseStart_7818454 : Nat := 118140960795 + 7818454 * 2 ^ 59
def prefixEnd_7818454 : Nat := 4983230072969 + 3 ^ 40 * 7818454 * 2
def baseEnd_7818454 : Nat := 4014624877067658496468591

theorem tailTrace_7818454 : CollatzResearch.WordTrace tailWord_7818454 prefixEnd_7818454 4014624877067658496468591 := by
  unfold tailWord_7818454
  simp only [CollatzResearch.WordTrace]
  refine ⟨17822652776067744905049401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 190108296278055945653860277 17822652776067744905049401)
  ·
    refine ⟨13366989582050808678787051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17822652776067744905049401 13366989582050808678787051)
    ·
      refine ⟨20050484373076213018180577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13366989582050808678787051 20050484373076213018180577)
      ·
        refine ⟨15037863279807159763635433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20050484373076213018180577 15037863279807159763635433)
        ·
          refine ⟨11278397459855369822726575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15037863279807159763635433 11278397459855369822726575)
          ·
            refine ⟨16917596189783054734089863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11278397459855369822726575 16917596189783054734089863)
            ·
              refine ⟨25376394284674582101134795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16917596189783054734089863 25376394284674582101134795)
              ·
                refine ⟨38064591427011873151702193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25376394284674582101134795 38064591427011873151702193)
                ·
                  refine ⟨28548443570258904863776645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38064591427011873151702193 28548443570258904863776645)
                  ·
                    refine ⟨5352833169423544661958121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28548443570258904863776645 5352833169423544661958121)
                    ·
                      refine ⟨4014624877067658496468591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5352833169423544661958121 4014624877067658496468591)
                      ·
                        rfl

theorem cell23_7818454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 1, 1, 2, 4, 2].length) (baseStart_7818454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7818454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7818454 prefixEnd_7818454 := by exact prefixLift 7818454
  have htrace : WordTrace (prefixWord ++ tailWord_7818454) baseStart_7818454 baseEnd_7818454 := by
    simpa [prefixWord, tailWord_7818454, baseEnd_7818454] using wordTrace_append hprefix tailTrace_7818454
  have hstable : (prefixWord ++ tailWord_7818454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7818454).length < 2 ^ (prefixWord ++ tailWord_7818454).sum := by decide
  have hdescent : baseEnd_7818454 < baseStart_7818454 := by decide
  rcases family_descends (prefixWord ++ tailWord_7818454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7818513 : List Nat := [1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 5]
def baseStart_7818513 : Nat := 118140960795 + 7818513 * 2 ^ 59
def prefixEnd_7818513 : Nat := 4983230072969 + 3 ^ 40 * 7818513 * 2
def baseEnd_7818513 : Nat := 4014655172426273765630819

theorem tailTrace_7818513 : CollatzResearch.WordTrace tailWord_7818513 prefixEnd_7818513 4014655172426273765630819 := by
  unfold tailWord_7818513
  simp only [CollatzResearch.WordTrace]
  refine ⟨285164596323870171557188193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190109730882580114371458795 285164596323870171557188193)
  ·
    refine ⟨213873447242902628667891145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 285164596323870171557188193 213873447242902628667891145)
    ·
      refine ⟨160405085432176971500918359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 213873447242902628667891145 160405085432176971500918359)
      ·
        refine ⟨240607628148265457251377539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160405085432176971500918359 240607628148265457251377539)
        ·
          refine ⟨360911442222398185877066309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 240607628148265457251377539 360911442222398185877066309)
          ·
            refine ⟨67670895416699659851949933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 360911442222398185877066309 67670895416699659851949933)
            ·
              refine ⟨25376585781262372444481225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67670895416699659851949933 25376585781262372444481225)
              ·
                refine ⟨19032439335946779333360919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25376585781262372444481225 19032439335946779333360919)
                ·
                  refine ⟨28548659003920169000041379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19032439335946779333360919 28548659003920169000041379)
                  ·
                    refine ⟨42822988505880253500062069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28548659003920169000041379 42822988505880253500062069)
                    ·
                      refine ⟨4014655172426273765630819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42822988505880253500062069 4014655172426273765630819)
                      ·
                        rfl

theorem cell23_7818513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 5].length) (baseStart_7818513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7818513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7818513 prefixEnd_7818513 := by exact prefixLift 7818513
  have htrace : WordTrace (prefixWord ++ tailWord_7818513) baseStart_7818513 baseEnd_7818513 := by
    simpa [prefixWord, tailWord_7818513, baseEnd_7818513] using wordTrace_append hprefix tailTrace_7818513
  have hstable : (prefixWord ++ tailWord_7818513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7818513).length < 2 ^ (prefixWord ++ tailWord_7818513).sum := by decide
  have hdescent : baseEnd_7818513 < baseStart_7818513 := by decide
  rcases family_descends (prefixWord ++ tailWord_7818513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7818520 : List Nat := [2, 1, 2, 3, 1, 5, 1, 1, 1, 6]
def baseStart_7818520 : Nat := 118140960795 + 7818520 * 2 ^ 59
def prefixEnd_7818520 : Nat := 4983230072969 + 3 ^ 40 * 7818520 * 2
def baseEnd_7818520 : Nat := 1338219588930285079414429

theorem tailTrace_7818520 : CollatzResearch.WordTrace tailWord_7818520 prefixEnd_7818520 1338219588930285079414429 := by
  unfold tailWord_7818520
  simp only [CollatzResearch.WordTrace]
  refine ⟨142582425817422405876346507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190109901089896541168462009 142582425817422405876346507)
  ·
    refine ⟨213873638726133608814519761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142582425817422405876346507 213873638726133608814519761)
    ·
      refine ⟨160405229044600206610889821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 213873638726133608814519761 160405229044600206610889821)
      ·
        refine ⟨60151960891725077479083683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 160405229044600206610889821 60151960891725077479083683)
        ·
          refine ⟨90227941337587616218625525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60151960891725077479083683 90227941337587616218625525)
          ·
            refine ⟨8458869500398839020496143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 90227941337587616218625525 8458869500398839020496143)
            ·
              refine ⟨12688304250598258530744215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8458869500398839020496143 12688304250598258530744215)
              ·
                refine ⟨19032456375897387796116323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12688304250598258530744215 19032456375897387796116323)
                ·
                  refine ⟨28548684563846081694174485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19032456375897387796116323 28548684563846081694174485)
                  ·
                    refine ⟨1338219588930285079414429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28548684563846081694174485 1338219588930285079414429)
                    ·
                      rfl

theorem cell23_7818520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 5, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 5, 1, 1, 1, 6].length) (baseStart_7818520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7818520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7818520 prefixEnd_7818520 := by exact prefixLift 7818520
  have htrace : WordTrace (prefixWord ++ tailWord_7818520) baseStart_7818520 baseEnd_7818520 := by
    simpa [prefixWord, tailWord_7818520, baseEnd_7818520] using wordTrace_append hprefix tailTrace_7818520
  have hstable : (prefixWord ++ tailWord_7818520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7818520).length < 2 ^ (prefixWord ++ tailWord_7818520).sum := by decide
  have hdescent : baseEnd_7818520 < baseStart_7818520 := by decide
  rcases family_descends (prefixWord ++ tailWord_7818520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7818527 : List Nat := [1, 1, 2, 4, 4, 1, 2, 2, 1, 1, 4]
def baseStart_7818527 : Nat := 118140960795 + 7818527 * 2 ^ 59
def prefixEnd_7818527 : Nat := 4983230072969 + 3 ^ 40 * 7818527 * 2
def baseEnd_7818527 : Nat := 4014662361155436710855755

theorem tailTrace_7818527 : CollatzResearch.WordTrace tailWord_7818527 prefixEnd_7818527 4014662361155436710855755 := by
  unfold tailWord_7818527
  simp only [CollatzResearch.WordTrace]
  refine ⟨285165106945819451948197835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190110071297212967965465223 285165106945819451948197835)
  ·
    refine ⟨427747660418729177922296753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285165106945819451948197835 427747660418729177922296753)
    ·
      refine ⟨320810745314046883441722565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 427747660418729177922296753 320810745314046883441722565)
      ·
        refine ⟨60152014746383790645322981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 320810745314046883441722565 60152014746383790645322981)
        ·
          refine ⟨11278502764946960745998059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 60152014746383790645322981 11278502764946960745998059)
          ·
            refine ⟨16917754147420441118997089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11278502764946960745998059 16917754147420441118997089)
            ·
              refine ⟨12688315610565330839247817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16917754147420441118997089 12688315610565330839247817)
              ·
                refine ⟨9516236707923998129435863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12688315610565330839247817 9516236707923998129435863)
                ·
                  refine ⟨14274355061885997194153795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9516236707923998129435863 14274355061885997194153795)
                  ·
                    refine ⟨21411532592828995791230693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14274355061885997194153795 21411532592828995791230693)
                    ·
                      refine ⟨4014662361155436710855755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21411532592828995791230693 4014662361155436710855755)
                      ·
                        rfl

theorem cell23_7818527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 2, 2, 1, 1, 4].length) (baseStart_7818527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7818527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7818527 prefixEnd_7818527 := by exact prefixLift 7818527
  have htrace : WordTrace (prefixWord ++ tailWord_7818527) baseStart_7818527 baseEnd_7818527 := by
    simpa [prefixWord, tailWord_7818527, baseEnd_7818527] using wordTrace_append hprefix tailTrace_7818527
  have hstable : (prefixWord ++ tailWord_7818527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7818527).length < 2 ^ (prefixWord ++ tailWord_7818527).sum := by decide
  have hdescent : baseEnd_7818527 < baseStart_7818527 := by decide
  rcases family_descends (prefixWord ++ tailWord_7818527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7818533 : List Nat := [1, 3, 1, 2, 4, 2, 1, 9]
def baseStart_7818533 : Nat := 118140960795 + 7818533 * 2 ^ 59
def prefixEnd_7818533 : Nat := 4983230072969 + 3 ^ 40 * 7818533 * 2
def baseEnd_7818533 : Nat := 148691312668124581014101

theorem tailTrace_7818533 : CollatzResearch.WordTrace tailWord_7818533 prefixEnd_7818533 148691312668124581014101 := by
  unfold tailWord_7818533
  simp only [CollatzResearch.WordTrace]
  refine ⟨285165325783797714972916253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190110217189198476648610835 285165325783797714972916253)
  ·
    refine ⟨106936997168924143114843595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 285165325783797714972916253 106936997168924143114843595)
    ·
      refine ⟨160405495753386214672265393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106936997168924143114843595 160405495753386214672265393)
      ·
        refine ⟨120304121815039661004199045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 160405495753386214672265393 120304121815039661004199045)
        ·
          refine ⟨22557022840319936438287321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 120304121815039661004199045 22557022840319936438287321)
          ·
            refine ⟨16917767130239952328715491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22557022840319936438287321 16917767130239952328715491)
            ·
              refine ⟨25376650695359928493073237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16917767130239952328715491 25376650695359928493073237)
              ·
                refine ⟨148691312668124581014101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 25376650695359928493073237 148691312668124581014101)
                ·
                  rfl

theorem cell23_7818533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 1, 9].length) (baseStart_7818533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7818533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7818533 prefixEnd_7818533 := by exact prefixLift 7818533
  have htrace : WordTrace (prefixWord ++ tailWord_7818533) baseStart_7818533 baseEnd_7818533 := by
    simpa [prefixWord, tailWord_7818533, baseEnd_7818533] using wordTrace_append hprefix tailTrace_7818533
  have hstable : (prefixWord ++ tailWord_7818533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7818533).length < 2 ^ (prefixWord ++ tailWord_7818533).sum := by decide
  have hdescent : baseEnd_7818533 < baseStart_7818533 := by decide
  rcases family_descends (prefixWord ++ tailWord_7818533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7818543 : List Nat := [1, 1, 2, 1, 2, 1, 3, 3, 3, 3, 3]
def baseStart_7818543 : Nat := 118140960795 + 7818543 * 2 ^ 59
def prefixEnd_7818543 : Nat := 4983230072969 + 3 ^ 40 * 7818543 * 2
def baseEnd_7818543 : Nat := 4014670576845908648255681

theorem tailTrace_7818543 : CollatzResearch.WordTrace tailWord_7818543 prefixEnd_7818543 4014670576845908648255681 := by
  unfold tailWord_7818543
  simp only [CollatzResearch.WordTrace]
  refine ⟨285165690513761486680780283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190110460342507657787186855 285165690513761486680780283)
  ·
    refine ⟨427748535770642230021170425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285165690513761486680780283 427748535770642230021170425)
    ·
      refine ⟨320811401827981672515877819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 427748535770642230021170425 320811401827981672515877819)
      ·
        refine ⟨481217102741972508773816729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 320811401827981672515877819 481217102741972508773816729)
        ·
          refine ⟨360912827056479381580362547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 481217102741972508773816729 360912827056479381580362547)
          ·
            refine ⟨541369240584719072370543821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 360912827056479381580362547 541369240584719072370543821)
            ·
              refine ⟨203013465219269652138953933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 541369240584719072370543821 203013465219269652138953933)
              ·
                refine ⟨76130049457226119552107725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 203013465219269652138953933 76130049457226119552107725)
                ·
                  refine ⟨28548768546459794832040397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 76130049457226119552107725 28548768546459794832040397)
                  ·
                    refine ⟨10705788204922423062015149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28548768546459794832040397 10705788204922423062015149)
                    ·
                      refine ⟨4014670576845908648255681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10705788204922423062015149 4014670576845908648255681)
                      ·
                        rfl

theorem cell23_7818543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 3, 3, 3, 3].length) (baseStart_7818543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7818543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7818543 prefixEnd_7818543 := by exact prefixLift 7818543
  have htrace : WordTrace (prefixWord ++ tailWord_7818543) baseStart_7818543 baseEnd_7818543 := by
    simpa [prefixWord, tailWord_7818543, baseEnd_7818543] using wordTrace_append hprefix tailTrace_7818543
  have hstable : (prefixWord ++ tailWord_7818543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7818543).length < 2 ^ (prefixWord ++ tailWord_7818543).sum := by decide
  have hdescent : baseEnd_7818543 < baseStart_7818543 := by decide
  rcases family_descends (prefixWord ++ tailWord_7818543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7818560 : List Nat := [2, 1, 1, 2, 2, 1, 3, 3, 4, 1, 3]
def baseStart_7818560 : Nat := 118140960795 + 7818560 * 2 ^ 59
def prefixEnd_7818560 : Nat := 4983230072969 + 3 ^ 40 * 7818560 * 2
def baseEnd_7818560 : Nat := 4014679306017035081743103

theorem tailTrace_7818560 : CollatzResearch.WordTrace tailWord_7818560 prefixEnd_7818560 4014679306017035081743103 := by
  unfold tailWord_7818560
  simp only [CollatzResearch.WordTrace]
  refine ⟨142583155277349949292074567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190110873703133265722766089 142583155277349949292074567)
  ·
    refine ⟨213874732916024923938111851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142583155277349949292074567 213874732916024923938111851)
    ·
      refine ⟨320812099374037385907167777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213874732916024923938111851 320812099374037385907167777)
      ·
        refine ⟨240609074530528039430375833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 320812099374037385907167777 240609074530528039430375833)
        ·
          refine ⟨180456805897896029572781875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 240609074530528039430375833 180456805897896029572781875)
          ·
            refine ⟨270685208846844044359172813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 180456805897896029572781875 270685208846844044359172813)
            ·
              refine ⟨101506953317566516634689805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 270685208846844044359172813 101506953317566516634689805)
              ·
                refine ⟨38065107494087443738008677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 101506953317566516634689805 38065107494087443738008677)
                ·
                  refine ⟨7137207655141395700876627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38065107494087443738008677 7137207655141395700876627)
                  ·
                    refine ⟨10705811482712093551314941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7137207655141395700876627 10705811482712093551314941)
                    ·
                      refine ⟨4014679306017035081743103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10705811482712093551314941 4014679306017035081743103)
                      ·
                        rfl

theorem cell23_7818560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 3, 4, 1, 3].length) (baseStart_7818560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7818560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7818560 prefixEnd_7818560 := by exact prefixLift 7818560
  have htrace : WordTrace (prefixWord ++ tailWord_7818560) baseStart_7818560 baseEnd_7818560 := by
    simpa [prefixWord, tailWord_7818560, baseEnd_7818560] using wordTrace_append hprefix tailTrace_7818560
  have hstable : (prefixWord ++ tailWord_7818560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7818560).length < 2 ^ (prefixWord ++ tailWord_7818560).sum := by decide
  have hdescent : baseEnd_7818560 < baseStart_7818560 := by decide
  rcases family_descends (prefixWord ++ tailWord_7818560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7818561 : List Nat := [1, 2, 5, 2, 1, 3, 1, 1, 3, 2, 2]
def baseStart_7818561 : Nat := 118140960795 + 7818561 * 2 ^ 59
def prefixEnd_7818561 : Nat := 4983230072969 + 3 ^ 40 * 7818561 * 2
def baseEnd_7818561 : Nat := 4014679819497689577830599

theorem tailTrace_7818561 : CollatzResearch.WordTrace tailWord_7818561 prefixEnd_7818561 4014679819497689577830599 := by
  unfold tailWord_7818561
  simp only [CollatzResearch.WordTrace]
  refine ⟨285166347027696275754935537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190110898018464183836623691 285166347027696275754935537)
  ·
    refine ⟨213874760270772206816201653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 285166347027696275754935537 213874760270772206816201653)
    ·
      refine ⟨20050758775384894389018905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 213874760270772206816201653 20050758775384894389018905)
      ·
        refine ⟨15038069081538670791764179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20050758775384894389018905 15038069081538670791764179)
        ·
          refine ⟨22557103622308006187646269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15038069081538670791764179 22557103622308006187646269)
          ·
            refine ⟨8458913858365502320367351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22557103622308006187646269 8458913858365502320367351)
            ·
              refine ⟨12688370787548253480551027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8458913858365502320367351 12688370787548253480551027)
              ·
                refine ⟨19032556181322380220826541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12688370787548253480551027 19032556181322380220826541)
                ·
                  refine ⟨7137208567995892582809953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19032556181322380220826541 7137208567995892582809953)
                  ·
                    refine ⟨5352906425996919437107465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7137208567995892582809953 5352906425996919437107465)
                    ·
                      refine ⟨4014679819497689577830599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5352906425996919437107465 4014679819497689577830599)
                      ·
                        rfl

theorem cell23_7818561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 3, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 3, 1, 1, 3, 2, 2].length) (baseStart_7818561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7818561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7818561 prefixEnd_7818561 := by exact prefixLift 7818561
  have htrace : WordTrace (prefixWord ++ tailWord_7818561) baseStart_7818561 baseEnd_7818561 := by
    simpa [prefixWord, tailWord_7818561, baseEnd_7818561] using wordTrace_append hprefix tailTrace_7818561
  have hstable : (prefixWord ++ tailWord_7818561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7818561).length < 2 ^ (prefixWord ++ tailWord_7818561).sum := by decide
  have hdescent : baseEnd_7818561 < baseStart_7818561 := by decide
  rcases family_descends (prefixWord ++ tailWord_7818561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7818577 : List Nat := [1, 2, 2, 1, 4, 1, 3, 3, 2, 1, 3]
def baseStart_7818577 : Nat := 118140960795 + 7818577 * 2 ^ 59
def prefixEnd_7818577 : Nat := 4983230072969 + 3 ^ 40 * 7818577 * 2
def baseEnd_7818577 : Nat := 4014688035188161515230525

theorem tailTrace_7818577 : CollatzResearch.WordTrace tailWord_7818577 prefixEnd_7818577 4014688035188161515230525 := by
  unfold tailWord_7818577
  simp only [CollatzResearch.WordTrace]
  refine ⟨285166930595638310487517985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190111287063758873658345323 285166930595638310487517985)
  ·
    refine ⟨213875197946728732865638489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 285166930595638310487517985 213875197946728732865638489)
    ·
      refine ⟨160406398460046549649228867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 213875197946728732865638489 160406398460046549649228867)
      ·
        refine ⟨240609597690069824473843301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160406398460046549649228867 240609597690069824473843301)
        ·
          refine ⟨45114299566888092088845619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 240609597690069824473843301 45114299566888092088845619)
          ·
            refine ⟨67671449350332138133268429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45114299566888092088845619 67671449350332138133268429)
            ·
              refine ⟨25376793506374551799975661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67671449350332138133268429 25376793506374551799975661)
              ·
                refine ⟨9516297564890456924990873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25376793506374551799975661 9516297564890456924990873)
                ·
                  refine ⟨7137223173667842693743155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9516297564890456924990873 7137223173667842693743155)
                  ·
                    refine ⟨10705834760501764040614733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7137223173667842693743155 10705834760501764040614733)
                    ·
                      refine ⟨4014688035188161515230525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10705834760501764040614733 4014688035188161515230525)
                      ·
                        rfl

theorem cell23_7818577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 3, 3, 2, 1, 3].length) (baseStart_7818577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7818577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7818577 prefixEnd_7818577 := by exact prefixLift 7818577
  have htrace : WordTrace (prefixWord ++ tailWord_7818577) baseStart_7818577 baseEnd_7818577 := by
    simpa [prefixWord, tailWord_7818577, baseEnd_7818577] using wordTrace_append hprefix tailTrace_7818577
  have hstable : (prefixWord ++ tailWord_7818577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7818577).length < 2 ^ (prefixWord ++ tailWord_7818577).sum := by decide
  have hdescent : baseEnd_7818577 < baseStart_7818577 := by decide
  rcases family_descends (prefixWord ++ tailWord_7818577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7818603 : List Nat := [1, 1, 1, 1, 2, 2, 2, 1, 3, 6, 3]
def baseStart_7818603 : Nat := 118140960795 + 7818603 * 2 ^ 59
def prefixEnd_7818603 : Nat := 4983230072969 + 3 ^ 40 * 7818603 * 2
def baseEnd_7818603 : Nat := 4014701385685178413505405

theorem tailTrace_7818603 : CollatzResearch.WordTrace tailWord_7818603 prefixEnd_7818603 4014701385685178413505405 := by
  unfold tailWord_7818603
  simp only [CollatzResearch.WordTrace]
  refine ⟨285167878893544116927964463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190111919262362744618642975 285167878893544116927964463)
  ·
    refine ⟨427751818340316175391946695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285167878893544116927964463 427751818340316175391946695)
    ·
      refine ⟨641627727510474263087920043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 427751818340316175391946695 641627727510474263087920043)
      ·
        refine ⟨962441591265711394631880065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 641627727510474263087920043 962441591265711394631880065)
        ·
          refine ⟨721831193449283545973910049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 962441591265711394631880065 721831193449283545973910049)
          ·
            refine ⟨541373395086962659480432537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 721831193449283545973910049 541373395086962659480432537)
            ·
              refine ⟨406030046315221994610324403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 541373395086962659480432537 406030046315221994610324403)
              ·
                refine ⟨609045069472832991915486605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 406030046315221994610324403 609045069472832991915486605)
                ·
                  refine ⟨228391901052312371968307477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 609045069472832991915486605 228391901052312371968307477)
                  ·
                    refine ⟨10705870361827142436014413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 228391901052312371968307477 10705870361827142436014413)
                    ·
                      refine ⟨4014701385685178413505405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10705870361827142436014413 4014701385685178413505405)
                      ·
                        rfl

theorem cell23_7818603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 1, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 1, 3, 6, 3].length) (baseStart_7818603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7818603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7818603 prefixEnd_7818603 := by exact prefixLift 7818603
  have htrace : WordTrace (prefixWord ++ tailWord_7818603) baseStart_7818603 baseEnd_7818603 := by
    simpa [prefixWord, tailWord_7818603, baseEnd_7818603] using wordTrace_append hprefix tailTrace_7818603
  have hstable : (prefixWord ++ tailWord_7818603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7818603).length < 2 ^ (prefixWord ++ tailWord_7818603).sum := by decide
  have hdescent : baseEnd_7818603 < baseStart_7818603 := by decide
  rcases family_descends (prefixWord ++ tailWord_7818603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7818617 : List Nat := [1, 2, 1, 3, 2, 1, 2, 3, 4, 2, 2]
def baseStart_7818617 : Nat := 118140960795 + 7818617 * 2 ^ 59
def prefixEnd_7818617 : Nat := 4983230072969 + 3 ^ 40 * 7818617 * 2
def baseEnd_7818617 : Nat := 4014708574414341358730341

theorem tailTrace_7818617 : CollatzResearch.WordTrace tailWord_7818617 prefixEnd_7818617 4014708574414341358730341 := by
  unfold tailWord_7818617
  simp only [CollatzResearch.WordTrace]
  refine ⟨285168389515493397318974105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190112259676995598212649403 285168389515493397318974105)
  ·
    refine ⟨213876292136620047989230579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 285168389515493397318974105 213876292136620047989230579)
    ·
      refine ⟨320814438204930071983845869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213876292136620047989230579 320814438204930071983845869)
      ·
        refine ⟨120305414326848776993942201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 320814438204930071983845869 120305414326848776993942201)
        ·
          refine ⟨90229060745136582745456651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120305414326848776993942201 90229060745136582745456651)
          ·
            refine ⟨135343591117704874118184977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90229060745136582745456651 135343591117704874118184977)
            ·
              refine ⟨101507693338278655588638733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 135343591117704874118184977 101507693338278655588638733)
              ·
                refine ⟨38065385001854495845739525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 101507693338278655588638733 38065385001854495845739525)
                ·
                  refine ⟨7137259687847717971076161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38065385001854495845739525 7137259687847717971076161)
                  ·
                    refine ⟨5352944765885788478307121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7137259687847717971076161 5352944765885788478307121)
                    ·
                      refine ⟨4014708574414341358730341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5352944765885788478307121 4014708574414341358730341)
                      ·
                        rfl

theorem cell23_7818617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 3, 4, 2, 2].length) (baseStart_7818617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7818617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7818617 prefixEnd_7818617 := by exact prefixLift 7818617
  have htrace : WordTrace (prefixWord ++ tailWord_7818617) baseStart_7818617 baseEnd_7818617 := by
    simpa [prefixWord, tailWord_7818617, baseEnd_7818617] using wordTrace_append hprefix tailTrace_7818617
  have hstable : (prefixWord ++ tailWord_7818617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7818617).length < 2 ^ (prefixWord ++ tailWord_7818617).sum := by decide
  have hdescent : baseEnd_7818617 < baseStart_7818617 := by decide
  rcases family_descends (prefixWord ++ tailWord_7818617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7818650 : List Nat := [3, 1, 1, 4, 1, 1, 1, 2, 1, 5, 3]
def baseStart_7818650 : Nat := 118140960795 + 7818650 * 2 ^ 59
def prefixEnd_7818650 : Nat := 4983230072969 + 3 ^ 40 * 7818650 * 2
def baseEnd_7818650 : Nat := 4014725519275939729617689

theorem tailTrace_7818650 : CollatzResearch.WordTrace tailWord_7818650 prefixEnd_7818650 4014725519275939729617689 := by
  unfold tailWord_7818650
  simp only [CollatzResearch.WordTrace]
  refine ⟨71292398281093460988731351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 190113062082915895969950269 71292398281093460988731351)
  ·
    refine ⟨106938597421640191483097027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71292398281093460988731351 106938597421640191483097027)
    ·
      refine ⟨160407896132460287224645541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106938597421640191483097027 160407896132460287224645541)
      ·
        refine ⟨30076480524836303854621039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 160407896132460287224645541 30076480524836303854621039)
        ·
          refine ⟨45114720787254455781931559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30076480524836303854621039 45114720787254455781931559)
          ·
            refine ⟨67672081180881683672897339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45114720787254455781931559 67672081180881683672897339)
            ·
              refine ⟨101508121771322525509346009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67672081180881683672897339 101508121771322525509346009)
              ·
                refine ⟨76131091328491894132009507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 101508121771322525509346009 76131091328491894132009507)
                ·
                  refine ⟨114196636992737841198014261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 76131091328491894132009507 114196636992737841198014261)
                  ·
                    refine ⟨10705934718069172612313837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 114196636992737841198014261 10705934718069172612313837)
                    ·
                      refine ⟨4014725519275939729617689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10705934718069172612313837 4014725519275939729617689)
                      ·
                        rfl

theorem cell23_7818650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 2, 1, 5, 3].length) (baseStart_7818650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7818650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7818650 prefixEnd_7818650 := by exact prefixLift 7818650
  have htrace : WordTrace (prefixWord ++ tailWord_7818650) baseStart_7818650 baseEnd_7818650 := by
    simpa [prefixWord, tailWord_7818650, baseEnd_7818650] using wordTrace_append hprefix tailTrace_7818650
  have hstable : (prefixWord ++ tailWord_7818650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7818650).length < 2 ^ (prefixWord ++ tailWord_7818650).sum := by decide
  have hdescent : baseEnd_7818650 < baseStart_7818650 := by decide
  rcases family_descends (prefixWord ++ tailWord_7818650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7818727 : List Nat := [1, 1, 5, 2, 1, 2, 1, 1, 4, 2, 3]
def baseStart_7818727 : Nat := 118140960795 + 7818727 * 2 ^ 59
def prefixEnd_7818727 : Nat := 4983230072969 + 3 ^ 40 * 7818727 * 2
def baseEnd_7818727 : Nat := 4014765057286335928354835

theorem tailTrace_7818727 : CollatzResearch.WordTrace tailWord_7818727 prefixEnd_7818727 4014765057286335928354835 := by
  unfold tailWord_7818727
  simp only [CollatzResearch.WordTrace]
  refine ⟨285172401545094886105478435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190114934363396590736985623 285172401545094886105478435)
  ·
    refine ⟨427758602317642329158217653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285172401545094886105478435 427758602317642329158217653)
    ·
      refine ⟨40102368967278968358582905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 427758602317642329158217653 40102368967278968358582905)
      ·
        refine ⟨30076776725459226268937179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40102368967278968358582905 30076776725459226268937179)
        ·
          refine ⟨45115165088188839403405769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30076776725459226268937179 45115165088188839403405769)
          ·
            refine ⟨33836373816141629552554327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45115165088188839403405769 33836373816141629552554327)
            ·
              refine ⟨50754560724212444328831491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33836373816141629552554327 50754560724212444328831491)
              ·
                refine ⟨76131841086318666493247237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50754560724212444328831491 76131841086318666493247237)
                ·
                  refine ⟨14274720203684749967483857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 76131841086318666493247237 14274720203684749967483857)
                  ·
                    refine ⟨10706040152763562475612893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14274720203684749967483857 10706040152763562475612893)
                    ·
                      refine ⟨4014765057286335928354835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10706040152763562475612893 4014765057286335928354835)
                      ·
                        rfl

theorem cell23_7818727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 1, 1, 4, 2, 3].length) (baseStart_7818727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7818727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7818727 prefixEnd_7818727 := by exact prefixLift 7818727
  have htrace : WordTrace (prefixWord ++ tailWord_7818727) baseStart_7818727 baseEnd_7818727 := by
    simpa [prefixWord, tailWord_7818727, baseEnd_7818727] using wordTrace_append hprefix tailTrace_7818727
  have hstable : (prefixWord ++ tailWord_7818727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7818727).length < 2 ^ (prefixWord ++ tailWord_7818727).sum := by decide
  have hdescent : baseEnd_7818727 < baseStart_7818727 := by decide
  rcases family_descends (prefixWord ++ tailWord_7818727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7818757 : List Nat := [1, 3, 1, 1, 2, 2, 1, 3, 5, 1, 3]
def baseStart_7818757 : Nat := 118140960795 + 7818757 * 2 ^ 59
def prefixEnd_7818757 : Nat := 4983230072969 + 3 ^ 40 * 7818757 * 2
def baseEnd_7818757 : Nat := 4014780461705970810979697

theorem tailTrace_7818757 : CollatzResearch.WordTrace tailWord_7818757 prefixEnd_7818757 4014780461705970810979697 := by
  unfold tailWord_7818757
  simp only [CollatzResearch.WordTrace]
  refine ⟨285173495734986201229070525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190115663823324134152713683 285173495734986201229070525)
  ·
    refine ⟨106940060900619825460901447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 285173495734986201229070525 106940060900619825460901447)
    ·
      refine ⟨160410091350929738191352171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106940060900619825460901447 160410091350929738191352171)
      ·
        refine ⟨240615137026394607287028257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160410091350929738191352171 240615137026394607287028257)
        ·
          refine ⟨180461352769795955465271193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 240615137026394607287028257 180461352769795955465271193)
          ·
            refine ⟨135346014577346966598953395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 180461352769795955465271193 135346014577346966598953395)
            ·
              refine ⟨203019021866020449898430093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 135346014577346966598953395 203019021866020449898430093)
              ·
                refine ⟨76132133199757668711911285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 203019021866020449898430093 76132133199757668711911285)
                ·
                  refine ⟨7137387487477281441741683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 76132133199757668711911285 7137387487477281441741683)
                  ·
                    refine ⟨10706081231215922162612525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7137387487477281441741683 10706081231215922162612525)
                    ·
                      refine ⟨4014780461705970810979697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10706081231215922162612525 4014780461705970810979697)
                      ·
                        rfl

theorem cell23_7818757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 3, 5, 1, 3].length) (baseStart_7818757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7818757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7818757 prefixEnd_7818757 := by exact prefixLift 7818757
  have htrace : WordTrace (prefixWord ++ tailWord_7818757) baseStart_7818757 baseEnd_7818757 := by
    simpa [prefixWord, tailWord_7818757, baseEnd_7818757] using wordTrace_append hprefix tailTrace_7818757
  have hstable : (prefixWord ++ tailWord_7818757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7818757).length < 2 ^ (prefixWord ++ tailWord_7818757).sum := by decide
  have hdescent : baseEnd_7818757 < baseStart_7818757 := by decide
  rcases family_descends (prefixWord ++ tailWord_7818757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7818800 : List Nat := [2, 1, 1, 1, 2, 3, 1, 3, 3, 1, 5]
def baseStart_7818800 : Nat := 118140960795 + 7818800 * 2 ^ 59
def prefixEnd_7818800 : Nat := 4983230072969 + 3 ^ 40 * 7818800 * 2
def baseEnd_7818800 : Nat := 4014802541374114142741999

theorem tailTrace_7818800 : CollatzResearch.WordTrace tailWord_7818800 prefixEnd_7818800 4014802541374114142741999 := by
  unfold tailWord_7818800
  simp only [CollatzResearch.WordTrace]
  refine ⟨142587532036915209786442927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190116709382553613048590569 142587532036915209786442927)
  ·
    refine ⟨213881298055372814679664391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142587532036915209786442927 213881298055372814679664391)
    ·
      refine ⟨320821947083059222019496587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213881298055372814679664391 320821947083059222019496587)
      ·
        refine ⟨481232920624588833029244881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 320821947083059222019496587 481232920624588833029244881)
        ·
          refine ⟨360924690468441624771933661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 481232920624588833029244881 360924690468441624771933661)
          ·
            refine ⟨135346758925665609289475123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 360924690468441624771933661 135346758925665609289475123)
            ·
              refine ⟨203020138388498413934212685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 135346758925665609289475123 203020138388498413934212685)
              ·
                refine ⟨76132551895686905225329757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 203020138388498413934212685 76132551895686905225329757)
                ·
                  refine ⟨28549706960882589459498659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 76132551895686905225329757 28549706960882589459498659)
                  ·
                    refine ⟨42824560441323884189247989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28549706960882589459498659 42824560441323884189247989)
                    ·
                      refine ⟨4014802541374114142741999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42824560441323884189247989 4014802541374114142741999)
                      ·
                        rfl

theorem cell23_7818800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 3, 3, 1, 5].length) (baseStart_7818800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7818800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7818800 prefixEnd_7818800 := by exact prefixLift 7818800
  have htrace : WordTrace (prefixWord ++ tailWord_7818800) baseStart_7818800 baseEnd_7818800 := by
    simpa [prefixWord, tailWord_7818800, baseEnd_7818800] using wordTrace_append hprefix tailTrace_7818800
  have hstable : (prefixWord ++ tailWord_7818800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7818800).length < 2 ^ (prefixWord ++ tailWord_7818800).sum := by decide
  have hdescent : baseEnd_7818800 < baseStart_7818800 := by decide
  rcases family_descends (prefixWord ++ tailWord_7818800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7818807 : List Nat := [1, 1, 3, 1, 2, 5, 2, 1, 1, 6]
def baseStart_7818807 : Nat := 118140960795 + 7818807 * 2 ^ 59
def prefixEnd_7818807 : Nat := 4983230072969 + 3 ^ 40 * 7818807 * 2
def baseEnd_7818807 : Nat := 1338268711912898538451489

theorem tailTrace_7818807 : CollatzResearch.WordTrace tailWord_7818807 prefixEnd_7818807 1338268711912898538451489 := by
  unfold tailWord_7818807
  simp only [CollatzResearch.WordTrace]
  refine ⟨285175319384805059768390675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190116879589870039845593783 285175319384805059768390675)
  ·
    refine ⟨427762979077207589652586013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285175319384805059768390675 427762979077207589652586013)
    ·
      refine ⟨160411117153952846119719755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 427762979077207589652586013 160411117153952846119719755)
      ·
        refine ⟨240616675730929269179579633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160411117153952846119719755 240616675730929269179579633)
        ·
          refine ⟨180462506798196951884684725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 240616675730929269179579633 180462506798196951884684725)
          ·
            refine ⟨16918360012330964239189193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 180462506798196951884684725 16918360012330964239189193)
            ·
              refine ⟨12688770009248223179391895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16918360012330964239189193 12688770009248223179391895)
              ·
                refine ⟨19033155013872334769087843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12688770009248223179391895 19033155013872334769087843)
                ·
                  refine ⟨28549732520808502153631765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19033155013872334769087843 28549732520808502153631765)
                  ·
                    refine ⟨1338268711912898538451489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28549732520808502153631765 1338268711912898538451489)
                    ·
                      rfl

theorem cell23_7818807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 2, 1, 1, 6].length) (baseStart_7818807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7818807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7818807 prefixEnd_7818807 := by exact prefixLift 7818807
  have htrace : WordTrace (prefixWord ++ tailWord_7818807) baseStart_7818807 baseEnd_7818807 := by
    simpa [prefixWord, tailWord_7818807, baseEnd_7818807] using wordTrace_append hprefix tailTrace_7818807
  have hstable : (prefixWord ++ tailWord_7818807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7818807).length < 2 ^ (prefixWord ++ tailWord_7818807).sum := by decide
  have hdescent : baseEnd_7818807 < baseStart_7818807 := by decide
  rcases family_descends (prefixWord ++ tailWord_7818807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7818840 : List Nat := [2, 1, 2, 2, 1, 2, 1, 2, 2, 2, 6]
def baseStart_7818840 : Nat := 118140960795 + 7818840 * 2 ^ 59
def prefixEnd_7818840 : Nat := 4983230072969 + 3 ^ 40 * 7818840 * 2
def baseEnd_7818840 : Nat := 4014823080600293986241815

theorem tailTrace_7818840 : CollatzResearch.WordTrace tailWord_7818840 prefixEnd_7818840 4014823080600293986241815 := by
  unfold tailWord_7818840
  simp only [CollatzResearch.WordTrace]
  refine ⟨142588261496842753202170987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190117681995790337602894649 142588261496842753202170987)
  ·
    refine ⟨213882392245264129803256481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142588261496842753202170987 213882392245264129803256481)
    ·
      refine ⟨160411794183948097352442361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 213882392245264129803256481 160411794183948097352442361)
      ·
        refine ⟨120308845637961073014331771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 160411794183948097352442361 120308845637961073014331771)
        ·
          refine ⟨180463268456941609521497657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120308845637961073014331771 180463268456941609521497657)
          ·
            refine ⟨135347451342706207141123243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 180463268456941609521497657 135347451342706207141123243)
            ·
              refine ⟨203021177014059310711684865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 135347451342706207141123243 203021177014059310711684865)
              ·
                refine ⟨152265882760544483033763649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 203021177014059310711684865 152265882760544483033763649)
                ·
                  refine ⟨114199412070408362275322737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 152265882760544483033763649 114199412070408362275322737)
                  ·
                    refine ⟨85649559052806271706492053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 114199412070408362275322737 85649559052806271706492053)
                    ·
                      refine ⟨4014823080600293986241815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 85649559052806271706492053 4014823080600293986241815)
                      ·
                        rfl

theorem cell23_7818840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 2, 2, 2, 6].length) (baseStart_7818840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7818840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7818840 prefixEnd_7818840 := by exact prefixLift 7818840
  have htrace : WordTrace (prefixWord ++ tailWord_7818840) baseStart_7818840 baseEnd_7818840 := by
    simpa [prefixWord, tailWord_7818840, baseEnd_7818840] using wordTrace_append hprefix tailTrace_7818840
  have hstable : (prefixWord ++ tailWord_7818840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7818840).length < 2 ^ (prefixWord ++ tailWord_7818840).sum := by decide
  have hdescent : baseEnd_7818840 < baseStart_7818840 := by decide
  rcases family_descends (prefixWord ++ tailWord_7818840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7818861 : List Nat := [1, 5, 1, 1, 4, 2, 1, 1, 1, 2, 4]
def baseStart_7818861 : Nat := 118140960795 + 7818861 * 2 ^ 59
def prefixEnd_7818861 : Nat := 4983230072969 + 3 ^ 40 * 7818861 * 2
def baseEnd_7818861 : Nat := 4014833863694038404079219

theorem tailTrace_7818861 : CollatzResearch.WordTrace tailWord_7818861 prefixEnd_7818861 4014833863694038404079219 := by
  unfold tailWord_7818861
  simp only [CollatzResearch.WordTrace]
  refine ⟨285177288926609426990856437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190118192617739617993904291 285177288926609426990856437)
  ·
    refine ⟨26735370836869633780392791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 285177288926609426990856437 26735370836869633780392791)
    ·
      refine ⟨40103056255304450670589187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26735370836869633780392791 40103056255304450670589187)
      ·
        refine ⟨60154584382956676005883781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40103056255304450670589187 60154584382956676005883781)
        ·
          refine ⟨11278984571804376751103209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 60154584382956676005883781 11278984571804376751103209)
          ·
            refine ⟨8459238428853282563327407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11278984571804376751103209 8459238428853282563327407)
            ·
              refine ⟨12688857643279923844991111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8459238428853282563327407 12688857643279923844991111)
              ·
                refine ⟨19033286464919885767486667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12688857643279923844991111 19033286464919885767486667)
                ·
                  refine ⟨28549929697379828651230001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19033286464919885767486667 28549929697379828651230001)
                  ·
                    refine ⟨21412447273034871488422501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28549929697379828651230001 21412447273034871488422501)
                    ·
                      refine ⟨4014833863694038404079219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21412447273034871488422501 4014833863694038404079219)
                      ·
                        rfl

theorem cell23_7818861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 2, 1, 1, 1, 2, 4].length) (baseStart_7818861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7818861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7818861 prefixEnd_7818861 := by exact prefixLift 7818861
  have htrace : WordTrace (prefixWord ++ tailWord_7818861) baseStart_7818861 baseEnd_7818861 := by
    simpa [prefixWord, tailWord_7818861, baseEnd_7818861] using wordTrace_append hprefix tailTrace_7818861
  have hstable : (prefixWord ++ tailWord_7818861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7818861).length < 2 ^ (prefixWord ++ tailWord_7818861).sum := by decide
  have hdescent : baseEnd_7818861 < baseStart_7818861 := by decide
  rcases family_descends (prefixWord ++ tailWord_7818861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7818864 : List Nat := [2, 1, 1, 1, 6, 1, 3, 1, 1, 3, 3]
def baseStart_7818864 : Nat := 118140960795 + 7818864 * 2 ^ 59
def prefixEnd_7818864 : Nat := 4983230072969 + 3 ^ 40 * 7818864 * 2
def baseEnd_7818864 : Nat := 4014835404136001892341705

theorem tailTrace_7818864 : CollatzResearch.WordTrace tailWord_7818864 prefixEnd_7818864 4014835404136001892341705 := by
  unfold tailWord_7818864
  simp only [CollatzResearch.WordTrace]
  refine ⟨142588699172799279251607823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190118265563732372335477097 142588699172799279251607823)
  ·
    refine ⟨213883048759198918877411735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142588699172799279251607823 213883048759198918877411735)
    ·
      refine ⟨320824573138798378316117603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213883048759198918877411735 320824573138798378316117603)
      ·
        refine ⟨481236859708197567474176405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 320824573138798378316117603 481236859708197567474176405)
        ·
          refine ⟨22557977798821760975352019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 481236859708197567474176405 22557977798821760975352019)
          ·
            refine ⟨33836966698232641463028029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22557977798821760975352019 33836966698232641463028029)
            ·
              refine ⟨12688862511837240548635511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33836966698232641463028029 12688862511837240548635511)
              ·
                refine ⟨19033293767755860822953267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12688862511837240548635511 19033293767755860822953267)
                ·
                  refine ⟨28549940651633791234429901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19033293767755860822953267 28549940651633791234429901)
                  ·
                    refine ⟨10706227744362671712911213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28549940651633791234429901 10706227744362671712911213)
                    ·
                      refine ⟨4014835404136001892341705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10706227744362671712911213 4014835404136001892341705)
                      ·
                        rfl

theorem cell23_7818864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 3, 1, 1, 3, 3].length) (baseStart_7818864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7818864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7818864 prefixEnd_7818864 := by exact prefixLift 7818864
  have htrace : WordTrace (prefixWord ++ tailWord_7818864) baseStart_7818864 baseEnd_7818864 := by
    simpa [prefixWord, tailWord_7818864, baseEnd_7818864] using wordTrace_append hprefix tailTrace_7818864
  have hstable : (prefixWord ++ tailWord_7818864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7818864).length < 2 ^ (prefixWord ++ tailWord_7818864).sum := by decide
  have hdescent : baseEnd_7818864 < baseStart_7818864 := by decide
  rcases family_descends (prefixWord ++ tailWord_7818864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
